(* ========================================================================= *)
(* System of tactics (slightly different from any traditional LCF method).   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2012                         *)
(* ========================================================================= *)

needs "tactic_types.ml";;

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

let (inst_goal:instantiation->goal->goal) =
  fun p (thms,w) ->
    map (I F_F INSTANTIATE_ALL p) thms,instantiate p w;;

(* ------------------------------------------------------------------------- *)
(* Perform a sequential composition (left first) of instantiations.          *)
(* ------------------------------------------------------------------------- *)

let (compose_insts :instantiation->instantiation->instantiation) =
  fun (pats1,tmin1,tyin1) ((pats2,tmin2,tyin2) as i2) ->
    let tmin = map (instantiate i2 F_F inst tyin2) tmin1
    and tyin = map (type_subst tyin2 F_F I) tyin1 in
    let tmin' = filter (fun (_,x) -> not (can (rev_assoc x) tmin)) tmin2
    and tyin' = filter (fun (_,a) -> not (can (rev_assoc a) tyin)) tyin2 in
    pats1@pats2,tmin@tmin',tyin@tyin';;

(* ------------------------------------------------------------------------- *)
(* Construct A,_FALSITY_ |- p; contortion so falsity is the last element.    *)
(* ------------------------------------------------------------------------- *)

let _FALSITY_ = new_definition `_FALSITY_ = F`;;

let mk_fthm =
  let pth = UNDISCH(fst(EQ_IMP_RULE _FALSITY_))
  and qth = ASSUME `_FALSITY_` in
  fun (asl,c) -> PROVE_HYP qth (itlist ADD_ASSUM (rev asl) (CONTR c pth));;

(* ------------------------------------------------------------------------- *)
(* Validity checking of tactics. This cannot be 100% accurate without making *)
(* arbitrary theorems, but "mk_fthm" brings us quite close.                  *)
(* ------------------------------------------------------------------------- *)

let (VALID:tactic->tactic) =
  let fake_thm (asl,w) =
    let asms = itlist (union o hyp o snd) asl [] in
    mk_fthm(asms,w)
  and false_tm = `_FALSITY_` in
  fun tac (asl,w) ->
    let ((mvs,i),gls,just,_ as res) = tac (asl,w) in
    let ths = map fake_thm gls in
    let asl',w' = dest_thm(just null_inst ths) in
    let asl'',w'' = inst_goal i (asl,w) in
    let maxasms =
      itlist (fun (_,th) -> union (insert (concl th) (hyp th))) asl'' [] in
    if aconv w' w'' &
       forall (fun t -> exists (aconv t) maxasms) (subtract asl' [false_tm])
    then res else failwith "VALID: Invalid tactic";;

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

let (THEN),(THENL) =
  let propagate_empty i [] = []
  and propagate_thm th i [] = INSTANTIATE_ALL i th in
  let compose_justs n just1 just2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 i ths1)::(just2 i ths2) in
  let rec seqapply l1 l2 = match (l1,l2) with
     ([],[]) -> null_meta,[],propagate_empty,[]
   | ((tac:tactic)::tacs),((goal:goal)::goals) ->
            let ((mvs1,insts1),gls1,just1,rosebud) = tac goal in
            let goals' = map (inst_goal insts1) goals in
            let ((mvs2,insts2),gls2,just2,rosebuds) = seqapply tacs goals' in
            (union mvs1 mvs2,compose_insts insts1 insts2),
            gls1@gls2,
            compose_justs (length gls1) just1 just2,
            rosebud::rosebuds
   | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence ((mvs1,insts1),gls1,just1,rosebud) tacl =
    let ((mvs2,insts2),gls2,just2,rosebuds) = seqapply tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    (union mvs1 mvs2,compose_insts insts1 insts2),
    gls2,
    just,
    (* To do: if necessary, inline this into seqapply *)
    seqbuds rosebud rosebuds in
  let (then_: tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
      let _,gls,_,_ as gstate = tac1 g in
      tacsequence gstate (replicate tac2 (length gls))
  and (thenl_: tactic -> tactic list -> tactic) =
    fun tac1 tac2l g ->
      let _,gls,_,_ as gstate = tac1 g in
      if gls = [] then tacsequence gstate []
      else tacsequence gstate tac2l in
  then_,thenl_;;

let rose_of_thm th =
  Some (Batoption.bind (get_dep_info th)
                       ((function
                          | Tracked id -> Some (Tracked_thm id)
                          | _ -> None) o get_tracking)
        |> Batoption.default (Concl (concl th)));;

let (add_rose : string -> thm list
                -> (term list * instantiation) * goal list * justification
                -> goalstate) = fun name ths gstate ->
  let inst,gls,j = gstate in
  inst,gls,j,rose_split (length gls) [name,Batlist.filter_map rose_of_thm ths];;

let (simple_rose : (term list * instantiation) * goal list * justification
                   -> goalstate) = fun gstate ->
  let inst,gls,j = gstate in
  inst,gls,j,rose_split (length gls) [];;

(* ------------------------------------------------------------------------- *)
(* Basic tactic to use a theorem equal to the goal. Does *no* matching.      *)
(* ------------------------------------------------------------------------- *)

let (ACCEPT_TAC: thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  fun th (asl,w) ->
    if aconv (concl th) w then
      add_rose "ACCEPT_TAC" [th] (null_meta,[],propagate_thm th)
    else failwith "ACCEPT_TAC";;

(* ------------------------------------------------------------------------- *)
(* Create tactic from a conversion. This allows the conversion to return     *)
(* |- p rather than |- p = T on a term "p". It also eliminates any goals of  *)
(* the form "T" automatically.                                               *)
(* ------------------------------------------------------------------------- *)

let (CONV_TAC: conv -> tactic) =
  let t_tm = `T` in
  fun conv ((asl,w) as g) ->
    let th = conv w in
    let tm = concl th in
    if aconv tm w then ACCEPT_TAC th g else
    let l,r = dest_eq tm in
    if not(aconv l w) then failwith "CONV_TAC: bad equation" else
    if r = t_tm then ACCEPT_TAC(EQT_ELIM th) g else
    let th' = SYM th in
    add_rose "CONV_TAC" [th]
             (null_meta,
              [asl,r],
              (fun i [th] -> EQ_MP (INSTANTIATE_ALL i th') th));;

let (UNDISCH_TAC: term -> tactic) =
 fun tm (asl,w) ->
   try let sthm,asl' = remove (fun (_,asm) -> aconv (concl asm) tm) asl in
       let thm = snd sthm in
       add_rose "UNDISCH_TAC" [thm]
                (null_meta,
                 [asl',mk_imp(tm,w)],
                 (fun i [th] -> MP th (INSTANTIATE_ALL i thm)))
   with Failure _ -> failwith "UNDISCH_TAC";;

let (BOX_TAC : string -> thm list -> tactic -> tactic) = fun name ths tac g ->
  let inst,gls,j,rose_bud = tac g in
  let rose_bud =
    Rose_bud (fun trees -> let Rose(tacs,subtrees),trees = bloom rose_bud trees in
                           let ths = Batlist.filter_map rose_of_thm ths in
                           Rose(((name,ths) :: tacs), subtrees),trees) in
  inst,gls,j,rose_bud;;
