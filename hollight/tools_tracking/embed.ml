(* ========================================================================= *)
(* Object level reasoning for sequent calculus-style, propositional embedded *)
(* logics using meta-level natural deduction.                                *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2009-2017                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "IsabelleLight/make.ml";;
needs "tools/make.ml";;
needs "tools/Library/multisets.ml";;

(* ------------------------------------------------------------------------- *)
(* Embedded interactive prover.                                              *)
(* ------------------------------------------------------------------------- *)
(* This is built in the style of Isabelle Light.                             *)
(* However, it is designed to work for the embedded logic.                   *)
(* ------------------------------------------------------------------------- *)
(* - This means that we need to take care of multisets when matching.        *)
(* - We are also taking care of type theory term construction using          *)
(* metavariables. Since we are using unification, construction works both    *)
(* when proving backwards and forwards.                                      *)
(* - When proving backwards, it makes sense to define a goal of the form:    *)
(*   ? P . |-- (...) P                                                       *)
(* Then using META_EXISTS_TAC will convert P into a meta-variable that can   *)
(* be constructed during the backwards proof.                                *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Embedded logics are expected to have an (inductively?) defined relation   *)
(* for logical consequence (turnstile). Depending on the embedded logic,     *)
(* this can have the following types of arguments:                           *)
(* - Static terms (e.g. single conclusion intuitionistic logic)              *)
(* - Multisets of terms (e.g. assumptions in sequents)                       *)
(* - Construction terms (type theory translations)                           *)
(* The matching algorithm tries to use multiset matching for all arguments   *)
(* and falls back to term matching if that fails.                            *)
(* If your embedded logic includes type theory construction, you need to     *)
(* implement a sequent splitting function of type:                           *)
(* term -> string * term list * term list                                    *)
(* Given a sequent in your embedded logic, this function needs to be able to *)
(* return:                                                                   *)
(* (a) the string representation of the logical consequence operator         *)
(* (b) the list of standard logical arguments (multisets and static terms)   *)
(* (c) the list of type theory translation terms                             *)
(* We use unification for the last case instead of term matching to allow    *)
(* proofs in both directions (construction vs. verification),                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* This is the default sequent splitting function. This assumes all          *)
(* arguments are part of the logic.                                          *)
(* ------------------------------------------------------------------------- *)
(* The system will fall back to this if no explicit splitting function is    *)
(* provided. Basically you only need to define a sequent splitting function  *)
(* if you are doing type theory stuff.                                       *)
(* ------------------------------------------------------------------------- *)

let default_split_seq tm =
  let comb,args = strip_comb tm in
  (fst o dest_const) comb,args,([]:term list);;


(* ------------------------------------------------------------------------- *)
(* A reference to hold all sequent splitting functions.                      *)
(* ------------------------------------------------------------------------- *)

let split_seq_funs = ref ([]:(string * (term->string * term list * term list)) list);;


(* ------------------------------------------------------------------------- *)
(* Add/remove a sequent splitting function for a particular logic consequence*)
(* operator (comb).                                                          *)
(* ------------------------------------------------------------------------- *)

let add_split_seq_fun comb f =
  let rest = try (snd (remove (fun (l,f) -> l = comb) (!split_seq_funs)))
    with Failure _ -> (!split_seq_funs) in
  split_seq_funs := (comb,f) :: rest;;

let remove_split_seq_fun comb =
  let f,rest = remove (fun (l,f) -> l = comb) (!split_seq_funs) in
  split_seq_funs := rest ; snd f;;


(* ------------------------------------------------------------------------- *)
(* The main sequent splitting function. Tries the functions in the reference *)
(* table and reverts to the default if none of those match.                  *)
(* ------------------------------------------------------------------------- *)

let split_seq tm =
  try (
    let comb = (fst o dest_const o fst o strip_comb) tm in
    let splitter = try (assoc comb (!split_seq_funs))
     with Failure _ -> default_split_seq in
    splitter tm
  ) with Failure _ -> failwith "split_seq";;


(* ------------------------------------------------------------------------- *)
(* A function used in the justification of our rule tactics.                 *)
(* Discharges a list of terms dischl from theorem thm after instantiating    *)
(* both with i.                                                              *)
(* ------------------------------------------------------------------------- *)

let dischi_pair = 
  fun i (dischl,thm) -> 
    DISCHL (map (instantiate i) dischl) (INSTANTIATE_ALL i thm);;


(* Advanced multiset matching. *)
    
let munion_match =
  fun avoids rl gl ->
    let prop_ty = try ( (hd o snd o dest_type o type_of) gl )
      with Failure _ -> failwith "munion_match: invalid type" in
    
    let gargs = flat_munion gl 
    and rargs = flat_munion rl in
    let is_mset_var = fun x -> (is_var x) && not (mem x avoids) in

    let rargs_var,rargs_nonvar = partition is_mset_var rargs in

    (* First we try to match nonvariable assumptions since they need to match directly *)
    let ins = term_match_list avoids rargs_nonvar gargs in 

    (* Apply the instantiations that we've found so far *)
    let rargs_var_new = map (instantiate ins) rargs_var
    and rargs_nonvar_new = map (instantiate ins) rargs_nonvar in

    (* Filter all the remaining assumptions that need to be matched *)
    let gargs_rest = remove_list gargs rargs_nonvar_new in

    (* Instantiate mempty with the appropriate type. *)
    let mempty = inst [prop_ty,`:A`] `mempty:(A)multiset` in

    (* Make sure all remaining rule assumptions get a pair and no goal assumptions remain *)
    let gargs_rest = adjust_munion_list_length mempty (length rargs_var_new) gargs_rest in

    (* Pair them up *)
    let pairs = zip rargs_var_new gargs_rest in

    let insts = map (fun x,y -> term_match avoids x y) pairs in
      itlist compose_insts insts ins;;



(* ------------------------------------------------------------------------- *)
(* Version of PROVE_HYP that matches multisets.                              *)
(* ------------------------------------------------------------------------- *)

let MSET_PROVE_HYP ath bth =
  try (
    let eq = tryfind (multiset_eq (concl ath)) (hyp bth) in
      PROVE_HYP (EQ_MP eq ath) bth
  ) with Failure _ -> bth;;   


(* ------------------------------------------------------------------------- *)
(* Matching of 2 sequents.                                                   *)
(* ------------------------------------------------------------------------- *)

let seq_match = 
  fun avoids rl gl ->

    let gcomb,gargs,gconstr = split_seq gl
    and rcomb,rargs,rconstr = split_seq rl in

    if (not(gcomb = rcomb))
    then failwith "seq_match: Sequent operators (turnstiles) don't match."
    else 
    
    let constr_unify i (r,g) =
      let ri,gi = (instantiate i r),(instantiate i g) in
      let res = term_unify (union (frees ri) (frees gi)) ri gi in (* TODO? subtract vs avoids ? *)
      compose_insts i res in
    
    let constr_inst = List.fold_left constr_unify null_inst (zip rconstr gconstr) in

    let mset_match i (r,g) =
      let ri,gi = (instantiate i r),(instantiate i g) in
      let res = try ( munion_match avoids ri gi )
	with Failure _ -> term_match avoids ri gi in
      compose_insts i res in

    List.fold_left mset_match constr_inst (zip rargs gargs);;
 

(* ------------------------------------------------------------------------- *)
(* Matching a sequent-based theorem (assumption) to a term.                  *)
(* See Isabelle Light on why we need these.                                  *)
(* We just use our sequent matcher instead of term_match.                    *)
(* ------------------------------------------------------------------------- *)

let REV_PART_SEQMATCH_I =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc in
  fun avoids partfn th ->
    let bod = concl th in
    let pbod = partfn bod in
    let lconsts = union avoids (intersect (frees (concl th)) (freesl(hyp th))) in
    fun tm ->
      let bvms = match_bvs pbod tm [] in
      let atm = deep_alpha bvms tm in
      seq_match lconsts atm (partfn bod);; 


let rec (term_to_asm_seqmatch: term list -> term -> (string * thm) list -> (string * thm) list * ((string * thm) * instantiation)) =
  fun avoids key asms ->
    if (asms = []) then failwith ("No assumptions match `" ^ (string_of_term key) ^ "`!")
    else try 
      let l,asm = hd asms in
      let i = REV_PART_SEQMATCH_I avoids I asm key in
      (tl asms),((l,asm),i)
    with Failure _ -> 
      let res,inst = term_to_asm_seqmatch avoids key (tl asms) in 
	((hd asms)::res),inst;;


let rec (term_to_asm_lbl_seqmatch: term list -> 
	 term -> (string * thm) list -> 
	 string -> (string * thm) list * ((string * thm) * instantiation)) =
  fun avoids key asms lbl ->
    let (l,asm),re_asms = try ( remove (fun l,_ -> l = lbl) asms ) 
      with Failure _ -> failwith "No such assumption found!" in
    let i = try ( REV_PART_SEQMATCH_I avoids I asm key )
      with Failure _ -> 
	failwith ("Assumption `" ^ 
		     ((string_of_term o concl) asm) ^ 
		     "` doesn't match `" ^ (string_of_term key) ^ "`!") in
    re_asms,((l,asm),i);;


(* ------------------------------------------------------------------------- *)
(* apply_seqtac does more than its Isabelle Light counter part.              *)
(* - It renames variables in the theorem (rule) into fresh variables. Also   *)
(* renames the instlist so that the variables there match.                   *)
(* - It eliminates empty multisets (mempty) in  both the conclusion and      *)
(* the assumptions.                                                          *)
(* - Upon failure restores the counter in an attempt for some bookkeeping.   *)
(* ------------------------------------------------------------------------- *)

let apply_seqtac rtac instlist rl ctr (asl,w) =
    let fnum = if (ctr < 0) then fresh_proofctr () else ctr + 1 in
    let finstlist = number_vars_instlist fnum instlist and
	frl = number_vars_meta_rule fnum rl in
    let tac = (rtac finstlist frl) THEN 
     TRY (rule conjI) THEN 
     ELIM_EMPTY_TAC THEN 
     RULE_ASSUM_TAC (PURE_REWRITE_RULE[MUNION_EMPTY;MUNION_EMPTY2])
    in tac (asl,w), if (ctr < 0) then ctr else ctr + 1;;


(* ------------------------------------------------------------------------- *)
(* RULE / RULE_TAC for embedded sequent calculus logics.                     *)
(* ------------------------------------------------------------------------- *)

let (rulem_seqtac:(term*term) list->meta_rule->tactic) =
  fun instlist r ((asl,w) as g) ->
    let glf = gl_frees g in
    let r = inst_meta_rule_vars instlist r glf in  

    let ins = try ( seq_match glf (fst3 r) w ) 
    with Failure s -> failwith ("Rule doesn't match: " ^ s) in

    let (c,new_hyps,thm) = inst_meta_rule ins r in
    let (asl,w) as g = inst_goal ins g in

    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = map (create_goal asl) new_hyps in

    let rec create_dischl = 
      fun (asms,g) -> if (asms = []) then [] else 
	((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) glf in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in

(*
print_string ">>>" ; print_newline();
      let _ =  (map print_goal new_goals) in () ; print_newline() ;
print_string ">>>" ; print_newline();
*)
(*    let thm = (INSTANTIATE_ALL ins) thm in *)
    let thm = (NORMALIZE_MULTISET_ALL o INSTANTIATE_ALL ins) thm in
(*
print_string "1:" ; print_thm thm ; print_newline(); 
print_string "Check if:"; print_newline(); print_term (concl thm); print_newline() ; print_string "is equal to:" ; print_newline (); 
print_term (instantiate ins w); print_newline(); 
*)
    let thm2 = 
      (EQT_ELIM o PURE_REWRITE_CONV[MUNION_AC;REFL_CLAUSE;MUNION_EMPTY;MUNION_EMPTY2]) 
	(mk_eq (concl thm, w)) in
(*
print_string "2:" ; print_thm thm2 ; print_newline () ; print_newline (); 
*)
    (mvs,ins),new_goals,fun i l ->  
(*
      print_string "1i:" ; print_thm (INSTANTIATE_ALL i thm) ; print_newline(); 
      (*print_string "1i:" ; print_thm ((NORMALIZE_MULTISET_ALL o INSTANTIATE_ALL i) thm) ; print_newline(); *)
      print_string "2i:" ; print_thm (INSTANTIATE_ALL i thm2) ; print_newline () ; 
   print_string "---" ; print_newline (); 
      print_thl (map (disch_pair i) (List.combine dischls l)) ; print_string "----" ; print_int (length l) ; print_newline();
*)
      let res = List.fold_left 
	(fun t1 t2 -> MSET_PROVE_HYP (INSTANTIATE_ALL i t2) t1) 
	((INSTANTIATE_ALL i) thm) 
	(map (dischi_pair i) (List.combine dischls l)) in
(*
      print_string "r:" ; print_thm res ; print_newline(); 
  print_string "ret:" ; print_thm (EQ_MP (INSTANTIATE_ALL i thm2) res) ; print_newline();
*)
	EQ_MP (INSTANTIATE_ALL i thm2) res;;


let rule_seqtac instlist thm = apply_seqtac rulem_seqtac instlist (mk_meta_rule thm);;

let ruleseq = rule_seqtac [];;


(* ------------------------------------------------------------------------- *)
(* DRULE / DRULE_TAC  for embedded sequent calculus logics.                  *)
(* ------------------------------------------------------------------------- *)      

let (drulem_seqtac:?lbl:string->string->(term*term) list->meta_rule->tactic) =
  fun ?(lbl="") reslbl instlist rl ((asl,w) as gl) -> 
    let glf = gl_frees gl in
    let ((cn,hyps,thm) as rl) = inst_meta_rule_vars instlist rl glf in

    let (prems,major_prem) = 
      if (hyps = []) then 
	failwith "drule: Not a proper destruction rule: no premises!" 
      else hd hyps in
   
    let avoids = gl_frees gl in
    let asl,((lbl,major_thm),elim_inst) = 
      if (prems = [])
      then 
        try if (String.length lbl = 0)
	    then term_to_asm_seqmatch glf major_prem asl
	    else term_to_asm_lbl_seqmatch glf major_prem asl lbl
	with Failure s -> failwith ("drule: " ^ s) 
      else 
	failwith "drule: not a proper destruction rule: major premise has assumptions!" in

    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let thm = (NORMALIZE_MULTISET_ALL o INSTANTIATE_ALL elim_inst) thm in

    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = (map (create_goal asl) new_hyps) @ 
      [create_goal asl ([reslbl,ASSUME (instantiate elim_inst cn)],w)] in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    (* We add an empty discharge list at the end for the extra goal. *)
    let dischls = map create_dischl new_hyps @ [[]] in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) glf in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in

    (mvs,elim_inst),new_goals,fun i l ->  
      let major_thmi = (INSTANTIATE_ALL i) major_thm in
      let l = (major_thmi :: map (ADD_HYP major_thmi) 
		 (map (dischi_pair i) (List.combine dischls l))) in
      MSET_PROVE_HYP 
	(List.fold_left 
	   (fun t1 t2 -> MSET_PROVE_HYP (INSTANTIATE_ALL i t2) t1) 
	   (INSTANTIATE_ALL i thm) ((butlast) l)) 
	(last l)

let drule_seqtac ?(lbl="") ?(reslbl="") instlist thm =
(*  let res = if (String.length reslbl = 0) <-- what if we DO want reslbl to be "" ?
	    then if (ctr < 0) then proofctr_label lbl else set_label lbl ctr
	    else reslbl in *)
  apply_seqtac (drulem_seqtac ~lbl:lbl reslbl) instlist (mk_meta_rule thm)

let druleseq ?(lbl="") ?(reslbl="") = drule_seqtac ~lbl:lbl ~reslbl:reslbl []


(* ------------------------------------------------------------------------- *)
(* FRULE / FRULE_TAC  for embedded sequent calculus logics.                  *)
(* ------------------------------------------------------------------------- *)      

let (frulem_seqtac:?lbl:string->string->(term*term) list->meta_rule->tactic) =
  fun ?(lbl="") reslbl instlist rl ((asl,w) as gl) -> 
    let glf = gl_frees gl in
    let ((cn,hyps,thm) as rl) = inst_meta_rule_vars instlist rl glf in

    let (prems,major_prem) = 
      if (hyps = []) then 
	failwith "frule: Not a proper destruction rule: no premises!" 
      else hd hyps in
    let avoids = gl_frees gl in

    let _,((lbl,major_thm),elim_inst) = 
      if (prems = [])
      then 
        try if (String.length lbl = 0)
	    then term_to_asm_seqmatch glf major_prem asl
	    else term_to_asm_lbl_seqmatch glf major_prem asl lbl
	with Failure s -> failwith ("frule: " ^ s) 
      else 
	failwith "frule: not a proper destruction rule: major premise has assumptions!" in

    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let thm = (NORMALIZE_MULTISET_ALL o INSTANTIATE_ALL elim_inst) thm in
    (* print_string "1:" ; print_thm thm ; print_newline(); *)

    let create_goal = fun asms (hs,gl) -> (hs@asms,gl) in
    let new_goals = (map (create_goal asl) new_hyps) @ 
      [create_goal asl ([reslbl,ASSUME (instantiate elim_inst cn)],w)] in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    (* We add an empty discharge list at the end for the extra goal. *)
    let dischls = map create_dischl new_hyps @ [[]] in

    let normalfrees = itlist union (map ( fun (_,y) -> frees y ) instlist ) glf in
    let mvs = subtract (itlist union (map gl_frees new_goals) []) normalfrees in

    (mvs,elim_inst),new_goals,fun i l ->  
      let major_thmi = (INSTANTIATE_ALL i) major_thm in
      let l = (major_thmi :: map (dischi_pair i) (List.combine dischls l)) in
      MSET_PROVE_HYP 
	(List.fold_left 
	   (fun t1 t2 -> MSET_PROVE_HYP (INSTANTIATE_ALL i t2) t1) 
	   (INSTANTIATE_ALL i thm) ((butlast) l)) 
	(last l)

	
let frule_seqtac ?(lbl="") ?(reslbl="") instlist thm =
(*  let res = if (String.length reslbl = 0)
	    then if (ctr < 0) then proofctr_label lbl else set_label lbl ctr
	    else reslbl *)
  apply_seqtac (frulem_seqtac ~lbl:lbl reslbl) instlist (mk_meta_rule thm)

let fruleseq ?(lbl="") ?(reslbl="") = frule_seqtac ~lbl:lbl ~reslbl:reslbl []

					


(* ------------------------------------------------------------------------- *)
(* "e" tactic application for the embedded logic tactics.                    *)
(* ------------------------------------------------------------------------- *)
						   
let eseq tac = e (ETAC_TAC (-1) tac);;

(* ------------------------------------------------------------------------- *)
(* "prove" a theorem using the embedded logic tactics.                       *)
(* ------------------------------------------------------------------------- *)

let prove_seq (tm,tac) = prove(tm,ETAC_TAC 0 tac);;

  
(* ------------------------------------------------------------------------- *)
(* Assumption matching.                                                      *)
(* ------------------------------------------------------------------------- *)
(* Simply normalizes multisets in assumptions and goals, then tries to match *)
(* them directly. Since this concludes the proof, there is nothing stopping  *)
(* us from rewriting things.                                                 *)
(* ------------------------------------------------------------------------- *)

let seq_assumption :int etactic =
  ETAC (PURE_REWRITE_ASM_TAC[MUNION_AC] THEN 
  REWRITE_TAC[MUNION_AC] THEN assumption);;


(* ------------------------------------------------------------------------- *)
(* Assumption unification (when using metavariables).                        *)
(* ------------------------------------------------------------------------- *)
(* NOTE:                                                                     *)
(* I should implement a custom term_unify based tactic that does multiset    *)
(* unification with an assumption.                                           *)
(* As pointed out by Phil (he faced the same problem) a variable multiset    *)
(* may be moved around randomly (based on the variable name) when normalizing*)
(* thus breaking what would otherwise be a normal unification.               *)
(* eg. A ^ {D} does not currently unify with {NEG B} ^ {D} because           *)
(* normalization moves {NEG B} on the right of {D} whereas A is on the left. *)
(* The solution for now is to use instlists to instantiate variable          *)
(* multisets. I should, however, consider this as future work.               *)
(* ------------------------------------------------------------------------- *)

let seq_meta_assumption : term list -> int etactic =
  fun metas -> ETAC ( PURE_REWRITE_ASM_TAC[MUNION_AC] 
  THEN REWRITE_TAC[MUNION_AC] THEN meta_assumption metas );; 


(* ------------------------------------------------------------------------- *)
(* Shortcut for interactive proofs so that you don't have to enumerate       *)
(* metavariables.                                                            *)
(* ------------------------------------------------------------------------- *)

let seqema () = (eseq o seq_meta_assumption o top_metas o p) ()  


(* ------------------------------------------------------------------------- *)
(* Matching labelled assumptions.                                            *)
(* ------------------------------------------------------------------------- *)
  
let seq_lbl_asm : string -> int etactic =
  fun lbl -> ETAC (
    PURE_REWRITE_TAC[MUNION_AC] THEN 
    USE_THEN lbl (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE[MUNION_AC]));;

let seq_meta_lbl_asm : string -> term list -> int etactic =
  fun lbl mvs -> ETAC ( 
    PURE_REWRITE_TAC[MUNION_AC] THEN 
    ((USE_THEN lbl (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE[MUNION_AC]) ORELSE 
    (USE_THEN lbl (ALL_UNIFY_ACCEPT_TAC mvs o PURE_REWRITE_RULE[MUNION_AC])))));;

let prove_by_seq s = (eseq o seq_meta_lbl_asm s o top_metas o p) ()

  

(* ------------------------------------------------------------------------- *)
(* Tactic to cut with a known lemma in the embedded logic.                   *)
(* ------------------------------------------------------------------------- *)
(* TODO
let cut_seqtac =
  fun setlist thm ->
    let thm = (UNDISCH_ALL o MIMP_TO_IMP_RULE o SPEC_ALL) thm in
    let primed_ll_cut = inst_meta_rule_vars [] (mk_meta_rule ll_cut) (thm_frees thm) in
    let cut_term = (hd o tl o hyp o thd3) primed_ll_cut in
    let cut_ins = ll_term_match (thm_frees thm) cut_term (concl thm) in
    let new_rule = inst_meta_rule (cut_ins) primed_ll_cut in
    llapply llrulem_tac setlist new_rule 

(*
let llcut_tac = 
  fun setlist thm ->
    let thm = (UNDISCH_ALL o MIMP_TO_IMP_RULE o SPEC_ALL) thm in
    let primed_ll_cut = thm_mk_primed_vars (thm_frees thm) ll_cut in
    let cut_term = (snd o dest_conj o fst o dest_mimp o concl) primed_ll_cut in
    let cut_ins = ll_rule_match (thm_frees thm) cut_term (concl thm) in
    let ll_cut_inst = INSTANTIATE cut_ins primed_ll_cut in
    let ADD_DISCH d t = DISCH d (ADD_HYP (ASSUME d) t) in
    let new_rule = MIMP_RULE (List.fold_right ADD_DISCH (fst (dest_thm thm)) ll_cut_inst) in
    llapply (llrulem_tac setlist (mk_meta_rule new_rule)) ;;
*)

let llcut = llcut_tac []
*)





(* ------------------------------------------------------------------------- *)

