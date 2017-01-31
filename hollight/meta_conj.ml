(*needs "meta_tactic.ml"*)

let rebind_boxed_tactic ident vd =
  match tactic_antecedents vd with
  | Some ants ->
     let tac_name = ident.Ident.name in
     let box = BOX_TAC tac_name [] in
     let rebind f =
       tac_name
       |> Toploop.getvalue
       |> Obj.obj
       |> f
       |> Obj.repr
       |> Toploop.setvalue tac_name in
     let ap1 f = box o f in
     let ap2 f = ap1 o f in
     let ap3 f = ap2 o f in
     let ap4 f = ap3 o f in
     (match length ants with
      | 0 -> rebind box
      | 1 -> rebind ap1
      | 2 -> rebind ap2
      | 3 -> rebind ap3
      | 4 -> rebind ap4)
  | None -> ();;

let list_type_path =
  !Toploop.toplevel_env
  |> Env.lookup_type (Longident.Lident "list")
  |> fst;;

let rec get_list_arg t = get_list_arg_of_desc t.Types.desc
and get_list_arg_of_desc = function
  | Types.Tconstr (p,[arg],_) when p = list_type_path -> Some (arg.Types.desc)
  | Types.Tlink t -> get_list_arg t
  | Types.Tsubst t -> get_list_arg t
  | t -> None;;

(* Rebind a tactic to one which boxes itself with the theorems it has been applied *
to. *)
(* NOTE: This is dangerously magical -- expect bugs to manifest as segfaults. *)
(* TODO: Extend magic_extract to extract theorems from more foldable data
structures. Right now, we only deal with the identity and list foldables. *)
let rebind_magically ident vd =
  let tac_name = ident.Ident.name in
  let (boxed : thm list -> tactic -> tactic) = fun thms tac ->
    BOX_TAC tac_name thms tac in
  let rec magic_ap : 'a 'b 'c. (thm list -> 'a -> 'b) -> Types.type_expr list -> 'c =
    fun f args ->
    match args with
    | [] -> Obj.magic f
    | arg_vd::args_vds ->
       magic_ap (fun ths g x -> f (ths @ magic_extract arg_vd x) (g x)) args_vds
  and magic_extract : 'a. Types.type_expr -> 'a -> thm list = fun arg_vd ->
    match get_constr arg_vd with
    | Some (c,[list_arg_vd]) when Path.same list_type_path c ->
       let f = magic_extract list_arg_vd in
       Obj.magic (fun thms -> Batlist.bind thms f)
    | Some (c,args) when Path.same thm_type_path c -> Obj.magic (fun thm -> [thm])
    | _ -> fun _ -> [] in
  let tac = Obj.obj (Toploop.getvalue tac_name) in
  match tactic_antecedents vd with
  | Some ants ->
     Toploop.setvalue tac_name (Obj.repr (magic_ap boxed (rev ants) [] tac))
  | None -> ();;

let split_and_reprove thm =
  let (asl,c) = dest_thm thm in
  let vs,thm' = splitlist SPEC_VAR thm in
  let conjs = map (itlist GEN vs) (CONJUNCTS thm') in
  let f cs thm =
    match get_trivial_duplicates thm with
    | [] -> let id,c = with_tracking_nodup thm in
            (id,c)::cs, (id,c)
    | [id,dup] -> cs, (id,dup)
    | _ -> failwith ("Theorem is duplicated several times in " ^
                       "its dependency graph.") in
  match conjs with
  | [_] -> let id,thm = with_tracking_nodup thm in thm,[id,thm],[id,thm]
  | _::_ ->
     let (newly_tracked, conjs) = map_accum_l f [] conjs in
     let trivial = map (ACCEPT_TAC o SPECL vs o snd) conjs in
     TAC_PROOF ((map (fun asm -> ("",ASSUME asm)) asl, c),
                REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL trivial),
     newly_tracked,
     conjs

let zip_with_index xs =
  rev (snd (rev_itlist (fun x (n,xs) -> (n+1,(x,n) :: xs)) xs (0,[])))

let meta_conj_tactic_diff_hook =
  {
    meta_tactic_diff_hook with
    Toploop.env_diff_ident =
      (fun ident vd (dep_source_thms, dep_source_tactics) ->
       if is_thm vd then
         begin
           let thm,newly_tracked,id_thms = Ident.name ident
                                           |> Toploop.getvalue
                                           |> Obj.obj
                                           |> split_and_reprove in
           Toploop.setvalue (Ident.name ident) (Obj.repr thm);
           let src = register_thm_ident ident vd (id_thms,thm) in
           meta_map :=
             rev_itlist
               (fun ((id,c),index) ->
                let thm_type =
                  if length id_thms = 1
                  then Meta.Toplevel
                  else Meta.Conjunct index in
                let meta =
                  { meta_of_thm src id thm_type c with
                    Meta.dep_source_thms = dep_source_thms;
                    Meta.dep_source_tactics = dep_source_tactics
                  } in
                Batintmap.add id (c,meta))
               (zip_with_index (rev newly_tracked)) !meta_map
         end
       else if is_tactic vd then
         rebind_magically ident vd;
         ignore (register_tactic_ident ident vd);
         ([], []))
  };;

Toploop.set_env_diff_hook () meta_conj_tactic_diff_hook;;
