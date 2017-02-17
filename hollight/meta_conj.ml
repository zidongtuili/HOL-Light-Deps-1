(*needs "meta_tactic.ml"*)

let split_and_reprove thm =
  let (asl,c) = dest_thm thm in
  let vs,thm' = splitlist SPEC_VAR thm in
  let conjs = CONJUNCTS thm' in
  let keep_v thm v = not (free_in v (concl thm')) || free_in v (concl thm) in
  let vss = map (fun c -> filter (keep_v c) vs) conjs in
  let conjs = map2 (itlist GEN) vss (CONJUNCTS thm') in
  match conjs with
  | [_] -> let id,thm,is_new = with_tracking_nodup thm in
           thm,[id,thm,is_new]
  | _::_ ->
     let conjs = map (with_tracking_nodup) conjs in
     let snd (_,x,_) = x in
     let trivial = map2 (fun vs -> ACCEPT_TAC o SPECL vs o snd) vss conjs in
     TAC_PROOF ((map (fun asm -> ("",ASSUME asm)) asl, c),
                REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL trivial),
     conjs

let zip_with_index xs =
  rev (snd (rev_itlist (fun x (n,xs) -> (n+1,(x,n) :: xs)) xs (0,[])))

let meta_conj_tactic_diff_hook =
  {
    meta_tactic_diff_hook with
    Toploop.env_diff_ident =
      (fun ident vd (dep_src_thms, dep_src_tactics) ->
       if is_thm vd then
         begin
           let thm,id_thms_new = Ident.name ident
                                 |> Toploop.getvalue
                                 |> Obj.obj
                                 |> split_and_reprove in
           let id_thm (id,thm,_) = id,thm in
           let src =
             register_thm_ident ident vd (map id_thm id_thms_new,thm) in
           match id_thms_new with
           | [id,thm,is_new] ->
              let meta =
                meta_of_thm id thm src Meta.Toplevel dep_src_thms dep_src_tactics in
              Toploop.setvalue (Ident.name ident) (Obj.repr (clear_local thm));
              if is_new then register_thm_meta thm meta
           | idthms ->
              let () = Toploop.setvalue (Ident.name ident) (Obj.repr thm) in
              Batlist.iter
                (fun ((id,c,is_new),index) ->
                 let meta =
                   meta_of_thm id c src (Meta.Conjunct index)
                               dep_src_thms dep_src_tactics in
                 let c = clear_local c in
                 if is_new then register_thm_meta c meta)
                (zip_with_index idthms)
         end
       else if is_tactic vd then
         let src = register_tactic_ident ident vd () in
         ident.Ident.name
         |> Toploop.getvalue
         |> rebind_magically vd (fun thms tac -> BOX_TAC src thms tac)
         |> Obj.repr
         |> Toploop.setvalue ident.Ident.name
       else ();
       ([], []))
  };;

let restore_hook = Toploop.set_env_diff_hook () meta_conj_tactic_diff_hook;;
