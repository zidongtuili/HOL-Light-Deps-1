(*needs "meta_tactic.ml"*)

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
           let src = register_thm_ident ident vd (id_thms,thm) in
           match id_thms with
           | [id,thm] ->
              let meta =
                {
                  meta_of_thm src id Meta.Toplevel thm with
                  Meta.dep_source_thms = dep_source_thms;
                  Meta.dep_source_tactics = dep_source_tactics
                } in
              let thm = modify_meta (fun (_,ts) -> (Some meta,ts)) thm in
              register_thm thm;
              Toploop.setvalue (Ident.name ident) (Obj.repr thm)
           | idthms ->
              let () = Toploop.setvalue (Ident.name ident) (Obj.repr thm) in
              Batlist.iter
                (fun ((id,c),index) ->
                 let meta =
                   { meta_of_thm src id (Meta.Conjunct index) c with
                     Meta.dep_source_thms = dep_source_thms;
                     Meta.dep_source_tactics = dep_source_tactics
                   } in
                 let c = modify_meta (fun (_,ts) -> (Some meta,ts)) c in
                 register_thm c)
                (zip_with_index (rev newly_tracked))
         end
       else if is_tactic vd then
         let src = register_tactic_ident ident vd in
         ident.Ident.name
         |> Toploop.getvalue
         |> rebind_magically vd (fun thms tac -> BOX_TAC src thms tac)
         |> Obj.repr
         |> Toploop.setvalue ident.Ident.name
       else ();
       ([], []))
  };;

let restore_hook = Toploop.set_env_diff_hook () meta_conj_tactic_diff_hook;;
