needs "tactics.ml"

let split_and_reprove thm =
  let (asl,c) = dest_thm thm in
  let vs,thm' = splitlist SPEC_VAR thm in
  let conjs = map (itlist GEN vs) (CONJUNCTS thm') in
  let f cs thm =
    match get_trivial_duplicates thm with
    | [] -> let id,c = with_tracking thm in
            (id,c)::cs, (id,c)
    | [id,dup] -> cs, (id,dup)
    | _ -> failwith ("Theorem is duplicated several times in " ^
                       "its dependency graph.") in
  match conjs with
  | [_] -> let id,thm = with_tracking thm in thm,[id,thm],[id,thm]
  | _::_ ->
     let (newly_tracked, conjs) = map_accum_l f [] conjs in
     let trivial = map (ACCEPT_TAC o SPECL vs o snd) conjs in
     TAC_PROOF ((map (fun asm -> ("",ASSUME asm)) asl, c),
                REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL trivial),
     newly_tracked,
     conjs

let zip_with_index xs =
  rev (snd (rev_itlist (fun x (n,xs) -> (n+1,(x,n) :: xs)) xs (0,[])))

let meta_conj_diff_hook =
  {
    meta_diff_hook with
    Toploop.env_diff_ident =
      fun ident vd dep_idents ->
      if is_thm vd then
        begin
          let thm,newly_tracked,id_thms = Ident.name ident
                                          |> Toploop.getvalue
                                          |> Obj.obj
                                          |> split_and_reprove in
          Toploop.setvalue (Ident.name ident) (Obj.repr thm);
          let ident_meta =
            register_ident ident thm vd (map (fun (id,_) -> id) id_thms) in
          meta_map :=
            rev_itlist
              (fun ((id,c),index) ->
               let thm_type =
                 if length id_thms = 1 then Meta.Toplevel else Meta.Conjunct index in
               let meta = meta_of_thm (ident_meta, thm_type) id c in
               let meta = { meta with Meta.source_code_deps = dep_idents } in
               Intmap.add id (c,meta))
              (zip_with_index (rev newly_tracked)) !meta_map
        end;
      dep_idents
  };;

Toploop.set_env_diff_hook () meta_conj_diff_hook;;