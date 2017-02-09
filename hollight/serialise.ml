let all_json () =
  let all_thm_metas = get_thm_metas () in
  let thm_jsons = Ezjsonm.list Meta.Json.of_thm_meta all_thm_metas in
  let json_of_thm_src src =
    Meta.Json.fields_of_src
      src
      (fun (thms,_) ->
       [ "tracked_ids", Ezjsonm.list (fun (id,_) -> Ezjsonm.int id) thms ]) in
  let json_of_tac_src src = Meta.Json.fields_of_src src (fun () -> []) in
  let thm_src_jsons = get_thm_srcs () |> Ezjsonm.list json_of_thm_src in
  let tac_src_jsons = get_tactic_srcs () |> Ezjsonm.list json_of_tac_src in
  let (const_defs, const_ty_defs) =
    let add_all meta map =
      List.fold_left
        (fun map c ->
         Batstringmap.modify_def [meta.Meta.thm_id] c
                                 (fun ids -> union [meta.Meta.thm_id] ids) map)
        map in
    List.fold_left
      (fun (const_defs, const_ty_defs) (_,meta) ->
       (add_all meta const_defs (meta.Meta.new_consts),
        add_all meta const_ty_defs (meta.Meta.new_ty_consts)))
      (Batstringmap.empty, Batstringmap.empty) all_thm_metas in
  let of_map =
    Ezjsonm.dict
      o Batstringmap.to_list
      o Batstringmap.map (Ezjsonm.list Ezjsonm.int) in
  let const_jsons = of_map const_defs in
  let ty_const_jsons = of_map const_ty_defs in
  [ "theorem_idents", thm_src_jsons;
    "tactic_idents", tac_src_jsons;
    "tracked_theorems", thm_jsons;
       "const_definitions", const_jsons;
       "ty_const_jsons", ty_const_jsons
  ];;
