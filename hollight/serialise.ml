let all_json () =
  let all_thm_metas = get_thm_metas () in
  let thm_jsons = Ezjsonm.list Meta.Json.of_thm_meta all_thm_metas in
  let json_of_thm_src src =
    Meta.Json.fields_of_src
      src
      (fun (thms,_) ->
       [ "tracked_ids", Ezjsonm.list (fun (id,_) -> Ezjsonm.int id) thms ]) in
  let json_of_tac_src src = Meta.Json.fields_of_src src (fun () -> []) in
  let thm_src_jsons = all_thm_srcs () |> Ezjsonm.list json_of_thm_src in
  let tac_src_jsons = all_tactic_srcs () |> Ezjsonm.list json_of_tac_src in
  let of_map =
    Ezjsonm.dict
      o Batstringmap.to_list
      o Batstringmap.map (Ezjsonm.list Ezjsonm.int) in
  let const_jsons = of_map !const_def_map in
  let ty_const_jsons = of_map !ty_const_def_map in
  [ "theorem_idents", thm_src_jsons;
    "tactic_idents", tac_src_jsons;
    "tracked_theorems", thm_jsons;
       "const_definitions", const_jsons;
       "ty_const_jsons", ty_const_jsons
  ];;
