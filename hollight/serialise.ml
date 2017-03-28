let all_json () =
  Meta.(
  Ezjsonm.(
  let rec of_ty = function
    | Tyvar v -> string v
    | Tyapp (c,args) -> list I (string c::List.map of_ty args) in
  let rec of_tm = function
    | Var (v,ty) -> list I [string "V"; string v; of_ty ty]
    | Const (c,ty) -> list I [string "C"; string c; of_ty ty]
    | Comb (s,t) -> list I [of_tm s; of_tm t]
    | Abs (v,body) -> list I [string "\\"; of_tm v; of_tm body] in
  let of_thm thm =
    dict
      [ "hyp", list of_tm (hyp thm)
      ; "concl", of_tm (concl thm)
      ] in
  let of_thm_origin = function
    | Toplevel ->  string "toplevel"
    | Conjunct n ->
       (* Convert the integer to a string for Neo4j. *)
       pair string (string o string_of_int) ("conjunct",n) in
  let of_ident id =
    dict
      [ "name", string id.Ident.name
      ] in
  let strip_prefix pre str =
    match Batstring.Exceptionless.split ~by:pre str with
    | Some("",rest) -> rest
    | _ -> failwith "strip_prefix" in
  let of_location loc =
    let fname = loc.Location.loc_start.Lexing.pos_fname in
    let fname = tryfind (C strip_prefix fname) [!hol_dir; Sys.getcwd ()] in
    dict
      [ "loc_start",
        dict
          [ "pos_fname", string fname
          ; "pos_lnum", int loc.Location.loc_start.Lexing.pos_lnum
          ]
      ] in
  let fields_of_src src of_meta =
    dict
      ([ "src_id", int src.source_id
       ; "src_ident", of_ident src.source_ident
       ; "src_loc", of_location src.location
       ]
       @ of_meta src.src_obj) in
  let of_tactic_dep (tac,thms) =
    dict
      ["tactic", int tac.source_id
      ;"theorem_arguments", list (int o fun m -> m.source_id) thms ] in
  let src_id thm_meta = thm_meta.source.source_id in
  let id_of_meta_src meta =
    fst (src_id meta,meta.source.source_id) in
  let of_thm_arg = function
    | Tracked_thm i -> int i
    | Concl tm -> of_tm tm in
  let of_src_tactic_thms (src_tactic,thms) =
    dict
      [ "tactic_id", int src_tactic.source_id;
        "thm_args", list of_thm_arg thms
      ] in
  let rec of_tac_proof (Rose (src_tactic_thms, tac_proofs)) =
    dict
      [ "tactic", list of_src_tactic_thms src_tactic_thms;
        "subproofs", list of_tac_proof tac_proofs
      ] in
  let of_thm_meta (thm,meta) =
    dict
      [ "tracking_id", int meta.tracking_id
      ; "source_id", int (id_of_meta_src meta)
      ; "theorem", of_thm thm
      ; "stringified", string (string_of_thm thm)
      ; "originates_as", of_thm_origin meta.originates_as
      ; "tracked_dependencies", list (int o fst) meta.tracked_dependencies
      ; "tactic_proofs", list of_tac_proof meta.tactic_proofs
      ; "constants", list string (tm_consts (concl thm))
      ; "type_constants", list string (tm_ty_consts (concl thm))
      ; "source_code_theorem_dependencies",
        list (fun meta -> int meta.source_id)
             meta.source_code_theorem_dependencies
      ; "source_code_tactic_dependencies",
        list of_tactic_dep meta.source_code_tactic_dependencies
      ; "new_constants", list string (new_consts thm)
      ; "new_type_constants", list string (new_ty_consts thm)
      ] in
  let all_thm_metas = get_thm_metas () in
  let thm_jsons = Ezjsonm.list of_thm_meta all_thm_metas in
  let json_of_thm_src src =
    fields_of_src
      src
      (fun (thms,_) ->
       [ "tracked_ids", Ezjsonm.list (fun (id,_) -> Ezjsonm.int id) thms ]) in
  let json_of_tac_src src = fields_of_src src (fun () -> []) in
  let thm_src_jsons = get_thm_srcs () |> Ezjsonm.list json_of_thm_src in
  let tac_src_jsons = get_tactic_srcs () |> Ezjsonm.list json_of_tac_src in
  let (const_defs, const_ty_defs) =
    let add_all meta map =
      List.fold_left
        (fun map c ->
         Batstringmap.modify_def [meta.Meta.tracking_id] c
                                 (fun ids -> union [meta.Meta.tracking_id] ids) map)
        map in
    List.fold_left
      (fun (const_defs, const_ty_defs) (thm,meta) ->
       (add_all meta const_defs (new_consts thm),
        add_all meta const_ty_defs (new_ty_consts thm)))
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
  ]));;
