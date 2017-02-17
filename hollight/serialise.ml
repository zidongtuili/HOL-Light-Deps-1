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
  ];;

let iter_subterm f = function
  | Comb(rat,rand) as tm -> f rat; f rand; f tm
  | Abs(v,bod) as tm -> f v; f bod; f tm
  | tm -> f tm;;

let all_subterms () =
  let count = ref 0 in
  let module Tbl = Hashtbl.Make(struct type t = term
                                       let equal = (=)
                                       let hash = Hashtbl.hash
                                end) in
  let all_thm_metas = get_thm_metas () in
  let tbl = Tbl.create 1000 in
  let rec add_from_rose (Rose (src_thms, tac_proofs)) =
    List.iter
      (fun (_,thms) ->
       List.iter (function
                   | Tracked_thm _ -> ()
                   | Concl tm ->
                      iter_subterm (fun tm ->
                                    incr count;
                                    Tbl.replace tbl tm ()) tm)
                 thms)
      src_thms;
    List.iter add_from_rose tac_proofs in
  let add_from_thm_meta (thm,_) =
    let _,tac_proofs = get_meta thm in
    Tacset.iter add_from_rose tac_proofs in
  List.iter add_from_thm_meta all_thm_metas;
  Tbl.length tbl, !count

let rec of_tac_proof (Rose (src_thms, tac_proofs)) =
  let of_thm_arg = function
    | Tracked_thm i -> Ezjsonm.int i
    | Concl tm -> Ezjsonm.int (-1) in
  let of_src_thms (src,thms) =
    Ezjsonm.dict
      [ "tactic_id", Ezjsonm.int src.Meta.source_id;
        "thms", Ezjsonm.list of_thm_arg thms
    ] in
  Ezjsonm.dict
    [ "tactic", Ezjsonm.list of_src_thms src_thms;
      "subproof", Ezjsonm.list of_tac_proof tac_proofs
    ];;

let rec num_tac_proof (Rose (src_thms, tac_proofs)) =
  let of_thm_arg = function
    | Tracked_thm i -> i
    | Concl tm -> -1 in
  let of_src_thms (src,thms) =
    src.Meta.source_ident.Ident.name, map of_thm_arg thms in
  Rose (map of_src_thms src_thms, map num_tac_proof tac_proofs);;

let rec print_tac out (Rose (src_thmss, tac_proofs)) =
  let print_tac_thm out = function
    | Tracked_thm n -> Batprintf.fprintf out "%s" (string_of_int n)
    | Concl tm ->
       Batprintf.fprintf out "%s" (string_of_term tm) in
  let print_src_thms out = function
    | (src,[]) ->
       Batprintf.fprintf out "%s" src.Meta.source_ident.Ident.name
    | (src,thms) ->
       Batprintf.fprintf
         out
         "%s %a"
         src.Meta.source_ident.Ident.name (Batlist.print print_tac_thm) thms in
  let rec print_src_thmss out = function
    | [src_thms] ->
       Batprintf.fprintf out "%a" print_src_thms src_thms
    | src_thms::src_thmss ->
       Batprintf.fprintf out "%a → %a"
                      print_src_thms src_thms
                      print_src_thmss src_thmss in
  Batprintf.fprintf out "(%a %a)"
                    print_src_thmss src_thmss
                    (Batlist.print ~first:"" ~last:"" ~sep:" " print_tac)
                    tac_proofs;;
