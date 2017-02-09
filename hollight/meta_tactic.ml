needs "tactic_types.ml"

(* Tactic identification. *)
let tactic_type_path =
  !Toploop.toplevel_env
  |> Env.lookup_type (Longident.Lident "tactic")
  |> fst;;

let rec get_ty_ants_concl t = get_ty_ants_concl_of_desc t.Types.desc
and get_ty_ants_concl_of_desc = function
  | Types.Tconstr (p,_,_) as ty -> [],ty
  | Types.Tarrow (_, a, c, _) -> let ants,c = get_ty_ants_concl c in (a::ants),c
  | Types.Tlink t -> get_ty_ants_concl t
  | Types.Tsubst t -> get_ty_ants_concl t
  | t -> [],t;;

let rec tactic_antecedents d =
  let rec get_indirect_tactic_path_ants = function
    | Path.Pident p ->
       let id = Longident.Lident p.Ident.name in
       let decl = snd (Env.lookup_type id !Toploop.toplevel_env) in
       Batoption.map_default get_tactic_ty_expr_ants None (decl.Types.type_manifest)
    | _ -> None
  and get_tactic_path_ants p =
    if Path.same p tactic_type_path then Some []
    else get_indirect_tactic_path_ants p
  and get_tactic_ty_expr_ants expr =
    let ants,c = get_ty_ants_concl expr in
    Batoption.bind (get_constr_of_desc c)
                   (fun (p,_) -> get_tactic_path_ants p
                                 |> Batoption.map (fun ants' -> ants @ ants')) in
  get_tactic_ty_expr_ants d.Types.val_type;;

let is_tactic d = Batoption.is_some (tactic_antecedents d);;

type tactic_meta =
  {
    tactic_src  : unit Meta.srced;
    tactic_thms : thm list
  }

(* Registration of tactic identifiers. *)
let register_tactic_ident, find_tactic_src, get_tactic_srcs  =
  let reg, find_from_ident, get_tactic_srcs = mk_src_fns () in
  (fun ident vd -> reg ident vd.Types.val_loc),
  find_from_ident,
  get_tactic_srcs;;

(* Find tactic rators and return them together with any theorem arguments. *)
let collect_tactics tree =
  let tacs = ref [] in
  let module Find_tactics =
    Typedtreeiter.Makeiterator(
        struct
          include Typedtreeiter.Defaultiteratorargument
          let enter_expression exp = match exp.Typedtree.exp_desc with
            | Typedtree.Texp_apply (f_exp,xs) ->
               (match f_exp.exp_desc with
                | Texp_ident (Path.Pident ident,_,_) ->
                   (match find_tactic_src ident with
                    | Some tac_meta ->
                       let f ident_map ident =
                         match find_thm_src ident with
                         | Some thm_meta -> Identmap.add ident thm_meta ident_map
                         | None -> ident_map in
                       let g b = function
                         | _,Some exp,_ -> fold_ident_expr f b exp
                         | _ -> b in
                       let thms = List.fold_left g Identmap.empty xs
                                  |> Identmap.to_list
                                  |> List.map snd in
                       tacs := (tac_meta, thms) :: !tacs
                    | None -> ())
                | _ -> ())
            | _ -> ()
        end) in
  Find_tactics.iter_structure tree; !tacs

let meta_tactic_diff_hook =
  {
    (env_diff_default () ([],[])) with
    Toploop.env_diff_parse =
      (fun tree e1 e2 () ->
       let thm_idents = meta_diff_hook.env_diff_parse tree e1 e2 () in
       let tac_idents = collect_tactics tree in
       (thm_idents,tac_idents));
    Toploop.env_diff_ident =
      (fun ident vd (dep_source_thms, dep_source_tactics) ->
       meta_diff_hook.env_diff_ident ident vd (dep_source_thms);
       if is_tactic vd then ignore (register_tactic_ident ident vd);
       ([], []))
  };;

let restore_hook = Toploop.set_env_diff_hook () meta_tactic_diff_hook;;
