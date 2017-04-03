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

let rec tactic_antecedents ty =
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
  get_tactic_ty_expr_ants ty;;

let is_tactic_ty = Batoption.is_some o tactic_antecedents;;

type tactic_meta =
  {
    tactic_src  : unit Meta.srced;
    tactic_thms : thm list
  }

(* Registration of tactic identifiers. *)
let register_tactic_ident, find_tactic_src, get_tactic_srcs  =
  let reg, find_from_ident, get_tactic_srcs = mk_src_fns () in
  (fun modules ident vd -> reg modules ident vd.Types.val_loc),
  find_from_ident,
  get_tactic_srcs;;

(* Find tactic rators and return them together with any theorem arguments. *)
let collect_tactics tree =
  let module Tacset =
    Batset.Make(struct
                   type t = unit Meta.srced *
                              ((int * thm) list * thm) Meta.srced Identmap.t
                   let compare (src,thms) (src',thms') =
                     Batord.bin_comp
                       Meta.src_compare src src'
                       (Identmap.compare Meta.src_compare) thms thms'
                 end) in
  let tacs = ref Tacset.empty in
  let module Find_tactics =
    Typedtreeiter.Makeiterator(
        struct
          include Typedtreeiter.Defaultiteratorargument
          let enter_expression exp = match exp.Typedtree.exp_desc with
            | Typedtree.Texp_apply (f_exp,xs) ->
               (match f_exp.Typedtree.exp_desc with
                | Typedtree.Texp_ident (p,_,_) ->
                   (match resolve_path p with
                    | None -> ()
                    | Some (modules,ident) ->
                       (match find_tactic_src modules ident with
                        | Some tac_meta ->
                           let f ident_map modules id =
                             match find_thm_src modules id with
                            | Some thm_meta ->
                               Identmap.add (modules,id) thm_meta ident_map
                            | None -> ident_map in
                           let g b = function
                             | _,Some exp,_ -> fold_ident_expr f b exp
                             | _ -> b in
                           let thms = List.fold_left g Identmap.empty xs in
                           tacs := Tacset.add (tac_meta, thms) !tacs
                       | None -> ()))
                | _ -> ())
            | Typedtree.Texp_ident (p,_,_) ->
               (match resolve_path p with
                | Some (modules,ident) ->
                   (match find_tactic_src modules ident with
                    | Some tac_meta ->
                       tacs := Tacset.add (tac_meta, Identmap.empty) !tacs
                    | None -> ())
                | None -> ())
            | _ -> ()
        end) in
  Find_tactics.iter_expression tree;
  !tacs
  |> Tacset.to_list
  |> map (fun (tac,thms) -> tac,Identmap.to_list thms |> map snd)

let mk_tracked_thm = mk_tracked_thm_of_get_tactics collect_tactics

let list_type_path =
  !Toploop.toplevel_env
  |> Env.lookup_type (Longident.Lident "list")
  |> fst;;

(* Rebind a tactic to one which boxes itself with the theorems it has been applied *
to. *)
(* NOTE: This is dangerously magical -- expect bugs to manifest as segfaults. *)
(* TODO: Extend magic_extract to extract theorems from more foldable data
structures. Right now, we only deal with the identity and list foldables. *)
let (box_magically : (unit Meta.srced -> thm list -> tactic -> tactic)
                     -> int -> Obj.t -> Obj.t) = fun box_tac store_id tac ->
  let (modules,ident),vd = List.nth !id_vd_store store_id in
  let src = register_tactic_ident modules ident vd () in
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
  match tactic_antecedents vd.Types.val_type with
  | Some ants -> Obj.repr (magic_ap (box_tac src) (rev ants) [] tac)
  | None -> tac;;

let (box_tactic : int -> Obj.t -> Obj.t) = fun _ tac -> tac;;

Toploop.set_str_transformer
  ()
  (fun str () ->
   try
     resolve_str str;
     transform_str "thm_setup" "thm_teardown"
                   (fun ty ->
                    if is_tactic_ty ty then
                      Some "box_tactic"
                    else None)
                   (fun ty ->
                    if is_thm_ty ty then
                      Some "mk_tracked_thm"
                    else None)
                   str, ()
   with exn -> exns := exn :: !exns; str,());;
