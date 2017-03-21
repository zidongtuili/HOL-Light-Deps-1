type modular_id =
  Module of Ident.t
            * Types.module_type
            * Env.t
            * Types.signature
            * Env.t
            * modular_id list
  | Ident of Ident.t * Types.value_description

let rec split3 = function
  | [] -> [],[],[]
  | (x,y,z) :: xyzs ->
     let xs,ys,zs = split3 xyzs in
     x::xs, y::ys, z::zs

(* Replace every module item ... which defines idents xs recursively with
     let retry () = ... in
     let ... in
       let _ = setup result in
       try
         retry
       with _ -> result
     where ys consists of those xs of setup_arg_ty
 *)
let rec get_constr t = get_constr_of_desc t.Types.desc
and get_constr_of_desc = function
  | Types.Tconstr (p,args,_) -> Some (p,args)
  | Types.Tlink t -> get_constr t
  | Types.Tsubst t -> get_constr t
  | _ -> None;;

let rec transform_item setup_id rec_flag bnds env =
  let module T = Typedtree in
  let module Ty = Types in
  let module L = Longident in
  let noloc = Location.mknoloc "" in
  let anon_pat desc ty =
    {
      T.pat_desc = desc;
      T.pat_loc = Location.none;
      T.pat_extra = [];
      T.pat_type = ty;
      T.pat_env = Env.empty (* TODO: Okay?*)
    } in
  let anon_exp desc ty =
    {
      T.exp_desc = desc;
      T.exp_loc = Location.none;
      T.exp_extra = [];
      T.exp_type = ty;
      T.exp_env = Env.empty (* TODO: Okay?*)
    } in
  let anon_ty desc =
    {
      Ty.desc = desc;
      Ty.level = -1; (* TODO: Double check *)
      Ty.id = -1 (* TODO: Double check *)
    } in
  let setup_fun_desc, setup_arg_ty =
    let setup_path,setup_vd =
      Env.lookup_value (Longident.Lident setup_id) !Toploop.toplevel_env in
    let Path.Pident setup_id = setup_path in
    let setup_id_desc =
      T.Texp_ident (setup_path,
                    Location.mknoloc (Longident.Lident setup_id.Ident.name),
                    setup_vd) in
    let setup_ty = setup_vd.Ty.val_type in
    let setup_fun = anon_exp setup_id_desc setup_ty in
    let rec get_arg_ty t = get_arg_ty_of_desc t.Ty.desc
    and get_arg_ty_of_desc = function
      | Ty.Tlink t -> get_arg_ty t
      | Ty.Tsubst t -> get_arg_ty t
      | Ty.Tarrow (_,codom,_,_) -> get_elt_ty codom
    and get_elt_ty t = get_elt_ty_of_desc t.Ty.desc
    and get_elt_ty_of_desc = function
      | Ty.Tlink t -> get_elt_ty t
      | Ty.Tsubst t -> get_elt_ty t
      | Ty.Tconstr (_,[ty],_) -> ty in
    setup_fun,get_arg_ty setup_ty in
  let setup_arg_constr = get_constr setup_arg_ty in
  let cunit =
    Env.lookup_constructor (Longident.Lident "()") !Toploop.toplevel_env in
  let cnil =
    Env.lookup_constructor (Longident.Lident "[]") !Toploop.toplevel_env in
  let ccons =
    Env.lookup_constructor (Longident.Lident "::") !Toploop.toplevel_env in
  let plist,_ = Env.lookup_type (Longident.Lident "list") !Toploop.toplevel_env in
  let punit,_ = Env.lookup_type (Longident.Lident "unit") !Toploop.toplevel_env in
  let unit_ty = Types.Tconstr (punit,[],ref Types.Mnil) in
  let nil =
    anon_exp (Typedtree.Texp_construct (Location.mknoloc (Longident.Lident "[]"),
                                        cnil,
                                        [],
                                        false))
             (anon_ty (Types.Tconstr (plist,[setup_arg_ty],ref Types.Mnil))) in
  let list_ty = anon_ty (Types.Tconstr (plist,[setup_arg_ty],ref Types.Mnil)) in
  let mk_cons exp exps =
    anon_exp (Typedtree.Texp_construct (Location.mknoloc (Longident.Lident "::"),
                                        ccons,
                                        [exp;exps],
                                        false))
             list_ty in
  let mk_list args = List.fold_right mk_cons args nil in
  let exn_ty =
    let p = !Toploop.toplevel_env
            |> Env.lookup_type (Longident.Lident "exn")
            |> fst in
    Ty.Tconstr (p,[],ref Ty.Mnil) in
  let unit_loc = Location.mknoloc (Longident.Lident "unit") in
  let unit_pat =
    anon_pat (T.Tpat_construct (unit_loc,
                                cunit,
                                [],
                                true))
             (anon_ty unit_ty) in
  let exn_pat = anon_pat T.Tpat_any (anon_ty exn_ty) in
  let unit_exp = anon_exp (T.Texp_construct (unit_loc,cunit,[],true))
                          (anon_ty unit_ty) in
  let item_desc = T.Tstr_value (rec_flag,bnds) in
  let item =
    {
      T.str_desc = item_desc;
      T.str_loc = Location.none;
      T.str_env = env
    } in
  let ids = Translmod.defined_idents [item] in
  let get_pat_exp id =
    let newid = Ident.rename id in
    let p = Path.Pident id in
    let newp = Path.Pident newid in
    let vd = Env.find_value p env in
    let ty = vd.Ty.val_type in
    let lid = Location.mknoloc (Longident.Lident (id.Ident.name)) in
    anon_pat (T.Tpat_var (newid, noloc)) ty,
    anon_exp (T.Texp_ident (p, lid, vd)) ty,
    ty in
  let mk_setup exps =
    match List.filter (fun exp -> get_constr exp.T.exp_type = setup_arg_constr)
                      exps with
    | [] -> None
    | exps ->
       let list = mk_list exps in
       Some (anon_exp (T.Texp_apply (setup_fun_desc, ["",Some list,T.Required]))
                      (anon_ty unit_ty)) in
  let tuple_pat, tuple_exp, setup_exp, tuple_ty =
    match List.map get_pat_exp ids with
    | [pat,exp,ty] -> pat,exp,mk_setup [exp],ty
    | patexpstys ->
       let pats,exps,tys = split3 patexpstys in
       let tuple_pat_desc = T.Tpat_tuple pats in
       let tuple_exp_desc = T.Texp_tuple exps in
       let tuple_ty_desc = Ty.Ttuple tys in
       let tuple_ty = anon_ty tuple_ty_desc in
       anon_pat tuple_pat_desc tuple_ty,
       anon_exp tuple_exp_desc tuple_ty,
       mk_setup exps,
       tuple_ty in
  let retry rest ty =
    let retry_ident = Ident.create "retry" in
    let retry_body = anon_exp (T.Texp_let (rec_flag,bnds,tuple_exp)) tuple_ty in
    let retry_loc = Location.mknoloc (Longident.Lident (retry_ident.Ident.name)) in
    let retry_ty = Ty.Tarrow ("",anon_ty unit_ty,tuple_ty,Ty.Cok) in
    let retry_vd =
      {
        Ty.val_type = anon_ty retry_ty;
        Ty.val_kind = Ty.Val_reg;
        Ty.val_loc = Location.none
      } in
    anon_exp
      (T.Texp_let (Asttypes.Nonrecursive,
                   [anon_pat (Tpat_var (retry_ident,noloc)) ty,
                    anon_exp (Texp_function ("",[unit_pat,retry_body],T.Total))
                             tuple_ty],
                   rest (anon_exp (T.Texp_ident (Path.Pident retry_ident,
                                                 retry_loc,
                                                 retry_vd))
                                  (anon_ty retry_ty))))
      ty in
  let app_retry retry =
    anon_exp (T.Texp_apply (retry, ["",Some unit_exp,T.Required]))
             tuple_ty in
  let local =
    match setup_exp with
    | None -> anon_exp (T.Texp_let (rec_flag,bnds,tuple_exp)) tuple_ty
    | Some setup_exp ->
       retry
         (fun retry_exp ->
          anon_exp
            (T.Texp_let
               (rec_flag,
                bnds,
                anon_exp (T.Texp_let (Asttypes.Nonrecursive,
                                      [unit_pat,setup_exp],
                                      anon_exp (T.Texp_try (app_retry retry_exp,
                                                            [exn_pat,tuple_exp]))
                                               tuple_ty))
                         tuple_ty))
            tuple_ty)
         tuple_ty in
  T.Tstr_value (Asttypes.Nonrecursive,[tuple_pat,local]);;

let transform_str setup_id =
  let rec transform_str str =
    let module T = Typedtree in
    let transform_item item =
      { item with
        T.str_desc =
          match item.T.str_desc with
          | T.Tstr_value (rec_flag, bnds) ->
             transform_item setup_id rec_flag bnds str.T.str_final_env
          | T.Tstr_module (id,loc,mod_exp) ->
             let mod_exp =
               { mod_exp with
                 T.mod_desc =
                   match mod_exp.T.mod_desc with
                   | T.Tmod_structure str -> T.Tmod_structure (transform_str str)
                   | str -> str
               } in
             T.Tstr_module (id,loc,mod_exp)
          | desc -> desc
      } in
    { str with T.str_items = List.map transform_item str.T.str_items } in
  transform_str;;

let foo xs = Printf.printf "%d\n%!" (List.fold_left (+) 0 xs);;
let transform_str_foo = transform_str "foo";;
let strs = ref [];;
  Toploop.set_str_transformer ()
                              (fun str () ->
                               try
                                 let str = transform_str_foo str in
                                 Printtyped.implementation Format.std_formatter str;
                                 str,()
                               with _ -> str,());;
