(* Replace every module item ... which defines idents xs recursively with
     let retry () = let xs = ... in xs in
     let xs = ... in
       let () = setup result in
       let xs =
         try
           retry ys
         with _ -> result
       let () = tear_down () in
       xs
     where ys consists of those xs of setup_arg_ty
 *)
let rec get_constr t = get_constr_of_desc t.Types.desc
and get_constr_of_desc = function
  | Types.Tconstr (p,args,_) -> Some (p,args)
  | Types.Tlink t -> get_constr t
  | Types.Tsubst t -> get_constr t
  | _ -> None;;

let id_vd_store = ref [];;
let rhs_tree = ref [];;
let rec transform_item path setup_id teardown_id rec_flag bnds env wrap =
  let module T = Typedtree in
  let module Ty = Types in
  let module L = Longident in
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
  let noloc = Location.mknoloc "" in
  let cunit =
    Env.lookup_constructor (Longident.Lident "()") !Toploop.toplevel_env in
  let cnil =
    Env.lookup_constructor (Longident.Lident "[]") !Toploop.toplevel_env in
  let ccons =
    Env.lookup_constructor (Longident.Lident "::") !Toploop.toplevel_env in
  let punit,_ = Env.lookup_type (Longident.Lident "unit") !Toploop.toplevel_env in
  let plist,_ = Env.lookup_type (Longident.Lident "list") !Toploop.toplevel_env in
  let unit_ty = Types.Tconstr (punit,[],ref Types.Mnil) in
  let exn_ty =
    let p,_ = Env.lookup_type (Longident.Lident "exn") !Toploop.toplevel_env in
    Ty.Tconstr (p,[],ref Ty.Mnil) in
  let int_ty =
    let p,_ = Env.lookup_type (Longident.Lident "int") !Toploop.toplevel_env in
    anon_ty (Ty.Tconstr (p,[],ref Ty.Mnil)) in
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
  (* TODO: Assert types of setup and teardown *)
  let setup_desc, setup_arg_ty =
    let setup_path,setup_vd =
      Env.lookup_value (Longident.Lident setup_id) !Toploop.toplevel_env in
    let Path.Pident setup_id = setup_path in
    let setup_id_desc =
      T.Texp_ident (setup_path,
                    Location.mknoloc (Longident.Lident setup_id.Ident.name),
                    setup_vd) in
    let setup_ty = setup_vd.Ty.val_type in
    let setup = anon_exp setup_id_desc setup_ty in
    let rec get_comp_ty t = get_comp_ty_of_desc t.Ty.desc
    and get_comp_ty_of_desc = function
      | Ty.Tlink t -> get_comp_ty t
      | Ty.Tsubst t -> get_comp_ty t
      | Ty.Ttuple [ty;_] -> ty in
    let rec get_elt_ty t = get_elt_ty_of_desc t.Ty.desc
    and get_elt_ty_of_desc = function
      | Ty.Tlink t -> get_elt_ty t
      | Ty.Tsubst t -> get_elt_ty t
      | Ty.Tconstr (_,[ty],_) -> get_comp_ty ty in
    let rec get_arg_ty t = get_arg_ty_of_desc t.Ty.desc
    and get_arg_ty_of_desc = function
      | Ty.Tlink t -> get_arg_ty t
      | Ty.Tsubst t -> get_arg_ty t
      | Ty.Tarrow (_,codom,_,_) -> get_elt_ty codom in
    setup,get_arg_ty setup_ty in
  let setup_arg_constr = get_constr setup_arg_ty in
  let teardown_exp =
    let teardown_path,teardown_vd =
      Env.lookup_value (Longident.Lident teardown_id) !Toploop.toplevel_env in
    let Path.Pident teardown_id = teardown_path in
    let teardown_desc =
      T.Texp_ident (teardown_path,
                    Location.mknoloc (Longident.Lident teardown_id.Ident.name),
                    teardown_vd) in
    let teardown_ty = teardown_vd.Ty.val_type in
    anon_exp (T.Texp_apply (anon_exp teardown_desc teardown_ty,
                            ["",Some unit_exp,T.Required]))
             (anon_ty unit_ty) in
  let nil_exp =
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
  let mk_list args = List.fold_right mk_cons args nil_exp in
  let item_desc = T.Tstr_value (rec_flag,bnds) in
  let item =
    {
      T.str_desc = item_desc;
      T.str_loc = Location.none;
      T.str_env = env
    } in
  let ids = Translmod.defined_idents [item] in
  let mk_setup exps =
    match exps with
    | [] -> None
    | exps ->
       let list = mk_list exps in
       Some (anon_exp (T.Texp_apply (setup_desc, ["",Some list,T.Required]))
                      (anon_ty unit_ty)) in
  let mk_wrap wrap_id i_exp exp ty =
    let wrap_path,wrap_vd =
      Env.lookup_value (Longident.Lident wrap_id) !Toploop.toplevel_env in
    let Path.Pident wrap_id = wrap_path in
    let wrap_desc =
      T.Texp_ident (wrap_path,
                    Location.mknoloc (Longident.Lident wrap_id.Ident.name),
                    wrap_vd) in
    let wrap_ty = wrap_vd.Ty.val_type in
    let wrap_ap1_ty = anon_ty (Ty.Tarrow ("",ty,ty,Ty.Cok)) in
    let wrap_ap1 =
      anon_exp (T.Texp_apply (anon_exp wrap_desc wrap_ty,
                              ["",Some i_exp,T.Required]))
               wrap_ap1_ty in
    anon_exp (T.Texp_apply (wrap_ap1, ["",Some exp,T.Required])) ty in
  let mk_tuples id_vds =
    let pats,exps,tys =
      List.fold_left (fun (pats,exps,tys) (id,vd,i_exp) ->
                      let lid =
                        Location.mknoloc (Longident.Lident (id.Ident.name)) in
                      let p = Path.Pident id in
                      let ty = vd.Ty.val_type in
                      let exp = anon_exp (T.Texp_ident (p, lid, vd)) ty in
                      let exp =
                        match wrap ty with
                        | None -> exp
                        | Some wrap_id -> mk_wrap wrap_id i_exp exp ty in
                      let pat = anon_pat (T.Tpat_var (id, noloc)) ty in
                      pat::pats,exp::exps,ty::tys)
                     ([],[],[]) id_vds in
    match List.rev pats,List.rev exps,List.rev tys with
    | [pat],[exp],[ty] -> pat,exp,ty
    | pats,exps,tys ->
       let tuple_pat_desc = T.Tpat_tuple pats in
       let tuple_exp_desc = T.Texp_tuple exps in
       let tuple_ty_desc = Ty.Ttuple tys in
       let tuple_ty = anon_ty tuple_ty_desc in
       anon_pat tuple_pat_desc tuple_ty,
       anon_exp tuple_exp_desc tuple_ty,
       tuple_ty in
  let id_vds,setup_id_vds,setup_exp =
    let id_vds,setup_id_vds,setup_exps,_ =
      List.fold_left (fun (id_vds,setup_id_vds,setup_exps,id_vd_num) id ->
                      let p = Path.Pident id in
                      let vd = Env.find_value p env in
                      let i_exp =
                        anon_exp (T.Texp_constant (Asttypes.Const_int id_vd_num))
                                 int_ty in
                      let pat,exp,ty = mk_tuples [id,vd,i_exp] in
                      let pair_ty = anon_ty (Ty.Ttuple [ty;int_ty]) in
                      let setup_pair =
                        anon_exp (T.Texp_tuple [exp;i_exp]) pair_ty in
                      let setup_exps,setup_id_vds =
                        if get_constr vd.Ty.val_type = setup_arg_constr then
                          setup_pair :: setup_exps, (id,vd) :: setup_id_vds
                        else setup_exps, setup_id_vds in
                      (id,vd,i_exp) :: id_vds,
                      setup_id_vds,
                      setup_exps,
                      id_vd_num + 1)
                     ([],[],[],List.length !id_vd_store) ids in
    List.rev id_vds,List.rev setup_id_vds,mk_setup (List.rev setup_exps) in
  let pid_vds =
    List.map (fun (id,_,vid) -> List.rev (id::path),vid) id_vds in
  id_vd_store := !id_vd_store @ pid_vds;
  rhs_tree := List.map snd bnds;
  let retry rest ty =
    let _,tuple_exp,tuple_ty = mk_tuples id_vds in
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
                   [anon_pat (T.Tpat_var (retry_ident,noloc)) ty,
                    anon_exp (T.Texp_function ("",[unit_pat,retry_body],T.Total))
                             tuple_ty],
                   rest (anon_exp (T.Texp_ident (Path.Pident retry_ident,
                                                 retry_loc,
                                                 retry_vd))
                                  (anon_ty retry_ty))))
      ty in
  let tuple_pat,tuple_exp,tuple_ty = mk_tuples id_vds in
  let local =
    match setup_exp with
    | None ->
       anon_exp (T.Texp_let (rec_flag,bnds,tuple_exp)) tuple_ty
    | Some setup_exp ->
       let app_retry retry =
         anon_exp (T.Texp_apply (retry, ["",Some unit_exp,T.Required]))
                  tuple_ty in
       let setup body = anon_exp (T.Texp_let (Asttypes.Nonrecursive,
                                              [unit_pat,setup_exp],
                                              body)) in
       let teardown body = anon_exp (T.Texp_let (Asttypes.Nonrecursive,
                                                 [unit_pat,teardown_exp],
                                                 body)) in
       let call_retry retry_exp =
         anon_exp (T.Texp_try (app_retry retry_exp,
                               [exn_pat,tuple_exp]))
                  tuple_ty in
       let id_vds2 =
         List.map (fun (id,vd,i_exp) -> Ident.rename id,vd,i_exp) id_vds in
       let tuple_pat2,tuple_exp2,_ = mk_tuples id_vds2 in
       retry
         (fun retry_exp ->
          anon_exp
            (T.Texp_let
               (rec_flag,
                bnds,
                setup (anon_exp (T.Texp_let (Asttypes.Nonrecursive,
                                             [tuple_pat2,call_retry retry_exp],
                                             teardown tuple_exp tuple_ty))
                                tuple_ty)
                      tuple_ty))
            tuple_ty)
         tuple_ty in
  let id_vds2 =
    List.map (fun (id,vd,i_exp) -> Ident.rename id,vd,i_exp) id_vds in
  let tuple_pat2,_,_ = mk_tuples id_vds2 in
  T.Tstr_value (Asttypes.Nonrecursive,[tuple_pat2,local]);;

let transform_str setup_id teardown_id wrap =
  id_vd_store := [];
  let rec transform_str path str =
    let module T = Typedtree in
    let transform_item item =
      { item with
        T.str_desc =
          match item.T.str_desc with
          | T.Tstr_value (rec_flag, bnds) ->
             transform_item path
                            setup_id
                            teardown_id
                            rec_flag
                            bnds
                            str.T.str_final_env
                            wrap
          | T.Tstr_module (id,loc,mod_exp) ->
             let mod_exp =
               { mod_exp with
                 T.mod_desc =
                   match mod_exp.T.mod_desc with
                   | T.Tmod_structure str ->
                      let str = transform_str (id :: path) str in
                      T.Tmod_structure str
                   | str -> str
               } in
             T.Tstr_module (id,loc,mod_exp)
          | desc -> desc
      } in
    { str with T.str_items = List.map transform_item str.T.str_items } in
  transform_str [];;

let print_path =
  BatList.print ~first:"" ~last:"" ~sep:"."
                (fun out id -> BatPrintf.fprintf out "%s" id.Ident.name);;
let foo_setup xs =
  let print out =
    BatPrintf.fprintf out "SETUP\n";
    List.iter (fun (x,i) -> BatPrintf.fprintf out "%d %a = %d\n%!"
                                              i print_path
                                              (fst (List.nth !id_vd_store i)) x)
              xs;
    () in
  print BatIO.stdout;;

let foo_teardown () = Printf.printf "TEARDOWN\n%!";;
let transform_str_foo = transform_str "foo_setup" "foo_teardown";;
let modify i x =
  BatPrintf.fprintf BatIO.stdout "Modifying: %a\n" print_path
                    (fst (List.nth !id_vd_store i));
  x * 100;;
let strs = ref [];;
  Toploop.set_str_transformer
    ()
    (fun str () ->
     try
       let p,_ = Env.lookup_type (Longident.Lident "int") !Toploop.toplevel_env in
       let str = transform_str_foo (fun ty ->
                                    let f = function
                                      | p',[] when p = p' -> Some "modify"
                                      | _ -> None in
                                    BatOption.bind (get_constr ty) f) str in
       Printtyped.implementation Format.std_formatter str;
       str,()
     with _ -> str,());;
(* Toploop.set_str_transformer () (fun str () -> str,());; *)
