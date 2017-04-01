let zip_with_index f xs =
  List.rev (snd (List.fold_left (fun (n,xs) x -> (n+1,f x n :: xs)) (0,[]) xs));;

let rec get_constr t = get_constr_of_desc t.Types.desc
and get_constr_of_desc = function
  | Types.Tconstr (p,args,_) -> Some (p,args)
  | Types.Tlink t -> get_constr t
  | Types.Tsubst t -> get_constr t
  | _ -> None;;

(* Replace the module item
     let x = ...
   with
     let x = [init] [i] x in
     let () = [setup [x,i]] in
     let x = try
               [init] [i] x in
             with _ -> x
     let () = [teardown ()] in
     [post_setup] [i] x
*)
let id_vd_store = ref [];;
let rhs_tree = ref [];;
let rec transform_item
          qualifiers setup_id teardown_id rec_flag bnds env wrap_init post_setup =
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
  let vds = List.map (fun id -> let p = Path.Pident id in
                                let vd = Env.find_value p env in
                                vd) ids in
  let ids_fresh = List.map (fun id -> id,Ident.rename id) ids in
  let id_vds = List.combine ids vds in
  let id_vds_fresh = BatList.map2 (fun (_,id) vd -> id,vd) ids_fresh vds in
  let refresh id_vds = List.map (fun (id,vd) -> Ident.rename id,vd) id_vds in
  let module Rename : TypedtreeMap.MapArgument =
    struct
      include TypedtreeMap.DefaultMapArgument
      let enter_pattern pat =
        { pat with
          T.pat_desc = match pat.T.pat_desc with
                       | T.Tpat_var (id,loc) as p ->
                          (try
                              let id = List.assoc id ids_fresh in
                              T.Tpat_var (id,loc)
                            with _ -> p)
                       | T.Tpat_alias (pat,id,loc) as p ->
                          (try
                              let id = List.assoc id ids_fresh in
                              T.Tpat_alias (pat,id,loc)
                          with _ -> p)
                       | p -> p
        }
      let enter_expression exp =
        { exp with
          T.exp_desc = match exp.T.exp_desc with
                       | T.Texp_ident (Path.Pident id,l,vd) ->
                          (try
                              let id = List.assoc id ids_fresh in
                              T.Texp_ident (Path.Pident id,l,vd)
                            with _ -> exp.T.exp_desc)
                       | exp -> exp
        }
    end in
  let module RenameMap = TypedtreeMap.MakeMap(Rename) in
  let bnds_fresh =
    List.map (fun (pat,rhs) ->
              RenameMap.map_pattern pat, RenameMap.map_expression rhs) bnds in
  let mk_setup exps =
    match exps with
    | [] -> None
    | exps ->
       let list = mk_list exps in
       Some (anon_exp (T.Texp_apply (setup_desc, ["",Some list,T.Required]))
                      (anon_ty unit_ty)) in
  let mk_wrap wrap_id iexp exp ty =
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
                              ["",Some iexp,T.Required]))
               wrap_ap1_ty in
    anon_exp (T.Texp_apply (wrap_ap1, ["",Some exp,T.Required])) ty in
  let mk_ty vd = vd.Ty.val_type in
  let mk_tuple_ty = function
    | [vd] -> mk_ty vd
    | vds ->
       let tys = List.map mk_ty vds in
       let tuple_ty_desc = Ty.Ttuple tys in
       anon_ty tuple_ty_desc in
  let mk_pat (id,vd) =
    let ty = vd.Ty.val_type in
    anon_pat (T.Tpat_var (id, noloc)) ty in
  let mk_tuple_pat = function
    | [id,vd] -> mk_pat (id,vd)
    | id_vds ->
       let pats = List.map mk_pat id_vds in
       let tuple_pat_desc = T.Tpat_tuple pats in
       let ty = mk_tuple_ty (List.map snd id_vds) in
       anon_pat tuple_pat_desc ty in
  let mk_exp_ty (id,vd) =
    let lid =
      Location.mknoloc (Longident.Lident (id.Ident.name)) in
    let p = Path.Pident id in
    let ty = vd.Ty.val_type in
    anon_exp (T.Texp_ident (p, lid, vd)) ty,ty in
  let mk_wrap_exp wrap (id,vd,iexp) =
    let exp,ty = mk_exp_ty (id,vd) in
    match wrap ty with
    | None -> exp
    | Some wrap_id -> mk_wrap wrap_id iexp exp ty in
  let mk_tuple_exp = function
    | [id_vd] -> fst (mk_exp_ty id_vd)
    | id_vds ->
       let exps = List.map (fst % mk_exp_ty) id_vds in
       let tuple_exp_desc = T.Texp_tuple exps in
       let tuple_ty = mk_tuple_ty (List.map snd id_vds) in
       anon_exp tuple_exp_desc tuple_ty in
  let mk_tuple_exp_wrap wrap = function
    | [id_vd_iexp] -> mk_wrap_exp wrap id_vd_iexp
    | id_vd_iexps ->
       let exps = List.map (mk_wrap_exp wrap) id_vd_iexps in
       let tuple_exp_desc = T.Texp_tuple exps in
       let tuple_ty = mk_tuple_ty (List.map (fun (_,vd,_) -> vd) id_vd_iexps) in
       anon_exp tuple_exp_desc tuple_ty in
  let store_length = List.length !id_vd_store in
  let mk_id_vd_iexps id_vds =
    zip_with_index (fun (id,vd) i ->
                    let i = i + store_length in
                    let iexp =
                      anon_exp (T.Texp_constant (Asttypes.Const_int i)) int_ty in
                    id,vd,iexp) id_vds in
  let pid_vds =
    List.map (fun (id,vid) -> (List.rev qualifiers,id),vid) id_vds in
  id_vd_store := !id_vd_store @ pid_vds;
  rhs_tree := List.map snd bnds;
  let tuple_ty = mk_tuple_ty (List.map snd id_vds) in
  let wrap_bnds rest ty =
    let id_vd_iexps = mk_id_vd_iexps id_vds_fresh in
    let wrap_init_tuple = mk_tuple_exp_wrap wrap_init id_vd_iexps in
    let id_vds2 = refresh id_vds in
    let tuple_pat = mk_tuple_pat id_vds2 in
    let tuple_exp = mk_tuple_exp id_vds2 in
    anon_exp (T.Texp_let (rec_flag,
                          bnds_fresh,
                          anon_exp (T.Texp_let (Asttypes.Nonrecursive,
                                                [tuple_pat,wrap_init_tuple],
                                                rest id_vd_iexps tuple_exp))
                                   ty))
             ty in
  let let_retry rest ty =
    let retry_ident = Ident.create "retry" in
    let retry_loc = Location.mknoloc (Longident.Lident (retry_ident.Ident.name)) in
    let retry_ty = Ty.Tarrow ("",anon_ty unit_ty,tuple_ty,Ty.Cok) in
    let retry_vd =
      {
        Ty.val_type = anon_ty retry_ty;
        Ty.val_kind = Ty.Val_reg;
        Ty.val_loc = Location.none
      } in
    let retry_exp =
      anon_exp (T.Texp_ident (Path.Pident retry_ident,
                              retry_loc,
                              retry_vd))
               (anon_ty retry_ty) in
    anon_exp
      (T.Texp_let (Asttypes.Nonrecursive,
                   [anon_pat (T.Tpat_var (retry_ident,noloc)) ty,
                    anon_exp (T.Texp_function ("",[unit_pat,
                                                   wrap_bnds (fun _ tuple -> tuple)
                                                             tuple_ty],
                                               T.Total))
                             tuple_ty],
                   rest retry_exp ty))
      ty in
  let main =
    let rest retry ty =
      let rest id_vd_iexps tuple_exp =
        let setup_exp =
          let setup_args =
            BatList.filter_map
              (fun (id,vd,iexp) ->
               let exp,ty = mk_exp_ty (id,vd) in
               let pair_ty = anon_ty (Ty.Ttuple [ty;int_ty]) in
               let setup_pair =
                 anon_exp (T.Texp_tuple [exp;iexp]) pair_ty in
               if get_constr vd.Ty.val_type = setup_arg_constr then
                 Some setup_pair
               else None)
              id_vd_iexps in
          mk_setup setup_args in
        match setup_exp with
        | None -> tuple_exp
        | Some setup_exp ->
           let app_retry =
             anon_exp (T.Texp_apply (retry, ["",Some unit_exp,T.Required]))
                      tuple_ty in
           let setup body = anon_exp (T.Texp_let (Asttypes.Nonrecursive,
                                                  [unit_pat,setup_exp],
                                                  body)) in
           let teardown body = anon_exp (T.Texp_let (Asttypes.Nonrecursive,
                                                     [unit_pat,teardown_exp],
                                                     body)) in
           let id_vds2 = refresh id_vds in
           let tuple_pat2 = mk_tuple_pat id_vds2 in
           let id_vd_iexps2 = mk_id_vd_iexps id_vds2 in
           let tuple_exp2 = mk_tuple_exp_wrap post_setup id_vd_iexps2 in
           let retry_and_teardown =
             anon_exp
               (T.Texp_let (Asttypes.Nonrecursive,
                            [tuple_pat2,anon_exp (T.Texp_try (app_retry,
                                                              [exn_pat,tuple_exp]))
                                                 tuple_ty],
                            teardown tuple_exp2 tuple_ty))
               tuple_ty in
           setup retry_and_teardown tuple_ty in
      wrap_bnds rest tuple_ty in
    let_retry rest tuple_ty in
  let tuple_pat = mk_tuple_pat id_vds in
  T.Tstr_value (Asttypes.Nonrecursive,[tuple_pat,main]);;

let transform_str setup_id teardown_id wrap_init post_setup =
  id_vd_store := [];
  let rec transform_str qualifiers str =
    let module T = Typedtree in
    let transform_item item =
      { item with
        T.str_desc =
          match item.T.str_desc with
          | T.Tstr_value (rec_flag, bnds) ->
             transform_item qualifiers
                            setup_id
                            teardown_id
                            rec_flag
                            bnds
                            str.T.str_final_env
                            wrap_init
                            post_setup
          | T.Tstr_module (id,loc,mod_exp) ->
             let mod_exp =
               { mod_exp with
                 T.mod_desc =
                   match mod_exp.T.mod_desc with
                   | T.Tmod_structure str ->
                      let str = transform_str (id :: qualifiers) str in
                      T.Tmod_structure str
                   | str -> str
               } in
             T.Tstr_module (id,loc,mod_exp)
          | desc -> desc
      } in
    { str with T.str_items = List.map transform_item str.T.str_items } in
  transform_str [];;

let my_vds = ref [];;
let print_path out (ids,id) =
  BatList.print ~first:"" ~last:"" ~sep:"."
                (fun out id -> BatPrintf.fprintf out "%s" id.Ident.name)
                out
                (ids @ [id]);;
let foo_setup xs =
  let print out =
    BatPrintf.fprintf out "SETUP\n";
    List.iter (fun (x,i) ->
               let p,vd = List.nth !id_vd_store i in
               my_vds := vd :: !my_vds;
               BatPrintf.fprintf out "%d %a = %d\n%!"
                                 i
                                 print_path p
                                 x)
              xs;
    () in
  print BatIO.stdout;;

let foo_teardown () = Printf.printf "TEARDOWN\n%!";;
let transform_str_foo = transform_str "foo_setup" "foo_teardown";;
let modify i x =
  BatPrintf.fprintf BatIO.stdout "Modifying: %a\n" print_path
                    (fst (List.nth !id_vd_store i));
  x * 100;;
let modify2 i x =
  BatPrintf.fprintf BatIO.stdout "Modifying again: %a\n" print_path
                    (fst (List.nth !id_vd_store i));
  x * 200;;
let exns = ref [];;
let strs = ref [];;
Toploop.set_str_transformer
  ()
  (fun str () ->
   try
     let p,_ = Env.lookup_type (Longident.Lident "int") !Toploop.toplevel_env in
     (* Printtyped.implementation Format.std_formatter str; *)
     let str = transform_str_foo (fun ty ->
                                  let f = function
                                    | p',[] when p = p' -> Some "modify"
                                    | _ -> None in
                                  BatOption.bind (get_constr ty) f)
                                 (fun ty ->
                                  let f = function
                                    | p',[] when p = p' -> Some "modify2"
                                    | _ -> None in
                                  BatOption.bind (get_constr ty) f)
                                 str in
     (* Printtyped.implementation Format.std_formatter str; *)
     str,()
   with exn -> exns := exn :: !exns; str,());;
(* Toploop.set_str_transformer () (fun str () -> str,());; *)
