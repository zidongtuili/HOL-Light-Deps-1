needs "tactics.ml";;

let rebind_boxed_tactic ident vd =
  match tactic_antecedents vd with
  | Some ants ->
     let tac_name = ident.Ident.name in
     let box = BOX_TAC tac_name [] in
     let rebind f =
       tac_name
       |> Toploop.getvalue
       |> Obj.obj
       |> f
       |> Obj.repr
       |> Toploop.setvalue tac_name in
     let ap1 f = box o f in
     let ap2 f = ap1 o f in
     let ap3 f = ap2 o f in
     let ap4 f = ap3 o f in
     (match length ants with
      | 0 -> rebind box
      | 1 -> rebind ap1
      | 2 -> rebind ap2
      | 3 -> rebind ap3
      | 4 -> rebind ap4)
  | None -> ();;

let list_type_path =
  !Toploop.toplevel_env
  |> Env.lookup_type (Longident.Lident "list")
  |> fst;;

let rec get_list_arg t = get_list_arg_of_desc t.Types.desc
and get_list_arg_of_desc = function
  | Types.Tconstr (p,[arg],_) when p = list_type_path -> Some (arg.Types.desc)
  | Types.Tlink t -> get_list_arg t
  | Types.Tsubst t -> get_list_arg t
  | t -> None;;

(* Rebind a tactic to one which boxes itself with the theorems it has been applied *
to. *)
(* NOTE: This is dangerously magical -- expect bugs to manifest as segfaults. *)
(* TODO: Extend magic_extract to extract theorems from more foldable data
structures. Right now, we only deal with the identity and list foldables. *)
let rebind_magically ident vd =
  let tac_name = ident.Ident.name in
  let (boxed : thm list -> tactic -> tactic) = fun thms tac ->
    BOX_TAC tac_name thms tac in
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
  let tac = Obj.obj (Toploop.getvalue tac_name) in
  match tactic_antecedents vd with
  | Some ants ->
     Toploop.setvalue tac_name (Obj.repr (magic_ap boxed (rev ants) [] tac))
  | None -> ();;

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
       if is_tactic vd then
         begin
           rebind_magically ident vd;
           ignore (register_tactic_ident ident vd)
         end;
       ([], []))

  };;
