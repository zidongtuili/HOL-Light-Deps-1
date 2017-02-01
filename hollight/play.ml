let magical ident vd =
  let tac_name = ident.Ident.name in
  let box = BOX_TAC tac_name [] in
  let tac = Obj.obj (Toploop.getvalue tac_name) in
  let rec magic_ap : 'a. Types.type_expr list -> 'a = function
    | [] -> tac
    | arg_vd::args_vds ->
       Obj.magic (magic_ap args_vds o magic_extract arg_vd)
  and magic_extract arg_vd =
    match get_constr arg_vd with
    | Some (c,[list_arg_vd]) when Path.same list_type_path c ->
       let f = magic_extract list_arg_vd in
       Obj.magic (fun thms -> Batlist.bind thms f)
    | Some (c,args) when Path.same thm_type_path c -> Obj.magic (fun thm -> [thm])
    | _ -> Obj.magic (fun _ -> []) in
  match tactic_antecedents vd with
  | Some ants -> Toploop.setvalue tac_name (Obj.repr (magic_ap ants))
  | None -> ()
