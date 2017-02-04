type tac_thm = Tracked_thm of int | Concl of term
type tac_tree = (Ident.t * tac_thm list) list rose_tree
module Tacset = Batset.Make(struct type t = tac_tree let compare = compare end)

let rec tm_consts = function
  | Var _ -> []
  | Const (c,_) -> [c]
  | Comb (s,t) -> union (tm_consts s) (tm_consts t)
  | Abs (_,body) -> tm_consts body

let rec ty_consts = function
  | Tyvar _ -> []
  | Tyapp (c,args) ->
     Batlist.fold_left (fun tys ty -> union tys (ty_consts ty))
                       [c] args

let rec tm_ty_consts = function
  | Var (_,ty) -> ty_consts ty
  | Const (_,ty) -> ty_consts ty
  | Comb (s,t) -> union (tm_ty_consts s) (tm_ty_consts t)
  | Abs (Var (_,vty),body) ->
     union (ty_consts vty) (tm_ty_consts body)
  | Abs (_,_) -> failwith "BUG: Abstraction must be over a var."

module Meta =
  struct
    type 'a src =
      {
        src_id      : int;
        src_ident   : Ident.t;
        src_loc     : Location.t;
        src_obj     : 'a
      }
    type origination = Toplevel | Conjunct of int
    type 'thm t =
      {
        thm_id             : int;
        thm_src            : unit src;
        thm_origin         : origination;
        tracked_deps       : (int * 'thm) list;
        const_deps         : string list;
        ty_const_deps      : string list;
        new_consts         : string list;
        new_ty_consts      : string list;
        dep_source_thms    : ((int * 'thm) list * 'thm) src list;
        dep_source_tactics : (unit src * ((int * 'thm) list * 'thm) src list) list;
      }
    module Json =
      struct
        open Ezjsonm
        let rec of_ty = function
          | Tyvar v -> string v
          | Tyapp (c,args) -> list I (string c::List.map of_ty args)
        let rec of_tm = function
          | Var (v,ty) -> list I [string "V"; string v; of_ty ty]
          | Const (c,ty) -> list I [string "C"; string c; of_ty ty]
          | Comb (s,t) -> list I [of_tm s; of_tm t]
          | Abs (v,body) -> list I [string "\\"; of_tm v; of_tm body]
        let of_thm thm =
          dict
            [ "hyp", list of_tm (hyp thm)
            ; "concl", of_tm (concl thm)
            ]
        let of_thm_origin = function
          | Toplevel ->  string "toplevel"
          | Conjunct n ->
             (* Convert the integer to a string for Neo4j. *)
             pair string (string o string_of_int) ("conjunct",n)
        let of_ident id =
          dict
            [ "name", string id.Ident.name
            ]
        let strip_prefix pre str =
          match Batstring.Exceptionless.split ~by:pre str with
          | Some("",rest) -> rest
          | _ -> failwith "strip_prefix";;
        let of_location loc =
          let fname = loc.Location.loc_start.Lexing.pos_fname in
          let fname = tryfind (C strip_prefix fname) [!hol_dir; Sys.getcwd ()] in
          dict
            [ "filename", string fname
            ; "line", int loc.Location.loc_start.Lexing.pos_lnum
            ]
        let fields_of_src of_meta src =
          [ "src_id", int src.src_id
          ; "name", string (src.src_ident.Ident.name)
          ; "location", of_location src.src_loc ]
          @ of_meta src.src_obj
        let of_tactic_dep (tac,thms) =
          dict
            ["tactic", int tac.src_id
            ;"theorem_arguments", list (int o fun m -> m.src_id) thms ]
        let src_id thm_meta = thm_meta.thm_src.src_id
        let id_of_meta_src meta =
          fst (src_id meta,meta.thm_src.src_id)
        let of_id_thm_meta (id,thm,meta) =
          dict
            [ "tracking_id", int id
            ; "src_id", int (id_of_meta_src meta)
            ; "as", of_thm_origin meta.thm_origin
            ; "theorem", of_thm thm
            ; "stringified", string (string_of_thm thm)
            ; "constants", list string (tm_consts (concl thm))
            ; "type_constants", list string (tm_ty_consts (concl thm))
            ; "new_constants", list string meta.new_consts
            ; "new_type_constants", list string meta.new_ty_consts
            ; "tracked_dependencies", list (int o fst) meta.tracked_deps
            ; "source_code_theorem_dependencies",
              list (fun meta -> int meta.src_id) meta.dep_source_thms
            ; "source_code_tactic_dependencies",
              list of_tactic_dep meta.dep_source_tactics
            ]
      end
  end
