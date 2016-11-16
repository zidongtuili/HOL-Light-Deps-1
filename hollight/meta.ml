needs "record.ml";;
needs "more-lib.ml";;

module Identifying(Ord: Orderedtype) :
sig
  val lookup : Ord.t -> int
end =
  struct
    module Map = Batmap.Make(Ord)
    let counter = ref 0
    let map = ref Map.empty
    let lookup x =
      match Map.Exceptionless.find x !map with
      | None ->
         let id = !counter in
         incr counter;
         map := Map.add x id !map;
         id
      | Some id -> id
  end

(* Identify theorems in Ocaml syntax tree. *)
let rec get_constr t = get_constr_of_desc t.Types.desc
and get_constr_of_desc = function
  | Types.Tconstr (p,_,_) -> Some p
  | Types.Tlink t -> get_constr t
  | Types.Tsubst t -> get_constr t
  | _ -> None;;

let thm_type_path =
  !Toploop.toplevel_env
  |> Env.lookup_type (Longident.Lident "thm")
  |> fst;;

let is_thm d =
  d.Types.val_type
  |> get_constr
  |> Batoption.map_default (Path.same thm_type_path) false;;

(* TODO: Exceptions here will be thrown in the other hook. These
   should only indicate bugs in the dependency tracking, but still,
   better error rep orting would be nice. *)
let exns = ref []
let env_diff_default s t =
  {
    Toploop.env_diff_default s t with
    Toploop.env_diff_parse_exc = (fun exn _ -> exns := exn :: !exns;
                                               Printf.printf "Exception!"; t);
    Toploop.env_diff_ident_exc = (fun exn _ -> exns := exn :: !exns;
                                               Printf.printf "Exception!"; s)
  };;

module Stringmap = Batmap.Make_ext(struct type t = string let compare = compare end)
module Intmap = Batmap.Make_ext(struct type t = int let compare = compare end)
module Identcmp =
  struct
    type t = Ident.t
    let compare id id' = compare (id.Ident.stamp) (id'.Ident.stamp)
  end
module Identmap = Batmap.Make_ext(Identcmp)

module Depmap =
  Batmap.Make_ext(struct type t = dep_info let compare = compare_dep_info end)

(* info_deps is a map from the dep_info of a theorem to that theorem's transitive
   dependencies. get_iterated_deps updates this map with the transitive dependencies
   for all depinfos that can be reached from thm. *)
let get_iterated_deps info_deps thm =
  let rec iterated_deps info_deps (thm,info) =
    match Depmap.Exceptionless.find info info_deps with
    | Some (deps,trans_deps) -> deps,trans_deps,info_deps
    | None ->
       let depinfos = thm_deps thm in
       let deps,trans_deps,info_deps =
         List.fold_left f (Intmap.empty,Intmap.empty,info_deps) depinfos in
       deps,trans_deps,Depmap.add info (deps,trans_deps) info_deps
  and f (deps,trans_deps,info_deps) (dep,info) =
    (* We're accumulating dependencies at the same level as (dep,info). *)
    let sub_deps,sub_trans_deps,info_deps = iterated_deps info_deps (dep,info) in
    (* sub_deps and sub_trans_deps are, respectively, the dependencies and transitive
       dependencies of dep. *)
    let union = Intmap.merge (fun _ x y -> sum_option_fst x y) in
    (* Update the deps. If dep is tracked, we add it to the accumulating deps, and
    add its own dependencies to its transitive dependency map. If dep is a duplicate,
    we leave the transitive dependency map unchanged. If the duplicate isn't a
    transitive dependency, we add the dependencies of dep to the accumulating
    deps. If the duplicate is a unique tracked transitive dependency, we add the
    tracked theorem to the accumulating deps. *)
    let deps, trans_deps =
      match get_tracking info with
      | Tracked id -> Intmap.add id dep deps, Intmap.add id sub_deps trans_deps
      | Duplicate ids ->
         let deps =
           match filter (C Intmap.mem sub_trans_deps) ids with
           | [] -> union deps sub_deps
           | [dup_id] -> Intmap.add dup_id dep deps
           | _ -> failwith "Duplicate has two proofs in the dependency graph." in
         deps, trans_deps in
    deps,trans_deps,info_deps in
  List.fold_left f (Intmap.empty,Intmap.empty,info_deps) (thm_deps thm)

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
    type thm_origination = Toplevel | Conjunct of int
    type ident_meta =
      {
        ident_id    : int;
        ident_loc   : string * Location.t;
        filename_id : int;
        ident_thm   : thm;
        tracked_ids : int list;
      }
    type meta =
      {
        tracking_src_loc : ident_meta * thm_origination;
        tracked_deps     : (int * thm) list;
        const_deps       : string list;
        ty_const_deps    : string list;
        new_consts       : string list;
        new_ty_consts    : string list;
        source_code_deps : ident_meta list;
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
        let of_thm_type = function
          | Toplevel ->  string "toplevel"
          | Conjunct n ->
             (* Convert the integer to a string for Neo4j. *)
             pair string (string o string_of_int) ("conjunct",n)
        let of_ident id =
          dict
            [ "name", string id.Ident.name
            ]
        let of_location loc =
          let fname =
            Batstring.lchop ~n:(Batstring.length !hol_dir + 1)
                            (loc.Location.loc_start.Lexing.pos_fname) in
          dict
            [ "filename", string fname
            ; "line", int loc.Location.loc_start.Lexing.pos_lnum
            ]
        let of_ident_meta_id meta = int meta.ident_id
        let of_ident_meta meta =
          let name,loc = meta.ident_loc in
          dict [ "ident_id", int meta.ident_id
               ; "name", string name
               ; "location", of_location loc
               ; "tracked_ids", list int meta.tracked_ids
               ; "stringified", string (string_of_thm meta.ident_thm)]
        let of_id_thm_meta (id,thm,meta) =
          dict
            [ "tracking_id", int id
            ; "src_id", pair of_ident_meta_id of_thm_type meta.tracking_src_loc
            ; "theorem", of_thm thm
            ; "stringified", string (string_of_thm thm)
            ; "constants", list string (tm_consts (concl thm))
            ; "type_constants", list string (tm_ty_consts (concl thm))
            ; "new_constants", list string meta.new_consts
            ; "new_type_constants", list string meta.new_ty_consts
            ; "tracked_dependencies", list (int o fst) meta.tracked_deps
            ; "source_code_dependencies", list of_ident_meta_id meta.source_code_deps
            ]
      end
  end

let (meta_map : (thm * Meta.meta) Intmap.t ref) = ref Intmap.empty;;
let (ident_meta_from_id_map : Meta.ident_meta Intmap.t ref) = ref Intmap.empty;;
let (const_def_map : int list Stringmap.t ref) = ref Stringmap.empty;;
let (ty_const_def_map : int list Stringmap.t ref) = ref Stringmap.empty;;

let get_deps, get_trivial_duplicates =
  let (dep_resolve : (thm Intmap.t * thm Intmap.t Intmap.t) Depmap.t ref) =
    ref Depmap.empty in
  let get_deps thm =
    let deps, trans_deps, the_dep_resolve = get_iterated_deps !dep_resolve thm in
    dep_resolve := the_dep_resolve;
    match map_option (fun (id,_) -> Intmap.Exceptionless.find id trans_deps)
                     (find_duplicates thm) with
    | [] -> deps |> Intmap.to_list
    | [deps] -> deps |> Intmap.to_list
    | _ -> failwith "Duplicate has two proofs in the dependency graph." in
  let get_trivial_duplicates thm =
    let deps, trans_deps, the_dep_resolve = get_iterated_deps !dep_resolve thm in
    dep_resolve := the_dep_resolve;
    filter (fun (id,thm) -> Intmap.mem id trans_deps or Intmap.mem id deps)
           (find_duplicates thm) in
  get_deps,get_trivial_duplicates

let meta_of_thm src_loc id thm =
  let const_subdeps =
    let deps = get_deps thm in
    Batlist.fold_left
      (fun consts (_,thm) -> union consts (const_deps thm)) [] deps in
  let ty_const_subdeps =
    let deps = get_deps thm in
    Batlist.fold_left (fun tys (_,thm) -> union tys (ty_const_deps thm)) [] deps in
  let new_consts = List.filter (not o C mem const_subdeps) (const_deps thm) in
  let new_ty_consts =
    List.filter (not o C mem ty_const_subdeps) (ty_const_deps thm) in
  const_def_map :=
    List.fold_left (fun map c ->
                    Stringmap.modify_def [id] c (fun ids -> union [id] ids) map)
                   !const_def_map new_consts;
  ty_const_def_map :=
    List.fold_left (fun map c ->
                    Stringmap.modify_def [id] c (fun ids -> union [id] ids) map)
                   !ty_const_def_map new_ty_consts;
  {
    Meta.tracking_src_loc = src_loc;
    Meta.tracked_deps = get_deps thm;
    Meta.const_deps = const_deps thm;
    Meta.ty_const_deps = ty_const_deps thm;
    Meta.new_consts =
      List.filter (not o C mem const_subdeps) (const_deps thm);
    Meta.new_ty_consts =
      List.filter (not o C mem ty_const_subdeps) (ty_const_deps thm);
    Meta.source_code_deps = []
  };;

let collect_ids, register_ident =
  let (ident_meta_map : Meta.ident_meta Identmap.t ref) =
    ref Identmap.empty in
  let collect_ids tree =
    let stamps = ref Identmap.empty in
    let module Idcollector =
      Typedtreeiter.Makeiterator(
          struct
            include Typedtreeiter.Defaultiteratorargument
            let enter_expression exp =
              match exp.Typedtree.exp_desc with
              | Typedtree.Texp_ident (Path.Pident ident,_,desc) ->
                 (match Identmap.Exceptionless.find ident !ident_meta_map with
                  | Some meta -> stamps := Identmap.add ident meta !stamps
                  | None -> ())
              | _ -> ()
          end) in
    Idcollector.iter_structure tree;
    map snd (Identmap.to_list !stamps) in
  let register_ident =
    let module Filename_ids =
      Identifying(struct type t = string let compare = compare end) in
    let ident_id_counter = ref 0 in
    fun ident thm vd ids ->
    match Identmap.Exceptionless.find ident !ident_meta_map with
    | None ->
       let ident_id = !ident_id_counter in
       incr ident_id_counter;
       let filename = vd.Types.val_loc.Location.loc_start.Lexing.pos_fname in
       let filename_id = Filename_ids.lookup filename in
       let meta =
         {
           Meta.ident_id = ident_id;
           Meta.ident_loc = ident.Ident.name, vd.Types.val_loc;
           Meta.filename_id = filename_id;
           Meta.ident_thm = thm;
           Meta.tracked_ids = ids
         } in
       ident_meta_map := Identmap.add ident meta !ident_meta_map;
       ident_meta_from_id_map := Intmap.add ident_id meta !ident_meta_from_id_map;
       meta
    | Some meta -> meta in
  collect_ids, register_ident;;

let (meta_diff_hook : (unit,'a list) Toploop.env_diff_hooks) =
  let register_toplevel_thm ident vd dep_idents thm =
    match get_trivial_duplicates thm with
    | [] ->
       let id,thm = with_tracking thm in
       Toploop.setvalue (Ident.name ident) (Obj.repr thm);
       let ident_meta = register_ident ident thm vd [id] in
       let src_loc = ident_meta, Meta.Toplevel in
       let meta = meta_of_thm src_loc id thm in
       let meta = { meta with Meta.source_code_deps = dep_idents } in
       meta_map := Intmap.add id (thm, meta) !meta_map
    | [id,dup] -> ignore (register_ident ident dup vd [id]) in
  {
    (env_diff_default () []) with
    Toploop.env_diff_parse =
      (fun tree _ _ () -> collect_ids tree);
    Toploop.env_diff_ident =
      (fun ident vd dep_idents ->
       if is_thm vd then
         begin
           let thm = Obj.obj (Toploop.getvalue (Ident.name ident)) in
           register_toplevel_thm ident vd dep_idents thm
         end;
       dep_idents)
  };;

Toploop.set_env_diff_hook () meta_diff_hook;;
