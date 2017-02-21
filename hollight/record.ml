needs "fusion.ml";
needs "more-lib.ml";

(** A simple map interface and a subsumption relation on its keys. *)
module type Acc_map =
  sig
    type k
    type 'v t
    val empty : 'v t
    (** `modify f kthm v` adds v to the map keyed by kthm, either using f to modify
    the value there, or inserting v. *)
    val modify : ('v -> 'v) -> k -> 'v -> 'v t -> 'v t
    val union : ('v -> 'v -> 'v) -> 'v t -> 'v t -> 'v t
    val iter : ('v -> unit) -> 'v t -> unit
    val find : k -> 'v t -> 'v option
    val is_subsumed_by : k -> k -> bool
  end

type tracking = Tracked of int | Duplicate of int list

(** Wrap a HOL kernel inside one which tracks theorems and introduced constants
    through proofs. Duplications of theorems can be automatically identified modulo a
    subsumption relation provided by Acc. Additional monoidal metadata is attached
    via Meta. *)
module type Recording_hol_kernel =
  functor(Hol_cert : Hol_kernel) ->
  functor(Acc : Acc_map with type k = Hol_cert.thm) ->
  functor(Meta : Monad.Monoid) ->
  sig
    include Hol_kernel with type hol_type = Hol_cert.hol_type
                        and type term = Hol_cert.term

    type dep_info

    val get_tracking : dep_info -> tracking
    val get_dep_info : thm -> dep_info option
    val compare_dep_info : dep_info -> dep_info -> int

    val dep_info_of_id : int -> dep_info

    (** The dependencies of a theorem. *)
    val thm_deps         : thm  -> (thm * dep_info) list

    val const_deps       : thm -> string list
    val ty_const_deps    : thm -> string list

    (** Return a version of a theorem that will be tracked as a depedency. *)
    val with_tracking    : thm -> int * thm

    val next_frame       : unit -> unit
    val clear_local      : thm -> thm
    val get_local_duplicates : thm -> thm list

    val get_meta         : thm -> Meta.t
    val modify_meta      : (Meta.t -> Meta.t) -> thm -> thm

    val find_duplicates  : thm -> (int * thm) list

    val thm_cert         : thm  -> Hol_cert.thm
  end

module Record_hol_kernel : Recording_hol_kernel =
  functor(Hol_cert : Hol_kernel) ->
  functor(Acc : Acc_map with type k = Hol_cert.thm) ->
  functor(Meta : Monad.Monoid) ->
  struct
    type cert = Hol_cert.thm

    include (Hol_cert : Hol_kernel with type thm := cert
                                   and type hol_type = Hol_cert.hol_type
                                   and type term = Hol_cert.term)

    (* Thmset needs a recursive compare function, which will be unsafe for BatSet.S,
       so we need to simplify the interface and make empty a function: *)
    module Intmap = Batmap.Make(struct type t = int let compare = compare end)
    module Stringset = Batset.Make(struct
                                     type t = string
                                     let compare = compare
                                   end)
    module rec Dep : BatInterfaces.OrderedType
           with type t = Thmrec.thm * Thmrec.dep_info =
         struct
           type t = Thmrec.thm * Thmrec.dep_info
           let compare d1 d2 = Thmrec.compare_dep_info (snd d1) (snd d2)
         end
       and Depset : Batset.S with type elt = Dep.t = Batset.Make(Dep)
       and Thmrec : sig
           type dep_info = Identified of int
                         | Duplicate_of of thm Intmap.t * int
            and thm =
              {
                thm_cert : Hol_cert.thm;
                thm_deps : Depset.t;
                thm_dep_info : dep_info option;
                thm_local_deps : int * (thm list Acc.t ref);
                thm_const_deps : Stringset.t;
                thm_ty_const_deps : Stringset.t;
                thm_meta : Meta.t
              }
           val thm_cert : thm -> Hol_cert.thm
           val compare_dep_info : dep_info -> dep_info -> int
           val get_tracking : dep_info -> tracking
           val get_dep_info : thm -> dep_info option
           val dep_info_of_id : int -> dep_info
         end =
         struct
           type dep_info = Identified of int | Duplicate_of of thm Intmap.t * int
            and thm =
              {
                thm_cert : Hol_cert.thm;
                thm_deps : Depset.t;
                thm_dep_info : dep_info option;
                thm_local_deps : int * (thm list Acc.t ref);
                thm_const_deps : Stringset.t;
                thm_ty_const_deps : Stringset.t;
                thm_meta : Meta.t;
              }
           let thm_cert thm = thm.thm_cert
           let get_tracking = function
             | Identified id -> Tracked id
             | Duplicate_of (ids,_) ->
                Duplicate (Batenum.fold (fun xs x -> x :: xs) [] (Intmap.keys ids))
           let get_dep_info thm = thm.thm_dep_info
           let dep_info_of_id id = Identified id
           let is_dep_of id = function
             | Identified id' -> id = id'
             | Duplicate_of (ids,_) -> Intmap.mem id ids
           let compare_dep_info d1 d2 =
             match d1,d2 with
             | Identified i1, Identified i2 -> compare i1 i2
             | Identified _, _ -> -1
             | _, Identified _ -> 1
             | Duplicate_of (_,i1), Duplicate_of (_,i2) -> compare i1 i2
           let compare_on_tracking thm1 thm2 =
             match thm1.thm_dep_info,thm2.thm_dep_info with
             | Some dinfo1, Some dinfo2 -> Some (compare_dep_info dinfo1 dinfo2)
             | _, _ -> None
         end

    include Thmrec

    let dest_thm thm = Hol_cert.dest_thm thm.thm_cert

    let hyp = fst o dest_thm

    let concl = snd o dest_thm

    let thm_deps thm = Depset.to_list thm.thm_deps

    let const_deps thm = Stringset.to_list thm.thm_const_deps

    let ty_const_deps thm = Stringset.to_list thm.thm_ty_const_deps

    let get_id thm = match thm.thm_dep_info with
      | Some (Identified n) -> Some n
      | _ -> None

    let rec clear_all deps =
      Acc.iter (Batlist.iter (fun thm ->
                              let _,deps = thm.thm_local_deps in clear_all deps))
               !deps;
      deps := Acc.empty

    let current_frame = ref 0
    let next_frame () = incr current_frame
    let clear_local thm = clear_all (snd thm.thm_local_deps); thm
    let get_local_duplicates thm =
      let frame,deps = thm.thm_local_deps in
      Batoption.map_default (filter (Acc.is_subsumed_by thm.thm_cert o thm_cert)) []
                            (Acc.find (thm_cert thm) !deps)

    let thm_id_counter = ref 0

    let (ack_certs : thm Intmap.t Acc.t ref) = ref Acc.empty
    let with_tracking thm =
      let id = !thm_id_counter in
      let dep_info = Identified id in
      let thm =
        {
          thm with
          thm_dep_info = Some dep_info;
        } in
      ack_certs := Acc.modify (Intmap.add id thm)
                              thm.thm_cert
                              (Intmap.singleton id thm)
                              !ack_certs;
      incr thm_id_counter;
      id, thm

    let get_meta thm = thm.thm_meta
    let modify_meta f thm = { thm with thm_meta = f thm.thm_meta }

    let find_duplicates thm =
      match Acc.find thm.thm_cert !ack_certs with
      | Some idthms ->
         Intmap.filterv (Acc.is_subsumed_by thm.thm_cert o thm_cert) idthms
         |> Intmap.enum |> Batenum.fold (fun xs x -> x :: xs) []
      | None -> []

    let dup_id_counter = ref 0
    let record thm =
      let cert = thm.thm_cert in
      {
        thm with
        thm_dep_info =
          match Acc.find cert !ack_certs with
          | Some idthms ->
             let dup_id = !dup_id_counter in
             let idthms' =
               Intmap.filterv (Acc.is_subsumed_by cert o thm_cert) idthms in
             let depinfo =
               if Intmap.is_empty idthms' then None
               else Some (Duplicate_of (idthms',dup_id)) in
             incr dup_id_counter;
             depinfo
          | None -> None
      }

    let record0 cert =
      {
        thm_cert = cert;
        thm_deps = Depset.empty;
        thm_local_deps = (!current_frame,ref Acc.empty);
        thm_dep_info = None;
        thm_const_deps = Stringset.empty;
        thm_ty_const_deps = Stringset.empty;
        thm_meta = Meta.zero ()
      }

    let add_local_dep thm (frame,deps) =
      if frame = !current_frame then
        if Batoption.is_none thm.thm_dep_info then
          (frame,ref (Acc.modify ((@) [thm]) thm.thm_cert [thm] !deps))
        else (frame,deps)
      else
        let () = clear_all deps in
        (!current_frame,ref (Acc.modify ((@) [thm]) thm.thm_cert [thm] Acc.empty))

    (* Lift recording over a one argument inference rule. *)
    let record1 rule thm =
      record
        { thm with
          thm_cert = rule thm.thm_cert;
          thm_deps =
            (match thm.thm_dep_info with
             | None      -> thm.thm_deps
             | Some info -> Depset.singleton (thm,info));
          thm_local_deps = add_local_dep thm thm.thm_local_deps
        }

    (* Lift recording over a two argument inference rule which does not delete
       assumptions from the input theorems. *)
    let record2 rule thm1 thm2 =
      let deps1 =
        match thm1.thm_dep_info with
        | None      -> thm1.thm_deps
        | Some info -> Depset.singleton (thm1,info) in
      let deps2 =
        match thm2.thm_dep_info with
        | None      -> thm2.thm_deps
        | Some info -> Depset.singleton (thm2,info) in
      let union xs ys =
        let rec u acc = function
          | [] -> acc
          | y::ys when exists ((==) y) xs -> u acc ys
          | y::ys -> u (y::acc) xs in
        u xs ys in
      let union_deps (frame1,deps1) (frame2,deps2) =
        (!current_frame,
         if frame1 == !current_frame then
           if frame2 == !current_frame then
             ref (Acc.union union !deps1 !deps2)
           else let () = clear_all deps2 in
                deps1
         else if frame2 == !current_frame then
           let () = clear_all deps1 in
           deps2
         else
           let () = clear_all deps1; clear_all deps2 in
           ref Acc.empty) in
      record
        {
          thm_cert = rule thm1.thm_cert thm2.thm_cert;
          thm_deps = Depset.union deps1 deps2;
          thm_dep_info = None;
          thm_local_deps =
            union_deps thm1.thm_local_deps thm2.thm_local_deps
            |> add_local_dep thm1
            |> add_local_dep thm2;
          thm_const_deps = Stringset.union thm1.thm_const_deps thm2.thm_const_deps;
          thm_ty_const_deps =
            Stringset.union thm1.thm_ty_const_deps thm2.thm_ty_const_deps;
          thm_meta = Meta.plus thm1.thm_meta thm2.thm_meta
        }

    let REFL tm = record0 (REFL tm)
    let TRANS = record2 TRANS
    let MK_COMB (thm1,thm2) = record2 (curry MK_COMB) thm1 thm2
    let ABS v = record1 (ABS v)
    let BETA tm = record0 (BETA tm)
    let ASSUME tm = record0 (ASSUME tm)
    let EQ_MP = record2 EQ_MP
    let DEDUCT_ANTISYM_RULE = record2 DEDUCT_ANTISYM_RULE
    let INST_TYPE theta = record1 (Hol_cert.INST_TYPE theta)
    let INST theta = record1 (INST theta)

    let the_axioms = ref ([]:thm list)
    let axioms () = !the_axioms

    let new_axiom tm =
      let ax = record0 (Hol_cert.new_axiom tm) in
      the_axioms := ax :: !the_axioms;
      ax

    let the_definitions = ref ([]:thm list)
    let definitions () = !the_definitions

    let new_basic_definition tm =
      let cert = Hol_cert.new_basic_definition tm in
      let cname = match tm with
        | Comb(Comb(Const("=",_),Var(cname,ty)),_) -> cname
        | _ -> failwith "BUG: Not a basic definition." in
      let def =
        record
          {
            thm_cert = cert;
            thm_deps = Depset.empty;
            thm_local_deps = (!current_frame,ref Acc.empty);
            thm_dep_info = None;
            thm_const_deps = Stringset.singleton cname;
            thm_ty_const_deps = Stringset.empty;
            thm_meta = Meta.zero ()
          } in
      the_definitions := def :: !the_definitions;
      def

    let new_basic_type_definition tyname (abs,rep) thm =
      let abs_cert,rep_cert =
        Hol_cert.new_basic_type_definition tyname (abs,rep) thm.thm_cert in
      let deps = match thm.thm_dep_info with
        | None      -> thm.thm_deps
        | Some info -> Depset.singleton (thm,info) in
      let constdeps =
        Stringset.union (Stringset.of_list [abs;rep]) thm.thm_const_deps in
      let typedeps = Stringset.add tyname thm.thm_ty_const_deps in
      record
        {
          thm with
          thm_cert = abs_cert;
          thm_deps = deps;
          thm_dep_info = None;
          thm_const_deps = constdeps;
          thm_ty_const_deps = typedeps
        },
      record
        {
          thm with
          thm_cert = rep_cert;
          thm_deps = deps;
          thm_dep_info = None;
          thm_const_deps = constdeps;
          thm_ty_const_deps = typedeps
        }
  end
