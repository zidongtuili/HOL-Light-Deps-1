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
           type dep_info = Identified of int | Duplicate_of of thm Intmap.t * int
           and thm = Record of Hol_cert.thm * Depset.t * dep_info option *
                               Stringset.t * Stringset.t * Meta.t
           val thm_cert : thm -> Hol_cert.thm
           val compare_dep_info : dep_info -> dep_info -> int
           val get_tracking : dep_info -> tracking
           val get_dep_info : thm -> dep_info option
           val dep_info_of_id : int -> dep_info
         end =
         struct
           type dep_info = Identified of int | Duplicate_of of thm Intmap.t * int
            and thm = Record of Hol_cert.thm * Depset.t * dep_info option *
                                Stringset.t * Stringset.t * Meta.t
           let thm_cert (Record(cert,_,_,_,_,_)) = cert
           let get_tracking = function
             | Identified id -> Tracked id
             | Duplicate_of (ids,_) ->
                Duplicate (Batenum.fold (fun xs x -> x :: xs) [] (Intmap.keys ids))
           let get_dep_info (Record(_,_,dep_info,_,_,_)) = dep_info
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
             match thm1,thm2 with
             | Record (cert1,_,Some dinfo1,_,_,_),
               Record (cert2,_,Some dinfo2,_,_,_) ->
                Some (compare_dep_info dinfo1 dinfo2)
             | _, _ -> None
         end

    include Thmrec

    let dest_thm (Record(cert,_,_,_,_,_)) = Hol_cert.dest_thm cert

    let hyp = fst o dest_thm

    let concl = snd o dest_thm

    let thm_deps (Record(_,deps,_,_,_,_)) = Depset.to_list deps

    let const_deps (Record (_,_,_,deps,_,_)) = Stringset.to_list deps

    let ty_const_deps (Record (_,_,_,_,deps,_)) = Stringset.to_list deps

    let get_id = function
      | Record(_,_,Some (Identified n),_,_,_) -> Some n
      | _ -> None

    let thm_id_counter = ref 0

    let (ack_certs : thm Intmap.t Acc.t ref) = ref Acc.empty
    let with_tracking (Record(cert,deps,_,constdeps,typedeps,meta)) =
      begin
        let id = !thm_id_counter in
        let dep_info = Identified id in
        let thm = Record(cert,deps,Some dep_info,constdeps,typedeps,meta) in
        ack_certs := Acc.modify (Intmap.add id thm)
                                cert
                                (Intmap.singleton id thm)
                                !ack_certs;
        incr thm_id_counter;
        id, thm
      end
    let get_meta (Record(_,_,_,_,_,meta)) = meta
    let modify_meta f (Record(cert,deps,dep_info,constdeps,typedeps,meta)) =
      Record(cert,deps,dep_info,constdeps,typedeps,f meta)

    let find_duplicates (Record (cert,_,_,_,_,_)) =
      match Acc.find cert !ack_certs with
      | Some idthms -> Intmap.filterv (Acc.is_subsumed_by cert o thm_cert) idthms
                       |> Intmap.enum |> Batenum.fold (fun xs x -> x :: xs) []
      | None -> []

    let dup_id_counter = ref 0
    let record cert deps constdeps typedeps meta =
      match Acc.find cert !ack_certs with
      | Some idthms ->
         let dup_id = !dup_id_counter in
         let idthms' =
           Intmap.filterv (Acc.is_subsumed_by cert o thm_cert) idthms in
         let thm =
           if Intmap.is_empty idthms'
           then Record(cert,deps,None,constdeps,typedeps,meta)
           else Record(cert,deps,Some (Duplicate_of (idthms',dup_id)),
                       constdeps,typedeps,meta) in
         incr dup_id_counter;
         thm
      | None -> Record(cert,deps,None,constdeps,typedeps,meta)

    let record0 cert =
      Record(cert,Depset.empty,None,Stringset.empty,Stringset.empty,Meta.zero ())

    (* Lift recording over a one argument inference rule. *)
    let record1 rule (Record(cert,deps,dep_info,constdeps,typedeps,meta) as thm) =
      let deps = match dep_info with
        | None      -> deps
        | Some info -> Depset.singleton (thm,info) in
      let cert = rule cert in
      record cert deps constdeps typedeps meta

    (* Lift recording over a two argument inference rule which does not delete
       assumptions from the input theorems. *)
    let record2 rule
                ((Record(cert1,deps1,dep_info1,constdeps1,typedeps1,meta1))
                 as thm1)
                ((Record(cert2,deps2,dep_info2,constdeps2,typedeps2,meta2))
                 as thm2) =
      let deps1 =
        match dep_info1 with
        | None      -> deps1
        | Some info -> Depset.singleton (thm1,info) in
      let deps2 =
        match dep_info2 with
        | None      -> deps2
        | Some info -> Depset.singleton (thm2,info) in
      let deps  = Depset.union deps1 deps2 in
      let cert  = rule cert1 cert2 in
      record cert deps
             (Stringset.union constdeps1 constdeps2)
             (Stringset.union typedeps1 typedeps2)
             (Meta.plus meta1 meta2)

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
      let constdeps = Stringset.singleton cname in
      let typedeps = Stringset.empty in
      let def = record cert Depset.empty constdeps typedeps (Meta.zero ()) in

      the_definitions := def :: !the_definitions;
      def

    let new_basic_type_definition
          tyname (abs,rep) ((Record(cert,deps,dep_info,constdeps,typedeps,meta))
                            as thm) =
      let abs_cert,rep_cert =
        Hol_cert.new_basic_type_definition tyname (abs,rep) cert in
      let deps = match dep_info with
        | None      -> deps
        | Some info -> Depset.singleton (thm,info) in
      let constdeps = Stringset.union (Stringset.of_list [abs;rep]) constdeps in
      let typedeps = Stringset.add tyname typedeps in
      record abs_cert deps constdeps typedeps meta,
      record rep_cert deps constdeps typedeps meta
  end
