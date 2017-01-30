#use "topfind";;
#require "compiler-libs.common";;
#thread;;
#require "batteries";;
#require "camlp5";;
#require "sexplib";;
#require "ezjsonm";;
#require "monadlib";;
#use "batteries.ml";;
module Typedtreeiter = struct
    include TypedtreeIter
    module Defaultiteratorargument = DefaultIteratorArgument
    module Makeiterator = MakeIterator
  end;;
let output_string = Pervasives.output_string;;
let close_out = Pervasives.close_out;;

(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

let hol_version = "2.20++";;

#directory "+compiler-libs";;

let hol_dir = ref
  (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> Sys.getcwd());;

(* ------------------------------------------------------------------------- *)
(* Should eventually change to "ref(Filename.temp_dir_name)".                *)
(* However that's not available in 3.08, which is still the default          *)
(* in Cygwin, and I don't want to force people to upgrade Ocaml.             *)
(* ------------------------------------------------------------------------- *)

let temp_path = ref "/tmp";;

Topdirs.dir_load Format.std_formatter "camlp5o.cma";;
Topdirs.dir_load Format.std_formatter (Filename.concat (!hol_dir) "pa_j.cmo");;

(* ------------------------------------------------------------------------- *)
(* Load files from system and/or user-settable directories.                  *)
(* Paths map initial "$/" to !hol_dir dynamically; use $$ to get the actual  *)
(* $ character at the start of a directory.                                  *)
(* ------------------------------------------------------------------------- *)

let use_file s =
  if Toploop.use_file Format.std_formatter s then ()
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;

let hol_expand_directory s =
  if s = "$" or s = "$/" then !hol_dir
  else if s = "$$" then "$"
  else if String.length s <= 2 then s
  else if String.sub s 0 2 = "$$" then (String.sub s 1 (String.length s - 1))
  else if String.sub s 0 2 = "$/"
  then Filename.concat (!hol_dir) (String.sub s 2 (String.length s - 2))
  else s;;

let load_path = ref ["."; "$"];;

let loaded_files = ref [];;

let file_on_path p s =
  if not (Filename.is_relative s) then s else
  let p' = List.map hol_expand_directory p in
  let d = List.find (fun d -> Sys.file_exists(Filename.concat d s)) p' in
  Filename.concat (if d = "." then Sys.getcwd() else d) s;;

let load_on_path p s =
  let s' = file_on_path p s in
  let fileid = (Filename.basename s',Digest.file s') in
  (use_file s'; loaded_files := fileid::(!loaded_files));;

let loads s = load_on_path ["$"] s;;

let loadt s = load_on_path (!load_path) s;;

let needs s =
  let s' = file_on_path (!load_path) s in
  let fileid = (Filename.basename s',Digest.file s') in
  if List.mem fileid (!loaded_files)
  then Format.print_string("File \""^s^"\" already loaded\n") else loadt s;;

(* ------------------------------------------------------------------------- *)
(* Various tweaks to OCaml and general library functions. *)
(* ------------------------------------------------------------------------- *)

loads "system.ml";;     (* Set up proper parsing and load bignums            *)
loads "lib.ml";;        (* Various useful general library functions          *)

loadt "more-lib.ml";;

(* ------------------------------------------------------------------------- *)
(* The logical core.                                                         *)
(* ------------------------------------------------------------------------- *)

loads "fusion.ml";;
loadt "record.ml";;

module Noack : Acc_map with type k = thm =
  struct
    type k = thm
    type 'v t = unit
    let empty = ()
    let modify _ _ _ () = ()
    let union _ () () = ()
    let find _ () = None
    let filter _ () = ()
    let is_subsumed_by _ _ = false
  end

module Notag : Monad.Monoid =
  struct
    type t = unit
    let zero () = ()
    let plus () () = ()
  end

module Setack(H : Hol_kernel) : Acc_map with type k = H.thm =
  struct
    type k = H.thm
    module Acks = Batmap.Make(struct
                                 type t = H.thm
                                 let compare thm1 thm2 =
                                   compare (H.concl thm1) (H.concl thm2)
                               end)
    type 'v t = 'v Acks.t
    let empty = Acks.empty
    let modify f thm v = Acks.modify_def v thm f
    let union f =
      Acks.merge (fun _ xs ys -> match xs,ys with
                                 | Some xs,Some ys -> Some (f xs ys)
                                 | None,Some ys -> Some ys
                                 | Some xs,None -> Some xs
                                 | None,None -> None)
    let find = Acks.Exceptionless.find
    let filter = Acks.filterv
    let subset xs ys = List.for_all (fun x -> List.mem x ys) xs
    let is_subsumed_by thm1 thm2 = subset (H.hyp thm2) (H.hyp thm1)
  end

module Setack_noasm(H : Hol_kernel) : Acc_map with type k = H.thm =
  struct
    type k = H.thm
    module Acks = Batmap.Make(struct
                                 type t = H.thm
                                 let compare thm1 thm2 =
                                   compare (H.concl thm1) (H.concl thm2)
                               end)
    type 'v t = 'v Acks.t
    let empty = Acks.empty
    let modify f thm v map =
      if H.hyp thm = [] then Acks.modify_def v thm f map else map
    let union f =
      Acks.merge (fun _ xs ys -> match xs,ys with
                                 | Some xs,Some ys -> Some (f xs ys)
                                 | None,Some ys -> Some ys
                                 | Some xs,None -> Some xs
                                 | None,None -> None)
    let find thm map =
      if H.hyp thm = [] then Acks.Exceptionless.find thm map else None
    let filter = Acks.filterv
    let is_subsumed_by thm1 thm2 = H.concl thm1 = H.concl thm2
  end

module Hol_cert = Hol;;
module Hol = Record_hol_kernel(Hol_cert)(Setack_noasm(Hol_cert))(Notag);;
include Hol;;
let compare = Pervasives.compare;;

let equals_thm th th' = dest_thm th = dest_thm th';;

(* ------------------------------------------------------------------------- *)
(* Some extra support stuff needed outside the core.                         *)
(* ------------------------------------------------------------------------- *)

loads "basics.ml";;    (* Additional syntax operations and other utilities  *)
loads "nets.ml";;      (* Term nets for fast matchability-based lookup      *)

(* ------------------------------------------------------------------------- *)
(* The interface.                                                            *)
(* ------------------------------------------------------------------------- *)

loads "printer.ml";;   (* Crude prettyprinter                               *)
loads "preterm.ml";;  (* Preterms and their interconversion with terms     *)
loads "parser.ml";;    (* Lexer and parser                                  *)

loadt "meta.ml";;

(* ------------------------------------------------------------------------- *)
(* Higher level deductive system.                                            *)
(* ------------------------------------------------------------------------- *)

loads "equal.ml";;        (* Basic equality reasoning and conversionals      *)
loads "bool.ml";;         (* Boolean theory and basic derived rules          *)
loads "drule.ml";;        (* Additional derived rules                        *)
loadt "tactic_types.ml";; (* Tactics, tacticals and goal stack               *)
loadt "meta_tactic.ml";;

loadt "tactics.ml";;      (* Tactics, tacticals and goal stack               *)
loadt "meta_conj.ml";;

loads "itab.ml";;       (* Toy prover for intuitionistic logic               *)
loads "simp.ml";;       (* Basic rewriting and simplification tools.         *)
loads "theorems.ml";;   (* Additional theorems (mainly for quantifiers) etc. *)
loads "ind_defs.ml";;   (* Derived rules for inductive definitions           *)
loads "class.ml";;      (* Classical reasoning: Choice and Extensionality    *)
loads "trivia.ml";;     (* Some very basic theories, e.g. type ":1"          *)
loads "canon.ml";;      (* Tools for putting terms in canonical forms        *)
loads "meson.ml";;      (* First order automation: MESON (model elimination) *)
loads "metis.ml";;      (* More advanced first-order automation: Metis       *)
loads "quot.ml";;       (* Derived rules for defining quotient types         *)
loads "impconv.ml";;    (* More powerful implicational rewriting etc.        *)

(* ------------------------------------------------------------------------- *)
(* Mathematical theories and additional proof tools.                         *)
(* ------------------------------------------------------------------------- *)

loads "pair.ml";;       (* Theory of pairs                                   *)
loads "nums.ml";;       (* Axiom of Infinity, definition of natural numbers  *)
loads "recursion.ml";;  (* Tools for primitive recursion on inductive types  *)
loads "arith.ml";;      (* Natural number arithmetic                         *)
loads "wf.ml";;         (* Theory of wellfounded relations                   *)
loads "calc_num.ml";;   (* Calculation with natural numbers                  *)
loads "normalizer.ml";; (* Polynomial normalizer for rings and semirings     *)
loads "grobner.ml";;    (* Groebner basis procedure for most semirings.      *)
loads "ind_types.ml";;  (* Tools for defining inductive types                *)
loads "lists.ml";;      (* Theory of lists                                   *)
loads "realax.ml";;     (* Definition of real numbers                        *)
loads "calc_int.ml";;   (* Calculation with integer-valued reals             *)
loads "realarith.ml";;  (* Universal linear real decision procedure          *)
loads "real.ml";;       (* Derived properties of reals                       *)
loads "calc_rat.ml";;   (* Calculation with rational-valued reals            *)
loads "int.ml";;        (* Definition of integers                            *)
loads "sets.ml";;       (* Basic set theory.                                 *)
loads "iterate.ml";;    (* Iterated operations                               *)
loads "cart.ml";;       (* Finite Cartesian products                         *)
loads "define.ml";;     (* Support for general recursive definitions         *)

(* ------------------------------------------------------------------------- *)
(* The help system. *)
(* ------------------------------------------------------------------------- *)

loads "help.ml";;       (* Online help using the entries in Help directory   *)
loads "database.ml";;   (* List of name-theorem pairs for search system      *)

open Pervasives;;
