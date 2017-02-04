(* ========================================================================= *)
(* System of tactics (slightly different from any traditional LCF method).   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2012                         *)
(* ========================================================================= *)

needs "roses.ml";;

(* ------------------------------------------------------------------------- *)
(* The common case of trivial instantiations.                                *)
(* ------------------------------------------------------------------------- *)

let null_inst = ([],[],[] :instantiation);;

let null_meta = (([]:term list),null_inst);;

(* ------------------------------------------------------------------------- *)
(* A goal has labelled assumptions, and the hyps are now thms.               *)
(* ------------------------------------------------------------------------- *)

type goal = (string * thm) list * term;;

let equals_goal ((a,w):goal) ((a',w'):goal) =
  forall2 (fun (s,th) (s',th') -> s = s' & equals_thm th th') a a' & w = w';;

(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)
type justification = instantiation -> thm list -> thm;;

(* ------------------------------------------------------------------------- *)
(* The goalstate stores the subgoals, justification, current instantiation,  *)
(* a list of metavariables. and a recording of the current tactics used in a *)
(* rose tree with holes.                                                     *)
(* ------------------------------------------------------------------------- *)

type goalstate = (term list * instantiation)
                 * goal list
                 * justification
                 * (unit Meta.src * tac_thm list) list rose_bud;;

(* ------------------------------------------------------------------------- *)
(* A goalstack is just a list of goalstates. Could go for more...            *)
(* ------------------------------------------------------------------------- *)

type goalstack = goalstate list;;

(* ------------------------------------------------------------------------- *)
(* A refinement, applied to a goalstate [A1 ?- g1; ...; An ?- gn]            *)
(* yields a new goalstate with updated justification function, to            *)
(* give a possibly-more-instantiated version of the initial goal.            *)
(* ------------------------------------------------------------------------- *)

type refinement = goalstate -> goalstate;;

(* ------------------------------------------------------------------------- *)
(* A tactic, applied to a goal A ?- g, returns:                              *)
(*                                                                           *)
(*  o A list of new metavariables introduced                                 *)
(*  o An instantiation (%)                                                   *)
(*  o A list of subgoals                                                     *)
(*  o A justification f such that for any instantiation @ we have            *)
(*    f(@) [A1@  |- g1@; ...; An@ |- gn@] = A(%;@) |- g(%;@)                 *)
(*  o A rose tree of the component tactics used with holes for later tactics *)
(* ------------------------------------------------------------------------- *)

type tactic = goal -> goalstate;;

type thm_tactic = thm -> tactic;;

type thm_tactical = thm_tactic -> thm_tactic;;
