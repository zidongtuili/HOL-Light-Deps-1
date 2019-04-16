val _ = set_fixity "'" (Infixl 2000);    (* fmap application *)

val _ = set_fixity "|+"  (Infixl 600);   (* fmap update *)
val _ = set_fixity "|++" (Infixl 500);   (* iterated update *)

val NOT_FDOM_DRESTRICT = Q.store_thm
("NOT_FDOM_DRESTRICT",
 `!^fmap x. ~(x IN FDOM f) ==> (DRESTRICT f (COMPL {x}) = f)`,
 SRW_TAC [][GSYM fmap_EQ_THM, DRESTRICT_DEF, EXTENSION] THEN PROVE_TAC []);

val FUPDATE_DRESTRICT = Q.store_thm
("FUPDATE_DRESTRICT",
 `!^fmap x y. FUPDATE f (x,y) = FUPDATE (DRESTRICT f (COMPL {x})) (x,y)`,
 SRW_TAC [][GSYM fmap_EQ_THM, FDOM_FUPDATE, EXTENSION, DRESTRICT_DEF,
            FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);

val STRONG_DRESTRICT_FUPDATE_THM = Q.store_thm
("STRONG_DRESTRICT_FUPDATE_THM",
 `!^fmap r x y.
  DRESTRICT (FUPDATE f (x,y)) r
     =
  if x IN r then FUPDATE (DRESTRICT f (COMPL {x} INTER r)) (x,y)
  else DRESTRICT f (COMPL {x} INTER r)`,
 SRW_TAC [][GSYM fmap_EQ_THM, DRESTRICT_DEF, FDOM_FUPDATE, EXTENSION,
            FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);


val DRESTRICT_EQ_DRESTRICT = store_thm(
"DRESTRICT_EQ_DRESTRICT",
``!f1 f2 s1 s2.
   (DRESTRICT f1 s1 = DRESTRICT f2 s2) =
   (DRESTRICT f1 s1 SUBMAP f2 /\ DRESTRICT f2 s2 SUBMAP f1 /\
    (s1 INTER FDOM f1 = s2 INTER FDOM f2))``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF,SUBMAP_DEF,EXTENSION] THEN
METIS_TAC[])


val FUNION_IDEMPOT = store_thm("FUNION_IDEMPOT",
``FUNION fm fm = fm``,
  SRW_TAC[][GSYM fmap_EQ_THM,FUNION_DEF])
val _ = export_rewrites["FUNION_IDEMPOT"]


(*---------------------------------------------------------------------------
       Universal quantifier on finite maps
 ---------------------------------------------------------------------------*)

val FEVERY_DEF = Q.new_definition
("FEVERY_DEF",
 `FEVERY P ^fmap = !x. x IN FDOM f ==> P (x, FAPPLY f x)`);

val FEVERY_FEMPTY = Q.store_thm
("FEVERY_FEMPTY",
 `!P:'a#'b -> bool. FEVERY P FEMPTY`,
 SRW_TAC [][FEVERY_DEF, FDOM_FEMPTY]);

val FEVERY_FUPDATE = Q.store_thm
("FEVERY_FUPDATE",
 `!P ^fmap x y.
     FEVERY P (FUPDATE f (x,y))
        =
     P (x,y) /\ FEVERY P (DRESTRICT f (COMPL {x}))`,
 SRW_TAC [][FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM,
            DRESTRICT_DEF, EQ_IMP_THM] THEN PROVE_TAC []);

val FEVERY_FLOOKUP = Q.store_thm(
"FEVERY_FLOOKUP",
`FEVERY P f /\ (FLOOKUP f k = SOME v) ==> P (k,v)`,
SRW_TAC [][FEVERY_DEF,FLOOKUP_DEF] THEN RES_TAC);

(*---------------------------------------------------------------------------
      Composition of finite maps
 ---------------------------------------------------------------------------*)

val f_o_f_lemma = Q.prove
(`!f:'b |-> 'c.
  !g:'a |-> 'b.
     ?comp. (FDOM comp = FDOM g INTER { x | FAPPLY g x IN FDOM f })
       /\   (!x. x IN FDOM comp ==>
                    (FAPPLY comp x = (FAPPLY f (FAPPLY g x))))`,
 GEN_TAC THEN INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL [
   Q.EXISTS_TAC `FEMPTY` THEN SRW_TAC [][FDOM_FEMPTY],
   REPEAT STRIP_TAC THEN
   Cases_on  `y IN FDOM f` THENL [
     Q.EXISTS_TAC `FUPDATE comp (x, FAPPLY f y)` THEN
     SRW_TAC [][FDOM_FUPDATE, FAPPLY_FUPDATE_THM, EXTENSION] THEN
     PROVE_TAC [],
     Q.EXISTS_TAC `comp` THEN
     SRW_TAC [][FDOM_FUPDATE, FAPPLY_FUPDATE_THM, EXTENSION] THEN
     PROVE_TAC []
   ]
 ]);

val f_o_f_DEF = new_specification
  ("f_o_f_DEF", ["f_o_f"],
   CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) f_o_f_lemma);

val _ = set_fixity "f_o_f" (Infixl 500);

val f_o_f_FEMPTY_1 = Q.store_thm
("f_o_f_FEMPTY_1",
 `!^fmap. (FEMPTY:('b,'c)fmap) f_o_f f = FEMPTY`,
 SRW_TAC [][GSYM fmap_EQ_THM, f_o_f_DEF, FDOM_FEMPTY, EXTENSION]);

val f_o_f_FEMPTY_2 = Q.store_thm (
  "f_o_f_FEMPTY_2",
  `!f:'b|->'c. f f_o_f (FEMPTY:('a,'b)fmap) = FEMPTY`,
  SRW_TAC [][GSYM fmap_EQ_THM, f_o_f_DEF, FDOM_FEMPTY]);

val _ = export_rewrites["f_o_f_FEMPTY_1","f_o_f_FEMPTY_2"];

val o_f_lemma = Q.prove
(`!f:'b->'c.
  !g:'a|->'b.
    ?comp. (FDOM comp = FDOM g)
      /\   (!x. x IN FDOM comp ==> (FAPPLY comp x = f (FAPPLY g x)))`,
 GEN_TAC THEN INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL [
   Q.EXISTS_TAC `FEMPTY` THEN SRW_TAC [][FDOM_FEMPTY],
   REPEAT STRIP_TAC THEN Q.EXISTS_TAC `FUPDATE comp (x, f y)` THEN
   SRW_TAC [][FDOM_FUPDATE, FAPPLY_FUPDATE_THM]
 ]);

val o_f_DEF = new_specification
  ("o_f_DEF", ["o_f"],
   CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) o_f_lemma);

val _ = set_fixity "o_f" (Infixl 500);

val o_f_FDOM = Q.store_thm
("o_f_FDOM",
 `!f:'b -> 'c. !g:'a |->'b. FDOM  g = FDOM (f o_f g)`,
REWRITE_TAC [o_f_DEF]);

val FDOM_o_f = save_thm("FDOM_o_f", GSYM o_f_FDOM);
val _ = export_rewrites ["FDOM_o_f"]

val o_f_FAPPLY = Q.store_thm
("o_f_FAPPLY",
 `!f:'b->'c. !g:('a,'b) fmap.
   !x. x IN FDOM  g ==> (FAPPLY (f o_f g) x = f (FAPPLY g x))`,
 SRW_TAC [][o_f_DEF]);
val _ = export_rewrites ["o_f_FAPPLY"]

val o_f_FEMPTY = store_thm(
  "o_f_FEMPTY",
  ``f o_f FEMPTY = FEMPTY``,
  SRW_TAC [][GSYM fmap_EQ_THM, FDOM_o_f])
val _ = export_rewrites ["o_f_FEMPTY"]

val FEVERY_o_f = store_thm (
  "FEVERY_o_f",
  ``!m P f. FEVERY P (f o_f m) = FEVERY (\x. P (FST x, (f (SND x)))) m``,
  SIMP_TAC std_ss [FEVERY_DEF, FDOM_FEMPTY, NOT_IN_EMPTY, o_f_DEF]);

val o_f_o_f = store_thm(
  "o_f_o_f",
  ``(f o_f (g o_f h)) = (f o g) o_f h``,
  SRW_TAC [][GSYM fmap_EQ_THM, o_f_FAPPLY]);
val _ = export_rewrites ["o_f_o_f"]

val FLOOKUP_o_f = Q.store_thm(
"FLOOKUP_o_f",
`FLOOKUP (f o_f fm) k = case FLOOKUP fm k of NONE => NONE | SOME v => SOME (f v)`,
SRW_TAC [][FLOOKUP_DEF,o_f_FAPPLY]);

(*---------------------------------------------------------------------------
          Range of a finite map
 ---------------------------------------------------------------------------*)

val FRANGE_DEF = Q.new_definition
("FRANGE_DEF",
 `FRANGE ^fmap = { y | ?x. x IN FDOM f /\ (FAPPLY f x = y)}`);

val FRANGE_FEMPTY = Q.store_thm
("FRANGE_FEMPTY",
 `FRANGE FEMPTY = {}`,
 SRW_TAC [][FRANGE_DEF, FDOM_FEMPTY, EXTENSION]);
val _ = export_rewrites ["FRANGE_FEMPTY"]

val FRANGE_FUPDATE = Q.store_thm
("FRANGE_FUPDATE",
 `!^fmap x y.
     FRANGE (FUPDATE f (x,y))
       =
     y INSERT FRANGE (DRESTRICT f (COMPL {x}))`,
 SRW_TAC [][FRANGE_DEF, FDOM_FUPDATE, DRESTRICT_DEF, EXTENSION,
            FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);

val SUBMAP_FRANGE = Q.store_thm
("SUBMAP_FRANGE",
 `!^fmap g. f SUBMAP g ==> FRANGE f SUBSET FRANGE g`,
 SRW_TAC [][SUBMAP_DEF,FRANGE_DEF, SUBSET_DEF] THEN PROVE_TAC []);

val FINITE_FRANGE = store_thm(
  "FINITE_FRANGE",
  ``!fm. FINITE (FRANGE fm)``,
  HO_MATCH_MP_TAC fmap_INDUCT THEN
  SRW_TAC [][FRANGE_FUPDATE] THEN
  Q_TAC SUFF_TAC `DRESTRICT fm (COMPL {x}) = fm` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][GSYM fmap_EQ_THM, DRESTRICT_DEF, EXTENSION] THEN
  PROVE_TAC []);
val _ = export_rewrites ["FINITE_FRANGE"]

val o_f_FRANGE = store_thm(
  "o_f_FRANGE",
  ``x IN FRANGE g ==> f x IN FRANGE (f o_f g)``,
  SRW_TAC [][FRANGE_DEF] THEN METIS_TAC [o_f_FAPPLY]);
val _ = export_rewrites ["o_f_FRANGE"]

val FRANGE_FLOOKUP = store_thm(
  "FRANGE_FLOOKUP",
  ``v IN FRANGE f <=> ?k. FLOOKUP f k = SOME v``,
  SRW_TAC [][FLOOKUP_DEF,FRANGE_DEF]);

val FRANGE_FUNION = store_thm(
  "FRANGE_FUNION",
  ``DISJOINT (FDOM fm1) (FDOM fm2) ==>
    (FRANGE (FUNION fm1 fm2) = FRANGE fm1 UNION FRANGE fm2)``,
  STRIP_TAC THEN
  `!x. x IN FDOM fm2 ==> x NOTIN FDOM fm1`
     by (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
         METIS_TAC []) THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss ++ boolSimps.CONJ_ss)
               [FRANGE_DEF, FUNION_DEF, EXTENSION]);

(*---------------------------------------------------------------------------
        Range restriction
 ---------------------------------------------------------------------------*)

val ranres_lemma = Q.prove
(`!^fmap (r:'b set).
    ?res. (FDOM res = { x | x IN FDOM f /\ FAPPLY f x IN r})
      /\  (!x. FAPPLY res x =
                 if x IN FDOM f /\ FAPPLY f x IN r
                   then FAPPLY f x
                   else FAPPLY FEMPTY x)`,
 CONV_TAC SWAP_VARS_CONV THEN GEN_TAC THEN
 INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL [
   Q.EXISTS_TAC `FEMPTY` THEN SRW_TAC [][FDOM_FEMPTY, EXTENSION],
   REPEAT STRIP_TAC THEN
   Cases_on `y IN r` THENL [
     Q.EXISTS_TAC `FUPDATE res (x,y)` THEN
     SRW_TAC [][FDOM_FUPDATE, FAPPLY_FUPDATE_THM, EXTENSION] THEN
     PROVE_TAC [],
     Q.EXISTS_TAC `res` THEN
     SRW_TAC [][FDOM_FUPDATE, FAPPLY_FUPDATE_THM, EXTENSION] THEN
     PROVE_TAC []
   ]
 ]);

val RRESTRICT_DEF = new_specification
  ("RRESTRICT_DEF", ["RRESTRICT"],
   CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) ranres_lemma);

val RRESTRICT_FEMPTY = Q.store_thm
("RRESTRICT_FEMPTY",
 `!r. RRESTRICT FEMPTY r = FEMPTY`,
 SRW_TAC [][GSYM fmap_EQ_THM, RRESTRICT_DEF, FDOM_FEMPTY, EXTENSION]);

val RRESTRICT_FUPDATE = Q.store_thm
("RRESTRICT_FUPDATE",
`!^fmap r x y.
    RRESTRICT (FUPDATE f (x,y)) r =
      if y IN r then FUPDATE (RRESTRICT f r) (x,y)
      else RRESTRICT (DRESTRICT f (COMPL {x})) r`,
 SRW_TAC [][GSYM fmap_EQ_THM, FDOM_FUPDATE, RRESTRICT_DEF, DRESTRICT_DEF,
            EXTENSION, FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);

(*---------------------------------------------------------------------------
       Functions as finite maps.

 ---------------------------------------------------------------------------*)

val ffmap_lemma = Q.prove
(`!(f:'a -> 'b) (P: 'a set).
     FINITE P ==>
        ?ffmap. (FDOM ffmap = P)
           /\   (!x. x IN P ==> (FAPPLY ffmap x = f x))`,
 GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL [
   Q.EXISTS_TAC `FEMPTY` THEN BETA_TAC THEN
   REWRITE_TAC [FDOM_FEMPTY, NOT_IN_EMPTY],
   REPEAT STRIP_TAC THEN Q.EXISTS_TAC `FUPDATE ffmap (e, f e)` THEN
   ASM_REWRITE_TAC [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM] THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   COND_CASES_TAC THENL [
     POP_ASSUM SUBST_ALL_TAC THEN RES_TAC,
     FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []
   ]
 ]);

val FUN_FMAP_DEF = new_specification
  ("FUN_FMAP_DEF", ["FUN_FMAP"],
   CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC
              ONCE_DEPTH_CONV SKOLEM_CONV) ffmap_lemma);

val FUN_FMAP_EMPTY = store_thm(
  "FUN_FMAP_EMPTY",
  ``FUN_FMAP f {} = FEMPTY``,
  SRW_TAC [][GSYM fmap_EQ_THM, FUN_FMAP_DEF]);
val _ = export_rewrites ["FUN_FMAP_EMPTY"]

val FRANGE_FMAP = store_thm(
  "FRANGE_FMAP",
  ``FINITE P ==> (FRANGE (FUN_FMAP f P) = IMAGE f P)``,
  SRW_TAC [boolSimps.CONJ_ss][EXTENSION, FRANGE_DEF, FUN_FMAP_DEF] THEN
  PROVE_TAC []);
val _ = export_rewrites ["FRANGE_FMAP"]

val FDOM_FMAP = store_thm(
"FDOM_FMAP",
``!f s. FINITE s ==> (FDOM (FUN_FMAP f s) = s)``,
SRW_TAC[][FUN_FMAP_DEF])
val _ = export_rewrites ["FDOM_FMAP"]

val FLOOKUP_FUN_FMAP = Q.store_thm(
  "FLOOKUP_FUN_FMAP",
  `FINITE P ==>
   (FLOOKUP (FUN_FMAP f P) k = if k IN P then SOME (f k) else NONE)`,
  SRW_TAC [][FUN_FMAP_DEF,FLOOKUP_DEF]);

(*---------------------------------------------------------------------------
         Composition of finite map and function
 ---------------------------------------------------------------------------*)

val f_o_DEF = new_infixl_definition
("f_o_DEF",
Term`$f_o (f:('b,'c)fmap) (g:'a->'b)
      = f f_o_f (FUN_FMAP g { x | g x IN FDOM f})`, 500);

val FDOM_f_o = Q.store_thm
("FDOM_f_o",
 `!(f:'b|->'c)  (g:'a->'b).
     FINITE {x | g x IN FDOM f }
       ==>
     (FDOM (f f_o g) = { x | g x IN FDOM f})`,
 SRW_TAC [][f_o_DEF, f_o_f_DEF, EXTENSION, FUN_FMAP_DEF, EQ_IMP_THM]);
val _ = export_rewrites["FDOM_f_o"];

val f_o_FEMPTY = store_thm(
"f_o_FEMPTY",
``!g. FEMPTY f_o g = FEMPTY``,
SRW_TAC[][f_o_DEF])
val _ = export_rewrites["f_o_FEMPTY"]

val f_o_FUPDATE = store_thm(
"f_o_FUPDATE",
``!fm k v g.
  FINITE {x | g x IN FDOM fm} /\
  FINITE {x | (g x = k)} ==>
(fm |+ (k,v) f_o g = FMERGE (combin$C K) (fm f_o g) (FUN_FMAP (K v) {x | g x = k}))``,
SRW_TAC[][] THEN
`FINITE {x | (g x = k) \/ g x IN FDOM fm}` by (
 REPEAT (POP_ASSUM MP_TAC) THEN
 Q.MATCH_ABBREV_TAC `FINITE s1 ==> FINITE s2 ==> FINITE s` THEN
 Q_TAC SUFF_TAC `s = s1 UNION s2` THEN1 SRW_TAC[][] THEN
 UNABBREV_ALL_TAC THEN
 SRW_TAC[][EXTENSION,EQ_IMP_THM] THEN
 SRW_TAC[][]) THEN
SRW_TAC[][GSYM fmap_EQ_THM] THEN1 (
  SRW_TAC[][EXTENSION,EQ_IMP_THM] THEN
  SRW_TAC[][] ) THEN
SRW_TAC[][FMERGE_DEF,FUN_FMAP_DEF,f_o_DEF,f_o_f_DEF
,FAPPLY_FUPDATE_THM])

val FAPPLY_f_o = Q.store_thm
("FAPPLY_f_o",
 `!(f:'b |-> 'c)  (g:'a-> 'b).
    FINITE { x | g x IN FDOM f }
      ==>
    !x. x IN FDOM (f f_o g) ==> (FAPPLY (f f_o g) x = FAPPLY f (g x))`,
 SRW_TAC [][FDOM_f_o, FUN_FMAP_DEF, f_o_DEF, f_o_f_DEF]);


val FINITE_PRED_11 = Q.store_thm
("FINITE_PRED_11",
 `!(g:'a -> 'b).
      (!x y. (g x = g y) = (x = y))
        ==>
      !f:'b|->'c. FINITE { x | g x IN  FDOM f}`,
 GEN_TAC THEN STRIP_TAC THEN
 INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL [
   SRW_TAC [][FDOM_FEMPTY, GSPEC_F],
   SRW_TAC [][FDOM_FUPDATE, GSPEC_OR] THEN
   Cases_on `?y. g y = x` THENL [
     POP_ASSUM (STRIP_THM_THEN SUBST_ALL_TAC o GSYM) THEN
     SRW_TAC [][GSPEC_EQ],
     POP_ASSUM MP_TAC THEN SRW_TAC [][GSPEC_F]
   ]
 ]);

(* ----------------------------------------------------------------------
    Domain subtraction (at a single point)
   ---------------------------------------------------------------------- *)

val fmap_domsub = new_definition(
  "fmap_domsub",
  ``fdomsub fm k = DRESTRICT fm (COMPL {k})``);
val _ = overload_on ("\\\\", ``fdomsub``);
(* this has been set up as an infix in relationTheory *)

val DOMSUB_FEMPTY = store_thm(
  "DOMSUB_FEMPTY",
  ``!k. FEMPTY \\ k = FEMPTY``,
  SRW_TAC [][GSYM fmap_EQ_THM, fmap_domsub, FDOM_DRESTRICT]);

val DOMSUB_FUPDATE = store_thm(
  "DOMSUB_FUPDATE",
  ``!fm k v. fm |+ (k,v) \\ k = fm \\ k``,
  SRW_TAC [][GSYM fmap_EQ_THM, fmap_domsub,
             pred_setTheory.EXTENSION, DRESTRICT_DEF,
             FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);

val DOMSUB_FUPDATE_NEQ = store_thm(
  "DOMSUB_FUPDATE_NEQ",
  ``!fm k1 k2 v. ~(k1 = k2) ==> (fm |+ (k1, v) \\ k2 = fm \\ k2 |+ (k1, v))``,
  SRW_TAC [][GSYM fmap_EQ_THM, fmap_domsub,
             pred_setTheory.EXTENSION, DRESTRICT_DEF,
             FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);

val DOMSUB_FUPDATE_THM = store_thm(
  "DOMSUB_FUPDATE_THM",
  ``!fm k1 k2 v. fm |+ (k1,v) \\ k2 = if k1 = k2 then fm \\ k2
                                      else (fm \\ k2) |+ (k1, v)``,
  SRW_TAC [][GSYM fmap_EQ_THM, fmap_domsub,
             pred_setTheory.EXTENSION, DRESTRICT_DEF,
             FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);

val FDOM_DOMSUB = store_thm(
  "FDOM_DOMSUB",
  ``!fm k. FDOM (fm \\ k) = FDOM fm DELETE k``,
  SRW_TAC [][fmap_domsub, FDOM_DRESTRICT, pred_setTheory.EXTENSION]);

val DOMSUB_FAPPLY = store_thm(
  "DOMSUB_FAPPLY",
  ``!fm k. (fm \\ k) ' k = FEMPTY ' k``,
  SRW_TAC [][fmap_domsub, DRESTRICT_DEF]);

val DOMSUB_FAPPLY_NEQ = store_thm(
  "DOMSUB_FAPPLY_NEQ",
  ``!fm k1 k2. ~(k1 = k2) ==> ((fm \\ k1) ' k2 = fm ' k2)``,
  SRW_TAC [][fmap_domsub, DRESTRICT_DEF, NOT_FDOM_FAPPLY_FEMPTY]);

val DOMSUB_FAPPLY_THM = store_thm(
  "DOMSUB_FAPPLY_THM",
  ``!fm k1 k2. (fm \\ k1) ' k2 = if k1 = k2 then FEMPTY ' k2 else fm ' k2``,
  SRW_TAC [] [DOMSUB_FAPPLY, DOMSUB_FAPPLY_NEQ]);

val DOMSUB_FLOOKUP = store_thm(
  "DOMSUB_FLOOKUP",
  ``!fm k. FLOOKUP (fm \\ k) k = NONE``,
  SRW_TAC [][FLOOKUP_DEF, FDOM_DOMSUB]);

val DOMSUB_FLOOKUP_NEQ = store_thm(
  "DOMSUB_FLOOKUP_NEQ",
  ``!fm k1 k2. ~(k1 = k2) ==> (FLOOKUP (fm \\ k1) k2 = FLOOKUP fm k2)``,
  SRW_TAC [][FLOOKUP_DEF, FDOM_DOMSUB, DOMSUB_FAPPLY_NEQ]);

val DOMSUB_FLOOKUP_THM = store_thm(
  "DOMSUB_FLOOKUP_THM",
  ``!fm k1 k2. FLOOKUP (fm \\ k1) k2 = if k1 = k2 then NONE else FLOOKUP fm k2``,
  SRW_TAC [][DOMSUB_FLOOKUP, DOMSUB_FLOOKUP_NEQ]);

val FRANGE_FUPDATE_DOMSUB = store_thm(
  "FRANGE_FUPDATE_DOMSUB",
  ``!fm k v. FRANGE (fm |+ (k,v)) = v INSERT FRANGE (fm \\ k)``,
  SRW_TAC [][FRANGE_FUPDATE, fmap_domsub]);

val _ = export_rewrites ["DOMSUB_FEMPTY", "DOMSUB_FUPDATE", "FDOM_DOMSUB",
                         "DOMSUB_FAPPLY", "DOMSUB_FLOOKUP", "FRANGE_FUPDATE_DOMSUB"]

val o_f_DOMSUB = store_thm(
  "o_f_DOMSUB",
  ``(g o_f fm) \\ k = g o_f (fm \\ k)``,
  SRW_TAC [][GSYM fmap_EQ_THM, DOMSUB_FAPPLY_THM, o_f_FAPPLY]);
val _ = export_rewrites ["o_f_DOMSUB"]

val DOMSUB_IDEM = store_thm(
  "DOMSUB_IDEM",
  ``(fm \\ k) \\ k = fm \\ k``,
  SRW_TAC [][GSYM fmap_EQ_THM, DOMSUB_FAPPLY_THM]);
val _ = export_rewrites ["DOMSUB_IDEM"]

val DOMSUB_COMMUTES = store_thm(
  "DOMSUB_COMMUTES",
  ``fm \\ k1 \\ k2 = fm \\ k2 \\ k1``,
  SRW_TAC [][GSYM fmap_EQ,DELETE_COMM] THEN
  SRW_TAC [][FUN_EQ_THM,DOMSUB_FAPPLY_THM] THEN
  SRW_TAC [][]);

val o_f_FUPDATE = store_thm(
  "o_f_FUPDATE",
  ``f o_f (fm |+ (k,v)) = (f o_f (fm \\ k)) |+ (k, f v)``,
  SRW_TAC [][GSYM fmap_EQ_THM]
  THENL [
    SRW_TAC [][pred_setTheory.EXTENSION] THEN PROVE_TAC [],
    SRW_TAC [][GSYM fmap_EQ_THM, o_f_FAPPLY],
    Cases_on `x = k` THEN
    SRW_TAC [][GSYM fmap_EQ_THM, o_f_FAPPLY, NOT_EQ_FAPPLY,
               DOMSUB_FAPPLY_NEQ]
  ]);
val _ = export_rewrites ["o_f_FUPDATE"]

val DOMSUB_NOT_IN_DOM = store_thm(
  "DOMSUB_NOT_IN_DOM",
  ``~(k IN FDOM fm) ==> (fm \\ k = fm)``,
  SRW_TAC [][GSYM fmap_EQ_THM, DOMSUB_FAPPLY_THM,
             EXTENSION] THEN PROVE_TAC []);

val fmap_CASES = Q.store_thm
("fmap_CASES",
 `!f:'a |-> 'b. (f = FEMPTY) \/ ?g x y. f = g |+ (x,y)`,
 HO_MATCH_MP_TAC fmap_SIMPLE_INDUCT THEN METIS_TAC []);

val IN_DOMSUB_NOT_EQUAL = Q.prove
(`!f:'a |->'b. !x1 x2. x2 IN FDOM (f \\ x1) ==> ~(x2 = x1)`,
 RW_TAC std_ss [FDOM_DOMSUB,IN_DELETE]);

val SUBMAP_DOMSUB = store_thm(
  "SUBMAP_DOMSUB",
  ``(f \\ k) SUBMAP f``,
  SRW_TAC [][fmap_domsub]);

val FMERGE_DOMSUB = store_thm(
"FMERGE_DOMSUB",
``!m m1 m2 k. (FMERGE m m1 m2) \\ k = FMERGE m (m1 \\ k) (m2 \\ k)``,
SRW_TAC[][fmap_domsub,FMERGE_DRESTRICT])


(*---------------------------------------------------------------------------*)
(* Is there a better statement of this?                                      *)
(*---------------------------------------------------------------------------*)

val SUBMAP_FUPDATE = Q.store_thm
("SUBMAP_FUPDATE",
 `!(f:'a |->'b) g x y.
     (f |+ (x,y)) SUBMAP g =
        x IN FDOM(g) /\ (g ' x = y) /\ (f\\x) SUBMAP (g\\x)`,
 SRW_TAC [boolSimps.DNF_ss][SUBMAP_DEF, DOMSUB_FAPPLY_THM,
                            FAPPLY_FUPDATE_THM] THEN
 METIS_TAC []);

(* ----------------------------------------------------------------------
    Iterated updates
   ---------------------------------------------------------------------- *)

val FEVERY_FUPDATE_LIST = Q.store_thm(
"FEVERY_FUPDATE_LIST",
`ALL_DISTINCT (MAP FST kvl) ==>
 (FEVERY P (fm |++ kvl) <=> EVERY P kvl /\ FEVERY P (DRESTRICT fm (COMPL (set (MAP FST kvl)))))`,
Q.ID_SPEC_TAC `fm` THEN
Induct_on `kvl` THEN SRW_TAC [][FUPDATE_LIST_THM,DRESTRICT_UNIV] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][FUPDATE_FUPDATE_LIST_COMMUTES,FEVERY_FUPDATE] THEN
FULL_SIMP_TAC (srw_ss()) [GSYM COMPL_UNION] THEN
SRW_TAC [][Once UNION_COMM] THEN
SRW_TAC [][Once (GSYM INSERT_SING_UNION)] THEN
SRW_TAC [][EQ_IMP_THM]);

local open listTheory in
val FUPDATE_LIST_APPLY_MEM = store_thm(
"FUPDATE_LIST_APPLY_MEM",
``!kvl f k v n. n < LENGTH kvl /\ (k = EL n (MAP FST kvl)) /\ (v = EL n (MAP SND kvl)) /\
  (!m. n < m /\ m < LENGTH kvl ==> (EL m (MAP FST kvl) <> k))
  ==> ((f |++ kvl) ' k = v)``,
Induct THEN1 SRW_TAC[][] THEN
Cases THEN NTAC 3 GEN_TAC THEN
Cases THEN1 (
  Q.MATCH_RENAME_TAC `0 < LENGTH ((q,r)::kvl) /\ _ ==> _` THEN
  Q.ISPECL_THEN [`kvl`,`f |+ (k,r)`,`k`] MP_TAC FUPDATE_LIST_APPLY_NOT_MEM THEN
  SRW_TAC[][FUPDATE_LIST_THM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][MEM_MAP,MEM_EL,pairTheory.EXISTS_PROD] THEN
  Q.MATCH_RENAME_TAC `_ \/ _ <> EL n kvl` THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `SUC n` MP_TAC) THEN
  SRW_TAC[][EL_MAP] THEN
  METIS_TAC[pairTheory.FST]) THEN
SRW_TAC[][] THEN
Q.MATCH_RENAME_TAC `(f |++ ((q,r)::kvl)) ' _ = _` THEN
Q.ISPECL_THEN [`(q,r)`,`kvl`] SUBST1_TAC rich_listTheory.CONS_APPEND THEN
REWRITE_TAC [FUPDATE_LIST_APPEND] THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
Q.MATCH_ASSUM_RENAME_TAC `n < LENGTH kvl` THEN
Q.EXISTS_TAC `n` THEN
SRW_TAC[][] THEN
Q.MATCH_RENAME_TAC `EL m (MAP FST kvl) <> _` THEN
FIRST_X_ASSUM (Q.SPEC_THEN `SUC m` MP_TAC) THEN
SRW_TAC[][])
end

val FOLDL_FUPDATE_LIST = store_thm("FOLDL_FUPDATE_LIST",
  ``!f1 f2 ls a. FOLDL (\fm k. fm |+ (f1 k, f2 k)) a ls =
    a |++ MAP (\k. (f1 k, f2 k)) ls``,
  SRW_TAC[][FUPDATE_LIST,rich_listTheory.FOLDL_MAP])

val FUPDATE_LIST_SNOC = store_thm("FUPDATE_LIST_SNOC",
  ``!xs x fm. fm |++ SNOC x xs = (fm |++ xs) |+ x``,
  Induct THEN SRW_TAC[][FUPDATE_LIST_THM])

(* ----------------------------------------------------------------------
    More theorems
   ---------------------------------------------------------------------- *)

val FUPD11_SAME_UPDATE = store_thm(
  "FUPD11_SAME_UPDATE",
  ``!f1 f2 k v. (f1 |+ (k,v) = f2 |+ (k,v)) =
                (DRESTRICT f1 (COMPL {k}) = DRESTRICT f2 (COMPL {k}))``,
  SRW_TAC [][GSYM fmap_EQ_THM, EXTENSION, DRESTRICT_DEF, FDOM_FUPDATE,
             FAPPLY_FUPDATE_THM] THEN PROVE_TAC []);

val FUPDATE_LIST_SAME_UPDATE = store_thm(
  "FUPDATE_LIST_SAME_UPDATE",
  ``!kvl f1 f2. (f1 |++ kvl = f2 |++ kvl) =
                (DRESTRICT f1 (COMPL (set (MAP FST kvl))) =
                 DRESTRICT f2 (COMPL (set (MAP FST kvl))))``,
  Induct THENL [
    SRW_TAC [][GSYM fmap_EQ_THM, FUPDATE_LIST_THM, DRESTRICT_DEF] THEN
    PROVE_TAC [],
    ASM_SIMP_TAC (srw_ss()) [FUPDATE_LIST_THM, pairTheory.FORALL_PROD] THEN
    POP_ASSUM (K ALL_TAC) THEN
    SRW_TAC [][GSYM fmap_EQ_THM, FUPDATE_LIST_THM, DRESTRICT_DEF,
               FDOM_FUPDATE, FDOM_FUPDATE_LIST, EXTENSION,
               FAPPLY_FUPDATE_THM] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
    SRW_TAC [][] THEN PROVE_TAC []
  ]);

val FUPDATE_LIST_SAME_KEYS_UNWIND = store_thm(
  "FUPDATE_LIST_SAME_KEYS_UNWIND",
  ``!f1 f2 kvl1 kvl2.
       (f1 |++ kvl1 = f2 |++ kvl2) /\
       (MAP FST kvl1 = MAP FST kvl2) /\ ALL_DISTINCT (MAP FST kvl1) ==>
       (kvl1 = kvl2) /\
       !kvl. (MAP FST kvl = MAP FST kvl1) ==>
             (f1 |++ kvl = f2 |++ kvl)``,
  CONV_TAC (BINDER_CONV SWAP_VARS_CONV THENC SWAP_VARS_CONV) THEN
  Induct THEN ASM_SIMP_TAC (srw_ss()) [FUPDATE_LIST_THM] THEN
  REPEAT GEN_TAC THEN
  `?k v. h = (k,v)` by PROVE_TAC [pair_CASES] THEN
  POP_ASSUM SUBST_ALL_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  `(kvl2 = []) \/ ?k2 v2 t2. kvl2 = (k2,v2) :: t2` by
       PROVE_TAC [pair_CASES, listTheory.list_CASES] THEN
  POP_ASSUM SUBST_ALL_TAC THEN SIMP_TAC (srw_ss()) [] THEN
  SIMP_TAC (srw_ss()) [FUPDATE_LIST_THM] THEN STRIP_TAC THEN
  `kvl1 = t2` by PROVE_TAC [] THEN POP_ASSUM SUBST_ALL_TAC THEN
  `v = v2` by (FIRST_X_ASSUM (MP_TAC o C Q.AP_THM `k` o Q.AP_TERM `(')`) THEN
               SRW_TAC [][FUPDATE_LIST_APPLY_NOT_MEM]) THEN
  SRW_TAC [][] THEN
  `(kvl = []) \/ (?k' v' t. kvl = (k',v') :: t)` by
     PROVE_TAC [pair_CASES, listTheory.list_CASES] THEN
  POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `fm : 'a |-> 'b = fm1` MP_TAC THEN
  SIMP_TAC (srw_ss()) [GSYM FUPDATE_LIST_THM] THEN
  ASM_SIMP_TAC (srw_ss()) [FUPDATE_LIST_SAME_UPDATE]);

val lemma = prove(
  ``!kvl k fm. MEM k (MAP FST kvl) ==>
               MEM (k, (fm |++ kvl) ' k) kvl``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, FUPDATE_LIST_THM,
                           DISJ_IMP_THM, FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `MEM p_1 (MAP FST kvl)` THEN
  SRW_TAC [][FUPDATE_LIST_APPLY_NOT_MEM]);

val FM_CONCRETE_EQ_ENUMERATE_CASES = store_thm(
  "FMEQ_ENUMERATE_CASES",
  ``!f1 kvl p. (f1 |+ p = FEMPTY |++ kvl) ==> MEM p kvl``,
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, GSYM fmap_EQ_THM,
                       FDOM_FUPDATE, FDOM_FUPDATE_LIST, DISJ_IMP_THM,
                       FORALL_AND_THM, FDOM_FEMPTY] THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
  PROVE_TAC [lemma]);

val FMEQ_SINGLE_SIMPLE_ELIM = store_thm(
  "FMEQ_SINGLE_SIMPLE_ELIM",
  ``!P k v ck cv nv. (?fm. (fm |+ (k, v) = FEMPTY |+ (ck, cv)) /\
                           P (fm |+ (k, nv))) =
                     (k = ck) /\ (v = cv) /\ P (FEMPTY |+ (ck, nv))``,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    `FEMPTY |+ (ck, cv) = FEMPTY |++ [(ck,cv)]`
       by SRW_TAC [][FUPDATE_LIST_THM] THEN
    `MEM (k,v) [(ck, cv)]` by PROVE_TAC [FM_CONCRETE_EQ_ENUMERATE_CASES] THEN
    FULL_SIMP_TAC (srw_ss()) [FUPDATE_LIST_THM] THEN
    PROVE_TAC [FUPD_SAME_KEY_UNWIND],
    Q.EXISTS_TAC `FEMPTY` THEN SRW_TAC [][]
  ]);

val FMEQ_SINGLE_SIMPLE_DISJ_ELIM = store_thm(
  "FMEQ_SINGLE_SIMPLE_DISJ_ELIM",
  ``!fm k v ck cv.
       (fm |+ (k,v) = FEMPTY |+ (ck, cv)) =
       (k = ck) /\ (v = cv) /\
       ((fm = FEMPTY) \/ (?v'. fm = FEMPTY |+ (k, v')))``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC (srw_ss()) [DISJ_IMP_THM, LEFT_AND_OVER_OR,
                       GSYM RIGHT_EXISTS_AND_THM,
                       GSYM LEFT_FORALL_IMP_THM] THEN
  SIMP_TAC (srw_ss() ++ boolSimps.CONJ_ss)
           [GSYM fmap_EQ_THM, DISJ_IMP_THM, FORALL_AND_THM] THEN
  SIMP_TAC (srw_ss()) [EXTENSION] THEN
  PROVE_TAC [FAPPLY_FUPDATE]);


val FUPDATE_PURGE = Q.store_thm
("FUPDATE_PURGE",
 `!f x y. f |+ (x,y) = (f \\ x) |+ (x,y)`,
 SRW_TAC [] [fmap_EXT,EXTENSION,FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM] THEN
 METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* For EVAL on terms with finite map expressions.                            *)
(*---------------------------------------------------------------------------*)

val _ =
 computeLib.add_persistent_funs
  ["FUPDATE_LIST_THM",
   "DOMSUB_FUPDATE_THM",
   "DOMSUB_FEMPTY",
   "FDOM_FUPDATE",
   "FAPPLY_FUPDATE_THM",
   "FDOM_FEMPTY",
   "FLOOKUP_EMPTY",
   "FLOOKUP_UPDATE"];


(*---------------------------------------------------------------------------*)
(* Mapping for finite maps with two arguments, compare to o_f                *)
(* added 17 March 2009 by Thomas Tuerk, updated 26 March                     *)
(*---------------------------------------------------------------------------*)

val FMAP_MAP2_def = Define
`FMAP_MAP2 f m = FUN_FMAP (\x. f (x,m ' x)) (FDOM m)`;


val FMAP_MAP2_THM = store_thm ("FMAP_MAP2_THM",
``(FDOM (FMAP_MAP2 f m) = FDOM m) /\
  (!x. x IN FDOM m ==> ((FMAP_MAP2 f m) ' x = f (x,m ' x)))``,

SIMP_TAC std_ss [FMAP_MAP2_def,
		 FUN_FMAP_DEF, FDOM_FINITE]);



val FMAP_MAP2_FEMPTY = store_thm ("FMAP_MAP2_FEMPTY",
``FMAP_MAP2 f FEMPTY = FEMPTY``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMAP_MAP2_THM,
		 FDOM_FEMPTY, NOT_IN_EMPTY]);


val FMAP_MAP2_FUPDATE = store_thm ("FMAP_MAP2_FUPDATE",
``FMAP_MAP2 f (m |+ (x, v)) =
  (FMAP_MAP2 f m) |+ (x, f (x,v))``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMAP_MAP2_THM,
		 FDOM_FUPDATE, IN_INSERT,
		 FAPPLY_FUPDATE_THM,
		 COND_RAND, COND_RATOR,
		 DISJ_IMP_THM]);

(*---------------------------------------------------------------------------*)
(* Some general stuff                                                        *)
(* added 17 March 2009 by Thomas Tuerk                                       *)
(*---------------------------------------------------------------------------*)

val FEVERY_STRENGTHEN_THM =
store_thm ("FEVERY_STRENGTHEN_THM",
``FEVERY P FEMPTY /\
  ((FEVERY P f /\ P (x,y)) ==> FEVERY P (f |+ (x,y)))``,

SIMP_TAC std_ss [FEVERY_DEF, FDOM_FEMPTY,
		 NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
		 FDOM_FUPDATE, IN_INSERT] THEN
METIS_TAC[]);



val FEVERY_DRESTRICT_COMPL = store_thm(
"FEVERY_DRESTRICT_COMPL",
``FEVERY P (DRESTRICT (f |+ (k, v)) (COMPL s)) =
  ((~(k IN s) ==> P (k,v)) /\
  (FEVERY P (DRESTRICT f (COMPL (k INSERT s)))))``,

SIMP_TAC std_ss [FEVERY_DEF, IN_INTER,
		 FDOM_DRESTRICT,
                 DRESTRICT_DEF, FAPPLY_FUPDATE_THM,
                 FDOM_FUPDATE, IN_INSERT,
		 RIGHT_AND_OVER_OR, IN_COMPL,
                 DISJ_IMP_THM, FORALL_AND_THM] THEN
PROVE_TAC[]);


(*---------------------------------------------------------------------------
     Merging of finite maps (added 17 March 2009 by Thomas Tuerk)
 ---------------------------------------------------------------------------*)

val DOMSUB_FUNION = store_thm ("DOMSUB_FUNION",
``(FUNION f g) \\ k = FUNION (f \\ k) (g \\ k)``,
SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, FUNION_DEF, EXTENSION,
   IN_UNION, IN_DELETE] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],
   ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_NEQ, FUNION_DEF],
   ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_NEQ, FUNION_DEF]
]);

val DRESTRICT_EQ_FUNION = store_thm ("DRESTRICT_EQ_FUNION",
   ``!h h1 h2. DISJOINT (FDOM h1) (FDOM h2) /\ (FUNION h1 h2 = h) ==>
               (h2 = DRESTRICT h (COMPL (FDOM h1)))``,
    SIMP_TAC std_ss [DRESTRICT_DEF, GSYM fmap_EQ_THM, EXTENSION,
      FUNION_DEF, IN_INTER, IN_UNION, IN_COMPL, DISJOINT_DEF,
      NOT_IN_EMPTY] THEN
    METIS_TAC[]);


val IN_FDOM_FOLDR_UNION = store_thm ("IN_FDOM_FOLDR_UNION",
``!x hL. x IN FDOM (FOLDR FUNION FEMPTY hL) =
         ?h. MEM h hL /\ x IN FDOM h``,

Induct_on `hL` THENL [
   SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

   FULL_SIMP_TAC list_ss [FDOM_FUNION, IN_UNION, DISJ_IMP_THM] THEN
   METIS_TAC[]
]);


val DRESTRICT_FUNION_DRESTRICT_COMPL = store_thm (
"DRESTRICT_FUNION_DRESTRICT_COMPL",
``FUNION (DRESTRICT f s) (DRESTRICT f (COMPL s)) = f ``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, DRESTRICT_DEF,
   EXTENSION, IN_INTER, IN_UNION, IN_COMPL] THEN
METIS_TAC[]);


(*---------------------------------------------------------------------------
mapping an injective function over the keys of a finite map
 ---------------------------------------------------------------------------*)

val MAP_KEYS_q =`
\f fm. if INJ f (FDOM fm) UNIV then
fm f_o_f (FUN_FMAP (LINV f (FDOM fm)) (IMAGE f (FDOM fm)))
else FUN_FMAP ARB (IMAGE f (FDOM fm))`

val MAP_KEYS_witness = store_thm(
"MAP_KEYS_witness",
``let m = ^(Term MAP_KEYS_q) in
!f fm. (FDOM (m f fm) = IMAGE f (FDOM fm)) /\
       ((INJ f (FDOM fm) UNIV) ==>
        (!x. x IN FDOM fm ==> (((m f fm) ' (f x)) = (fm ' x))))``,
SIMP_TAC (srw_ss()) [LET_THM] THEN
REPEAT GEN_TAC THEN
CONJ_ASM1_TAC THEN1 (
  SRW_TAC[][f_o_f_DEF,
            GSYM SUBSET_INTER_ABSORPTION,
            SUBSET_DEF,FUN_FMAP_DEF] THEN
  IMP_RES_TAC LINV_DEF THEN
  SRW_TAC[][] ) THEN
SRW_TAC[][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.MATCH_ABBREV_TAC `(fm f_o_f z) ' (f x) = fm ' x` THEN
`f x IN FDOM (fm f_o_f z)` by (
  SRW_TAC[][] THEN PROVE_TAC[] ) THEN
SRW_TAC[][f_o_f_DEF] THEN
Q.UNABBREV_TAC `z` THEN
Q.MATCH_ABBREV_TAC `fm ' ((FUN_FMAP z s) ' (f x)) = fm ' x` THEN
`f x IN s` by (
  SRW_TAC[][Abbr`s`] THEN PROVE_TAC[] ) THEN
`FINITE s` by SRW_TAC[][Abbr`s`] THEN
SRW_TAC[][FUN_FMAP_DEF,Abbr`z`] THEN
IMP_RES_TAC LINV_DEF THEN
SRW_TAC[][])

val MAP_KEYS_exists =
Q.EXISTS (`$? ^(rand(rator(concl(MAP_KEYS_witness))))`,MAP_KEYS_q)
(BETA_RULE (PURE_REWRITE_RULE [LET_THM] MAP_KEYS_witness))

val MAP_KEYS_def = new_specification(
"MAP_KEYS_def",["MAP_KEYS"],MAP_KEYS_exists)

val MAP_KEYS_FEMPTY = store_thm(
"MAP_KEYS_FEMPTY",
``!f. MAP_KEYS f FEMPTY = FEMPTY``,
SRW_TAC[][GSYM FDOM_EQ_EMPTY,MAP_KEYS_def])
val _ = export_rewrites["MAP_KEYS_FEMPTY"]

val MAP_KEYS_FUPDATE = store_thm(
"MAP_KEYS_FUPDATE",
``!f fm k v. (INJ f (k INSERT FDOM fm) UNIV) ==>
  (MAP_KEYS f (fm |+ (k,v)) = (MAP_KEYS f fm) |+ (f k,v))``,
SRW_TAC[][GSYM fmap_EQ_THM,MAP_KEYS_def] THEN
SRW_TAC[][MAP_KEYS_def,FAPPLY_FUPDATE_THM] THEN1 (
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF] THEN
  PROVE_TAC[] ) THEN
FULL_SIMP_TAC (srw_ss()) [INJ_INSERT] THEN
SRW_TAC[][MAP_KEYS_def])

val MAP_KEYS_using_LINV = store_thm(
"MAP_KEYS_using_LINV",
``!f fm. INJ f (FDOM fm) UNIV ==>
  (MAP_KEYS f fm = fm f_o_f (FUN_FMAP (LINV f (FDOM fm)) (IMAGE f (FDOM fm))))``,
SRW_TAC[][GSYM fmap_EQ_THM,MAP_KEYS_def] THEN
MP_TAC MAP_KEYS_witness THEN
SRW_TAC[][LET_THM] THEN
POP_ASSUM (Q.SPECL_THEN [`f`,`fm`] MP_TAC) THEN
SRW_TAC[][MAP_KEYS_def])

(* Relate the values in two finite maps *)

val fmap_rel_def = Define`
  fmap_rel R f1 f2 = (FDOM f2 = FDOM f1) /\ (!x. x IN FDOM f1 ==> R (f1 ' x) (f2 ' x))`

val fmap_rel_FUPDATE_same = store_thm(
"fmap_rel_FUPDATE_same",
``fmap_rel R f1 f2 /\ R v1 v2 ==> fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))``,
SRW_TAC[][fmap_rel_def,FAPPLY_FUPDATE_THM] THEN SRW_TAC[][])

val fmap_rel_FUPDATE_LIST_same = store_thm(
"fmap_rel_FUPDATE_LIST_same",
``!R ls1 ls2 f1 f2.
  fmap_rel R f1 f2 /\ (MAP FST ls1 = MAP FST ls2) /\ (LIST_REL R (MAP SND ls1) (MAP SND ls2))
  ==> fmap_rel R (f1 |++ ls1) (f2 |++ ls2)``,
GEN_TAC THEN
Induct THEN Cases THEN SRW_TAC[][FUPDATE_LIST_THM,listTheory.LIST_REL_CONS1] THEN
Cases_on `ls2` THEN FULL_SIMP_TAC(srw_ss())[FUPDATE_LIST_THM] THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC(srw_ss())[] THEN SRW_TAC[][] THEN
Q.MATCH_ASSUM_RENAME_TAC `R a (SND b)` THEN
Cases_on `b` THEN FULL_SIMP_TAC(srw_ss())[] THEN
SRW_TAC[][fmap_rel_FUPDATE_same])

val fmap_rel_FEMPTY = store_thm(
"fmap_rel_FEMPTY",
``fmap_rel R FEMPTY FEMPTY``,
SRW_TAC[][fmap_rel_def])
val _ = export_rewrites["fmap_rel_FEMPTY"]

val fmap_rel_FEMPTY2 = store_thm(
  "fmap_rel_FEMPTY2",
  ``(fmap_rel R FEMPTY f <=> (f = FEMPTY)) /\
    (fmap_rel R f FEMPTY <=> (f = FEMPTY))``,
  SRW_TAC [][fmap_rel_def, FDOM_EQ_EMPTY, EQ_IMP_THM] THEN
  METIS_TAC [FDOM_EQ_EMPTY]);
val _ = export_rewrites ["fmap_rel_FEMPTY2"]

val fmap_rel_refl = store_thm(
"fmap_rel_refl",
``(!x. R x x) ==> fmap_rel R x x``,
SRW_TAC[][fmap_rel_def])
val _ = export_rewrites["fmap_rel_refl"]

val fmap_rel_FUNION_rels = store_thm(
"fmap_rel_FUNION_rels",
``fmap_rel R f1 f2 /\ fmap_rel R f3 f4 ==> fmap_rel R (FUNION f1 f3) (FUNION f2 f4)``,
SRW_TAC[][fmap_rel_def,FUNION_DEF] THEN SRW_TAC[][])

val fmap_rel_FUPDATE_I = store_thm(
  "fmap_rel_FUPDATE_I",
  ``fmap_rel R (f1 \\ k) (f2 \\ k) /\ R v1 v2 ==>
    fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))``,
  SRW_TAC[][fmap_rel_def] THENL [
    Q.PAT_ASSUM `FDOM X DELETE EE = FDOM Y DELETE FF` MP_TAC THEN
    SRW_TAC [][EXTENSION] THEN METIS_TAC [],
    SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [DOMSUB_FAPPLY_THM] THEN
    SRW_TAC[][FAPPLY_FUPDATE_THM]
  ]);

val fmap_rel_mono = store_thm(
  "fmap_rel_mono",
  ``(!x y. R1 x y ==> R2 x y) ==> fmap_rel R1 f1 f2 ==> fmap_rel R2 f1 f2``,
  SRW_TAC [][fmap_rel_def]);
val _ = export_mono "fmap_rel_mono"


(*---------------------------------------------------------------------------
     Some helpers for fupdate_NORMALISE_CONV
 ---------------------------------------------------------------------------*)

val fmap_EQ_UPTO_def = Define `
fmap_EQ_UPTO f1 f2 vs =
  (FDOM f1 INTER (COMPL vs) = FDOM f2 INTER (COMPL vs)) /\
  (!x. x IN FDOM f1 INTER (COMPL vs) ==> (f1 ' x = f2 ' x))`

val fmap_EQ_UPTO___EMPTY = store_thm ("fmap_EQ_UPTO___EMPTY",
``!f1 f2. (fmap_EQ_UPTO f1 f2 EMPTY) = (f1 = f2)``,
SIMP_TAC std_ss [fmap_EQ_UPTO_def, COMPL_EMPTY, INTER_UNIV, fmap_EQ_THM])
val _ = export_rewrites ["fmap_EQ_UPTO___EMPTY"]

val fmap_EQ_UPTO___EQ = store_thm ("fmap_EQ_UPTO___EQ",
``!vs f. (fmap_EQ_UPTO f f vs)``,SIMP_TAC std_ss [fmap_EQ_UPTO_def])
val _ = export_rewrites ["fmap_EQ_UPTO___EQ"]

val fmap_EQ_UPTO___FUPDATE_BOTH = store_thm ("fmap_EQ_UPTO___FUPDATE_BOTH",
``!f1 f2 ks k v.
    (fmap_EQ_UPTO f1 f2 ks) ==>
    (fmap_EQ_UPTO (f1 |+ (k,v)) (f2 |+ (k,v)) (ks DELETE k))``,
SIMP_TAC std_ss [fmap_EQ_UPTO_def, EXTENSION, IN_INTER,
   FDOM_FUPDATE, IN_COMPL, IN_INSERT, IN_DELETE] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
CONJ_TAC THEN GEN_TAC THENL [
   Cases_on `x = k` THEN ASM_REWRITE_TAC[],
   Cases_on `x = k` THEN ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
]);


val fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE = store_thm (
"fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE",
``!f1 f2 ks k v.
     (fmap_EQ_UPTO f1 f2 ks) ==>
     (fmap_EQ_UPTO (f1 |+ (k,v)) (f2 |+ (k,v)) ks)``,

SIMP_TAC std_ss [fmap_EQ_UPTO_def, EXTENSION, IN_INTER,
   FDOM_FUPDATE, IN_COMPL, IN_INSERT] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
CONJ_TAC THEN GEN_TAC THENL [
   Cases_on `x = k` THEN ASM_REWRITE_TAC[],
   Cases_on `x = k` THEN ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
]);


val fmap_EQ_UPTO___FUPDATE_SING = store_thm ("fmap_EQ_UPTO___FUPDATE_SING",
``!f1 f2 ks k v.
     (fmap_EQ_UPTO f1 f2 ks) ==>
     (fmap_EQ_UPTO (f1 |+ (k,v)) f2 (k INSERT ks))``,

SIMP_TAC std_ss [fmap_EQ_UPTO_def, EXTENSION, IN_INTER,
   FDOM_FUPDATE, IN_COMPL, IN_INSERT, IN_DELETE] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
CONJ_TAC THEN GEN_TAC THENL [
   Cases_on `x = k` THEN ASM_REWRITE_TAC[],
   Cases_on `x = k` THEN ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
]);

(*---------------------------------------------------------------------------*)
(* From Ramana Kumar                                                         *)
(*---------------------------------------------------------------------------*)

val fmap_size_def =
 Define
   `fmap_size kz vz fm = SIGMA (\k. kz k + vz (fm ' k)) (FDOM fm)`;

(*---------------------------------------------------------------------------*)
(* Various lemmas from the CakeML project https://cakeml.org                 *)
(*---------------------------------------------------------------------------*)

local
  open lcsymtacs optionTheory rich_listTheory listTheory boolSimps sortingTheory
in

val o_f_FUNION = store_thm("o_f_FUNION",
  ``f o_f (FUNION f1 f2) = FUNION (f o_f f1) (f o_f f2)``,
  simp[GSYM fmap_EQ_THM,FUNION_DEF] >>
  rw[o_f_FAPPLY]);

val FDOM_FOLDR_DOMSUB = store_thm("FDOM_FOLDR_DOMSUB",
  ``!ls fm. FDOM (FOLDR (\k m. m \\ k) fm ls) = FDOM fm DIFF set ls``,
  Induct >> simp[] >>
  ONCE_REWRITE_TAC[EXTENSION] >>
  simp[] >> metis_tac[]);

val FEVERY_SUBMAP = store_thm("FEVERY_SUBMAP",
  ``FEVERY P fm /\ fm0 SUBMAP fm ==> FEVERY P fm0``,
  SRW_TAC[][FEVERY_DEF,SUBMAP_DEF]);

val FEVERY_ALL_FLOOKUP = store_thm("FEVERY_ALL_FLOOKUP",
  ``!P f. FEVERY P f <=> !k v. (FLOOKUP f k = SOME v) ==> P (k,v)``,
  SRW_TAC[][FEVERY_DEF,FLOOKUP_DEF]);

val FUPDATE_LIST_CANCEL = store_thm("FUPDATE_LIST_CANCEL",
  ``!ls1 fm ls2.
    (!k. MEM k (MAP FST ls1) ==> MEM k (MAP FST ls2))
    ==> (fm |++ ls1 |++ ls2 = fm |++ ls2)``,
  Induct THEN SRW_TAC[][FUPDATE_LIST_THM] THEN
  Cases_on`h` THEN
  MATCH_MP_TAC FUPDATE_FUPDATE_LIST_MEM THEN
  FULL_SIMP_TAC(srw_ss())[]);

val FUPDATE_EQ_FUNION = store_thm("FUPDATE_EQ_FUNION",
  ``!fm kv. fm |+ kv = FUNION (FEMPTY |+ kv) fm``,
  gen_tac >> Cases >>
  simp[GSYM fmap_EQ_THM,FDOM_FUPDATE,FAPPLY_FUPDATE_THM,FUNION_DEF] >>
  simp[EXTENSION]);

val FUPDATE_LIST_APPEND_COMMUTES = store_thm("FUPDATE_LIST_APPEND_COMMUTES",
  ``!l1 l2 fm. DISJOINT (set (MAP FST l1)) (set (MAP FST l2)) ==>
               (fm |++ l1 |++ l2 = fm |++ l2 |++ l1)``,
  Induct >- rw[FUPDATE_LIST_THM] >>
  Cases >> rw[FUPDATE_LIST_THM] >>
  metis_tac[FUPDATE_FUPDATE_LIST_COMMUTES]);

val fmap_rel_OPTREL_FLOOKUP = store_thm("fmap_rel_OPTREL_FLOOKUP",
  ``fmap_rel R f1 f2 = !k. OPTREL R (FLOOKUP f1 k) (FLOOKUP f2 k)``,
  rw[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF,EXTENSION] >>
  PROVE_TAC[]);

val FLOOKUP_DRESTRICT = store_thm("FLOOKUP_DRESTRICT",
  ``!fm s k. FLOOKUP (DRESTRICT fm s) k = if k IN s then FLOOKUP fm k else NONE``,
  SRW_TAC[][FLOOKUP_DEF,DRESTRICT_DEF] THEN FULL_SIMP_TAC std_ss []);

val FUPDATE_LIST_ALL_DISTINCT_PERM = store_thm("FUPDATE_LIST_ALL_DISTINCT_PERM",
  ``!ls ls' fm. ALL_DISTINCT (MAP FST ls) /\ PERM ls ls' ==> (fm |++ ls = fm |++ ls')``,
  Induct >> rw[] >>
  fs[sortingTheory.PERM_CONS_EQ_APPEND] >>
  rw[FUPDATE_LIST_THM] >>
  PairCases_on`h` >> fs[] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `(fm |++ (M ++ N)) |+ (h0,h1)` >>
  conj_tac >- metis_tac[sortingTheory.ALL_DISTINCT_PERM,sortingTheory.PERM_MAP] >>
  rw[FUPDATE_LIST_APPEND] >>
  `h0 NOTIN set (MAP FST N)`
  by metis_tac[sortingTheory.PERM_MEM_EQ,MEM_MAP,MEM_APPEND] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  rw[FUPDATE_LIST_THM]);

val IMAGE_FRANGE = store_thm("IMAGE_FRANGE",
  ``!f fm. IMAGE f (FRANGE fm) = FRANGE (f o_f fm)``,
  SRW_TAC[][EXTENSION] THEN
  EQ_TAC THEN1 PROVE_TAC[o_f_FRANGE] THEN
  SRW_TAC[][FRANGE_DEF] THEN
  SRW_TAC[][o_f_FAPPLY] THEN
  PROVE_TAC[]);

val SUBMAP_mono_FUPDATE = store_thm("SUBMAP_mono_FUPDATE",
  ``!f g x y. f \\ x SUBMAP g \\ x ==> f |+ (x,y) SUBMAP g |+ (x,y)``,
  SRW_TAC[][SUBMAP_FUPDATE]);

val SUBMAP_DOMSUB_gen = store_thm("SUBMAP_DOMSUB_gen",
  ``!f g k. f \\ k SUBMAP g <=> f \\ k SUBMAP g \\ k``,
  SRW_TAC[][SUBMAP_DEF,EQ_IMP_THM,DOMSUB_FAPPLY_THM]);

val DOMSUB_SUBMAP = store_thm("DOMSUB_SUBMAP",
  ``!f g x. f SUBMAP g /\ x NOTIN FDOM f ==> f SUBMAP g \\ x``,
  SRW_TAC[][SUBMAP_DEF,DOMSUB_FAPPLY_THM] THEN
  SRW_TAC[][] THEN METIS_TAC[]);

val DRESTRICT_DOMSUB = store_thm("DRESTRICT_DOMSUB",
  ``!f s k. DRESTRICT f s \\ k = DRESTRICT f (s DELETE k)``,
  SRW_TAC[][GSYM fmap_EQ_THM,FDOM_DRESTRICT] THEN1 (
    SRW_TAC[][EXTENSION] THEN METIS_TAC[] ) THEN
  SRW_TAC[][DOMSUB_FAPPLY_THM] THEN
  SRW_TAC[][DRESTRICT_DEF]);

val DRESTRICT_SUBSET_SUBMAP_gen = store_thm("DRESTRICT_SUBSET_SUBMAP_gen",
  ``!f1 f2 s t.
     DRESTRICT f1 s SUBMAP DRESTRICT f2 s /\ t SUBSET s ==>
     DRESTRICT f1 t SUBMAP DRESTRICT f2 t``,
  rw[SUBMAP_DEF,DRESTRICT_DEF,SUBSET_DEF])


val DRESTRICT_FUNION_SAME = store_thm("DRESTRICT_FUNION_SAME",
  ``!fm s. FUNION (DRESTRICT fm s) fm = fm``,
  SRW_TAC[][GSYM SUBMAP_FUNION_ABSORPTION])

val DRESTRICT_EQ_DRESTRICT_SAME = store_thm("DRESTRICT_EQ_DRESTRICT_SAME",
  ``(DRESTRICT f1 s = DRESTRICT f2 s) <=>
    (s INTER FDOM f1 = s INTER FDOM f2) /\
    (!x. x IN FDOM f1 /\ x IN s ==> (f1 ' x = f2 ' x))``,
  SRW_TAC[][DRESTRICT_EQ_DRESTRICT,SUBMAP_DEF,DRESTRICT_DEF,EXTENSION] THEN
  PROVE_TAC[])

val FOLDL2_FUPDATE_LIST = store_thm(
"FOLDL2_FUPDATE_LIST",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ==>
  (FOLDL2 (\fm b c. fm |+ (f1 b c, f2 b c)) a bs cs =
   a |++ ZIP (MAP2 f1 bs cs, MAP2 f2 bs cs))``,
SRW_TAC[][FUPDATE_LIST,FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,
          rich_listTheory.FOLDL_MAP,rich_listTheory.LENGTH_MAP2,
          LENGTH_ZIP,pairTheory.LAMBDA_PROD])

val FOLDL2_FUPDATE_LIST_paired = store_thm(
"FOLDL2_FUPDATE_LIST_paired",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ==>
  (FOLDL2 (\fm b (c,d). fm |+ (f1 b c d, f2 b c d)) a bs cs =
   a |++ ZIP (MAP2 (\b. UNCURRY (f1 b)) bs cs, MAP2 (\b. UNCURRY (f2 b)) bs cs))``,
rw[FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,LENGTH_ZIP,
   pairTheory.UNCURRY,pairTheory.LAMBDA_PROD,FUPDATE_LIST,
   rich_listTheory.FOLDL_MAP])

val DRESTRICT_FUNION_SUBSET = store_thm("DRESTRICT_FUNION_SUBSET",
  ``s2 SUBSET s1 ==>
    ?h. (FUNION (DRESTRICT f s1) g = FUNION (DRESTRICT f s2) h)``,
  strip_tac >>
  qexists_tac `FUNION (DRESTRICT f s1) g` >>
  match_mp_tac EQ_SYM >>
  REWRITE_TAC[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF] >>
  fs[SUBSET_DEF])

val FUPDATE_LIST_APPLY_NOT_MEM_matchable = store_thm(
"FUPDATE_LIST_APPLY_NOT_MEM_matchable",
``!kvl f k v. ~MEM k (MAP FST kvl) /\ (v = f ' k) ==> ((f |++ kvl) ' k = v)``,
PROVE_TAC[FUPDATE_LIST_APPLY_NOT_MEM])

val FUPDATE_LIST_APPLY_HO_THM = store_thm(
"FUPDATE_LIST_APPLY_HO_THM",
``!P f kvl k.
(?n. n < LENGTH kvl /\ (k = EL n (MAP FST kvl)) /\ P (EL n (MAP SND kvl)) /\
     (!m. n < m /\ m < LENGTH kvl ==> EL m (MAP FST kvl) <> k)) \/
(~MEM k (MAP FST kvl) /\ P (f ' k))
==> (P ((f |++ kvl) ' k))``,
metis_tac[FUPDATE_LIST_APPLY_MEM,FUPDATE_LIST_APPLY_NOT_MEM])

val FUPDATE_SAME_APPLY = store_thm(
"FUPDATE_SAME_APPLY",
``(x = FST kv) \/ (fm1 ' x = fm2 ' x) ==> ((fm1 |+ kv) ' x = (fm2 |+ kv) ' x)``,
Cases_on `kv` >> rw[FAPPLY_FUPDATE_THM])

val FUPDATE_SAME_LIST_APPLY = store_thm(
"FUPDATE_SAME_LIST_APPLY",
``!kvl fm1 fm2 x. MEM x (MAP FST kvl) ==> ((fm1 |++ kvl) ' x = (fm2 |++ kvl) ' x)``,
ho_match_mp_tac SNOC_INDUCT >>
conj_tac >- rw[] >>
rw[FUPDATE_LIST,FOLDL_SNOC] >>
match_mp_tac FUPDATE_SAME_APPLY >>
qmatch_rename_tac `(y = FST p) \/ _` >>
Cases_on `y = FST p` >> rw[] >>
first_x_assum match_mp_tac >>
fs[MEM_MAP] >>
PROVE_TAC[])

val FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM = store_thm(
"FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM",
``!P ls k v fm. ALL_DISTINCT (MAP FST ls) /\
  MEM (k,v) ls /\
  P v ==>
  P ((fm |++ ls) ' k)``,
rw[] >>
ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
disj1_tac >>
fs[EL_ALL_DISTINCT_EL_EQ,MEM_EL] >>
qpat_assum `(k,v) = X` (assume_tac o SYM) >>
qexists_tac `n` >> rw[EL_MAP] >>
first_x_assum (qspecl_then [`n`,`m`] mp_tac) >>
rw[EL_MAP] >> spose_not_then strip_assume_tac >>
rw[] >> fs[])

val FUPDATE_LIST_ALL_DISTINCT_REVERSE = store_thm("FUPDATE_LIST_ALL_DISTINCT_REVERSE",
  ``!ls. ALL_DISTINCT (MAP FST ls) ==> !fm. fm |++ (REVERSE ls) = fm |++ ls``,
  Induct >- rw[] >>
  qx_gen_tac `p` >> PairCases_on `p` >>
  rw[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM] >>
  fs[] >>
  rw[FUPDATE_FUPDATE_LIST_COMMUTES])

(* FRANGE subset stuff *)

val IN_FRANGE = store_thm(
"IN_FRANGE",
``!f v. v IN FRANGE f <=> ?k. k IN FDOM f /\ (f ' k = v)``,
SRW_TAC[][FRANGE_DEF])

val IN_FRANGE_FLOOKUP = store_thm("IN_FRANGE_FLOOKUP",
``!f v. v IN FRANGE f <=> ?k. FLOOKUP f k = SOME v``,
rw[IN_FRANGE,FLOOKUP_DEF])

val FRANGE_FUPDATE_LIST_SUBSET = store_thm(
"FRANGE_FUPDATE_LIST_SUBSET",
``!ls fm. FRANGE (fm |++ ls) SUBSET FRANGE fm UNION (set (MAP SND ls))``,
Induct >- rw[FUPDATE_LIST_THM] >>
qx_gen_tac `p` >> qx_gen_tac `fm` >>
pop_assum (qspec_then `fm |+ p` mp_tac) >>
srw_tac[DNF_ss][SUBSET_DEF] >>
first_x_assum (qspec_then `x` mp_tac) >> fs[FUPDATE_LIST_THM] >>
rw[] >> fs[] >>
PairCases_on `p` >>
fsrw_tac[DNF_ss][FRANGE_FLOOKUP,FLOOKUP_UPDATE] >>
pop_assum mp_tac >> rw[] >>
PROVE_TAC[])

val IN_FRANGE_FUPDATE_LIST_suff = store_thm(
"IN_FRANGE_FUPDATE_LIST_suff",
``(!v. v IN FRANGE fm ==> P v) /\ (!v. MEM v (MAP SND ls) ==> P v) ==>
    !v. v IN FRANGE (fm |++ ls) ==> P v``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_LIST_SUBSET) >>
PROVE_TAC[])

val FRANGE_FUNION_SUBSET = store_thm(
"FRANGE_FUNION_SUBSET",
``FRANGE (FUNION f1 f2) SUBSET FRANGE f1 UNION FRANGE f2``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,FUNION_DEF] >>
PROVE_TAC[])

val IN_FRANGE_FUNION_suff = store_thm(
"IN_FRANGE_FUNION_suff",
``(!v. v IN FRANGE f1 ==> P v) /\ (!v. v IN FRANGE f2 ==> P v) ==>
  (!v. v IN FRANGE (FUNION f1 f2) ==> P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUNION_SUBSET) >>
PROVE_TAC[])

val FRANGE_DOMSUB_SUBSET = store_thm(
"FRANGE_DOMSUB_SUBSET",
``FRANGE (fm \\ k) SUBSET FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
PROVE_TAC[])

val IN_FRANGE_DOMSUB_suff = store_thm(
"IN_FRANGE_DOMSUB_suff",
``(!v. v IN FRANGE fm ==> P v) ==> (!v. v IN FRANGE (fm \\ k) ==> P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DOMSUB_SUBSET) >>
PROVE_TAC[])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) SUBSET FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] >>
PROVE_TAC[])

val IN_FRANGE_DRESTRICT_suff = store_thm(
"IN_FRANGE_DRESTRICT_suff",
``(!v. v IN FRANGE fm ==> P v) ==> (!v. v IN FRANGE (DRESTRICT fm s) ==> P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DRESTRICT_SUBSET) >>
PROVE_TAC[])

val FRANGE_FUPDATE_SUBSET = store_thm(
"FRANGE_FUPDATE_SUBSET",
``FRANGE (fm |+ kv) SUBSET FRANGE fm UNION {SND kv}``,
Cases_on `kv` >>
rw[FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
rw[] >> PROVE_TAC[])

val IN_FRANGE_FUPDATE_suff = store_thm(
"IN_FRANGE_FUPDATE_suff",
`` (!v. v IN FRANGE fm ==> P v) /\ (P (SND kv))
==> (!v. v IN FRANGE (fm |+ kv) ==> P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_SUBSET) >>
fs[])

val IN_FRANGE_o_f_suff = store_thm("IN_FRANGE_o_f_suff",
  ``(!v. v IN FRANGE fm ==> P (f v)) ==> !v. v IN FRANGE (f o_f fm) ==> P v``,
  rw[IN_FRANGE] >> rw[] >> first_x_assum match_mp_tac >> PROVE_TAC[])

(* DRESTRICT stuff *)

val DRESTRICT_SUBMAP_gen = store_thm(
"DRESTRICT_SUBMAP_gen",
``f SUBMAP g ==> DRESTRICT f P SUBMAP g``,
SRW_TAC[][SUBMAP_DEF,DRESTRICT_DEF])

val DRESTRICT_SUBSET_SUBMAP = store_thm(
"DRESTRICT_SUBSET_SUBMAP",
``s1 SUBSET s2 ==> DRESTRICT f s1 SUBMAP DRESTRICT f s2``,
SRW_TAC[][SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF])

val DRESTRICTED_FUNION = store_thm(
"DRESTRICTED_FUNION",
``!f1 f2 s. DRESTRICT (FUNION f1 f2) s = FUNION (DRESTRICT f1 s) (DRESTRICT f2 (s DIFF FDOM f1))``,
rw[GSYM fmap_EQ_THM,DRESTRICT_DEF,FUNION_DEF] >> rw[] >>
rw[EXTENSION] >> PROVE_TAC[])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) SUBSET FRANGE fm``,
SRW_TAC[][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] THEN
SRW_TAC[][] THEN PROVE_TAC[])

val DRESTRICT_FDOM = store_thm(
"DRESTRICT_FDOM",
``!f. DRESTRICT f (FDOM f) = f``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF])

val DRESTRICT_SUBSET = store_thm("DRESTRICT_SUBSET",
  ``!f1 f2 s t.
    (DRESTRICT f1 s = DRESTRICT f2 s) /\ t SUBSET s ==>
    (DRESTRICT f1 t = DRESTRICT f2 t)``,
  rw[DRESTRICT_EQ_DRESTRICT]
    >- metis_tac[DRESTRICT_SUBSET_SUBMAP,SUBMAP_TRANS]
    >- metis_tac[DRESTRICT_SUBSET_SUBMAP,SUBMAP_TRANS] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,EXTENSION] >>
  metis_tac[])

val f_o_f_FUPDATE_compose = store_thm("f_o_f_FUPDATE_compose",
  ``!f1 f2 k x v. x NOTIN FDOM f1 /\ x NOTIN FRANGE f2 ==>
    (f1 |+ (x,v) f_o_f f2 |+ (k,x) = (f1 f_o_f f2) |+ (k,v))``,
  rw[GSYM fmap_EQ_THM,f_o_f_DEF,FAPPLY_FUPDATE_THM] >>
  simp[] >> rw[] >> fs[] >> rw[EXTENSION] >>
  fs[IN_FRANGE] >> rw[]
  >- PROVE_TAC[]
  >- PROVE_TAC[] >>
  qmatch_assum_rename_tac`y <> k` >>
  `y IN FDOM (f1 f_o_f f2)` by rw[f_o_f_DEF] >>
  rw[f_o_f_DEF])

val fmap_rel_trans = store_thm("fmap_rel_trans",
  ``(!x y z. R x y /\ R y z ==> R x z) ==>
    !x y z. fmap_rel R x y /\ fmap_rel R y z ==>
              fmap_rel R x z``,
  SRW_TAC[][fmap_rel_def] THEN METIS_TAC[])

val fmap_rel_sym = store_thm("fmap_rel_sym",
  ``(!x y. R x y ==> R y x) ==>
    !x y. fmap_rel R x y ==> fmap_rel R y x``,
  SRW_TAC[][fmap_rel_def])

val fmap_eq_flookup = Q.store_thm ("fmap_eq_flookup",
`!m1 m2. (m1 = m2) = !k. FLOOKUP m1 k = FLOOKUP m2 k`,
 rw [FLOOKUP_DEF, GSYM fmap_EQ_THM] >>
 eq_tac >>
 rw [EXTENSION]
 >- metis_tac [NOT_SOME_NONE]
 >- (Cases_on `x NOTIN FDOM m2` >>
     fs []
     >- metis_tac [NOT_SOME_NONE]
     >- metis_tac [SOME_11]));

val fupdate_list_map = Q.store_thm ("fupdate_list_map",
`!l f x y.
  x IN FDOM (FEMPTY |++ l)
   ==>
     ((FEMPTY |++ MAP (\(a,b). (a, f b)) l) ' x = f ((FEMPTY |++ l) ' x))`,
     rpt gen_tac >>
     Q.ISPECL_THEN[`FST`,`f o SND`,`l`,`FEMPTY:'a|->'c`]mp_tac(GSYM FOLDL_FUPDATE_LIST) >>
     simp[LAMBDA_PROD] >>
     disch_then kall_tac >>
     qid_spec_tac`l` >>
     ho_match_mp_tac SNOC_INDUCT >>
     simp[FUPDATE_LIST_THM] >>
     simp[FOLDL_SNOC,FORALL_PROD,FAPPLY_FUPDATE_THM,FDOM_FUPDATE_LIST,MAP_SNOC,FUPDATE_LIST_SNOC] >>
     rw[] >> rw[])

val fdom_fupdate_list2 = Q.store_thm ("fdom_fupdate_list2",
`!kvl fm. FDOM (fm |++ kvl) = (FDOM fm DIFF set (MAP FST kvl)) UNION set (MAP FST kvl)`,
rw [FDOM_FUPDATE_LIST, EXTENSION] >>
metis_tac []);

val flookup_thm = Q.store_thm ("flookup_thm",
`!f x v. ((FLOOKUP f x = NONE) = (x NOTIN FDOM f)) /\
         ((FLOOKUP f x = SOME v) = (x IN FDOM f /\ (f ' x = v)))`,
rw [FLOOKUP_DEF]);

val fmap_inverse_def = Define `
fmap_inverse m1 m2 =
  !k. k IN FDOM m1 ==> ?v. (FLOOKUP m1 k = SOME v) /\ (FLOOKUP m2 v = SOME k)`;

val fupdate_list_foldr = Q.store_thm ("fupdate_list_foldr",
`!m l. FOLDR (\(k,v) env. env |+ (k,v)) m l = m |++ REVERSE l`,
 Induct_on `l` >>
 rw [FUPDATE_LIST] >>
 PairCases_on `h` >>
 rw [FOLDL_APPEND]);

val fupdate_list_foldl = Q.store_thm ("fupdate_list_foldl",
`!m l. FOLDL (\env (k,v). env |+ (k,v)) m l = m |++ l`,
 Induct_on `l` >>
 rw [FUPDATE_LIST] >>
 PairCases_on `h` >>
 rw []);

val fmap_to_list = Q.store_thm ("fmap_to_list",
`!m. ?l. ALL_DISTINCT (MAP FST l) /\ (m = FEMPTY |++ l)`,
ho_match_mp_tac fmap_INDUCT >>
rw [FUPDATE_LIST_THM] >|
[qexists_tac `[]` >>
     rw [FUPDATE_LIST_THM],
 qexists_tac `(x,y)::l` >>
     rw [FUPDATE_LIST_THM] >>
     fs [FDOM_FUPDATE_LIST] >>
     rw [FUPDATE_FUPDATE_LIST_COMMUTES] >>
     fs [LIST_TO_SET_MAP] >>
     metis_tac [FST]]);

val disjoint_drestrict = Q.store_thm ("disjoint_drestrict",
`!s m. DISJOINT s (FDOM m) ==> (DRESTRICT m (COMPL s) = m)`,
 rw [fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
 Cases_on `k NOTIN s` >>
 rw [] >>
 fs [DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
 metis_tac []);

val drestrict_iter_list = Q.store_thm ("drestrict_iter_list",
`!m l. FOLDR (\k m. m \\ k) m l = DRESTRICT m (COMPL (set l))`,
 Induct_on `l` >>
 rw [DRESTRICT_UNIV, DRESTRICT_DOMSUB] >>
 match_mp_tac (PROVE [] ``(y = y') ==> (f x y = f x y')``) >>
 rw [EXTENSION] >>
 metis_tac []);

val fevery_funion = Q.store_thm ("fevery_funion",
`!P m1 m2. FEVERY P m1 /\ FEVERY P m2 ==> FEVERY P (FUNION m1 m2)`,
 rw [FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs []);

 (* Sorting stuff *)

val FUPDATE_LIST_ALL_DISTINCT_PERM = store_thm("FUPDATE_LIST_ALL_DISTINCT_PERM",
  ``!ls ls' fm. ALL_DISTINCT (MAP FST ls) /\ PERM ls ls' ==> (fm |++ ls = fm |++ ls')``,
  Induct >> rw[] >>
  fs[PERM_CONS_EQ_APPEND] >>
  rw[FUPDATE_LIST_THM] >>
  PairCases_on`h` >> fs[] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `(fm |++ (M ++ N)) |+ (h0,h1)` >>
  conj_tac >- metis_tac[ALL_DISTINCT_PERM,PERM_MAP] >>
  rw[FUPDATE_LIST_APPEND] >>
  `h0 NOTIN set (MAP FST N)` by metis_tac[PERM_MEM_EQ,MEM_MAP,MEM_APPEND] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  rw[FUPDATE_LIST_THM]);


end
(* end CakeML lemmas *)

(*---------------------------------------------------------------------------*)
(* Add fmap type to the TypeBase. Notice that we treat keys as being of size *)
(* zero, and make sure to add one to the size of each mapped value. This     *)
(* ought to handle the case where the map points to something of size 0:     *)
(* deleting it from the map will then make the map smaller.                  *)
(*---------------------------------------------------------------------------*)

val _ = adjoin_to_theory
  {sig_ps = NONE,
   struct_ps = SOME (fn pps =>
    let fun pp_line s = (PP.add_string pps s; PP.add_newline pps)
    in
     app pp_line
     ["val _ = ",
      " TypeBase.write",
      " [TypeBasePure.mk_nondatatype_info",
      "  (mk_type(\"fmap\",[alpha,beta]),",
      "    {nchotomy = SOME fmap_CASES,",
      "     induction = SOME fmap_INDUCT,",
      "     size = SOME(Parse.Term`\\(ksize:'a->num) (vsize:'b->num). fmap_size (\\k:'a. 0) (\\v. 1 + vsize v)`,",
      "                 fmap_size_def),",
      "     encode=NONE})];\n"
      ] end)};


(* ----------------------------------------------------------------------
    to close...
   ---------------------------------------------------------------------- *)

val _ = export_theory();
