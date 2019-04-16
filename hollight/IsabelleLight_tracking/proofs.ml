g `(!x:A. P x ==> Q x ) ==> ~(?x. P x /\ ~(Q x))`;;
e DISCH_TAC;;
e (DISCH_THEN (CHOOSE_THEN ASSUME_TAC));;
e (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC));;
e (FIRST_X_ASSUM (ANTE_RES_THEN MP_TAC));;
e (ASM_REWRITE_TAC[]);;

prove (`(!x:A. P x ==> Q x ) ==> ~(?x. P x /\ ~(Q x))`, 
DISCH_TAC THEN DISCH_THEN (CHOOSE_THEN ASSUME_TAC)
THEN FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) 
THEN FIRST_X_ASSUM (ANTE_RES_THEN MP_TAC)
THEN ASM_REWRITE_TAC[]);;


top_thm();;
val it : thm = |- (!x. P x ==> Q x) ==> ~(?x. P x /\ ~Q x)


g `2<=n /\ n<=2 ==> f(2,2) + n < f(n,n) + 7`;;
e (DISCH_TAC);;
e (simp[LE_ANTISYM;EQ_SYM_EQ]);;
e ARITH_TAC;;

b();;

g `!p q. p * p = 2 * q * q ==> q= 0`;;
e (MATCH_MP_TAC num_WF);;
e (REWRITE_TAC[RIGHT_IMP_FORALL_THM]);;
e (REPEAT STRIP_TAC);;
e (FIRST_ASSUM(MP_TAC o AP_TERM `EVEN`));;
e (REWRITE_TAC[EVEN_MULT; ARITH]);;
e (REWRITE_TAC[EVEN_EXISTS]);;
e (DISCH_THEN( X_CHOOSE_THEN `m:num` SUBST_ALL_TAC));;
e (FIRST_ASSUM(MP_TAC o SPECL [`q:num`;`m:num`]));;
e (POP_ASSUM MP_TAC);;
e (CONV_TAC SOS_RULE);;





























#use "Examples/multiplicative.ml";;


gm `~(m=0) ===> ~(n=0) ===> ~(m * n = 0)`;;
e (REPEAT (rule impI));;
e (simp[MULT_EQ_0]);;
let MULT_NEQ_0 = top_thm();;


g `!f g. (!n. ~(n = 0) ==> g(n) = f(n)) /\ multiplicative f ==> multiplicative g`;;
e (REPEAT allI);;
e (simp[MULTIPLICATIVE; ARITH_EQ]);;
e (rule impI);;
e (REPEAT(erule conjE));;
e (REPEAT allI);;
e (rule impI);;
e (REPEAT(erule conjE));;
e (erule_tac [`a`,`m`] allE);;
e (erule_tac [`a`,`n`] allE);;
e (REPEAT(drule mp));;
e (REPEAT(rule conjI) THEN assumption);;
e (meson[MULT_EQ_0]);;
let MULTIPLICATIVE_IGNOREZERO2 = top_thm();;


e (frule_tac [(`m`,`m`);(`n`,`n`)] MULT_NEQ_0);;
e assumption;;
e (erule_tac [`a`,`(m:num) * n`] allE);;
e (simp[]);;


g `!f g. (!n. ~(n = 0) ==> g(n) = f(n)) /\ multiplicative f ==> multiplicative g`;;
e (REPEAT GEN_TAC);;
e (SIMP_TAC[MULTIPLICATIVE; ARITH_EQ]);;
e (REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)));;
e (REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC));;
e (DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th));;
e (ASM_REWRITE_TAC[]);;
e (ASM_MESON_TAC[MULT_EQ_0]);;


let MULTIPLICATIVE_IGNOREZERO = prove
 (`!f g. (!n. ~(n = 0) ==> g(n) = f(n)) /\ multiplicative f
         ==> multiplicative g`,
  REPEAT GEN_TAC THEN SIMP_TAC[MULTIPLICATIVE; ARITH_EQ] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MULT_EQ_0]);;

g `(P==>Q/\R)==>((P==>Q) /\ (P==>R))`;;
e DISCH_TAC;;
e CONJ_TAC;;
e DISCH_TAC;;
e (UNDISCH_TAC `P ==> Q /\ R`);;
e ANTS_TAC;;
e (FIRST_ASSUM ACCEPT_TAC);;
e (DISCH_THEN (ACCEPT_TAC o CONJUNCT1));;

g `(P==>Q/\R)==>((P==>Q) /\ (P==>R))`;;
e (rule impI);;
e (rule conjI);;
e (rule impI);;
e (drule mp);;
e assumption;;
e (erule conjE);;
e assumption;;
e (rule impI);;
e (drule mp);;
e assumption;;
e (erule conjE);;
e assumption;;
