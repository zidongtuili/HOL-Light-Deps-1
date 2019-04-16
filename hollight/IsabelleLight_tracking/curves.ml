new_type ("pt",0);;
new_type ("curve",0);;

new_constant ("incident",`:pt -> curve -> bool`);;
parse_as_infix ("incident", (22,"right"));;

parse_as_infix("isPartOf", (22,"right"));;
parse_as_infix("isEndPoint", (22,"right"));;
parse_as_infix("isInnerPoint", (22,"right"));;

let isPartOf_def = new_definition `(c1:curve) isPartOf (c2:curve) <=> !p:pt . p incident c1 ==> p incident c2`;;

let isEndPoint_def = new_definition `(p:pt) isEndPoint (c:curve) <=> p incident c /\ (!c1 c2. (c1 isPartOf c /\ c2 isPartOf c /\ p incident c1 /\ p incident c2) ==> (c1 isPartOf c2) \/ (c2 isPartOf c1))`;;

let isInnerPoint_def = new_definition `(p:pt) isInnerPoint (c:curve) <=> p incident c /\ ~(p isEndPoint c)`;;

let meetAt_def = new_definition `meetAt (c1:curve) (c2:curve) (p:pt) <=> p incident c1 /\ p incident c2 /\ (!q. q incident c1 /\ q incident c2 ==> q isEndPoint c1 /\ q isEndPoint c2)`;;

let isSumOf_def = new_definition `isSumOf (c:curve) (c1:curve) (c2:curve) <=> !q. q incident c <=> (q incident c1 \/ q incident c2)`;;

let isClosedCurve_def = new_definition `isClosedCurve (c:curve) <=> ~(?p. p isEndPoint c)`;;

let isOpenCurve_def = new_definition `isOpenCurve (c:curve) <=> ?p. p isEndPoint c`;;

let axiom_c1 = new_axiom `c' isPartOf c ===> ~(c' = c) ===> isOpenCurve c'`;;

let axiom_c2 = new_axiom `c1 isPartOf c ===> c2 isPartOf c ===> c3 isPartOf c ===> p isEndPoint c1 ===> p isEndPoint c2 ===> p isEndPoint c3 ===> c2 isPartOf c3 \/ c3 isPartOf c2 \/ c1 isPartOf c2 \/ c2 isPartOf c1 \/ c1 isPartOf c3 \/ c3 isPartOf c1`

let axiom_c3 = new_axiom `?p. p isInnerPoint c`;;

let axiom_c4 = new_axiom `p isInnerPoint c ===> ? c1 c2. meetAt c1 c2 p /\ isSumOf c c1 c2`;;

let axiom_c5 = new_axiom `p isEndPoint c ===> q isEndPoint c ===> r isEndPoint c ===> ( p = q \/ q = r \/ p = r)`;;

let axiom_c6 = new_axiom `p isEndPoint c ===> ?q. (q isEndPoint c /\ ~(p = q))`;;

let axiom_c7 = new_axiom `isClosedCurve c ===> meetAt c1 c2 p ===> isSumOf c c1 c2 ===> q isEndPoint c1 ===> meetAt c1 c2 q`;;

let axiom_c8 = new_axiom `(?p. meetAt c1 c2 p) ===> (?c. isSumOf c c1 c2)`;;

let axiom_c9 = new_axiom `(!p. p incident c = p incident c') ===> c = c'`;;

let isPartOf_refl = prove (`c isPartOf c`, REWRITE_TAC[isPartOf_def]);;

let isPartOf_trans = prove (`c1 isPartOf c2 ===> c2 isPartOf c3 ===> c1 isPartOf c3`, MIMP_TAC THEN SIMP_TAC[isPartOf_def]);;

let isPartOf_antisym = prove (`c1 isPartOf c2 ===> c2 isPartOf c1 ===> c1=c2`, MIMP_TAC THEN REWRITE_TAC[isPartOf_def] THEN
				(REPEAT (rule impI)) THEN (rule axiom_c9) THEN GEN_TAC THEN 
				(REPEAT (erule_tac [`a`,`p`] allE)) THEN (rule iffI) THEN (erule mp)
				THEN assumption);;

let corollary_2_6_part1 = prove (`c2 isPartOf c3 ===> meetAt c1 c2 p ===> meetAt c1 c3 p ===> 
				 isSumOf c c1 c2 ===> isSumOf c' c1 c3 ===> c isPartOf c'`,
				 MIMP_TAC THEN 
				   REPEAT (rule impI) THEN 
				   FULL_REWRITE_TAC[meetAt_def;isSumOf_def;isEndPoint_def;isPartOf_def] THEN 
				   GEN_TAC THEN 
				   (rule impI) THEN 
				   (erule disjE) THENL [ rule disjI1 ; rule disjI2 ] THENL [ assumption ; 
				   REPEAT (erule_tac [`a`,`p'`] allE) ] THEN (drule mp) THEN assumption);;

let corollary_2_6_part2 = prove (`c1 isPartOf c3 ===> c2 isPartOf c3 ===> meetAt c1 c2 p ===>
				 isSumOf c c1 c2 ===> c isPartOf c3`, 
				 MIMP_TAC THEN REPEAT (rule impI) THEN 
				   FULL_REWRITE_TAC[meetAt_def;isSumOf_def;isEndPoint_def;isPartOf_def] THEN 
				   GEN_TAC THEN (rule impI) THEN 
				   (REPEAT (erule_tac [`a`,`p'`] allE)) THEN
				   (erule disjE) THENL [ drule mp ; drule_tac [`p`,`p' incident c2`] mp ] THEN
				   assumption);;

let theorem_2_7_part1 = prove (`isOpenCurve c ===> ?p q. ~(p = q) /\ p isEndPoint c /\ q isEndPoint c`, 
			       MIMP_TAC THEN (rule impI) THEN REWRITE_ASM_TAC[isOpenCurve_def] THEN
				 (exE `x:pt`) THEN frule axiom_c6 THEN exE `y:pt` THEN erule conjE THEN
				 rule_tac [`a`,`x:pt`] exI THEN rule_tac [`a`,`y:pt`] exI THEN
				 REPEAT (rule conjI) THEN assumption);;


gm `isOpenCurve c ===> c' isPartOf c ===> isOpenCurve c'`;;
e (case_tac `(c:curve)=c'`);;
e (simp[]);;
e (erule axiom_c1);;
e (simp[]);;
let theorem_2_7_part2 = qed();;


gm `c1 isPartOf c2 ===> ~(?p. meetAt c1 c2 p)`;;
e (cut_tac [`c`,`c1`] axiom_c3);;
e (simp[meetAt_def;isInnerPoint_def;isPartOf_def]);;
e (meson[]);;
(*
e (exE `y:pt`);;
e (exE `x:pt`);;
e (REPEAT (erule conjE));;
e (REPEAT (erule_tac [`a`,`y`] allE));;
e (drule mp);;
e assumption;;
e (simp[]);;
*)
let corollary_2_9 = qed();;

gm `c' isPartOf c ===> p isEndPoint c ===> p incident c' ===> p isEndPoint c'`;;
e (simp[isEndPoint_def;isPartOf_def]);;
e (meson[]);; (* Can be solved with: e (ASM_MESON_TAC[isEndPoint_def;isPartOf_def]);; but at 778345! *)
let theorem_2_10 = qed();;

gm `(?c'. c' isPartOf c /\ p isInnerPoint c') ===> p isInnerPoint c`;;
e (simp[isInnerPoint_def;isEndPoint_def;isPartOf_def]);; 
e (ASM_MESON_TAC[]);;
let corollary_2_11 = qed();;


gm `c2 isPartOf c1 ===> p incident c2 ===> meetAt c1 c' p ===> meetAt c2 c' p`;;
e (simp[meetAt_def]);;
e allI;;
e (rule impI);;
e (REPEAT (erule conjE));;
e (erule_tac [`a`,`q`] allE);;
e (simp[isEndPoint_def;isPartOf_def]);;
let corollary_2_12 = qed();;


(* Big proof starts here *)

(* Simple lemmas: *)

gm `isSumOf c c1 c2 ===> c1 isPartOf c /\ c2 isPartOf c`;;
e (simp[isSumOf_def;isPartOf_def]);;
let isSumOf_imp_isPartOf = qed();;

gm `p isEndPoint c ===> p incident c`;;
e (simp[isEndPoint_def]);;
let isEndPoint_imp_incident = qed();;

gm `p isInnerPoint c ===> q isEndPoint c ===> ~(p = q)`;;
e (simp[isInnerPoint_def;isEndPoint_def]);;
e (meson[]);;
let ipt_ne_ept = qed();;

gm `p incident c' ===> c' isPartOf c ===> p incident c`;;
e (simp[isPartOf_def]);;
let isPartOf_imp_incident = qed();;

gm `meetAt c1 c2 p ===> q incident c1 ===> q incident c2 ===> q isEndPoint c1 /\ q isEndPoint c2`;;
e (simp[meetAt_def]);;
let meetAt_imp_isEndPoint = qed();;


(* Step 1: *)

(* This lemma is the first sentence of Step 1 of the proof. The assumption that a is not equal to b is implied in the pen-and-paper proof.*)

gm `isOpenCurve c ===> p isInnerPoint c ===> a isEndPoint c ===> b isEndPoint c ===> ~( a=b) ===> ?c3 c4. c3 isPartOf c /\ p isEndPoint c3 /\ a isEndPoint c3 /\ c4 isPartOf c /\ p isEndPoint c4 /\ b isEndPoint c4 /\ meetAt c3 c4 p /\ isSumOf c c3 c4`;;
e (frule axiom_c4);;
e (exE `c1:curve`);;
e (exE `c2:curve`);;
e (erule conjE);;
e (frule isSumOf_imp_isPartOf);;
e (erule conjE);;
e (simp[meetAt_def]);;
e (subgoal_tac `meetAt c1 c2 p`);;
e (simp[meetAt_def]);;
e (REPEAT (erule conjE));;
e (erule_tac [`a`,`p`] allE);;
e (simp[]);;
e (frule_tac [`p`,`a`] isEndPoint_imp_incident);;
e (frule_tac [`p`,`b`] isEndPoint_imp_incident);;
e (REPEAT (erule conjE));;
e (subgoal_tac `isSumOf c c1 c2`);;
e (assumption);;
e (simp[isSumOf_def]);;
e (subgoal_tac `isSumOf c c1 c2`);;
e (simp[isSumOf_def]);;
e (erule_tac [`a`,`a`] allE);;
e (erule_tac [`a`,`b`] allE);;
e (simp[]);;
e (erule disjE THEN erule disjE);;
e (frule_tac [(`p`,`a`);(`c'`,`c1`)] theorem_2_10);;
e (assumption);;
e (assumption);;
e (frule_tac [(`p`,`b`);(`c'`,`c1`)] theorem_2_10);;
e (assumption);;
e (assumption);;
e (drule_tac [(`p`,`p`);(`q`,`a`);(`r`,`b`);(`c`,`c1`)] axiom_c5);;
e (simp[]);;
e (simp[]);;
e (simp[]);;
e (erule disjE);;
e (drule_tac [(`p`,`p`);(`q`,`a`)] ipt_ne_ept);;
e assumption;;
e (meson[]);;
e (drule_tac [(`p`,`p`);(`q`,`b`)] ipt_ne_ept);;
e assumption;;
e (meson[]);;


theorem_2_10;; 


(* lemma c3c4_have_diff_ept: "\<lbrakk> isOpenCurve c ; a isEndPoint c ; b isEndPoint c ; p isInnerPoint c ; q isInnerPoint c ;
                                     c3 isPartOf c ; p isEndPoint c3 ; a isEndPoint c3 ;
                                     c4 isPartOf c ; p isEndPoint c4 ; b isEndPoint c4 ;
                                     p\<noteq>q ; a\<noteq>b \<rbrakk> \<Longrightarrow> \<not>(a incident c4)" *)

gm `isOpenCurve c ===> a isEndPoint c ===> b isEndPoint c ===> p isInnerPoint c ===> q isInnerPoint c ===> c3 isPartOf c ===> p isEndPoint c3 ===> a isEndPoint c3 ===> c4 isPartOf c ===> p isEndPoint c4 ===> b isEndPoint c4 ===> ~(p=q) ===> ~(a=b) ===> ~(a incident c4)`;;
e (drule_tac [(`c'`,`c4`);(`c`,`c`);(`p`,`a`)] theorem_2_10);;
e assumption;;
e assumption;;
e (drule_tac [(`p`,`p`);(`q`,`a`);(`r`,`b`);(`c`,`c4`)] axiom_c5);;
e assumption;;
e assumption;;
e (erule disjE);;
e (drule_tac [(`p`,`p`);(`q`,`a`);(`c`,`c`)] ipt_ne_ept);;
e assumption;;
e (erule_tac [`a`,`p=a`] notE);;
e assumption;;
e (erule disjE);;
e (erule_tac [`a`,`a=b`] notE);;
e assumption;;
e (drule_tac [(`p`,`p`);(`q`,`b`);(`c`,`c`)] ipt_ne_ept);;
e assumption;;
e (erule_tac [`a`,`p=b`] notE);;
e assumption;;
let c3c4_have_diff_ept = qed();;


