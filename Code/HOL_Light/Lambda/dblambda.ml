(* ========================================================================= *)
(*  Initial semantics based on De Brujin encoding                            *)
(*  with dbmonads and their modules.                                         *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2005 2006 2017, 2020                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let FORALL_NUM_THM = prove
 (`!P. (!i. P i) <=> P 0 /\ (!i. P (SUC i))`,
  METIS_TAC[cases "num"]);;

(* ------------------------------------------------------------------------- *)
(* Handy tactics for cases analysis on inductive datatypes.                  *)
(* ------------------------------------------------------------------------- *)

let GEN_THEN (vtac:term->tactic) : tactic =
  fun (asl,w) as gl ->
    let x,bod = try dest_forall w with Failure _ ->
                  failwith "GEN_THEN: Not universally quantified" in
    let avoids = itlist (union o thm_frees o snd) asl (frees w) in
    let x' = mk_primed_var avoids x in
    (X_GEN_TAC x' THEN vtac  x') gl;;

let CASES_TAC (tm:term) : tactic =
  let ty = fst(dest_type(type_of tm)) in
  STRUCT_CASES_TAC (ISPEC tm (cases ty));;

let CASES_GEN_TAC : tactic = GEN_THEN CASES_TAC;;

(* ------------------------------------------------------------------------- *)
(* Type for lambda terms using de Bruijn notation.                           *)
(* ------------------------------------------------------------------------- *)

let dblambda_INDUCT, dblambda_RECURSION = define_type
  "dblambda = REF num
            | APP dblambda dblambda
            | ABS dblambda";;

(* ------------------------------------------------------------------------- *)
(* Handy tactics for induction and case analysis.                            *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_INDUCT_TAC =
  MATCH_MP_TAC dblambda_INDUCT THEN CONJ_TAC THENL
  [GEN_TAC; CONJ_TAC THEN GEN_TAC THENL
   [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC); DISCH_TAC]];;

(* 
let dblambda_CASES = MESON[dblambda_INDUCT]
  `!P. (!a. P (REF a)) /\ (!a0 a1. P (APP a0 a1)) /\ (!a. P (ABS a))
       ==> (!x. P x)`;;

let DBLAMBDA_CASES_TAC =
  MATCH_MP_TAC dblambda_INDUCT THEN CONJ_TAC THENL
  [GEN_TAC; CONJ_TAC THEN GEN_TAC THENL
   [GEN_TAC; ALL_TAC]];;
*)

(* ------------------------------------------------------------------------- *)
(* Free references.                                                          *)
(* ------------------------------------------------------------------------- *)

let FREES_RULES,FREES_INDUCT,FREES_CASES = new_inductive_set
  `(!i. i IN FREES (REF i)) /\
   (!x y i. i IN FREES x ==> i IN FREES (APP x y)) /\
   (!x y i. i IN FREES y ==> i IN FREES (APP x y)) /\
   (!x i. SUC i IN FREES x ==> i IN FREES (ABS x))`;;

let FREES_INVERSION = prove
 (`(!i j. j IN FREES (REF i) <=> j = i) /\
   (!x y i. i IN FREES (APP x y) <=> i IN FREES x \/ i IN FREES y) /\
   (!x i. i IN FREES (ABS x) <=> SUC i IN FREES x)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [FREES_CASES] THEN
  REWRITE_TAC[distinctness "dblambda"; injectivity "dblambda"] THEN
  MESON_TAC[]);;

let FREES_CLAUSES = prove
 (`(!i. FREES (REF i) = {i}) /\
   (!x y. FREES (APP x y) = FREES x UNION FREES y) /\
   (!x. FREES (ABS x) = {i | SUC i IN FREES x})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FREES_INVERSION] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Slide.                                                                    *)
(* ------------------------------------------------------------------------- *)

let SLIDE = new_recursive_definition num_RECURSION
  `(!f. SLIDE f 0 = 0) /\
   (!f i. SLIDE f (SUC i) = SUC (f i))`;;

let SLIDE_I = prove
 (`SLIDE I = I`,
  REWRITE_TAC[FUN_EQ_THM] THEN CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; I_THM]);;

let SLIDE_SLIDE = prove
 (`!f g i. SLIDE f (SLIDE g i) = SLIDE (f o g) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; o_THM]);;

let SLIDE_INJ = prove
 (`!f i j. (!k l. f k = f l ==> k = l) ==> (SLIDE f i = SLIDE f j <=> i = j)`,
  GEN_TAC THEN CASES_GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[SLIDE; NOT_SUC; SUC_INJ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reindexing.                                                               *)
(* ------------------------------------------------------------------------- *)

let REINDEX = new_recursive_definition dblambda_RECURSION
  `(!f i. REINDEX f (REF i) = REF (f i)) /\
   (!f x y. REINDEX f (APP x y) = APP (REINDEX f x) (REINDEX f y)) /\
   (!f x. REINDEX f (ABS x) = ABS (REINDEX (SLIDE f) x))`;;

let REINDEX_I = prove
 (`!x. REINDEX I x = x`,
  DBLAMBDA_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REINDEX; injectivity "dblambda"; SLIDE_I; I_THM]);;

let REINDEX_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> f i = g i) ==> REINDEX f x = REINDEX g x`,
  DBLAMBDA_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[FREES_INVERSION; REINDEX] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[injectivity "dblambda"] THEN ASM_SIMP_TAC[] THENL
  [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; SUC_INJ] THEN ASM_SIMP_TAC[]);;

let REINDEX_EXTENS_EQ = prove
 (`!x f g. REINDEX f x = REINDEX g x <=> (!i. i IN FREES x ==> f i = g i)`,
  SUBGOAL_THEN
    `!x f g i. REINDEX f x = REINDEX g x /\ i IN FREES x ==> f i = g i`
    (fun th -> MESON_TAC[th; REINDEX_EXTENS]) THEN
  DBLAMBDA_INDUCT_TAC THEN
  REWRITE_TAC[REINDEX; injectivity "dblambda"; FREES_INVERSION] THEN
  SIMP_TAC[] THENL
  [ASM_MESON_TAC[]; REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN `SLIDE f (SUC i) = SLIDE g (SUC i)` MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
   REWRITE_TAC[SLIDE; SUC_INJ]]);;

let REINDEX_ID = prove
 (`!x f. REINDEX f x = x <=> (!i. i IN FREES x ==> f i = i)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REINDEX_I] THEN
  REWRITE_TAC[REINDEX_EXTENS_EQ; I_THM]);;

let REINDEX_REINDEX = prove
 (`!x f g. REINDEX g (REINDEX f x) = REINDEX (g o f) x`,
  DBLAMBDA_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[REINDEX; o_THM; injectivity "dblambda";
                  REINDEX_EXTENS_EQ; SLIDE_SLIDE]);;

let REINDEX_INJ = prove
 (`!x y f. (!i j. f i = f j ==> i = j)
           ==> (REINDEX f x = REINDEX f y <=> x = y)`,
  DBLAMBDA_INDUCT_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[REINDEX; distinctness "dblambda"] THEN
  REWRITE_TAC[injectivity "dblambda"] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[SLIDE_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Derivation.                                                               *)
(* ------------------------------------------------------------------------- *)

let DERIV = new_recursive_definition num_RECURSION
  `(!f. DERIV f 0 = REF 0) /\
   (!f i. DERIV f (SUC i) = REINDEX SUC (f i))`;;

let DERIV_REF = prove
 (`DERIV REF = REF`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN REWRITE_TAC[DERIV; REINDEX]);;

let DERIV_EXTENS = prove
 (`!f g i. DERIV f i = DERIV g i <=> i = 0 \/ f (PRE i) = g (PRE i)`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[DERIV; NOT_SUC; PRE] THEN SIMP_TAC[REINDEX_INJ; SUC_INJ]);;

let DERIV_SLIDE = prove
 (`!f g i. DERIV g (SLIDE f i) = DERIV (g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[DERIV; SLIDE; o_THM]);;

let DERIV_O_SUC = prove
 (`!f. DERIV f o SUC = REINDEX SUC o f`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; DERIV]);;

(* ------------------------------------------------------------------------- *)
(* Parallel substitution (higher-order style).                               *)
(* ------------------------------------------------------------------------- *)

let SUBST = new_recursive_definition dblambda_RECURSION
  `(!f i. SUBST f (REF i) = f i) /\
   (!f x y. SUBST f (APP x y) = APP (SUBST f x) (SUBST f y)) /\
   (!f x. SUBST f (ABS x) = ABS (SUBST (DERIV f) x))`;;

let SUBST_REF = prove
 (`!x. SUBST REF x = x`,
  DBLAMBDA_INDUCT_TAC THEN ASM_REWRITE_TAC[SUBST; DERIV_REF]);;

let SUBST_EXTENS = prove
 (`!x f g. SUBST f x = SUBST g x <=> (!i. i IN FREES x ==> f i = g i)`,
  DBLAMBDA_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUBST; FREES_INVERSION; DERIV_EXTENS;
                  injectivity "dblambda"; FORALL_UNWIND_THM2] THENL
  [MESON_TAC[]; REPEAT GEN_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_NUM_THM] THEN
  REWRITE_TAC[PRE; NOT_SUC]);;

let SUBST_REF_EQ = prove
 (`!x f. SUBST f x = x <=> (!i. i IN FREES x ==> f i = REF i)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `SUBST f x = SUBST REF x` THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBST_REF]; REWRITE_TAC[SUBST_EXTENS]]);;

let SUBST_REINDEX = prove
 (`!x f g. SUBST g (REINDEX f x) = SUBST (g o f) x`,
  DBLAMBDA_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[SUBST; REINDEX; o_THM; injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST_EXTENS; o_THM; DERIV_SLIDE]);;

let REINDEX_SLIDE = prove
 (`!g f i. REINDEX (SLIDE g) (DERIV f i) = DERIV (REINDEX g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN REWRITE_TAC[DERIV; REINDEX] THEN
  REWRITE_TAC[SLIDE; REINDEX_REINDEX; REINDEX_EXTENS_EQ; o_THM]);;

let REINDEX_SUBST = prove
 (`!x f g. REINDEX g (SUBST f x) = SUBST (REINDEX g o f) x`,
  DBLAMBDA_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[SUBST; REINDEX; o_THM; injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST_EXTENS; o_THM; REINDEX_SLIDE]);;

let SUBST_DERIV = prove
 (`!f g i. SUBST (DERIV g) (DERIV f i) = DERIV (SUBST g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[DERIV; SUBST; SUBST_REINDEX; REINDEX_SUBST;
              SUBST_EXTENS; o_THM]);;

let SUBST_SUBST = prove
 (`!x f g. SUBST g (SUBST f x) = SUBST (SUBST g o f) x`,
  DBLAMBDA_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[SUBST; o_THM; injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST_EXTENS; o_THM; SUBST_DERIV]);;

let REINDEX_EQ_SUBST = prove
 (`!f. REINDEX f = SUBST (REF o f)`,
  SUBGOAL_THEN `!x f. REINDEX f x = SUBST (REF o f) x`
    (fun th -> REWRITE_TAC[th; FUN_EQ_THM]) THEN
  DBLAMBDA_INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[REINDEX; SUBST; o_THM; injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST_EXTENS] THEN CASES_GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; DERIV; SLIDE; REINDEX]);;

(* ------------------------------------------------------------------------- *)
(* Classical definition of linear substitution.                              *)
(* ------------------------------------------------------------------------- *)

let SHIFTI = new_recursive_definition dblambda_RECURSION
  `(!k n i. SHIFTI k n (REF i) = REF (if i < k then i else n + i)) /\
   (!k n x y. SHIFTI k n (APP x y) = APP (SHIFTI k n x) (SHIFTI k n y)) /\
   (!k n x. SHIFTI k n (ABS x) = ABS (SHIFTI (SUC k) n x))`;;

let SUBSTI1 = new_recursive_definition dblambda_RECURSION
  `(!k w i. SUBSTI1 k w (REF i) = if i = k then SHIFTI 0 k w
                                  else if i < k then REF i
                                  else REF (i-1)) /\
   (!k w t u. SUBSTI1 k w (APP t u) = APP (SUBSTI1 k w t) (SUBSTI1 k w u)) /\
   (!k w t. SUBSTI1 k w (ABS t) = ABS (SUBSTI1 (k+1) w t))`;;

let SUBST1 = new_definition
  `SUBST1 u t = SUBSTI1 0 u t`;;

(* ------------------------------------------------------------------------- *)
(* Link between linear and parallel substitution.                            *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;

let ITER_SLIDE = prove
 (`!n k i. ITER k SLIDE ((+) n) i = if i < k then i else n + i`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
  [REWRITE_TAC[LT]; CASES_GEN_TAC] THENL
  [REWRITE_TAC[SLIDE; LT_0; ITER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_SUC; SLIDE] THEN ARITH_TAC);;

let SHIFTI_EQ_REINDEX = prove
 (`!n t k. SHIFTI k n t = REINDEX (ITER k SLIDE ((+) n)) t`,
  GEN_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SHIFTI; REINDEX; injectivity "dblambda"] THENL
  [REWRITE_TAC[ITER_SLIDE]; GEN_TAC] THEN
  REWRITE_TAC[REINDEX_EXTENS_EQ; ITER]);;

let ITER_DERIV = prove
 (`!k i. ITER k DERIV f i =
         if i < k then REF i else REINDEX ((+) k) (f (i - k))`,
  INDUCT_TAC THEN REWRITE_TAC[ITER] THEN GEN_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC[REINDEX_ID; LT; SUB_0] THEN ARITH_TAC;
   CASES_TAC `i:num`] THEN
  ASM_REWRITE_TAC[DERIV; LT_0; LT_SUC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REINDEX; REINDEX_REINDEX] THEN
  REWRITE_TAC[SUB_SUC; REINDEX_EXTENS_EQ; o_THM; ADD]);;

let SUBSTI1_EQ_SUBST = prove
 (`!u t i. SUBSTI1 i u t =
           SUBST (ITER i DERIV (\i. if i = 0 then u else REF (i - 1))) t`,
  GEN_TAC THEN DBLAMBDA_INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[SUBST; SUBSTI1; injectivity "dblambda";
                  SUBST_EXTENS; ITER; GSYM ADD1] THEN
  REWRITE_TAC[ITER_DERIV] THEN COND_CASES_TAC THENL
  [POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC[LT_REFL; SUB_REFL; SHIFTI_EQ_REINDEX; ITER_POINTLESS; I_THM];
   ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REINDEX; injectivity "dblambda"] THEN
  ASM_ARITH_TAC);;

let PUSHENV = new_recursive_definition num_RECURSION
  `(!u:A f. PUSHENV u f 0 = u) /\
   (!u f i. PUSHENV u f (SUC i) = f i)`;;

let PUSHENV_SLIDE = prove
 (`!f g u:A i. PUSHENV u f (SLIDE g i) = PUSHENV u (f o g) i`,
  REPEAT GEN_TAC THEN CASES_TAC `i:num` THEN
  REWRITE_TAC[PUSHENV; SLIDE; o_THM]);;

let SUBST_PUSHENV_LEMMA = prove
 (`!f x i. SUBST (PUSHENV (SUBST f y) REF) (DERIV f i) =
           SUBST f (PUSHENV y REF i)`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[PUSHENV; DERIV; SUBST; SUBST_REINDEX] THEN
  REWRITE_TAC[SUBST_REF_EQ; o_THM; PUSHENV]);;

let SUBST1_EQ_SUBST = prove
 (`!t u. SUBST1 u t = SUBST (PUSHENV u REF) t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBST1; SUBSTI1_EQ_SUBST; SUBST_EXTENS; ITER] THEN
  GEN_TAC THEN DISCH_TAC THEN CASES_TAC `i:num` THEN
  REWRITE_TAC[PUSHENV; NOT_SUC; injectivity "dblambda"] THEN ARITH_TAC);;

let SUBST1_SUBST1 = prove
 (`!t u w. SUBST1 w (SUBST1 u t) = SUBST1 (SUBST1 w u) (SUBSTI1 1 w t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBST1_EQ_SUBST; SUBSTI1_EQ_SUBST; SUBST_SUBST;
              SUBST_EXTENS; ITER_BINARY; o_THM] THEN
  CASES_GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[DERIV; SUBST; PUSHENV; SUBST_REINDEX] THEN
  CASES_TAC `n:num` THEN REWRITE_TAC[PUSHENV; NOT_SUC; SUBST; o_THM] THENL
  [MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC[SUBST_REF_EQ; o_THM; PUSHENV];
   REWRITE_TAC[injectivity "dblambda"] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Structural relation relation between lambda terms.                        *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_REL_RULES, DBLAMBDA_REL_INDUCT, DBLAMBDA_REL_CASES =
  new_inductive_definition
  `(!x y. R x y ==> DBLAMBDA_REL R x y) /\
   (!x y. DBLAMBDA_REL R x y ==> DBLAMBDA_REL R (ABS x) (ABS y)) /\
   (!x y z. DBLAMBDA_REL R x y ==> DBLAMBDA_REL R (APP x z) (APP y z)) /\
   (!x y z. DBLAMBDA_REL R x y ==> DBLAMBDA_REL R (APP z x) (APP z y))`;;

let [DBLAMBDA_REL_INC; DBLAMBDA_REL_ABS;
     DBLAMBDA_REL_RATOR; DBLAMBDA_REL_RAND] =
  CONJUNCTS (REWRITE_RULE[FORALL_AND_THM] DBLAMBDA_REL_RULES);;

let DBLAMBDA_REL_REINDEX = prove
 (`!R x y f. (!u v g. R u v ==> R (REINDEX g u) (REINDEX g v)) /\
             DBLAMBDA_REL R x y
             ==> DBLAMBDA_REL R (REINDEX f x) (REINDEX f y)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `!x y. DBLAMBDA_REL R x y
           ==> !f. DBLAMBDA_REL R (REINDEX f x) (REINDEX f y)`
    (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC DBLAMBDA_REL_INDUCT THEN REWRITE_TAC[REINDEX] THEN
  ASM_SIMP_TAC[DBLAMBDA_REL_RULES]);;

let DBLAMBDA_REL_SUBST = prove
 (`!R x y f. (!u v g. R u v ==> R (SUBST g u) (SUBST g v)) /\
             DBLAMBDA_REL R x y
             ==> DBLAMBDA_REL R (SUBST f x) (SUBST f y)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `!x y. DBLAMBDA_REL R x y
           ==> !f. DBLAMBDA_REL R (SUBST f x) (SUBST f y)`
    (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC DBLAMBDA_REL_INDUCT THEN REWRITE_TAC[SUBST] THEN
  ASM_SIMP_TAC[DBLAMBDA_REL_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Structural reduction relation between lambda terms.                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/rstc.ml";;

let DBLAMBDA_RED = new_definition
  `!R. DBLAMBDA_RED R = RTC (DBLAMBDA_REL R)`;;

let DBLAMBDA_RED_INC = prove
 (`!R x y. R x y ==> DBLAMBDA_RED R x y`,
  SIMP_TAC[DBLAMBDA_RED; RTC_INC; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_RED_REFL = prove
 (`!R x. DBLAMBDA_RED R x x`,
  REWRITE_TAC[DBLAMBDA_RED; RTC_REFL]);;

let DBLAMBDA_RED_REFL_IMP = MESON[DBLAMBDA_RED_REFL]
  `!R x y. x = y ==> DBLAMBDA_RED R x y`;;

let DBLAMBDA_RED_TRANS = prove
 (`!R x y z. DBLAMBDA_RED R x y /\ DBLAMBDA_RED R y z ==> DBLAMBDA_RED R x z`,
  REWRITE_TAC[DBLAMBDA_RED; RTC_TRANS]);;

let DBLAMBDA_RED_ABS = prove
 (`!R x y. DBLAMBDA_RED R x y ==> DBLAMBDA_RED R (ABS x) (ABS y)`,
  GEN_TAC THEN REWRITE_TAC[DBLAMBDA_RED] THEN MATCH_MP_TAC RTC_INDUCT THEN
  MESON_TAC[RTC_RULES; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_RED_APP_L = prove
 (`!R z x y. DBLAMBDA_RED R x y ==> DBLAMBDA_RED R (APP x z) (APP y z)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[DBLAMBDA_RED] THEN
  MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC[RTC_RULES; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_RED_APP_R = prove
 (`!R z x y. DBLAMBDA_RED R x y ==> DBLAMBDA_RED R (APP z x) (APP z y)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[DBLAMBDA_RED] THEN
  MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC[RTC_RULES; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_RED_APP =
  MESON[DBLAMBDA_RED_TRANS; DBLAMBDA_RED_APP_L; DBLAMBDA_RED_APP_R]
  `!R x1 x2 y1 y2. DBLAMBDA_RED R x1 y1 /\ DBLAMBDA_RED R x2 y2
                   ==> DBLAMBDA_RED R (APP x1 x2) (APP y1 y2)`;;

let DBLAMBDA_RED_RULES =
  MESON[DBLAMBDA_RED_INC; DBLAMBDA_RED_APP; DBLAMBDA_RED_ABS;
        DBLAMBDA_RED_REFL; DBLAMBDA_RED_TRANS]
  `!R. (!x y. R x y ==> DBLAMBDA_RED R x y) /\
       (!x y. DBLAMBDA_RED R x y ==> DBLAMBDA_RED R (ABS x) (ABS y)) /\
       (!x1 x2 y1 y2. DBLAMBDA_RED R x1 y1 /\ DBLAMBDA_RED R x2 y2
                      ==> DBLAMBDA_RED R (APP x1 x2) (APP y1 y2)) /\
       (!x. DBLAMBDA_RED R x x) /\
       (!x y z. DBLAMBDA_RED R x y /\ DBLAMBDA_RED R y z
                ==> DBLAMBDA_RED R x z)`;;

let DBLAMBDA_RED_CASES = prove
 (`!a0 a1.
      DBLAMBDA_RED R a0 a1 <=>
      R a0 a1 \/
      (?x1 y1 x2 y2.
         a0 = APP x1 x2 /\ a1 = APP y1 y2 /\
         DBLAMBDA_RED R x1 y1 /\ DBLAMBDA_RED R x2 y2) \/
      (?x y. a0 = ABS x /\ a1 = ABS y /\ DBLAMBDA_RED R x y) \/
      (?y. DBLAMBDA_RED R a0 y /\ DBLAMBDA_RED R y a1)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [REWRITE_TAC[DBLAMBDA_RED] THEN MESON_TAC[RTC_CASES; RTC_RULES];
   MESON_TAC[DBLAMBDA_RED_RULES]]);;

let DBLAMBDA_RED_INDUCT = prove
 (`!RR R. (!x y. R x y ==> RR x y) /\
          (!x1 y1 x2 y2.
             RR x1 y1 /\ RR x2 y2 ==> RR (APP x1 x2) (APP y1 y2)) /\
          (!x y. RR x y ==> RR (ABS x) (ABS y)) /\
          (!x. RR x x) /\
          (!x y z. RR x y /\ RR y z ==> RR x z)
          ==> (!a0 a1. DBLAMBDA_RED R a0 a1 ==> RR a0 a1)`,
  GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[DBLAMBDA_RED] THEN
  MATCH_MP_TAC RTC_INDUCT THEN CONJ_TAC THEN
  TRY (MATCH_MP_TAC DBLAMBDA_REL_INDUCT) THEN ASM_MESON_TAC[]);;

let DBLAMBDA_RED_REINDEX = prove
 (`!R x y f. (!u v g. R u v ==> R (REINDEX g u) (REINDEX g v)) /\
             DBLAMBDA_RED R x y
             ==> DBLAMBDA_RED R (REINDEX f x) (REINDEX f y)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; DBLAMBDA_RED] THEN
  DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN
  ASM_MESON_TAC[RTC_RULES; DBLAMBDA_REL_REINDEX]);;

let DBLAMBDA_RED_SUBST = prove
 (`!R x y f. (!u v g. R u v ==> R (SUBST g u) (SUBST g v)) /\
             DBLAMBDA_RED R x y
             ==> DBLAMBDA_RED R (SUBST f x) (SUBST f y)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; DBLAMBDA_RED] THEN
  DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN
  ASM_MESON_TAC[RTC_RULES; DBLAMBDA_REL_SUBST]);;

(* ------------------------------------------------------------------------- *)
(* Structural equivalence relation between lambda terms.                     *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_EQV = new_definition
  `!R. DBLAMBDA_EQV R = RSTC (DBLAMBDA_REL R)`;;

let DBLAMBDA_EQV_INC = prove
 (`!R x y. R x y ==> DBLAMBDA_EQV R x y`,
  SIMP_TAC[DBLAMBDA_EQV; RSTC_INC; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_EQV_REFL = prove
 (`!R x. DBLAMBDA_EQV R x x`,
  REWRITE_TAC[DBLAMBDA_EQV; RSTC_REFL]);;

let DBLAMBDA_EQV_REFL_IMP = MESON[DBLAMBDA_EQV_REFL]
  `!R x y. x = y ==> DBLAMBDA_EQV R x y`;;

let DBLAMBDA_EQV_SYM = prove
 (`!R x y. DBLAMBDA_EQV R x y ==> DBLAMBDA_EQV R y x`,
  REWRITE_TAC[DBLAMBDA_EQV; RSTC_SYM]);;

let DBLAMBDA_EQV_TRANS = prove
 (`!R x y z. DBLAMBDA_EQV R x y /\ DBLAMBDA_EQV R y z ==> DBLAMBDA_EQV R x z`,
  REWRITE_TAC[DBLAMBDA_EQV; RSTC_TRANS]);;

let DBLAMBDA_EQV_ABS = prove
 (`!R x y. DBLAMBDA_EQV R x y ==> DBLAMBDA_EQV R (ABS x) (ABS y)`,
  GEN_TAC THEN REWRITE_TAC[DBLAMBDA_EQV] THEN MATCH_MP_TAC RSTC_INDUCT THEN
  MESON_TAC[RSTC_RULES; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_EQV_APP_L = prove
 (`!R z x y. DBLAMBDA_EQV R x y ==> DBLAMBDA_EQV R (APP x z) (APP y z)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[DBLAMBDA_EQV] THEN
  MATCH_MP_TAC RSTC_INDUCT THEN MESON_TAC[RSTC_RULES; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_EQV_APP_R = prove
 (`!R z x y. DBLAMBDA_EQV R x y ==> DBLAMBDA_EQV R (APP z x) (APP z y)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[DBLAMBDA_EQV] THEN
  MATCH_MP_TAC RSTC_INDUCT THEN MESON_TAC[RSTC_RULES; DBLAMBDA_REL_RULES]);;

let DBLAMBDA_EQV_APP =
  MESON[DBLAMBDA_EQV_TRANS; DBLAMBDA_EQV_APP_L; DBLAMBDA_EQV_APP_R]
  `!R x1 x2 y1 y2. DBLAMBDA_EQV R x1 y1 /\ DBLAMBDA_EQV R x2 y2
                   ==> DBLAMBDA_EQV R (APP x1 x2) (APP y1 y2)`;;

let DBLAMBDA_EQV_RULES =
  MESON[DBLAMBDA_EQV_INC; DBLAMBDA_EQV_APP; DBLAMBDA_EQV_ABS;
        DBLAMBDA_EQV_REFL; DBLAMBDA_EQV_SYM; DBLAMBDA_EQV_TRANS]
  `!R. (!x y. R x y ==> DBLAMBDA_EQV R x y) /\
       (!x y. DBLAMBDA_EQV R x y ==> DBLAMBDA_EQV R (ABS x) (ABS y)) /\
       (!x1 x2 y1 y2. DBLAMBDA_EQV R x1 y1 /\ DBLAMBDA_EQV R x2 y2
                      ==> DBLAMBDA_EQV R (APP x1 x2) (APP y1 y2)) /\
       (!x. DBLAMBDA_EQV R x x) /\
       (!x y. DBLAMBDA_EQV R x y ==> DBLAMBDA_EQV R y x) /\
       (!x y z. DBLAMBDA_EQV R x y /\ DBLAMBDA_EQV R y z
                ==> DBLAMBDA_EQV R x z)`;;

let DBLAMBDA_EQV_CASES = prove
 (`!a0 a1.
      DBLAMBDA_EQV R a0 a1 <=>
      R a0 a1 \/
      (?x1 y1 x2 y2.
         a0 = APP x1 x2 /\ a1 = APP y1 y2 /\
         DBLAMBDA_EQV R x1 y1 /\ DBLAMBDA_EQV R x2 y2) \/
      (?x y. a0 = ABS x /\ a1 = ABS y /\ DBLAMBDA_EQV R x y) \/
      DBLAMBDA_EQV R a1 a0 \/
      (?y. DBLAMBDA_EQV R a0 y /\ DBLAMBDA_EQV R y a1)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [REWRITE_TAC[DBLAMBDA_EQV] THEN MESON_TAC[RSTC_CASES; RSTC_RULES];
   MESON_TAC[DBLAMBDA_EQV_RULES]]);;

let DBLAMBDA_EQV_INDUCT = prove
 (`!RR R. (!x y. R x y ==> RR x y) /\
          (!x1 y1 x2 y2.
             RR x1 y1 /\ RR x2 y2 ==> RR (APP x1 x2) (APP y1 y2)) /\
          (!x y. RR x y ==> RR (ABS x) (ABS y)) /\
          (!x. RR x x) /\
          (!x y. RR x y ==> RR y x) /\
          (!x y z. RR x y /\ RR y z ==> RR x z)
          ==> (!a0 a1. DBLAMBDA_EQV R a0 a1 ==> RR a0 a1)`,
  GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[DBLAMBDA_EQV] THEN
  MATCH_MP_TAC RSTC_INDUCT THEN CONJ_TAC THEN
  TRY (MATCH_MP_TAC DBLAMBDA_REL_INDUCT) THEN ASM_MESON_TAC[]);;

let DBLAMBDA_EQV_REINDEX = prove
 (`!R x y f. (!u v g. R u v ==> R (REINDEX g u) (REINDEX g v)) /\
             DBLAMBDA_EQV R x y
             ==> DBLAMBDA_EQV R (REINDEX f x) (REINDEX f y)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; DBLAMBDA_EQV] THEN
  DISCH_TAC THEN MATCH_MP_TAC RSTC_INDUCT THEN
  ASM_MESON_TAC[RSTC_RULES; DBLAMBDA_REL_REINDEX]);;

let DBLAMBDA_EQV_SUBST = prove
 (`!R x y f. (!u v g. R u v ==> R (SUBST g u) (SUBST g v)) /\
             DBLAMBDA_EQV R x y
             ==> DBLAMBDA_EQV R (SUBST f x) (SUBST f y)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; DBLAMBDA_EQV] THEN
  DISCH_TAC THEN MATCH_MP_TAC RSTC_INDUCT THEN
  ASM_MESON_TAC[RSTC_RULES; DBLAMBDA_REL_SUBST]);;
