(* ========================================================================= *)
(*  Syntactic Lambda Calculus "a la" de Bruijn.                              *)
(*  Here syntactic means: "terms are not identified by beta-eta relation".   *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2005 2006 2017, 2020                *)
(* ========================================================================= *)

needs "Library/iter.ml";;

make_overloadable "===" `:A->A->bool`;;

(* ------------------------------------------------------------------------- *)
(*  DBLAMBDA_BETA                                                            *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_BETA_RULES, DBLAMBDA_BETA_INDUCT, DBLAMBDA_BETA_CASES =
  new_inductive_definition
  `!x y. DBLAMBDA_BETA (APP (ABS x) y) (SUBST (PUSHENV y REF) x)`;;

let DBLAMBDA_BETA_INVERSION = prove
 (`!x y z. DBLAMBDA_BETA (APP (ABS x) y) z <=> z = SUBST (PUSHENV y REF) x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [DBLAMBDA_BETA_CASES] THEN
  REWRITE_TAC[injectivity "dblambda"] THEN MESON_TAC[]);;

let DBLAMBDA_BETA_SUBST = prove
 (`!f x y. DBLAMBDA_BETA x y ==> DBLAMBDA_BETA (SUBST f x) (SUBST f y)`,
  GEN_TAC THEN MATCH_MP_TAC DBLAMBDA_BETA_INDUCT THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBST] THEN
  REWRITE_TAC[DBLAMBDA_BETA_INVERSION; SUBST_SUBST; SUBST_EXTENS; o_THM] THEN
  NUM_CASES_TAC THEN REWRITE_TAC[DERIV; SUBST; PUSHENV] THEN
  DISCH_THEN (K ALL_TAC) THEN REWRITE_TAC[SUBST_REINDEX] THEN
  MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC[SUBST_REF_EQ; o_THM; PUSHENV]);;

let DBLAMBDA_BETA_REINDEX = prove
 (`!f x y. DBLAMBDA_BETA x y ==> DBLAMBDA_BETA (REINDEX f x) (REINDEX f y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REINDEX_EQ_SUBST] THEN
  ASM_MESON_TAC[DBLAMBDA_BETA_SUBST]);;

(* ------------------------------------------------------------------------- *)
(*  DBLAMBDA_ETA                                                             *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_ETA_RULES, DBLAMBDA_ETA_INDUCT, DBLAMBDA_ETA_CASES =
  new_inductive_definition
  `!x. DBLAMBDA_ETA (ABS (APP (REINDEX SUC x) (REF 0))) x`;;

let DBLAMBDA_ETA_SUBST = prove
 (`!f x y. DBLAMBDA_ETA x y ==> DBLAMBDA_ETA (SUBST f x) (SUBST f y)`,
  GEN_TAC THEN MATCH_MP_TAC DBLAMBDA_ETA_INDUCT THEN GEN_TAC THEN
  REWRITE_TAC[SUBST; DERIV; SUBST_REINDEX; DBLAMBDA_ETA_CASES; REINDEX_SUBST;
              SUBST_EXTENS; o_THM; injectivity "dblambda"] THEN
  NUM_CASES_TAC THEN REWRITE_TAC[DERIV]);;

let DBLAMBDA_ETA_REINDEX = prove
 (`!f x y. DBLAMBDA_ETA x y ==> DBLAMBDA_ETA (REINDEX f x) (REINDEX f y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REINDEX_EQ_SUBST] THEN
  ASM_MESON_TAC[DBLAMBDA_ETA_SUBST]);;

(* ------------------------------------------------------------------------- *)
(* Beta-eta reduction binary relation.                                       *)
(* ------------------------------------------------------------------------- *)

let REDREL = new_definition
  `REDREL = DBLAMBDA_RED (\x y. DBLAMBDA_BETA x y \/ DBLAMBDA_ETA x y)`;;

let REDREL_BETA = prove
 (`!x y. DBLAMBDA_BETA x y ==> REDREL x y`,
  SIMP_TAC[REDREL; DBLAMBDA_RED_INC]);;

let REDREL_ETA = prove
 (`!x y. DBLAMBDA_ETA x y ==> REDREL x y`,
  SIMP_TAC[REDREL; DBLAMBDA_RED_INC]);;

let REDREL_ABS = prove
 (`!x y. REDREL x y ==> REDREL (ABS x) (ABS y)`,
  SIMP_TAC[REDREL; DBLAMBDA_RED_ABS]);;

let REDREL_APP = prove
 (`!x1 y1 x2 y2. REDREL x1 y1 /\ REDREL x2 y2
                 ==> REDREL (APP x1 x2) (APP y1 y2)`,
  SIMP_TAC[REDREL; DBLAMBDA_RED_APP]);;

let REDREL_REFL = prove
 (`!x. REDREL x x`,
  REWRITE_TAC[REDREL; DBLAMBDA_RED_REFL]);;

let REDREL_TRANS = prove
 (`!x y z. REDREL x y /\ REDREL y z ==> REDREL x z`,
  REWRITE_TAC[REDREL; DBLAMBDA_RED_TRANS]);;

let REDREL_RULES = prove
 (`(!x y. DBLAMBDA_BETA x y ==> REDREL x y) /\
   (!x y. DBLAMBDA_ETA x y ==> REDREL x y) /\
   (!x1 y1 x2 y2. REDREL x1 y1 /\ REDREL x2 y2
                  ==> REDREL (APP x1 x2) (APP y1 y2)) /\
   (!x y. REDREL x y ==> REDREL (ABS x) (ABS y)) /\
   (!x. REDREL x x) /\
   (!x y z. REDREL x y /\ REDREL y z ==> REDREL x z)`,
  REWRITE_TAC[REDREL_REFL; REDREL_BETA; REDREL_ETA;
              REDREL_ABS; REDREL_APP] THEN
  MESON_TAC[REDREL_TRANS]);;

let REDREL_INDUCT = prove
 (`!R. (!x y. DBLAMBDA_BETA x y ==> R x y) /\
       (!x y. DBLAMBDA_ETA x y ==> R x y) /\
       (!x1 y1 x2 y2. R x1 y1 /\ R x2 y2 ==> R (APP x1 x2) (APP y1 y2)) /\
       (!x y. R x y ==> R (ABS x) (ABS y)) /\
       (!x. R x x) /\
       (!x y z. R x y /\ R y z ==> R x z)
       ==> (!a0 a1. REDREL a0 a1 ==> R a0 a1)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REDREL; DBLAMBDA_RED] THEN
  MATCH_MP_TAC RTC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DBLAMBDA_REL_INDUCT THEN ASM_MESON_TAC[]);;

let REDREL_CASES = prove
 (`!a0 a1.
     REDREL a0 a1 <=>
     DBLAMBDA_BETA a0 a1 \/
     DBLAMBDA_ETA a0 a1 \/
     (?x1 y1 x2 y2.
        a0 = APP x1 x2 /\ a1 = APP y1 y2 /\ REDREL x1 y1 /\ REDREL x2 y2) \/
     (?x y. a0 = ABS x /\ a1 = ABS y /\ REDREL x y) \/
     (?y. REDREL a0 y /\ REDREL y a1)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [REWRITE_TAC[REDREL] THEN GEN_REWRITE_TAC LAND_CONV [DBLAMBDA_RED_CASES] THEN
   REWRITE_TAC[] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[injectivity "dblambda"] THEN ASM_MESON_TAC[];
   ASM_MESON_TAC[REDREL_RULES]]);;

let REDREL_REINDEX_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> f i = g i)
           ==> REDREL (REINDEX f x)  (REINDEX g x)`,
  DBLAMBDA_INDUCT_TAC THEN REWRITE_TAC[REINDEX; FREES_INVERSION] THENL
  [MESON_TAC[REDREL_REFL];
   ASM_MESON_TAC[REDREL_APP];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC REDREL_ABS THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN NUM_CASES_TAC THEN
   ASM_REWRITE_TAC[SLIDE; SUC_INJ]]);;

let REDREL_REINDEX = prove
 (`!x y f. REDREL x y ==> REDREL (REINDEX f x) (REINDEX f y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REDREL; DBLAMBDA_RED] THEN
  DISCH_TAC THEN MATCH_MP_TAC RTC_MAP THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DBLAMBDA_REL_REINDEX THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[DBLAMBDA_BETA_REINDEX; DBLAMBDA_ETA_REINDEX]);;

let REDREL_SUBST = prove
 (`!x y f. REDREL x y ==> REDREL (SUBST f x) (SUBST f y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REDREL; DBLAMBDA_RED] THEN
  DISCH_TAC THEN MATCH_MP_TAC RTC_MAP THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DBLAMBDA_REL_SUBST THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[DBLAMBDA_BETA_SUBST; DBLAMBDA_ETA_SUBST]);;

let REDREL_REINDEX_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> f i = g i)
           ==> REDREL (REINDEX f x) (REINDEX g x)`,
  DBLAMBDA_INDUCT_TAC THEN
  REWRITE_TAC[REINDEX; FREES_INVERSION; FORALL_UNWIND_THM2] THEN
  ASM_SIMP_TAC[REDREL_RULES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REDREL_ABS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  NUM_CASES_TAC THEN REWRITE_TAC[SLIDE] THEN ASM_MESON_TAC[]);;

let REDREL_SUBST_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> REDREL (f i) (g i))
           ==> REDREL (SUBST f x) (SUBST g x)`,
  DBLAMBDA_INDUCT_TAC THEN
  REWRITE_TAC[SUBST; FREES_INVERSION; FORALL_UNWIND_THM2] THEN
  ASM_SIMP_TAC[REDREL_APP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REDREL_ABS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  NUM_CASES_TAC THEN REWRITE_TAC[DERIV; REDREL_REFL] THEN
  ASM_MESON_TAC[REDREL_REINDEX]);;

(* ------------------------------------------------------------------------- *)
(*  LC relation                                                              *)
(* ------------------------------------------------------------------------- *)

let LC_REL = new_definition
  `LC_REL = DBLAMBDA_EQV (\x y. DBLAMBDA_BETA x y \/ DBLAMBDA_ETA x y)`;;

overload_interface ("===",`LC_REL:dblambda->dblambda->bool`);;

let LC_REL_BETA = prove
 (`!x y. DBLAMBDA_BETA x y ==> x === y`,
  SIMP_TAC[LC_REL; DBLAMBDA_EQV_INC]);;

let LC_REL_ETA = prove
 (`!x y. DBLAMBDA_ETA x y ==> x === y`,
  SIMP_TAC[LC_REL; DBLAMBDA_EQV_INC]);;

let LC_REL_ABS = prove
 (`!x y. x === y ==> ABS x === ABS y`,
  SIMP_TAC[LC_REL; DBLAMBDA_EQV_ABS]);;

let LC_REL_APP = prove
 (`!x1 y1 x2 y2. x1 === y1 /\ x2 === y2 ==> APP x1 x2 === APP y1 y2`,
  SIMP_TAC[LC_REL; DBLAMBDA_EQV_APP]);;

let LC_REL_REFL = prove
 (`!x. x === x`,
  REWRITE_TAC[LC_REL; DBLAMBDA_EQV_REFL]);;

let LC_REL_SYM = prove
 (`!x y. x === y ==> y === x`,
  REWRITE_TAC[LC_REL; DBLAMBDA_EQV_SYM]);;

let LC_REL_TRANS = prove
 (`!x y z. x === y /\ y === z ==> x === z`,
  REWRITE_TAC[LC_REL; DBLAMBDA_EQV_TRANS]);;

let LC_REL_RULES = prove
 (`(!x y. DBLAMBDA_BETA x y ==> x === y) /\
   (!x y. DBLAMBDA_ETA x y ==> x === y) /\
   (!x1 y1 x2 y2. x1 === y1 /\ x2 === y2 ==> APP x1 x2 === APP y1 y2) /\
   (!x y. x === y ==> ABS x === ABS y) /\
   (!x. x === x) /\
   (!x y. x === y ==> y === x) /\
   (!x y z. x === y /\ y === z ==> x === z)`,
  REWRITE_TAC[LC_REL_REFL; LC_REL_SYM; LC_REL_BETA;
              LC_REL_ETA; LC_REL_ABS; LC_REL_APP] THEN
  MESON_TAC[LC_REL_TRANS]);;

let LC_REL_INDUCT = prove
 (`!R. (!x y. DBLAMBDA_BETA x y ==> R x y) /\
       (!x y. DBLAMBDA_ETA x y ==> R x y) /\
       (!x1 y1 x2 y2. R x1 y1 /\ R x2 y2 ==> R (APP x1 x2) (APP y1 y2)) /\
       (!x y. R x y ==> R (ABS x) (ABS y)) /\
       (!x y. R x y ==> R y x) /\
       (!x y z. R x y /\ R y z ==> R x z)
       ==> (!a0 a1. a0 === a1 ==> R a0 a1)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LC_REL; DBLAMBDA_EQV] THEN
  SUBGOAL_THEN `!x:dblambda. R x x` ASSUME_TAC THENL
  [ASM_MESON_TAC[DBLAMBDA_ETA_RULES];
   MATCH_MP_TAC RSTC_INDUCT] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC DBLAMBDA_REL_INDUCT THEN ASM_MESON_TAC[]);;

let LC_REL_CASES = prove
 (`!a0 a1.
     a0 === a1 <=>
     DBLAMBDA_BETA a0 a1 \/
     DBLAMBDA_ETA a0 a1 \/
     (?x1 y1 x2 y2.
        a0 = APP x1 x2 /\ a1 = APP y1 y2 /\ x1 === y1 /\ x2 === y2) \/
     (?x y. a0 = ABS x /\ a1 = ABS y /\ x === y) \/
     a1 === a0 \/
     (?y. a0 === y /\ y === a1)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [REWRITE_TAC[LC_REL] THEN MESON_TAC[DBLAMBDA_EQV_CASES];
   ASM_MESON_TAC[LC_REL_RULES]]);;

let LC_REL_REINDEX_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> f i = g i) ==> REINDEX f x === REINDEX g x`,
  DBLAMBDA_INDUCT_TAC THEN REWRITE_TAC[REINDEX; FREES_INVERSION] THENL
  [MESON_TAC[LC_REL_REFL];
   ASM_MESON_TAC[LC_REL_APP];
   REPEAT STRIP_TAC THEN MATCH_MP_TAC LC_REL_ABS THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN NUM_CASES_TAC THEN
   ASM_REWRITE_TAC[SLIDE; SUC_INJ]]);;

let LC_REL_REINDEX = prove
 (`!x y f. x === y ==> REINDEX f x === REINDEX f y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LC_REL; DBLAMBDA_EQV] THEN
  DISCH_TAC THEN MATCH_MP_TAC RSTC_MAP THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DBLAMBDA_REL_REINDEX THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[DBLAMBDA_BETA_REINDEX; DBLAMBDA_ETA_REINDEX]);;

let LC_REL_SUBST = prove
 (`!x y f. x === y ==> SUBST f x === SUBST f y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LC_REL; DBLAMBDA_EQV] THEN
  DISCH_TAC THEN MATCH_MP_TAC RSTC_MAP THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DBLAMBDA_REL_SUBST THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[DBLAMBDA_BETA_SUBST; DBLAMBDA_ETA_SUBST]);;

let LC_REL_REINDEX_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> f i = g i) ==> REINDEX f x === REINDEX g x`,
  DBLAMBDA_INDUCT_TAC THEN
  REWRITE_TAC[REINDEX; FREES_INVERSION; FORALL_UNWIND_THM2] THEN
  ASM_SIMP_TAC[LC_REL_RULES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LC_REL_ABS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  NUM_CASES_TAC THEN REWRITE_TAC[SLIDE] THEN ASM_MESON_TAC[]);;

let LC_REL_SUBST_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> f i === g i) ==> SUBST f x === SUBST g x`,
  DBLAMBDA_INDUCT_TAC THEN
  REWRITE_TAC[SUBST; FREES_INVERSION; FORALL_UNWIND_THM2] THEN
  ASM_SIMP_TAC[LC_REL_APP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LC_REL_ABS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  NUM_CASES_TAC THEN REWRITE_TAC[DERIV; LC_REL_REFL] THEN
  ASM_MESON_TAC[LC_REL_REINDEX]);;

(* ------------------------------------------------------------------------- *)
(* APP0.                                                                     *)
(* ------------------------------------------------------------------------- *)

let APP0 = new_definition
  `APP0 x = APP (REINDEX SUC x) (REF 0)`;;

let APP_EQ_APP0 = prove
 (`!x y. APP x y = SUBST (\n. if n = 0 then y else REF (PRE n)) (APP0 x)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC[APP0; SUBST; SUBST_REINDEX; SUBST_REF_EQ;
              injectivity "dblambda"] THEN
  NUM_CASES_TAC THEN REWRITE_TAC[o_THM; PRE; NOT_SUC]);;

let APP0_SUBST = prove
 (`!f x. APP0 (SUBST f x) = SUBST (DERIV f) (APP0 x)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[APP0; SUBST; DERIV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REINDEX_SUBST; SUBST_REINDEX; SUBST_EXTENS; o_THM] THEN
  NUM_CASES_TAC THEN REWRITE_TAC[DERIV]);;

let DBLAMBDA_ETA_APP0 = prove
 (`!x y. DBLAMBDA_ETA x y <=> x = ABS (APP0 y)`,
  REWRITE_TAC[DBLAMBDA_ETA_CASES; APP0]);;

let LC_REL_APP0 = prove
 (`!x y. x === y ==> APP0 x === APP0 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[APP0] THEN
  ASM_SIMP_TAC[LC_REL_RULES; LC_REL_REINDEX]);;

let dblambda_INDUCT_ALT = prove
 (`!P. (!i. P (REF i)) /\
       (!x. P x ==> P (APP0 x)) /\
       (!x. P x ==> P (ABS x)) /\
       (!f x. (!i. P (f i)) /\ P x ==> P (SUBST f x))
       ==> (!x. P x)`,
  GEN_TAC THEN STRIP_TAC THEN DBLAMBDA_INDUCT_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[APP_EQ_APP0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN NUM_CASES_TAC THEN ASM_REWRITE_TAC[NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(*  A nice consequence of eta.                                               *)
(* ------------------------------------------------------------------------- *)

let LC_REL_ABS_APP0 = prove
 (`!x. ABS (APP0 x) === x`,
  SIMP_TAC[APP0; LC_REL_ETA; DBLAMBDA_ETA_RULES]);;

(* ------------------------------------------------------------------------- *)
(*  A nice consequence of beta.                                              *)
(* ------------------------------------------------------------------------- *)

let LC_REL_APP0_ABS = prove
 (`!x. APP0 (ABS x) === x`,
  GEN_TAC THEN REWRITE_TAC[APP0; REINDEX] THEN MATCH_MP_TAC LC_REL_BETA THEN
  REWRITE_TAC[DBLAMBDA_BETA_INVERSION] THEN MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC[SUBST_REINDEX] THEN REWRITE_TAC[SUBST_REF_EQ; o_THM] THEN
  REWRITE_TAC[PUSHENV_SLIDE] THEN NUM_CASES_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[PUSHENV; o_THM]);;

(* ------------------------------------------------------------------------- *)
(*  How to express APP in terms of APP0 (modulo LC_REL).                     *)
(* ------------------------------------------------------------------------- *)

let LC_REL_APP_APP0 = prove
 (`!x y. APP x y === SUBST1 y (APP0 x)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC LC_REL_TRANS `APP (ABS (APP (REINDEX SUC x) (REF 0))) y` THEN
  CONJ_TAC THENL [MESON_TAC[LC_REL_RULES; DBLAMBDA_ETA_RULES]; ALL_TAC] THEN
  REWRITE_TAC[APP0; SUBST1_EQ_SUBST; SUBST; PUSHENV; SUBST_REINDEX] THEN
  MATCH_MP_TAC LC_REL_APP THEN REWRITE_TAC[LC_REL_REFL] THEN
  MATCH_MP_TAC LC_REL_ETA THEN
  REWRITE_TAC[DBLAMBDA_ETA_CASES; injectivity "dblambda"] THEN
  SIMP_TAC[REINDEX_INJ; SUC_INJ] THEN MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC[SUBST_REF_EQ; o_THM; PUSHENV]);;
