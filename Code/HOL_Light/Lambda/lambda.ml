(* ========================================================================= *)
(*  Lambda Calculus.                                                         *)
(*  Terms of Syntactic Lambda Calculus defined in "dblambda.ml" are here     *)
(*  identified using beta-eta relation.                                      *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2005 2006 2017, 2020                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  LC relation                                                              *)
(* ------------------------------------------------------------------------- *)

let LC_REL = new_definition
  `LC_REL = DBLAMBDA_EQV (\x y. DBLAMBDA_BETA x y \/ DBLAMBDA_ETA x y)`;;

make_overloadable "===" `:A->A->bool`;;
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
   MATCH_MP_TAC DBLAMBDA_CONG_INDUCT THEN ASM_MESON_TAC[]);;

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
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DBLAMBDA_CONG_REINDEX THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[DBLAMBDA_BETA_REINDEX; DBLAMBDA_ETA_REINDEX]);;

let LC_REL_SUBST = prove
 (`!x y f. x === y ==> SUBST f x === SUBST f y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LC_REL; DBLAMBDA_EQV] THEN
  DISCH_TAC THEN MATCH_MP_TAC RSTC_MAP THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DBLAMBDA_CONG_SUBST THEN
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

(* ------------------------------------------------------------------------- *)
(*  LC lambda calculus                                                       *)
(* ------------------------------------------------------------------------- *)

let LC_TYBIJ = define_quotient_type "lc" ("MK_LC","DEST_LC") `LC_REL`;;

let LC_PROJ = new_definition
  `LC_PROJ n = MK_LC (LC_REL n)`;;

let LC_LIFT = new_definition
  `LC_LIFT y = (@x. LC_PROJ x = y)`;;

let LC_PROJ_REL = prove
 (`!x y. LC_PROJ x = LC_PROJ y <=> x === y`,
  REPEAT GEN_TAC THEN TRANS_TAC EQ_TRANS `LC_REL x = LC_REL y` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[LC_PROJ] THEN MESON_TAC[fst LC_TYBIJ; snd LC_TYBIJ];
   MESON_TAC[FUN_EQ_THM; LC_REL_REFL; LC_REL_TRANS; LC_REL_SYM]]);;

let LC_PROJ_SURJ = prove
 (`!y. ?x. LC_PROJ x = y`,
  REWRITE_TAC[LC_PROJ] THEN MESON_TAC[fst LC_TYBIJ; snd LC_TYBIJ]);;

let LC_PROJ_LIFT = prove
 (`!y. LC_PROJ (LC_LIFT y) = y`,
  REWRITE_TAC[LC_LIFT; LC_PROJ] THEN MESON_TAC[fst LC_TYBIJ; snd LC_TYBIJ]);;

let LC_LIFT_PROJ = prove
 (`!x. LC_LIFT (LC_PROJ x) === x`,
  REWRITE_TAC[LC_LIFT; LC_PROJ_REL] THEN MESON_TAC[SELECT_AX; LC_REL_REFL]);;

let FORALL_LC_THM = prove
 (`!P. (!x. P x) <=> (!x. P (LC_PROJ x))`,
  MESON_TAC[LC_PROJ_SURJ]);;

let FORALL_LC_FUN_THM = prove
 (`!P. (!f:num->lc. P f) <=> (!f. P (LC_PROJ o f))`,
  SUBGOAL_THEN `!f:num->lc. f = LC_PROJ o (LC_LIFT o f)`
    (fun th -> MESON_TAC[th]) THEN
  REWRITE_TAC[o_THM; LC_PROJ_LIFT; FUN_EQ_THM]);;

let lc_lift_function s th =
 let th1,th2 = lift_function (snd LC_TYBIJ) (LC_REL_REFL,LC_REL_TRANS) s th in
 (th1, REWRITE_RULE [GSYM LC_PROJ] (GSYM th2));;

let LC_ABS_DEF, LC_ABS = lc_lift_function "LC_ABS" LC_REL_ABS;;

let LC_APP_DEF, LC_APP = lc_lift_function "LC_APP" LC_REL_APP;;

let LC_REF_DEF = new_definition `LC_REF = LC_PROJ o REF`;;

let LC_REF = prove
 (`!i. LC_REF i = LC_PROJ (REF i)`,
  REWRITE_TAC[LC_REF_DEF; o_THM]);;

let LC_REINDEX_DEF = new_definition
  `!f x. LC_REINDEX f x = LC_PROJ (REINDEX f (LC_LIFT x))`;;

let LC_REINDEX = prove
 (`!f x. LC_REINDEX f (LC_PROJ x) = LC_PROJ (REINDEX f x)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[LC_REINDEX_DEF; LC_PROJ_REL] THEN
  MATCH_MP_TAC LC_REL_REINDEX THEN REWRITE_TAC[LC_LIFT_PROJ]);;

let LC_DERIV_DEF = new_definition
  `!f i. LC_DERIV f i = LC_PROJ (DERIV (LC_LIFT o f) i)`;;

let LC_DERIV = prove
 (`(!f. LC_DERIV f 0 = LC_REF 0) /\
   (!f i. LC_DERIV f (SUC i) = LC_REINDEX SUC (f i))`,
  CONJ_TAC THEN
  REWRITE_TAC[FORALL_LC_FUN_THM; LC_DERIV_DEF; DERIV; LC_REF] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LC_REINDEX; o_THM; LC_PROJ_REL] THEN
  MATCH_MP_TAC LC_REL_REINDEX THEN REWRITE_TAC[LC_LIFT_PROJ]);;

(*
let LC_SLIDEI_PROJ_o = prove
 (`!f. LC_SLIDE (LC_PROJ o f) = LC_PROJ o SLIDEI k f`,
  REWRITE_TAC[FORALL_LC_FUN_THM; FUN_EQ_THM; LC_SLIDEI; LC_REF; LC_SHIFTI;
              SLIDEI; o_THM; IF_DISTRIB]);;
*)

let LC_SUBST_DEF = new_definition
  `LC_SUBST f x = LC_PROJ (SUBST (LC_LIFT o f) (LC_LIFT x))`;;

let LC_SUBST_FUN_EXTENS = prove
 (`!f g x. (!n. f n = g n) ==> LC_SUBST f x = LC_SUBST g x`,
  REWRITE_TAC[GSYM FUN_EQ_THM] THEN MESON_TAC[]);;

let LC_SUBST_PROJ = prove
 (`!f x. LC_SUBST (LC_PROJ o f) (LC_PROJ x) = LC_PROJ (SUBST f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LC_SUBST_DEF; LC_PROJ_REL] THEN
  TRANS_TAC LC_REL_TRANS `SUBST f (LC_LIFT (LC_PROJ x))` THEN
  SIMP_TAC[LC_REL_SUBST; LC_REL_SUBST_EXTENS; LC_LIFT_PROJ; o_THM]);;

let LC_SUBST = prove
 (`(!f i. LC_SUBST f (LC_REF i) = f i) /\
   (!f x y. LC_SUBST f (LC_APP x y) =
            LC_APP (LC_SUBST f x) (LC_SUBST f y)) /\
   (!f x. LC_SUBST f (LC_ABS x) =
          LC_ABS (LC_SUBST (LC_DERIV f) x))`,
  REWRITE_TAC[FORALL_LC_FUN_THM; FORALL_LC_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[LC_REF; LC_APP; LC_ABS; LC_SUBST_PROJ; SUBST; o_THM] THEN
  SUBGOAL_THEN `!f. LC_DERIV (LC_PROJ o f) = LC_PROJ o DERIV f`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[FORALL_LC_FUN_THM; FUN_EQ_THM] THEN GEN_TAC THEN
   NUM_CASES_TAC THEN REWRITE_TAC[LC_DERIV; DERIV; o_THM; LC_REF; LC_REINDEX];
   REWRITE_TAC[LC_SUBST_PROJ; LC_ABS]]);;

let LC_APP0_DEF, LC_APP0 = lc_lift_function "LC_APP0" LC_REL_APP0;;

(* ------------------------------------------------------------------------- *)
(*  Monadic properties of LC_SUBST.                                          *)
(* ------------------------------------------------------------------------- *)

let LC_SUBST_LUNIT = prove
 (`!x. LC_SUBST LC_REF x = x`,
  REWRITE_TAC[FORALL_LC_THM; LC_REF_DEF; LC_SUBST_PROJ; SUBST_REF]);;

let LC_SUBST_RUNIT = prove
 (`!f i. LC_SUBST f (LC_REF i) = f i`,
  REWRITE_TAC[FORALL_LC_FUN_THM; LC_REF; LC_SUBST_PROJ; SUBST; o_THM]);;

let LC_SUBST_SUBST = prove
 (`!f g x. LC_SUBST f (LC_SUBST g x) = LC_SUBST (LC_SUBST f o g) x`,
  REWRITE_TAC[FORALL_LC_FUN_THM; FORALL_LC_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_SUBST_PROJ; SUBST_SUBST] THEN
  REWRITE_TAC[GSYM LC_SUBST_PROJ] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; LC_SUBST_PROJ]);;

(* ------------------------------------------------------------------------- *)
(*  APP0 and ABS are inverse each other.                                     *)
(* ------------------------------------------------------------------------- *)

let LC_ABS_APP0 = prove
 (`!x. LC_ABS (LC_APP0 x) = x`,
  REWRITE_TAC[FORALL_LC_THM; LC_APP0; LC_ABS; LC_PROJ_REL; LC_REL_ABS_APP0]);;

let LC_APP0_ABS = prove
 (`!x. LC_APP0 (LC_ABS x) = x`,
  REWRITE_TAC[FORALL_LC_THM; LC_APP0; LC_ABS; LC_PROJ_REL; LC_REL_APP0_ABS]);;

(* ------------------------------------------------------------------------- *)
(*  How to express LC_APP in terms of LC_APP0.                               *)
(* ------------------------------------------------------------------------- *)

let LC_APP_APP0 = prove
 (`!x y. LC_APP x y =
         LC_SUBST (\n. if n = 0 then y else LC_REF (PRE n)) (LC_APP0 x)`,
  REWRITE_TAC[FORALL_LC_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_APP; LC_REF; LC_APP0; IF_DISTRIB] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[LC_SUBST_PROJ; APP0; SUBST; SUBST_REINDEX] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC[SUBST_REF_EQ; o_THM; NOT_SUC; PRE]);;
