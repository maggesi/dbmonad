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
