(* -*- holl -*- *)

(* ========================================================================= *)
(*  Lambda Calculus.                                                         *)
(*  Terms of Syntactic Lambda Calculus defined in "dbterm.ml" are here       *)
(*  identified using beta-eta relation.                                      *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2006                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  LC lambda calculus                                                       *)
(* ------------------------------------------------------------------------- *)

let LC_TYBIJ =
  define_quotient_type "lc" ("MK_LC","DEST_LC") `LC_REL`;;

let LC_PROJ = new_definition
  `LC_PROJ n = MK_LC (LC_REL n)`;;

let LC_LIFT = new_definition
  `LC_LIFT y = (@x. LC_PROJ x = y)`;;

let LC_PROJ_REL = prove
  (`!x y. LC_PROJ x = LC_PROJ y <=> x === y`,
   REPEAT GEN_TAC THEN TRANS_TAC `LC_REL x = LC_REL y` THENL
   [REWRITE_TAC [LC_PROJ] THEN MESON_TAC [fst LC_TYBIJ; snd LC_TYBIJ];
    MESON_TAC [FUN_EQ_THM; LC_REL_REFL; LC_REL_TRANS; LC_REL_SYM]]);;

let LC_PROJ_SURJ = prove
  (`!y. ?x. LC_PROJ x = y`,
   REWRITE_TAC [LC_PROJ] THEN
   MESON_TAC [fst LC_TYBIJ; snd LC_TYBIJ]);;

let LC_PROJ_LIFT = prove
  (`!y. LC_PROJ (LC_LIFT y) = y`,
   REWRITE_TAC [LC_LIFT; LC_PROJ] THEN
   MESON_TAC [fst LC_TYBIJ; snd LC_TYBIJ]);;

let LC_LIFT_PROJ = prove
  (`!x. LC_LIFT (LC_PROJ x) === x`,
   REWRITE_TAC [LC_LIFT; LC_PROJ_REL] THEN
   MESON_TAC [SELECT_AX; LC_REL_REFL]);;

let LC_THM_LIFT = prove
  (`!P. (!x. P x) <=> (!x. P (LC_PROJ x))`,
   MESON_TAC [LC_PROJ_SURJ]);;

let LC_SUBST_FUN_EXTENS = prove
  (`!f g x. (!n. f n = g n) ==> LC_SUBST f x = LC_SUBST g x`,
   REWRITE_TAC [GSYM FUN_EQ_THM] THEN MESON_TAC []);;

let LC_THM_FUN_LIFT = prove
  (`!P. (!f. P f) <=> (!f:num->dbterm. P (LC_PROJ o f))`,
    SUBGOAL_THEN `!f:num->lc. f = LC_PROJ o (LC_LIFT o f)`
    (fun th -> MESON_TAC [th]) THEN
    REWRITE_TAC [o_THM; LC_PROJ_LIFT; FUN_EQ_THM]);;

let lc_lift_function s th =
  let th1, th2 =
    lift_function (snd LC_TYBIJ) (LC_REL_REFL,LC_REL_TRANS) s th
  in
  (th1, REWRITE_RULE [GSYM LC_PROJ] (GSYM th2));;

let LC_ABS_DEF, LC_ABS = lc_lift_function "LC_ABS" LC_REL_ABS;;

let LC_APP_DEF, LC_APP = lc_lift_function "LC_APP" LC_REL_APP;;

let LC_REF_DEF = new_definition `LC_REF = LC_PROJ o REF`;;

let LC_REF = prove
  (`!i. LC_REF i = LC_PROJ (REF i)`,
   REWRITE_TAC [LC_REF_DEF; o_THM]);;

let LC_SHIFT_DEF = new_definition
  `!k n x. LC_SHIFT k n x = LC_PROJ (SHIFT k n (LC_LIFT x))`;;

let LC_SHIFT = prove
  (`!k n x. LC_SHIFT k n (LC_PROJ x) = LC_PROJ (SHIFT k n x)`,
   REWRITE_TAC [LC_SHIFT_DEF; LC_PROJ_REL; LC_REL_SHIFT; LC_LIFT_PROJ]);;

let LC_SHIFTF_DEF = new_definition
  `!k f i. LC_SHIFTF k f i = LC_PROJ (SHIFTF k (LC_LIFT o f) i)`;;

let LC_SHIFTF = prove
  (`!f i k. LC_SHIFTF k f i =
      (if i < k then LC_REF i else LC_SHIFT 0 k (f (i - k)))`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LC_SHIFTF_DEF; LC_SHIFT; SHIFTF; o_THM] THEN
   SPEC_TAC (`f (i - k):lc`,`x:lc`) THEN REWRITE_TAC [LC_THM_LIFT] THEN
   GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [LC_REF; LC_SHIFT] THEN
   REWRITE_TAC [LC_PROJ_REL; LC_REL_SHIFT; LC_LIFT_PROJ]);;

let LC_SHIFTF_PROJ_o = prove
  (`!f k. LC_SHIFTF k (LC_PROJ o f) = LC_PROJ o SHIFTF k f`,
   REWRITE_TAC [LC_THM_FUN_LIFT; FUN_EQ_THM; LC_SHIFTF; LC_REF; LC_SHIFT;
                SHIFTF; o_THM; IF_DISTRIB]);;

let LC_SUBST_DEF = new_definition
  `LC_SUBST f x = LC_PROJ (SUBST (LC_LIFT o f) (LC_LIFT x))`;;

let LC_SUBST_PROJ = prove
  (`!f x. LC_SUBST (LC_PROJ o f) (LC_PROJ x) = LC_PROJ (SUBST f x)`,
   REPEAT GEN_TAC THEN REWRITE_TAC [LC_SUBST_DEF; o_DEF; LC_PROJ_REL] THEN
   MESON_TAC [LC_REL_SUBST; LC_LIFT_PROJ]);;

let LC_SUBST = prove
  (`(!f i. LC_SUBST f (LC_REF i) = f i) /\
   (!f x y. LC_SUBST f (LC_APP x y) = LC_APP (LC_SUBST f x) (LC_SUBST f y)) /\
   (!f x. LC_SUBST f (LC_ABS x) = LC_ABS (LC_SUBST (LC_SHIFTF (SUC 0) f) x))`,
   REWRITE_TAC [LC_THM_FUN_LIFT; LC_THM_LIFT; LC_REF; LC_APP; LC_ABS;
                LC_SUBST_PROJ; LC_SHIFTF_PROJ_o; SUBST; o_THM]);;

let LC_APP0_DEF, LC_APP0 = lc_lift_function "LC_APP0" LC_REL_APP0;;

(* ------------------------------------------------------------------------- *)
(*  Operadic properties of LC_SUBST.                                         *)
(* ------------------------------------------------------------------------- *)

let LC_SUBST_LUNIT = prove
  (`!x. LC_SUBST LC_REF x = x`,
   REWRITE_TAC [LC_THM_LIFT; LC_REF_DEF; LC_SUBST_PROJ; SUBST_LUNIT]);;

let LC_SUBST_RUNIT = prove
  (`!f i. LC_SUBST f (LC_REF i) = f i`,
   REWRITE_TAC [LC_THM_FUN_LIFT; LC_REF; LC_SUBST_PROJ; SUBST; o_THM]);;

let LC_SUBST_ASSOC = prove
  (`!f g x. LC_SUBST f (LC_SUBST g x) = LC_SUBST (LC_SUBST f o g) x`,
   REWRITE_TAC [LC_THM_FUN_LIFT; LC_THM_LIFT; LC_SUBST_PROJ; SUBST_ASSOC] THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [GSYM LC_SUBST_PROJ] THEN
   MATCH_MP_TAC LC_SUBST_FUN_EXTENS THEN REWRITE_TAC [o_THM; LC_SUBST_PROJ]);;

(* ------------------------------------------------------------------------- *)
(*  APP0 and ABS are inverse each other.                                     *)
(* ------------------------------------------------------------------------- *)

let LC_ABS_APP0 = prove
  (`!x. LC_ABS (LC_APP0 x) = x`,
   REWRITE_TAC [LC_THM_LIFT; LC_APP0; LC_ABS; LC_PROJ_REL; LC_REL_ABS_APP0]);;

let LC_APP0_ABS = prove
  (`!x. LC_APP0 (LC_ABS x) = x`,
   REWRITE_TAC [LC_THM_LIFT; LC_APP0; LC_ABS; LC_PROJ_REL; LC_REL_APP0_ABS]);;

(* ------------------------------------------------------------------------- *)
(*  How to express LC_APP in terms of LC_APP0.                               *)
(* ------------------------------------------------------------------------- *)

let LC_APP_APP0 = prove
  (`!x y. LC_APP x y =
            LC_SUBST (\n. if n = 0 then y else LC_REF (PRE n)) (LC_APP0 x)`,
   REWRITE_TAC [LC_THM_LIFT] THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [LC_APP; LC_REF; LC_APP0; IF_DISTRIB;
                GSYM o_DEF; LC_SUBST_PROJ; SUBST_APP0] THEN
   REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [DBTERM_CONSTR_INJ] THEN
   MATCH_MP_TAC (GSYM SUBST_LUNIT_IMP) THEN
   REWRITE_TAC [PRE; o_THM; NOT_SUC]);;
