(* ========================================================================= *)
(*  More definitions and theorems and tactics about lists.                   *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2005 2006 2017, 2020                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  Proof that dblambda and LC are operads.                                  *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_DBMONAD = prove
 (`DBMONAD SUBST`,
  REWRITE_TAC[DBMONAD_DEF; SUBST_SUBST; o_DEF] THEN
  EXISTS_TAC `REF` THEN REWRITE_TAC[SUBST; SUBST_REF]);;

let DBLAMBDA_DBUNIT = prove
 (`DBUNIT SUBST = REF`,
  MATCH_MP_TAC DBUNIT_UNIQUE THEN
  REWRITE_TAC[DBLAMBDA_DBMONAD; SUBST; SUBST_REF]);;

let LC_DBMONAD = prove
 (`DBMONAD LC_SUBST`,
  REWRITE_TAC[DBMONAD_DEF; LC_SUBST_SUBST; o_DEF] THEN
  EXISTS_TAC `LC_REF` THEN
  REWRITE_TAC[LC_SUBST_RUNIT; LC_SUBST_LUNIT]);;

let LC_DBUNIT = prove
 (`DBUNIT LC_SUBST = LC_REF`,
  MATCH_MP_TAC DBUNIT_UNIQUE THEN
  REWRITE_TAC[LC_DBMONAD; LC_SUBST_LUNIT; LC_SUBST_RUNIT]);;

(* ------------------------------------------------------------------------- *)
(*  Proof that LC is an exponential operad.                                  *)
(* ------------------------------------------------------------------------- *)

let LC_DMOP = prove
 (`!f x. DMOP LC_SUBST LC_SUBST (LC_PROJ o f) (LC_PROJ x) =
         LC_PROJ (DMOP SUBST SUBST f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DMOP; GSYM LC_SUBST_PROJ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  NUM_CASES_TAC THEN
  REWRITE_TAC[DBDERIV; DBLAMBDA_DBUNIT; LC_DBUNIT; LC_REF; o_THM] THEN
  REWRITE_TAC[DBREINDEX; GSYM LC_SUBST_PROJ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; DBLAMBDA_DBUNIT; LC_DBUNIT; LC_REF]);;

let LC_REINDEX_EQ_LC_SUBST = prove
 (`!f x. LC_REINDEX f x = LC_SUBST (LC_REF o f) x`,
  REWRITE_TAC[FORALL_LC_THM; FORALL_LC_FUN_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_REINDEX; REINDEX_EQ_SUBST; GSYM LC_SUBST_PROJ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; LC_REF]);;

let LC_ABS_MODULE_MOR = prove
 (`MODULE_MOR LC_SUBST (DMOP LC_SUBST LC_SUBST) LC_SUBST LC_ABS`,
  REWRITE_TAC[MODULE_MOR; SELF_MODULE; LC_DBMONAD] THEN
  SIMP_TAC[MODULE_DMOP; LC_DBMONAD; SELF_MODULE] THEN
  REWRITE_TAC[FORALL_LC_THM; FORALL_LC_FUN_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_SUBST] THEN AP_TERM_TAC THEN REWRITE_TAC[DMOP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  NUM_CASES_TAC THEN REWRITE_TAC[DBDERIV; LC_DERIV; LC_DBUNIT; DBREINDEX] THEN
  REWRITE_TAC[o_THM; LC_REINDEX_EQ_LC_SUBST]);;

let LC_APP0_MODULE_MOR = prove
 (`MODULE_ISOM LC_SUBST LC_SUBST (DMOP LC_SUBST LC_SUBST)
               LC_APP0 LC_ABS`,
  MESON_TAC[MODULE_ISOM_SYM; LC_APP0_ABS; LC_ABS_APP0;
            MODULE_ISOM; LC_ABS_MODULE_MOR]);;

let LC_EXP = prove
 (`EXP_DBMONAD LC_SUBST LC_APP0 LC_ABS`,
  REWRITE_TAC[EXP_DBMONAD; LC_APP0_MODULE_MOR]);;

(* ------------------------------------------------------------------------- *)
(*  Proof of the universal property of LC                                    *)
(* ------------------------------------------------------------------------- *)

let EXP_DBMONAD_UNFOLD = prove
 (`!op h:A->A g.
     EXP_DBMONAD op h g <=>
     DBMONAD op /\
     (!x. g (h x) = x) /\
     (!y. h (g y) = y) /\
     (!f x. h (op f x) = op (DBDERIV op f) (h x)) /\
     (!f x. op f (g x) = g (op (DBDERIV op f) x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_DBMONAD; SELF_MODULE; MODULE_ISOM_UNFOLD;
              MODULE_MOR; DMOP] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MODULE_DMOP; SELF_MODULE]);;

let DBLAMBDA_EXPMAP = new_recursive_definition dblambda_RECURSION
  `(!op h g:A->A i. DBLAMBDA_EXPMAP op h g (REF i) = DBUNIT op i) /\
   (!op h g x y.
      DBLAMBDA_EXPMAP op h g (APP x y) =
        op (PUSHENV (DBLAMBDA_EXPMAP op h g y) (DBUNIT op))
           (h (DBLAMBDA_EXPMAP op h g x))) /\
   (!op h g x. DBLAMBDA_EXPMAP op h g (ABS x) =
               g (DBLAMBDA_EXPMAP op h g x))`;;

let DBLAMBDA_EXPMAP_REINDEX = prove
 (`!op h:A->A g x f.
     EXP_DBMONAD op h g
     ==> DBLAMBDA_EXPMAP op h g (REINDEX f x) =
         op (DBUNIT op o f) (DBLAMBDA_EXPMAP op h g x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_DBMONAD_UNFOLD] THEN STRIP_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  GEN_TAC THEN ASM_REWRITE_TAC[REINDEX; DBLAMBDA_EXPMAP] THENL
  [ASM_SIMP_TAC[DBMONAD_RUNIT; o_THM];
   ASM_SIMP_TAC[DBMONAD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
   ASM_SIMP_TAC[DBDERIV; PUSHENV; o_THM; DBMONAD_RUNIT; DBREINDEX_DBUNIT];
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   REWRITE_TAC[DBDERIV; SLIDE; o_THM] THEN ASM_SIMP_TAC[DBREINDEX_DBUNIT]]);;

let DBREINDEX_DBLAMBDA_EXPMAP = prove
 (`!op h g x f.
     EXP_DBMONAD op h g
     ==> DBREINDEX op f (DBLAMBDA_EXPMAP op h g x) =
         DBLAMBDA_EXPMAP op h g (REINDEX f x):A`,

  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "exp" THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[EXP_DBMONAD_UNFOLD] THEN STRIP_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  GEN_TAC THEN ASM_REWRITE_TAC[DBLAMBDA_EXPMAP; REINDEX] THENL
  [ASM_SIMP_TAC[DBREINDEX_DBUNIT];
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; DBMONAD_ASSOC; DBREINDEX_DBSUBST] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
   NUM_CASES_TAC THEN
   ASM_SIMP_TAC[PUSHENV; DBDERIV; DBMONAD_RUNIT; DBLAMBDA_EXPMAP_REINDEX;
                DBREINDEX_DBUNIT; o_THM];
   ASM_SIMP_TAC[DBREINDEX; DBLAMBDA_EXPMAP_REINDEX] THEN
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   REWRITE_TAC[DBDERIV; SLIDE; o_THM] THEN ASM_SIMP_TAC[DBREINDEX_DBUNIT]]);;

let DBLAMBDA_EXPMAP_SUBST = prove
 (`!op h:A->A g x f.
     EXP_DBMONAD op h g
     ==> DBLAMBDA_EXPMAP op h g (SUBST f x) =
         op (DBLAMBDA_EXPMAP op h g o f) (DBLAMBDA_EXPMAP op h g x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "exp" THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[EXP_DBMONAD_UNFOLD] THEN STRIP_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  GEN_TAC THEN ASM_REWRITE_TAC[SUBST; DBLAMBDA_EXPMAP] THENL
  [ASM_SIMP_TAC[DBMONAD_RUNIT; o_THM];
   ASM_SIMP_TAC[DBMONAD_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   ASM_SIMP_TAC[DBMONAD_RUNIT; DBDERIV; PUSHENV] THEN
   ASM_SIMP_TAC[DBSUBST_DBREINDEX; o_THM] THEN
   MATCH_MP_TAC DBMONAD_LUNIT_IMP THEN
   ASM_REWRITE_TAC[o_THM; PUSHENV];
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   REWRITE_TAC[DERIV; DBDERIV; DBLAMBDA_EXPMAP; o_THM] THEN
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; DBREINDEX_DBLAMBDA_EXPMAP]]);;

let DBLAMBDA_EXPMAP_REL = prove
 (`!op h:A->A g x y.
     EXP_DBMONAD op h g /\ x === y
     ==> DBLAMBDA_EXPMAP op h g x = DBLAMBDA_EXPMAP op h g y`,
  INTRO_TAC "!op h g" THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  INTRO_TAC "exp" THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[EXP_DBMONAD_UNFOLD] THEN STRIP_TAC THEN
  MATCH_MP_TAC LC_REL_INDUCT THEN CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_BETA_INDUCT THEN GEN_TAC THEN GEN_TAC THEN
   REWRITE_TAC[DBLAMBDA_EXPMAP] THEN ASM_SIMP_TAC[DBLAMBDA_EXPMAP_SUBST] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
   NUM_CASES_TAC THEN REWRITE_TAC[PUSHENV; DBLAMBDA_EXPMAP];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_ETA_INDUCT THEN GEN_TAC THEN
   REWRITE_TAC[DBLAMBDA_EXPMAP] THEN
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; DBMONAD_ASSOC] THEN
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; DBMONAD_ASSOC] THEN
   SUBGOAL_THEN
     `(op (PUSHENV (DBUNIT op 0) (DBUNIT op)) o DBDERIV op (DBUNIT op o SUC)) =
      DBUNIT (op:(num->A)->A->A)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
    ASM_SIMP_TAC[DBDERIV; DBMONAD_RUNIT; PUSHENV] THEN
    ASM_SIMP_TAC[DBSUBST_DBREINDEX; o_THM; DBMONAD_RUNIT; PUSHENV];
    ASM_SIMP_TAC[DBMONAD_LUNIT]];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DBLAMBDA_EXPMAP]);;

let LC_EXPMAP = define
  `!op h g:A->A x. LC_EXPMAP op h g x = DBLAMBDA_EXPMAP op h g (LC_LIFT x)`;;

let LC_EXPMAP_FACTOR = prove
 (`!op h:A->A g x.
     EXP_DBMONAD op h g
     ==> LC_EXPMAP op h g (LC_PROJ x) = DBLAMBDA_EXPMAP op h g x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LC_EXPMAP] THEN
  MATCH_MP_TAC DBLAMBDA_EXPMAP_REL THEN ASM_REWRITE_TAC[LC_LIFT_PROJ]);;

g `!op h:A->A g.
      EXP_DBMONAD op h g
      ==> DBMONAD_MOR LC_SUBST op (LC_EXPMAP op h g)`;;
e (REPEAT STRIP_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_DBMONAD_UNFOLD]));;
e (ASM_REWRITE_TAC[DBMONAD_MOR; LC_DBMONAD]);;
e (REWRITE_TAC[LC_DBUNIT; LC_REF]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR; DBLAMBDA_EXPMAP]);;
e (REWRITE_TAC[LC_SUBST_DEF]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR]);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_SUBST]);;
e (REWRITE_TAC[LC_EXPMAP; o_DEF]);;
let DBMONAD_MOR_LC_EXPMAP = top_thm ();;

g `!op h:A->A g.
     EXP_DBMONAD op h g
     ==>
     (!i. DBLAMBDA_EXPMAP op h g (REF i) = DBUNIT op i) /\
     (!x. DBLAMBDA_EXPMAP op h g (APP0 x) = h (DBLAMBDA_EXPMAP op h g x)) /\
     (!x. DBLAMBDA_EXPMAP op h g (ABS x) = g (DBLAMBDA_EXPMAP op h g x)) /\
     (!t x. DBLAMBDA_EXPMAP op h g (SUBST t x) =
            op (DBLAMBDA_EXPMAP op h g o t) (DBLAMBDA_EXPMAP op h g x))`;;
e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_DBMONAD_UNFOLD]));;
e (ASM_REWRITE_TAC[APP0; DBLAMBDA_EXPMAP]);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; DBMONAD_ASSOC]);;
e (MATCH_MP_TAC DBMONAD_LUNIT_IMP);;
e (ASM_REWRITE_TAC[]);;
e (NUM_CASES_TAC THEN REWRITE_TAC[DBDERIV; o_THM] THEN
   ASM_SIMP_TAC[DBMONAD_RUNIT; DBREINDEX_DBUNIT; PUSHENV]);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_SUBST]);;
let DBLAMBDA_EXPMAP_ALT = top_thm ();;

g `!op h:A->A g.
      EXP_DBMONAD op h g
      ==> EXP_DBMONAD_MOR LC_SUBST LC_APP0 LC_ABS
                          op h g (LC_EXPMAP op h g)`;;
e (REPEAT STRIP_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_DBMONAD_UNFOLD]));;
e (ASM_REWRITE_TAC[EXP_DBMONAD_MOR; LC_EXP]);;
e (ASM_SIMP_TAC[DBMONAD_MOR_LC_EXPMAP]);;
e (REWRITE_TAC[FORALL_LC_THM]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR; LC_APP0]);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_ALT]);;
let EXP_DBMONAD_MOR_LC_EXPMAP = top_thm ();;

g `!op1 h1 g1 op2 h2 g2 f:A->B.
      EXP_DBMONAD_MOR op1 h1 g1 op2 h2 g2 f
      <=> EXP_DBMONAD op1 h1 g1 /\
          EXP_DBMONAD op2 h2 g2 /\
          DBMONAD_MOR op1 op2 f /\
          (!x. h2 (f x) = f (h1 x)) /\
          (!x. g2 (f x) = f (g1 x))`;;
e (REPEAT GEN_TAC THEN REWRITE_TAC[EXP_DBMONAD_MOR] THEN
   EQ_TAC THENL [ALL_TAC; MESON_TAC[]]);;
e (DISCH_THEN (fun th -> REWRITE_TAC[th] THEN MP_TAC th));;
e (REWRITE_TAC[EXP_DBMONAD; MODULE_ISOM_UNFOLD; MODULE_MOR]);;
e (REWRITE_TAC[CONJ_ACI]);;
e (STRIP_TAC THEN GEN_TAC);;
e (SUBGOAL_THEN `!x y : B. h2 x :B = h2 y ==> x = y` MATCH_MP_TAC);;
e (ASM_MESON_TAC[]);;
e (ASM_REWRITE_TAC[]);;
let EXP_DBMONAD_MOR_FACTS = top_thm ();;

g `!op h:A->A g m.
      EXP_DBMONAD op h g /\
      EXP_DBMONAD_MOR LC_SUBST LC_APP0 LC_ABS op h g m
      ==> m = LC_EXPMAP op h g`;;
e (REPEAT STRIP_TAC);;
e (STRIP_ASSUME_TAC
    (REWRITE_RULE [EXP_DBMONAD_UNFOLD]
                  (ASSUME `EXP_DBMONAD op (h:A->A) g`)));;
e (STRIP_ASSUME_TAC
     (REWRITE_RULE [EXP_DBMONAD_MOR_FACTS; LC_EXP]
                   (ASSUME `EXP_DBMONAD_MOR LC_SUBST LC_APP0 LC_ABS
                                           op (h:A->A) g m`)));;
e (STRIP_ASSUME_TAC
    (REWRITE_RULE [DBMONAD_MOR; LC_DBMONAD]
                  (ASSUME `DBMONAD_MOR LC_SUBST op (m:lc->A)`)));;
e (REWRITE_TAC[FUN_EQ_THM]);;
e (REWRITE_TAC[FORALL_LC_THM]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR]);;
e (DBLAMBDA_INDUCT_TAC);;
e (ASM_REWRITE_TAC[GSYM LC_REF; GSYM LC_DBUNIT; DBLAMBDA_EXPMAP]);;
e (ASM_REWRITE_TAC[GSYM LC_APP; LC_APP_APP0; DBLAMBDA_EXPMAP]);;
e (SUBGOAL_THEN `m (LC_APP0 (LC_PROJ a0)) :A = h (DBLAMBDA_EXPMAP op h g a0)`
    SUBST1_TAC);;
e (ASM_MESON_TAC[]);;
e (AP_THM_TAC THEN AP_TERM_TAC);;
e (REWRITE_TAC[FUN_EQ_THM; o_THM]);;
e (NUM_CASES_TAC THEN ASM_REWRITE_TAC[PUSHENV; NOT_SUC; PRE]);;
e (ASM_REWRITE_TAC[GSYM LC_DBUNIT]);;
e (ASM_REWRITE_TAC[GSYM LC_ABS; DBLAMBDA_EXPMAP]);;
e (ASM_MESON_TAC[]);;
let LC_EXPMAP_UNIQUE = top_thm ();;