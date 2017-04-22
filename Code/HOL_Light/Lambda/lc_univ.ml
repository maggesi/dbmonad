(* -*- holl -*- *)

(* ========================================================================= *)
(*  More definitions and theorems and tactics about lists.                   *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2006                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  Proof that dbterm and LC are operads.                                    *)
(* ------------------------------------------------------------------------- *)

let DBTERM_OPERAD = prove
  (`OPERAD SUBST`,
   REWRITE_TAC [OPERAD_DEF; SUBST_ASSOC; o_DEF] THEN
   EXISTS_TAC `REF` THEN REWRITE_TAC [SUBST; SUBST_LUNIT]);;

let DBTERM_OPERAD_UNIT = prove
  (`OPERAD_UNIT SUBST = REF`,
   MATCH_MP_TAC OPERAD_UNIT_UNIQUE THEN
   REWRITE_TAC [DBTERM_OPERAD; SUBST; SUBST_LUNIT]);;

let LC_OPERAD = prove
  (`OPERAD LC_SUBST`,
   REWRITE_TAC [OPERAD_DEF; LC_SUBST_ASSOC; o_DEF] THEN
   EXISTS_TAC `LC_REF` THEN
   REWRITE_TAC [LC_SUBST_RUNIT; LC_SUBST_LUNIT]);;

let LC_OPERAD_UNIT = prove
  (`OPERAD_UNIT LC_SUBST = LC_REF`,
   MATCH_MP_TAC OPERAD_UNIT_UNIQUE THEN
   REWRITE_TAC [LC_OPERAD; LC_SUBST_LUNIT; LC_SUBST_RUNIT]);;

(* ------------------------------------------------------------------------- *)
(*  Proof that LC is an exponential operad.                                  *)
(* ------------------------------------------------------------------------- *)

let LC_DMOP = prove
  (`!k f x. DMOP k LC_SUBST LC_SUBST (LC_PROJ o f) (LC_PROJ x) =
      LC_PROJ (DMOP k SUBST SUBST f x)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [DMOP; DBTERM_OPERAD_UNIT;
                LC_OPERAD_UNIT; GSYM LC_SUBST_PROJ] THEN
   MATCH_MP_TAC LC_SUBST_FUN_EXTENS THEN GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC [GSYM LC_SUBST_PROJ; o_THM; LC_REF] THEN
   MATCH_MP_TAC LC_SUBST_FUN_EXTENS THEN REWRITE_TAC [o_THM]);;

let LC_ABS_MODULE_MOR = prove
  (`MODULE_MOR LC_SUBST (DMOP (SUC 0) LC_SUBST LC_SUBST) LC_SUBST LC_ABS`,
   SIMP_TAC [MODULE_MOR; SELF_MODULE; LC_OPERAD; MODULE_DMOP] THEN
   REWRITE_TAC [LC_THM_FUN_LIFT; LC_THM_LIFT; LC_DMOP;
                LC_ABS; LC_SUBST_PROJ] THEN
   REPEAT GEN_TAC THEN REWRITE_TAC [SUBST; DMOP; DBTERM_OPERAD_UNIT] THEN
   REPEAT AP_TERM_TAC THEN MATCH_MP_TAC SUBST_FUN_EXTENS THEN
   REWRITE_TAC [FUN_EQ_THM; SHIFTF; SHIFT_EQ_SUBST; LT; SHIFTF_0]);;

let LC_APP0_MODULE_MOR = prove
  (`MODULE_ISOM LC_SUBST LC_SUBST (DMOP (SUC 0) LC_SUBST LC_SUBST)
      LC_APP0 LC_ABS`,
   MESON_TAC [MODULE_ISOM_SYM; LC_APP0_ABS; LC_ABS_APP0;
              MODULE_ISOM; LC_ABS_MODULE_MOR]);;

let LC_EXP = prove
  (`EXP_OPERAD LC_SUBST LC_APP0 LC_ABS`,
   REWRITE_TAC [EXP_OPERAD; LC_APP0_MODULE_MOR]);;


(* ------------------------------------------------------------------------- *)
(*  Proof of the universal property of LC                                    *)
(* ------------------------------------------------------------------------- *)

g `!op (h:A->A) g.
     EXP_OPERAD op h g <=>
     OPERAD op /\
     (!x. g (h x) = x) /\
     (!y. h (g y) = y) /\
     (!f (x:A). h (op f x) =
            op (\i. if i = 0 then OPERAD_UNIT op i else
                    op (OPERAD_UNIT op o SUC) (f (PRE i)))
               (h x)) /\
     (!f x. op f (g x) =
            g (op (\i. if i = 0 then OPERAD_UNIT op i else
                       op (OPERAD_UNIT op o SUC) (f (PRE i)))
                  x))`;;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC [EXP_OPERAD; SELF_MODULE; MODULE_ISOM_UNFOLD; MODULE_MOR]);;
e (REWRITE_TAC [DMOP; CONJ_ACI]);;
e (REWRITE_TAC [ADD; LT; o_DEF; ARITH_RULE `n - SUC 0 = PRE n`]);;
e (EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;
e (MATCH_MP_TAC MODULE_DMOP);;
e (ASM_REWRITE_TAC [SELF_MODULE]);;
let EXP_OPERAD_UNFOLD = top_thm ();;


let DBTERM_EXP_MAP = new_recursive_definition dbterm_RECURSION
  `(!op h g i. DBTERM_EXP_MAP op h g (REF i) = OPERAD_UNIT op i) /\
   (!op h g x y.
      DBTERM_EXP_MAP op h g (APP x y) =
        op (\n. if n = 0 then DBTERM_EXP_MAP op h g y else
                OPERAD_UNIT op (PRE n)) (h (DBTERM_EXP_MAP op h g x))) /\
   (!op h g x. DBTERM_EXP_MAP op h g (ABS x) = g (DBTERM_EXP_MAP op h g x))`;;

g `!op (h:A->A) g x k n.
     EXP_OPERAD op h g
     ==> DBTERM_EXP_MAP op h g (SHIFT k n x) =
         op (\i. if i < k then OPERAD_UNIT op i else OPERAD_UNIT op (n + i))
            (DBTERM_EXP_MAP op h g x)`;;
e (SUBGOAL_THEN
   `!op (h:A->A) g.
      EXP_OPERAD op h g
      ==> !x k n.
          DBTERM_EXP_MAP op h g (SHIFT k n x) =
          op (\i. if i < k then OPERAD_UNIT op i else OPERAD_UNIT op (n + i))
             (DBTERM_EXP_MAP op h g x)`
   (fun th -> ASM_MESON_TAC [th]));;
e (REPEAT GEN_TAC THEN REWRITE_TAC [EXP_OPERAD_UNFOLD] THEN STRIP_TAC);;
e (DBTERM_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC [SHIFT; DBTERM_EXP_MAP]);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (REWRITE_TAC [IF_DISTRIB]);;
e (ASM_SIMP_TAC [OPERAD_ASSOC]);;
e (AP_THM_TAC THEN AP_TERM_TAC);;
e (REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC);;
e (COND_CASES_TAC THEN ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (ASM_SIMP_TAC [OPERAD_ASSOC; o_THM]);;
e (MATCH_MP_TAC OPERAD_LUNIT_IMP);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (REWRITE_TAC [NOT_SUC; PRE]);;
e (AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC);;
e (REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC);;
e (REWRITE_TAC [IF_DISTRIB]);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (REWRITE_TAC [o_THM; IF_DISTRIB]);;
e (AP_TERM_TAC);;
e (ARITH_TAC);;
let DBTERM_EXP_MAP_SHIFT = top_thm ();;

g `!op (h:A->A) g x f.
     EXP_OPERAD op h g
     ==> DBTERM_EXP_MAP op h g (SUBST f x) =
         op (DBTERM_EXP_MAP op h g o f) (DBTERM_EXP_MAP op h g x)`;;
e (SUBGOAL_THEN
   `!op (h:A->A) g.
     EXP_OPERAD op h g
     ==> !x f. DBTERM_EXP_MAP op h g (SUBST f x) =
               op (DBTERM_EXP_MAP op h g o f) (DBTERM_EXP_MAP op h g x)`
      (fun th -> MESON_TAC [th]));;
e (REPEAT GEN_TAC);;
e (DISCH_THEN
     (fun th ->
        STRIP_ASSUME_TAC (REWRITE_RULE [EXP_OPERAD_UNFOLD] th) THEN
 	ASSUME_TAC th));;
e (DBTERM_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC [DBTERM_EXP_MAP; SUBST; o_THM]);;
e (ASM_SIMP_TAC [OPERAD_RUNIT; o_THM]);;
e (ASM_SIMP_TAC [OPERAD_ASSOC]);;
e (AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC);;
e (COND_CASES_TAC THEN ASM_REWRITE_TAC [o_THM]);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (ASM_SIMP_TAC [OPERAD_ASSOC; o_THM]);;
e (MATCH_MP_TAC OPERAD_LUNIT_IMP);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (REWRITE_TAC [NOT_SUC]);;
e (REWRITE_TAC [PRE]);;
e (AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC);;
e (REWRITE_TAC [FUN_EQ_THM; o_THM] THEN GEN_TAC);;
e (REWRITE_TAC [SHIFTF; LT]);;
e (COND_CASES_TAC THEN ASM_REWRITE_TAC []);;
e (REWRITE_TAC [DBTERM_EXP_MAP]);;
e (ASM_SIMP_TAC [DBTERM_EXP_MAP_SHIFT]);;
e (REWRITE_TAC [LT; ADD; o_DEF]);;
e (REPEAT AP_TERM_TAC);;
e (ARITH_TAC);;
let DBTERM_EXP_MAP_SUBST = top_thm ();;

g `!op (h:A->A) g x y.
     EXP_OPERAD op h g /\ x === y
     ==> DBTERM_EXP_MAP op h g x = DBTERM_EXP_MAP op h g y`;;
e (SUBGOAL_THEN
   `!op (h:A->A) g.
      EXP_OPERAD op h g
      ==> !x y. x === y
      ==> DBTERM_EXP_MAP op h g x = DBTERM_EXP_MAP op h g y`
   (fun th -> MESON_TAC [th]));;
e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_OPERAD_UNFOLD]));;
e (MATCH_MP_TAC LC_REL_INDUCT);;
e (REPEAT CONJ_TAC);;
e (MATCH_MP_TAC DBTERM_BETA_INDUCT);;
e (ASM_SIMP_TAC [DBTERM_EXP_MAP_SUBST]);;
e (ASM_REWRITE_TAC [DBTERM_EXP_MAP; o_DEF]);;
e (REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC);;
e (REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC);;
e (COND_CASES_TAC THEN ASM_REWRITE_TAC [DBTERM_EXP_MAP]);;
e (MATCH_MP_TAC DBTERM_ETA_INDUCT);;
e (REWRITE_TAC [DBTERM_EXP_MAP]);;
e (ASM_SIMP_TAC [DBTERM_EXP_MAP_SHIFT]);;
e (ASM_SIMP_TAC [OPERAD_ASSOC]);;
e (REWRITE_TAC [LT; ADD; GSYM IF_DISTRIB]);;
e (ASM_SIMP_TAC [OPERAD_RUNIT; o_THM]);;
e (REWRITE_TAC [NOT_SUC; PRE]);;
e (SUBGOAL_THEN ` (\n. if n = 0
                       then OPERAD_UNIT (op:(num->A)->A->A) 0
 		       else OPERAD_UNIT op (SUC (PRE n))) =
                  OPERAD_UNIT op`
    (fun th -> REWRITE_TAC [th]));;
e (REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC []);;
e (AP_TERM_TAC);;
e (ASM_ARITH_TAC);;
e (ASM_SIMP_TAC [OPERAD_LUNIT]);;
e (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [DBTERM_EXP_MAP]);;
e (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [DBTERM_EXP_MAP]);;
e (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;
e (MESON_TAC[]);;
let DBTERM_EXP_MAP_REL = top_thm ();;

let LC_EXP_MAP = define
  `!op h g x. LC_EXP_MAP op h g x = DBTERM_EXP_MAP op h g (LC_LIFT x)`;;

g `!op (h:A->A) g x.
     EXP_OPERAD op h g ==>
     LC_EXP_MAP op h g (LC_PROJ x) = DBTERM_EXP_MAP op h g x`;;
e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (REWRITE_TAC [LC_EXP_MAP]);;
e (MATCH_MP_TAC DBTERM_EXP_MAP_REL);;
e (ASM_REWRITE_TAC [LC_LIFT_PROJ]);;
let LC_EXP_MAP_FACTOR = top_thm ();;

g `!op (h:A->A) g.
      EXP_OPERAD op h g
      ==> OPERAD_MOR LC_SUBST op (LC_EXP_MAP op h g)`;;
e (REPEAT STRIP_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_OPERAD_UNFOLD]));;
e (ASM_REWRITE_TAC [OPERAD_MOR; LC_OPERAD]);;
e (REWRITE_TAC [LC_OPERAD_UNIT; LC_REF]);;
e (ASM_SIMP_TAC [LC_EXP_MAP_FACTOR; DBTERM_EXP_MAP]);;
e (REWRITE_TAC [LC_SUBST_DEF]);;
e (ASM_SIMP_TAC [LC_EXP_MAP_FACTOR]);;
e (ASM_SIMP_TAC [DBTERM_EXP_MAP_SUBST]);;
e (REWRITE_TAC [LC_EXP_MAP; o_DEF]);;
let OPERAD_MOR_LC_EXP_MAP = top_thm ();;


g `!op (h:A->A) g.
     EXP_OPERAD op h g
     ==>
     (!i. DBTERM_EXP_MAP op h g (REF i) = OPERAD_UNIT op i) /\
     (!x. DBTERM_EXP_MAP op h g (APP0 x) = h (DBTERM_EXP_MAP op h g x)) /\
     (!x. DBTERM_EXP_MAP op h g (ABS x) = g (DBTERM_EXP_MAP op h g x)) /\
     (!t x. DBTERM_EXP_MAP op h g (SUBST t x) =
            op (DBTERM_EXP_MAP op h g o t) (DBTERM_EXP_MAP op h g x))`;;
e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_OPERAD_UNFOLD]));;
e (ASM_REWRITE_TAC [APP0; DBTERM_EXP_MAP]);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [DBTERM_EXP_MAP_SHIFT; OPERAD_ASSOC]);;
e (MATCH_MP_TAC OPERAD_LUNIT_IMP);;
e (ASM_REWRITE_TAC [TRIVIAL_ARITH]);;
e (GEN_TAC THEN COND_CASES_TAC);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (ASM_SIMP_TAC [OPERAD_ASSOC]);;
e (ASM_SIMP_TAC [ARITH_RULE `~(i = 0) ==> SUC (PRE i) = i`]);;
e (MATCH_MP_TAC OPERAD_LUNIT_IMP);;
e (ASM_REWRITE_TAC [o_THM]);;
e (ASM_SIMP_TAC [OPERAD_RUNIT]);;
e (REWRITE_TAC [NOT_SUC; PRE]);;
e (ASM_SIMP_TAC [DBTERM_EXP_MAP_SUBST]);;
let DBTERM_EXP_MAP_ALT = top_thm ();;

g `!op (h:A->A) g.
      EXP_OPERAD op h g
      ==> EXP_OPERAD_MOR LC_SUBST LC_APP0 LC_ABS op h g (LC_EXP_MAP op h g)`;;
e (REPEAT STRIP_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_OPERAD_UNFOLD]));;
e (ASM_REWRITE_TAC [EXP_OPERAD_MOR; LC_EXP]);;
e (ASM_SIMP_TAC [OPERAD_MOR_LC_EXP_MAP]);;
e (REWRITE_TAC [LC_THM_LIFT]);;
e (ASM_SIMP_TAC [LC_EXP_MAP_FACTOR; LC_APP0]);;
e (ASM_SIMP_TAC [DBTERM_EXP_MAP_ALT]);;
let EXP_OPERAD_MOR_LC_EXP_MAP = top_thm ();;

g `!op1 h1 g1 op2 h2 g2 (f:A->B).
      EXP_OPERAD_MOR op1 h1 g1 op2 h2 g2 f
      <=> EXP_OPERAD op1 h1 g1 /\
          EXP_OPERAD op2 h2 g2 /\
      	  OPERAD_MOR op1 op2 f /\
      	  (!x. h2 (f x) = f (h1 x)) /\
    	  (!x. g2 (f x) = f (g1 x))`;;
e (REPEAT GEN_TAC THEN REWRITE_TAC [EXP_OPERAD_MOR] THEN
   EQ_TAC THENL [ALL_TAC; MESON_TAC[]]);;
e (DISCH_THEN (fun th -> REWRITE_TAC [th] THEN MP_TAC th));;
e (REWRITE_TAC [EXP_OPERAD; MODULE_ISOM_UNFOLD; MODULE_MOR]);;
e (REWRITE_TAC [CONJ_ACI]);;
e (STRIP_TAC THEN GEN_TAC);;
e (SUBGOAL_THEN `!x y : B. h2 x :B = h2 y ==> x = y` MATCH_MP_TAC);;
e (ASM_MESON_TAC[]);;
e (ASM_REWRITE_TAC []);;
let EXP_OPERAD_MOR_FACTS = top_thm ();;

g `!op (h:A->A) g m.
      EXP_OPERAD op h g /\
      EXP_OPERAD_MOR LC_SUBST LC_APP0 LC_ABS op h g m
      ==> m = LC_EXP_MAP op h g`;;
e (REPEAT STRIP_TAC);;
e (STRIP_ASSUME_TAC
    (REWRITE_RULE [EXP_OPERAD_UNFOLD]
                  (ASSUME `EXP_OPERAD op (h:A->A) g`)));;
e (STRIP_ASSUME_TAC
     (REWRITE_RULE [EXP_OPERAD_MOR_FACTS; LC_EXP]
                   (ASSUME `EXP_OPERAD_MOR LC_SUBST LC_APP0 LC_ABS
                                           op (h:A->A) g m`)));;
e (STRIP_ASSUME_TAC
    (REWRITE_RULE [OPERAD_MOR; LC_OPERAD]
                  (ASSUME `OPERAD_MOR LC_SUBST op (m:lc->A)`)));;
e (REWRITE_TAC [FUN_EQ_THM]);;
e (REWRITE_TAC [LC_THM_LIFT]);;
e (ASM_SIMP_TAC [LC_EXP_MAP_FACTOR]);;
e (DBTERM_INDUCT_TAC);;
e (ASM_REWRITE_TAC [GSYM LC_REF; GSYM LC_OPERAD_UNIT; DBTERM_EXP_MAP]);;
e (ASM_REWRITE_TAC [GSYM LC_APP; LC_APP_APP0; DBTERM_EXP_MAP]);;
e (SUBGOAL_THEN `m (LC_APP0 (LC_PROJ a0)) :A = h (DBTERM_EXP_MAP op h g a0)`
    SUBST1_TAC);;
e (ASM_MESON_TAC[]);;
e (AP_THM_TAC THEN AP_TERM_TAC);;
e (REWRITE_TAC [FUN_EQ_THM; o_THM]);;
e (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
e (ASM_REWRITE_TAC [GSYM LC_OPERAD_UNIT]);;
e (ASM_REWRITE_TAC [GSYM LC_ABS; DBTERM_EXP_MAP]);;
e (ASM_MESON_TAC[]);;
let LC_EXP_MAP_UNIQUE = top_thm ();;


