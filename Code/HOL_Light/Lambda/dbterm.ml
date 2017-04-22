(* -*- holl -*- *)

(* ========================================================================= *)
(*  Syntactic Lambda Calculus "a la" de Bruijn.                              *)
(*  Here syntactic means: "terms are not identified by beta-eta relation".   *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2006                                *)
(* ========================================================================= *)

parse_as_infix("===",(10,"right"));;
make_overloadable "===" `:A->A->bool`;;

(* ------------------------------------------------------------------------- *)
(*  Type for lambda terms using de Bruijn notation.                          *)
(* ------------------------------------------------------------------------- *)

let dbterm_INDUCT, dbterm_RECURSION = define_type
  "dbterm = REF num
          | APP dbterm dbterm
          | ABS dbterm";;

(* ------------------------------------------------------------------------- *)
(*  Basic operations on lambda terms.                                        *)
(* ------------------------------------------------------------------------- *)

let SHIFT = new_recursive_definition dbterm_RECURSION
  `(!k n i. SHIFT k n (REF i) = REF (if i < k then i else n + i)) /\
   (!k n x y. SHIFT k n (APP x y) = APP (SHIFT k n x) (SHIFT k n y)) /\
   (!k n x. SHIFT k n (ABS x) = ABS (SHIFT (SUC k) n x))`;;

let SHIFTF = new_definition
  `!f k i. SHIFTF k f i = if i < k then REF i else SHIFT 0 k (f (i - k))`;;

let SUBST = new_recursive_definition dbterm_RECURSION
  `(!f i. SUBST f (REF i) = f i) /\
   (!f x y. SUBST f (APP x y) = APP (SUBST f x) (SUBST f y)) /\
   (!f x. SUBST f (ABS x) = ABS (SUBST (SHIFTF (SUC 0) f) x))`;;

let APP0 = new_definition
  `APP0 x = APP (SHIFT 0 (SUC 0) x) (REF 0)`;;

let DBTERM_INDUCT_TAC =
  MATCH_MP_TAC dbterm_INDUCT THEN CONJ_TAC THENL
  [GEN_TAC; CONJ_TAC THEN GEN_TAC THENL
   [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC); DISCH_TAC]];;

let dbterm_CASES = MESON [dbterm_INDUCT]
  `!P. (!a. P (REF a)) /\ (!a0 a1. P (APP a0 a1)) /\ (!a. P (ABS a))
            ==> (!x. P x)`;;

let DBTERM_CASES_TAC =
  MATCH_MP_TAC dbterm_INDUCT THEN CONJ_TAC THENL
  [GEN_TAC; CONJ_TAC THEN GEN_TAC THENL
   [GEN_TAC; ALL_TAC]];;

(* ------------------------------------------------------------------------- *)
(*  Trivial lemmas                                                           *)
(* ------------------------------------------------------------------------- *)

let IF_REF = prove
  (`!b x y. (if b then REF x else REF y) = REF (if b then x else y)`,
   REWRITE_TAC [IF_DISTRIB]);;

let DBTERM_CONSTR_INJ = injectivity "dbterm";;

let DBTERM_CONSTR_DIST = distinctness "dbterm";;

let REF_INJ = MESON [DBTERM_CONSTR_INJ]
  `!x y. REF x = REF y <=> x = y`;;

(* ------------------------------------------------------------------------- *)
(*  SHIFT                                                                    *)
(* ------------------------------------------------------------------------- *)

let SHIFT_0 = prove
  (`!x k. SHIFT k 0 x = x`,
   MATCH_MP_TAC dbterm_INDUCT THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [SHIFT; ADD] THEN COND_CASES_TAC
   THEN REWRITE_TAC []);;

let SHIFT_INJ = prove
  (`!x y n k. SHIFT k n x = SHIFT k n y <=> x = y`,
   DBTERM_INDUCT_TAC THEN DBTERM_CASES_TAC THEN
   ASM_REWRITE_TAC [SHIFT; DBTERM_CONSTR_INJ; DBTERM_CONSTR_DIST] THEN
   ARITH_TAC);;

let SHIFTF_INJ = prove
  (`!f g k. (!i. SHIFTF k f i = SHIFTF k g i) <=> (!i. f i = g i)`,
   REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [SHIFTF] THENL
   [DISCH_THEN (ASSUME_TAC o REWRITE_RULE [SHIFT_INJ;
    ARITH_RULE `~(i + k < k) /\ (i + k) - k = i`] o SPEC `i + k`) THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [GSYM FUN_EQ_THM] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let LE_SHIFT_COMM = prove
  (`!x h k n m. h <= k ==> SHIFT h n (SHIFT k m x) =
                          SHIFT (k + n) m (SHIFT h n x)`,
   DBTERM_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [SHIFT; DBTERM_CONSTR_INJ; LE_SUC; ADD] THEN ASM_ARITH_TAC);;

let LE_SHIFT_COMM_0 = prove
  (`!x k n m. SHIFT 0 n (SHIFT k m x) =
              SHIFT (k + n) m (SHIFT 0 n x)`,
   SIMP_TAC [SPECL [`x:dbterm`; `0`] LE_SHIFT_COMM; LE_0]);;

(* Symmetric of LE_SHIFT_COMM *)
let GE_SHIFT_COMM = prove
  (`!x h k n m. m + k <= h ==> SHIFT h n (SHIFT k m x) =
                               SHIFT k m (SHIFT (h - m) n x)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `k <= h - m /\ h - m + m = h`
    (fun th -> SIMP_TAC [LE_SHIFT_COMM; th]) THEN
   ASM_ARITH_TAC);;

let SHIFT_SHIFT = prove
  (`!x n m h k. k <= h /\ h <= k + m
               ==> SHIFT h n (SHIFT k m x) = SHIFT k (m + n) x`,
   DBTERM_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [SHIFT; DBTERM_CONSTR_INJ; LE_SUC; ADD] THEN
   ASM_ARITH_TAC);;

let SHIFT_SHIFT_0 = prove
  (`(!k n m x. SHIFT k n (SHIFT k m x) = SHIFT k (m + n) x) /\
    (!k n x. SHIFT k n (SHIFT 0 k x) = SHIFT 0 (k + n) x)`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC SHIFT_SHIFT THEN
   REWRITE_TAC [LE_0; LE_REFL; ADD] THEN ARITH_TAC);;

let SHIFTF_0 = prove
  (`!f. SHIFTF 0 f = f`,
   REWRITE_TAC [FUN_EQ_THM; SHIFTF; SHIFT_0; LT; SUB_0]);;

let SHIFTF_REF = prove
  (`SHIFTF k REF = REF`,
   REWRITE_TAC [FUN_EQ_THM; SHIFTF; SHIFT; IF_REF; REF_INJ; LT] THEN
   ARITH_TAC);;

let SHIFTF_SHIFTF = prove
  (`!f h k. SHIFTF h (SHIFTF k f) = SHIFTF (h + k) f`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [SHIFTF; FUN_EQ_THM; ISPEC `SHIFT 0 h` (GSYM IF_DISTRIB);
                SHIFT; SHIFT_SHIFT_0; LT] THEN
   GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC [ARITH_RULE `x < h ==> x < h + k`];
    ASM_SIMP_TAC [ARITH_RULE `~(x < h) ==> (x - h < k <=> x < h + k)`] THEN
   COND_CASES_TAC THEN REWRITE_TAC [REF_INJ; ADD_AC] THEN
   REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(*  SUBST                                                                    *)
(* ------------------------------------------------------------------------- *)

let SUBST_FUN_EXTENS = prove
  (`!f g x. (!n. f n = g n) ==> SUBST f x = SUBST g x`,
   REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   ASM_REWRITE_TAC [FUN_EQ_THM]);;

let SUBST_LUNIT = prove
  (`!x n. SUBST REF x = x`,
   MATCH_MP_TAC dbterm_INDUCT THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [SUBST; SHIFTF_REF]);;

let SUBST_LUNIT_IMP = prove
  (`!f x. (!i. f i = REF i) ==> SUBST f x = x`,
   REPEAT GEN_TAC THEN REWRITE_TAC [GSYM FUN_EQ_THM] THEN
   DISCH_TAC THEN ASM_SIMP_TAC [SUBST_LUNIT]);;

let SHIFT_EQ_SUBST = time prove
  (`!x k n. SHIFT k n x = SUBST (\i. if i < k then REF i else REF (n + i)) x`,
   DBTERM_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC [SHIFT; SUBST; IF_REF; DBTERM_CONSTR_INJ] THEN
   MATCH_MP_TAC SUBST_FUN_EXTENS THEN
   REWRITE_TAC [SHIFTF; SHIFT; LT; IF_REF; REF_INJ] THEN
   NUM_CASES_TAC THEN REWRITE_TAC [TRIVIAL_ARITH; IF_DISTRIB; SUC_INJ] THEN
   ARITH_TAC);;

let SHIFT_SUBST = prove
  (`!x f k n. SHIFT k n (SUBST f x) = SUBST (SHIFT k n o f) x`,
   MATCH_MP_TAC dbterm_INDUCT THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [SHIFT; SUBST; DBTERM_CONSTR_INJ; o_THM] THEN
   MATCH_MP_TAC SUBST_FUN_EXTENS THEN GEN_TAC THEN
   REWRITE_TAC [o_THM; SHIFTF; TRIVIAL_ARITH] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC [SHIFT; LE_SHIFT_COMM_0; TRIVIAL_ARITH]);;

let SUBST_SHIFT = prove
  (`!x f k n. SUBST f (SHIFT k n x) =
      SUBST (\i. if i < k then f i else f (n + i)) x`,
   DBTERM_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC [SHIFT; SUBST; IF_DISTRIB; DBTERM_CONSTR_INJ] THEN
   MATCH_MP_TAC SUBST_FUN_EXTENS THEN
   NUM_CASES_TAC THEN ASM_REWRITE_TAC [SHIFTF; TRIVIAL_ARITH] THEN
   ASM_CASES_TAC `n' < k` THEN ASM_REWRITE_TAC [TRIVIAL_ARITH]);;

let SHIFT_SUBST_COMM = prove
  (`!x f n. SHIFT 0 n (SUBST f x) = SUBST (SHIFTF n f) (SHIFT 0 n x)`,
   REPEAT GEN_TAC THEN REWRITE_TAC [SHIFT_SUBST; SUBST_SHIFT; LT] THEN
   MATCH_MP_TAC SUBST_FUN_EXTENS THEN GEN_TAC THEN
   REWRITE_TAC [o_THM; SHIFTF] THEN
   REWRITE_TAC [ARITH_RULE `~(n + n' < n) /\ (n + n') - n = n'`]);;

g `!x f g. SUBST f (SUBST g x) = SUBST (SUBST f o g) x`;;
e (DBTERM_INDUCT_TAC THEN REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC [SUBST; DBTERM_CONSTR_INJ; o_THM]);;
e (MATCH_MP_TAC SUBST_FUN_EXTENS THEN GEN_TAC);;
e (REWRITE_TAC [o_THM; SHIFTF]);;
e (COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [SHIFT_SUBST_COMM; SUBST; SHIFTF]);;
let SUBST_ASSOC = top_thm ();;

let SHIFT_LEFT_INV = prove
  (`!k n x. SUBST (SHIFTF k (\i. REF (i - n))) (SHIFT k n x) = x`,
   REPEAT GEN_TAC THEN REWRITE_TAC [SUBST_SHIFT] THEN
   MATCH_MP_TAC SUBST_LUNIT_IMP THEN
   REWRITE_TAC [SHIFTF; SHIFT; LT; IF_REF; REF_INJ] THEN ARITH_TAC);;

let SHIFT_0_LEFT_INV = MESON [SHIFT_LEFT_INV; SHIFTF_0]
  `!n x. SUBST (\i. REF (i - n)) (SHIFT 0 n x) = x`;;

(* ------------------------------------------------------------------------- *)
(*  APP0                                                                     *)
(* ------------------------------------------------------------------------- *)

let APP0_SHIFT = prove
  (`!x k n. APP0 (SHIFT k n x) = SHIFT (SUC k) n (APP0 x)`,
   REWRITE_TAC [APP0; SHIFT; LE_SHIFT_COMM_0; TRIVIAL_ARITH]);;

let SUBST_APP0 = prove
  (`!x f. SUBST f (APP0 x) = APP (SUBST (f o SUC) x) (f 0)`,
   REWRITE_TAC [APP0; SUBST; o_DEF; SUBST_SHIFT; TRIVIAL_ARITH]);;

let APP0_SUBST = prove
  (`!x f. APP0 (SUBST f x) = SUBST (SHIFTF (SUC 0) f) (APP0 x)`,
   REWRITE_TAC [APP0; SUBST; SHIFTF; SHIFT_SUBST_COMM; TRIVIAL_ARITH]);;

let APP_EQ_APP0 = prove
  (`!x y. APP x y = SUBST (\n. if n = 0 then y else REF (PRE n)) (APP0 x)`,
   REWRITE_TAC [SUBST_APP0; o_DEF; TRIVIAL_ARITH; ETA_AX; SUBST_LUNIT]);;

let dbterm_INDUCT_ALT = prove
  (`!P. (!i. P (REF i)) /\
       (!x. P x ==> P (APP0 x)) /\
       (!x. P x ==> P (ABS x)) /\
       (!f x. (!i. P (f i)) /\ P x ==> P (SUBST f x))
       ==> (!x. P x)`,
   GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC dbterm_INDUCT THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [APP_EQ_APP0] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(*  DBTERM_BETA                                                              *)
(* ------------------------------------------------------------------------- *)

let DBTERM_BETA_RULES, DBTERM_BETA_INDUCT, DBTERM_BETA_CASES =
  new_inductive_definition
  `!x y. DBTERM_BETA (APP (ABS x) y)
           (SUBST (\n. if n = 0 then y else REF (PRE n)) x)`;;

let DBTERM_BETA_THM = prove
  (`!x y z. DBTERM_BETA (APP (ABS x) y) z <=>
            z = SUBST (\n. if n = 0 then y else REF (PRE n)) x`,
   REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [DBTERM_BETA_RULES] THEN
   ONCE_REWRITE_TAC [DBTERM_BETA_CASES] THEN
   REWRITE_TAC [DBTERM_CONSTR_INJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC []);;

let SHIFT_BETA = prove
  (`!x y k n. DBTERM_BETA x y ==> DBTERM_BETA (SHIFT k n x) (SHIFT k n y)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DBTERM_BETA_CASES]) THEN
   POP_ASSUM_LIST (MAP_EVERY SUBST1_TAC) THEN
   REWRITE_TAC [SHIFT; DBTERM_BETA_THM; SHIFT_SUBST; SUBST_SHIFT] THEN
   MATCH_MP_TAC SUBST_FUN_EXTENS THEN NUM_CASES_TAC THEN
   REWRITE_TAC [TRIVIAL_ARITH; o_THM; SHIFT; IF_REF]);;

let SUBST_BETA_TERM = prove
  (`!x y f. DBTERM_BETA x y ==> DBTERM_BETA (SUBST f x) (SUBST f y)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [DBTERM_BETA_CASES]) THEN
   POP_ASSUM_LIST (MAP_EVERY SUBST1_TAC) THEN
   REWRITE_TAC [SUBST; DBTERM_BETA_THM; SUBST_ASSOC] THEN
   MATCH_MP_TAC SUBST_FUN_EXTENS THEN NUM_CASES_TAC THEN
   REWRITE_TAC [SUBST; o_THM; SHIFTF; TRIVIAL_ARITH] THEN
   REWRITE_TAC [SUBST_SHIFT; TRIVIAL_ARITH] THEN
   REWRITE_TAC [ETA_AX; SUBST_LUNIT]);;

(* ------------------------------------------------------------------------- *)
(*  DBTERM_ETA                                                               *)
(* ------------------------------------------------------------------------- *)

let DBTERM_ETA_RULES, DBTERM_ETA_INDUCT, DBTERM_ETA_CASES =
  new_inductive_definition
  `!x. DBTERM_ETA (ABS (APP (SHIFT 0 (SUC 0) x) (REF 0))) x`;;

let DBTERM_ETA_CASES_ALT = prove
  (`!x y. DBTERM_ETA x y <=> x = ABS (APP0 y)`,
   REWRITE_TAC [DBTERM_ETA_CASES; APP0]);;

let SHIFT_ETA = prove
  (`!x y k n. DBTERM_ETA x y ==> DBTERM_ETA (SHIFT k n x) (SHIFT k n y)`,
   SUBGOAL_THEN `!x y. DBTERM_ETA x y
                       ==> (!n k. DBTERM_ETA (SHIFT k n x) (SHIFT k n y))`
     (fun th -> MESON_TAC [th]) THEN
   MATCH_MP_TAC DBTERM_ETA_INDUCT THEN REPEAT GEN_TAC THEN
   REWRITE_TAC [DBTERM_ETA_CASES; SHIFT; TRIVIAL_ARITH; LE_SHIFT_COMM_0]);;

let SUBST_ETA_TERM = prove
  (`!x y f. DBTERM_ETA x y ==> DBTERM_ETA (SUBST f x) (SUBST f y)`,
   REWRITE_TAC [DBTERM_ETA_CASES_ALT] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [SUBST; APP0_SUBST]);;

(* ------------------------------------------------------------------------- *)
(*  DBTERM_REL                                                               *)
(* ------------------------------------------------------------------------- *)

let DBTERM_REL_RULES, DBTERM_REL_INDUCT, DBTERM_REL_CASES =
  new_inductive_definition
  `(!x y. R x y ==> DBTERM_REL R x y) /\
   (!x y. DBTERM_REL R x y ==> DBTERM_REL R (ABS x) (ABS y)) /\
   (!x y z. DBTERM_REL R x y ==> DBTERM_REL R (APP x z) (APP y z)) /\
   (!x y z. DBTERM_REL R x y ==> DBTERM_REL R (APP z x) (APP z y))`;;

let DBTERM_EQV = new_definition
  `!R. DBTERM_EQV R = RSTC (DBTERM_REL R)`;;

let DBTERM_EQV_INC = prove
  (`!R x y. R x y ==> DBTERM_EQV R x y`,
   SIMP_TAC [DBTERM_EQV; RSTC_INC; DBTERM_REL_RULES]);;

let DBTERM_EQV_REFL = prove
  (`!R x. DBTERM_EQV R x x`,
   REWRITE_TAC [DBTERM_EQV; RSTC_REFL]);;

let DBTERM_EQV_REFL_IMP = MESON [DBTERM_EQV_REFL]
  `!R x y. x = y ==> DBTERM_EQV R x y`;;

let DBTERM_EQV_SYM = prove
  (`!R x y. DBTERM_EQV R x y ==> DBTERM_EQV R y x`,
   REWRITE_TAC [DBTERM_EQV; RSTC_SYM]);;

let DBTERM_EQV_TRANS = prove
  (`!R x y z. DBTERM_EQV R x y /\ DBTERM_EQV R y z ==> DBTERM_EQV R x z`,
   REWRITE_TAC [DBTERM_EQV; RSTC_TRANS]);;

let DBTERM_EQV_ABS = prove
  (`!R x y. DBTERM_EQV R x y ==> DBTERM_EQV R (ABS x) (ABS y)`,
   GEN_TAC THEN REWRITE_TAC [DBTERM_EQV] THEN MATCH_MP_TAC RSTC_INDUCT THEN
   MESON_TAC [RSTC_RULES; DBTERM_REL_RULES]);;

let DBTERM_EQV_APP_L = prove
  (`!R z x y. DBTERM_EQV R x y ==> DBTERM_EQV R (APP x z) (APP y z)`,
   GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [DBTERM_EQV] THEN
   MATCH_MP_TAC RSTC_INDUCT THEN MESON_TAC [RSTC_RULES; DBTERM_REL_RULES]);;

let DBTERM_EQV_APP_R = prove
  (`!R z x y. DBTERM_EQV R x y ==> DBTERM_EQV R (APP z x) (APP z y)`,
   GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [DBTERM_EQV] THEN
   MATCH_MP_TAC RSTC_INDUCT THEN MESON_TAC [RSTC_RULES; DBTERM_REL_RULES]);;

let DBTERM_EQV_APP =
  MESON [DBTERM_EQV_TRANS; DBTERM_EQV_APP_L; DBTERM_EQV_APP_R]
  `!R x1 x2 y1 y1. DBTERM_EQV R x1 y1 /\ DBTERM_EQV R x2 y2
                   ==> DBTERM_EQV R (APP x1 x2) (APP y1 y2)`;;

let DBTERM_EQV_RULES = MESON [DBTERM_EQV_INC; DBTERM_EQV_APP; DBTERM_EQV_ABS;
                           DBTERM_EQV_REFL; DBTERM_EQV_SYM; DBTERM_EQV_TRANS]
  `!R. (!x y. R x y ==> DBTERM_EQV R x y) /\
       (!x y. DBTERM_EQV R x y ==> DBTERM_EQV R (ABS x) (ABS y)) /\
       (!x1 x2 y1 y1. DBTERM_EQV R x1 y1 /\ DBTERM_EQV R x2 y2
                      ==> DBTERM_EQV R (APP x1 x2) (APP y1 y2)) /\
       (!x. DBTERM_EQV R x x) /\
       (!x y. DBTERM_EQV R x y ==> DBTERM_EQV R y x) /\
       (!x y z. DBTERM_EQV R x y /\ DBTERM_EQV R y z ==> DBTERM_EQV R x z)`;;

let DBTERM_EQV_CASES = prove
  (`!a0 a1.
       DBTERM_EQV R a0 a1 <=>
       R a0 a1 \/
       (?x1 y1 x2 y2.
            a0 = APP x1 x2 /\ a1 = APP y1 y2 /\
            DBTERM_EQV R x1 y1 /\ DBTERM_EQV R x2 y2) \/
       (?x y. a0 = ABS x /\ a1 = ABS y /\ DBTERM_EQV R x y) \/
       DBTERM_EQV R a1 a0 \/
       (?y. DBTERM_EQV R a0 y /\ DBTERM_EQV R y a1)`,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC [DBTERM_EQV] THEN MESON_TAC [RSTC_CASES; RSTC_RULES];
    MESON_TAC [DBTERM_EQV_RULES]]);;

let DBTERM_EQV_INDUCT = prove
  (`!RR R. (!x y. R x y ==> RR x y) /\
          (!x1 y1 x2 y2.
             RR x1 y1 /\ RR x2 y2 ==> RR (APP x1 x2) (APP y1 y2)) /\
          (!x y. RR x y ==> RR (ABS x) (ABS y)) /\
          (!x. RR x x) /\
          (!x y. RR x y ==> RR y x) /\
          (!x y z. RR x y /\ RR y z ==> RR x z)
          ==> (!a0 a1. DBTERM_EQV R a0 a1 ==> RR a0 a1)`,
   GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [DBTERM_EQV] THEN
   MATCH_MP_TAC RSTC_INDUCT THEN CONJ_TAC THEN
   TRY (MATCH_MP_TAC DBTERM_REL_INDUCT) THEN ASM_MESON_TAC []);;

(* ------------------------------------------------------------------------- *)
(*  LC relation                                                              *)
(* ------------------------------------------------------------------------- *)

let LC_REL = new_definition
  `LC_REL = DBTERM_EQV (\x y. DBTERM_BETA x y \/ DBTERM_ETA x y)`;;

overload_interface ("===",`LC_REL:dbterm->dbterm->bool`);;

let LC_REL_BETA = prove
  (`!x y. DBTERM_BETA x y ==> x === y`,
   SIMP_TAC [LC_REL; DBTERM_EQV_INC]);;

let LC_REL_ETA = prove
  (`!x y. DBTERM_ETA x y ==> x === y`,
   SIMP_TAC [LC_REL; DBTERM_EQV_INC]);;

let LC_REL_ABS = prove
  (`!x y. x === y ==> ABS x === ABS y`,
   SIMP_TAC [LC_REL; DBTERM_EQV_ABS]);;

let LC_REL_APP = prove
  (`!x1 y1 x2 y2. x1 === y1 /\ x2 === y2 ==> APP x1 x2 === APP y1 y2`,
   SIMP_TAC [LC_REL; DBTERM_EQV_APP]);;

let LC_REL_REFL = prove
  (`!x. x === x`,
   REWRITE_TAC [LC_REL; DBTERM_EQV_REFL]);;

let LC_REL_SYM = prove
  (`!x y. x === y ==> y === x`,
   REWRITE_TAC [LC_REL; DBTERM_EQV_SYM]);;

let LC_REL_TRANS = prove
  (`!x y z. x === y /\ y === z ==> x === z`,
   REWRITE_TAC [LC_REL; DBTERM_EQV_TRANS]);;

let LC_REL_RULES = prove
  (`(!x y. DBTERM_BETA x y ==> x === y) /\
    (!x y. DBTERM_ETA x y ==> x === y) /\
    (!x1 y1 x2 y2. x1 === y1 /\ x2 === y2 ==> APP x1 x2 === APP y1 y2) /\
    (!x y. x === y ==> ABS x === ABS y) /\
    (!x. x === x) /\
    (!x y. x === y ==> y === x) /\
    (!x y z. x === y /\ y === z ==> x === z)`,
  REWRITE_TAC [LC_REL_REFL; LC_REL_SYM; LC_REL_BETA;
               LC_REL_ETA; LC_REL_ABS; LC_REL_APP] THEN
  MESON_TAC [LC_REL_TRANS]);;

let LC_REL_INDUCT = prove
  (`!R. (!x y. DBTERM_BETA x y ==> R x y) /\
          (!x y. DBTERM_ETA x y ==> R x y) /\
          (!x1 y1 x2 y2.
             R x1 y1 /\ R x2 y2 ==> R (APP x1 x2) (APP y1 y2)) /\
          (!x y. R x y ==> R (ABS x) (ABS y)) /\
          (!x y. R x y ==> R y x) /\
          (!x y z. R x y /\ R y z ==> R x z)
          ==> (!a0 a1. a0 === a1 ==> R a0 a1)`,
   GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [LC_REL; DBTERM_EQV] THEN
   SUBGOAL_THEN `!x:dbterm. R x x` ASSUME_TAC THENL
   [ASM_MESON_TAC [DBTERM_ETA_RULES];
    MATCH_MP_TAC RSTC_INDUCT] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DBTERM_REL_INDUCT THEN ASM_MESON_TAC []);;

let LC_REL_CASES = prove
  (`!a0 a1.
       a0 === a1 <=>
       DBTERM_BETA a0 a1 \/
       DBTERM_ETA a0 a1 \/
       (?x1 y1 x2 y2.
            a0 = APP x1 x2 /\ a1 = APP y1 y2 /\ x1 === y1 /\ x2 === y2) \/
       (?x y. a0 = ABS x /\ a1 = ABS y /\ x === y) \/
       a1 === a0 \/
       (?y. a0 === y /\ y === a1)`,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC [LC_REL] THEN MESON_TAC [DBTERM_EQV_CASES];
    ASM_MESON_TAC [LC_REL_RULES]]);;

let LC_REL_SHIFT_IMP = prove
  (`!x y k n. x === y ==> SHIFT k n x === SHIFT k n y`,
   SUBGOAL_THEN `!x y. x === y ==> !k n. SHIFT k n x === SHIFT k n y`
    (fun th -> SIMP_TAC [th]) THEN
   MATCH_MP_TAC LC_REL_INDUCT THEN REWRITE_TAC [SHIFT] THEN
   MESON_TAC [LC_REL_RULES; SHIFT_BETA; SHIFT_ETA]);;

let LC_REL_SHIFTF = prove
  (`!f g k n. (!n. f n === g n) ==> SHIFTF k f n === SHIFTF k g n`,
   REWRITE_TAC [SHIFTF] THEN ASM_MESON_TAC [LC_REL_SHIFT_IMP; LC_REL_REFL]);;

let LC_REL_SUBST_FUN = prove
  (`!x f g. (!i. f i === g i) ==> SUBST f x === SUBST g x`,
   DBTERM_INDUCT_TAC THEN ASM_SIMP_TAC [SUBST; LC_REL_APP] THEN
   ASM_MESON_TAC [LC_REL_ABS; LC_REL_SHIFTF]);;

let LC_REL_SUBST_TERM = prove
  (`!x y f. x === y ==> SUBST f x === SUBST f y`,
   SUBGOAL_THEN `!x y. x === y ==> !f. SUBST f x === SUBST f y`
     (fun th -> MESON_TAC [th]) THEN
   MATCH_MP_TAC LC_REL_INDUCT THEN REWRITE_TAC [SUBST] THEN
   ASM_MESON_TAC [LC_REL_RULES; SUBST_BETA_TERM; SUBST_ETA_TERM]);;

let LC_REL_SUBST = prove
  (`!f g x y. (!n. f n === g n) /\ x === y
              ==> SUBST f x === SUBST g y`,
   MESON_TAC [LC_REL_SUBST_TERM; LC_REL_SUBST_FUN; LC_REL_TRANS]);;

let LC_REL_SHIFT = prove
  (`!k n x y. SHIFT k n x === SHIFT k n y <=> x === y`,
   MESON_TAC [LC_REL_SHIFT_IMP; SHIFT_LEFT_INV; LC_REL_SUBST_TERM]);;

let LC_REL_APP0 = prove
  (`!x y. x === y ==> APP0 x === APP0 y`,
   REPEAT STRIP_TAC THEN REWRITE_TAC [APP0] THEN
   ASM_SIMP_TAC [LC_REL_RULES; LC_REL_SHIFT; LC_REL_REFL]);;

(* ------------------------------------------------------------------------- *)
(*  A nice consequence of eta.                                               *)
(* ------------------------------------------------------------------------- *)

let LC_REL_ABS_APP0 = prove
  (`!x. ABS (APP0 x) === x`,
   SIMP_TAC [APP0; LC_REL_ETA; DBTERM_ETA_RULES]);;

(* ------------------------------------------------------------------------- *)
(*  A nice consequence of beta.                                              *)
(* ------------------------------------------------------------------------- *)

let LC_REL_APP0_ABS = prove
  (`!x. APP0 (ABS x) === x`,
   GEN_TAC THEN REWRITE_TAC [APP0; SHIFT] THEN MATCH_MP_TAC LC_REL_BETA THEN
   REWRITE_TAC [DBTERM_BETA_THM; SHIFT_EQ_SUBST; SUBST_ASSOC] THEN
   MATCH_MP_TAC (GSYM SUBST_LUNIT_IMP) THEN NUM_CASES_TAC THEN
   REWRITE_TAC [SUBST; IF_REF; o_THM; TRIVIAL_ARITH]);;

(* ------------------------------------------------------------------------- *)
(*  How to express APP in terms of APP0 (modulo LC_REL).                     *)
(* ------------------------------------------------------------------------- *)

let LC_REL_APP_APP0 = prove
  (`!x y. APP x y === SUBST (\n. if n = 0 then y else REF (PRE n)) (APP0 x)`,
   REPEAT GEN_TAC THEN MATCH_MP_TAC LC_REL_TRANS THEN
   EXISTS_TAC `APP (ABS (APP (SHIFT 0 (SUC 0) x) (REF 0))) y` THEN
   REWRITE_TAC [APP0] THEN
   MESON_TAC [LC_REL_RULES; DBTERM_ETA_RULES; DBTERM_BETA_RULES]);;

let APP0_ABS_REL_RULES, APP0_ABS_REL_INDUCT, APP0_ABS_REL_CASES =
   new_inductive_definition
    `!x. APP0_ABS_REL (APP0 (ABS x)) x`;;

let ABS_APP0_REL_RULES, ABS_APP0_REL_INDUCT, ABS_APP0_REL_CASES =
   new_inductive_definition
    `!x. ABS_APP0_REL (ABS (APP0 x)) x`;;

(*
prove
  (`!x y. DBTERM_EQV (\x y. APP0_ABS_REL x y \/ ABS_APP0_REL x y) x y
         ==> x === y`,
   MATCH_MP_TAC DBTERM_EQV_INDUCT THEN
   REWRITE_TAC [APP0_ABS_REL_CASES; ABS_APP0_REL_CASES] THEN
   MESON_TAC [LC_REL_RULES; LC_REL_ABS_APP0; LC_REL_APP0_ABS]);;
*)

(* ------------------------------------------------------------------------- *)
(*  Alternative, equivalent, definition of the beta-eta relation.            *)
(* ------------------------------------------------------------------------- *)

let DBTERM_ETA_INDUCT_ALT = prove
  (`!DBTERM_ETA'. (!x. DBTERM_ETA' (ABS (APP0 x)) x)
              ==> (!a0 a1. DBTERM_ETA a0 a1 ==> DBTERM_ETA' a0 a1)`,
    SIMP_TAC [DBTERM_ETA_CASES_ALT]);;

let DBTERM_REL0_RULES, DBTERM_REL0_INDUCT, DBTERM_REL0_CASES =
  new_inductive_definition
  `(!x y. R x y ==> DBTERM_REL0 R x y) /\
   (!x y. DBTERM_REL0 R x y ==> DBTERM_REL0 R (ABS x) (ABS y)) /\
   (!x y. DBTERM_REL0 R x y ==> DBTERM_REL0 R (APP0 x) (APP0 y)) /\
   (!f x y. DBTERM_REL0 R x y ==> DBTERM_REL0 R (SUBST f x) (SUBST f y)) /\
   (!f g x. (?n. DBTERM_REL0 R (f n) (g n) /\ (!i. i = n \/  f i = g i))
            ==> DBTERM_REL0 R (SUBST f x) (SUBST g x))`;;

let DBTERM_REL0_SUBST_TERM = MESON [DBTERM_REL0_RULES]
  `!f x y. DBTERM_REL0 R x y ==> DBTERM_REL0 R (SUBST f x) (SUBST f y)`;;

let DBTERM_REL0_SUBST_FUN = MESON [DBTERM_REL0_RULES]
   `!f g x. (?n. DBTERM_REL0 R (f n) (g n) /\ (!i. i = n \/  f i = g i))
            ==> DBTERM_REL0 R (SUBST f x) (SUBST g x)`;;

let DBTERM_REL0_SHIFT = prove
  (`!R k n x y. DBTERM_REL0 R x y
                ==> DBTERM_REL0 R (SHIFT k n x) (SHIFT k n y)`,
   SIMP_TAC [SHIFT_EQ_SUBST; DBTERM_REL0_SUBST_TERM]);;

let DBTERM_REL0_APP_L = prove
  (`!R z x y. DBTERM_REL0 R x y ==> DBTERM_REL0 R (APP x z) (APP y z)`,
   SIMP_TAC [APP_EQ_APP0; DBTERM_REL0_RULES]);;

let DBTERM_REL0_APP_R = prove
  (`!R z x y. DBTERM_REL0 R x y ==> DBTERM_REL0 R (APP z x) (APP z y)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC [APP_EQ_APP0] THEN
   MATCH_MP_TAC DBTERM_REL0_SUBST_FUN THEN ASM_MESON_TAC []);;

let DBTERM_EQV0 = new_definition
  `!R. DBTERM_EQV0 R = RSTC (DBTERM_REL0 R)`;;

let DBTERM_EQV0_INDUCT = prove
  (`!E R. (!x y. R x y ==> E x y) /\
          (!x y. E x y ==> E (APP0 x) (APP0 y)) /\
          (!x y. E x y ==> E (ABS x) (ABS y)) /\
  	  (!f x y. E x y ==> E (SUBST f x) (SUBST f y)) /\
   	  (!f g x. (?n. E (f n) (g n) /\ (!i. i = n \/  f i = g i))
                   ==> E (SUBST f x) (SUBST g x)) /\
          (!x. E x x) /\
          (!x y. E x y ==> E y x) /\
          (!x y z. E x y /\ E y z ==> E x z)
          ==> (!a0 a1. DBTERM_EQV0 R a0 a1 ==> E a0 a1)`,
   GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC [DBTERM_EQV0] THEN MATCH_MP_TAC RSTC_INDUCT THEN
   REPEAT CONJ_TAC THEN ASM_SIMP_TAC [] THENL
   [MATCH_MP_TAC DBTERM_REL0_INDUCT THEN ASM_SIMP_TAC [];
    ASM_MESON_TAC []]);;

let DBTERM_EQV0_INC = prove
  (`!R x y. R x y ==> DBTERM_EQV0 R x y`,
   SIMP_TAC [DBTERM_EQV0; RSTC_INC; DBTERM_REL0_RULES]);;

let DBTERM_EQV0_REFL = prove
  (`!R x. DBTERM_EQV0 R x x`,
   REWRITE_TAC [DBTERM_EQV0; RSTC_REFL]);;

let DBTERM_EQV0_REFL_IMP = MESON [DBTERM_EQV0_REFL]
  `!R x y. x = y ==> DBTERM_EQV0 R x y`;;

let DBTERM_EQV0_SYM = prove
  (`!R x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R y x`,
   REWRITE_TAC [DBTERM_EQV0; RSTC_SYM]);;

let DBTERM_EQV0_TRANS = prove
  (`!R x y z. DBTERM_EQV0 R x y /\ DBTERM_EQV0 R y z ==> DBTERM_EQV0 R x z`,
   REWRITE_TAC [DBTERM_EQV0; RSTC_TRANS]);;

let DBTERM_EQV0_ABS = prove
  (`!R x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (ABS x) (ABS y)`,
   GEN_TAC THEN REWRITE_TAC [DBTERM_EQV0] THEN MATCH_MP_TAC RSTC_INDUCT THEN
   MESON_TAC [RSTC_RULES; DBTERM_REL0_RULES]);;

let DBTERM_EQV0_APP0 = prove
  (`!R x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (APP0 x) (APP0 y)`,
   GEN_TAC THEN REWRITE_TAC [DBTERM_EQV0] THEN MATCH_MP_TAC RSTC_INDUCT THEN
   MESON_TAC [RSTC_RULES; DBTERM_REL0_RULES]);;

let DBTERM_EQV0_SUBST_TERM = prove
  (`!R f x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (SUBST f x) (SUBST f y)`,
   GEN_TAC THEN
   SUBGOAL_THEN `!x y. DBTERM_EQV0 R x y
                       ==> !f. DBTERM_EQV0 R (SUBST f x) (SUBST f y)`
     (fun th -> MESON_TAC [th]) THEN
   REWRITE_TAC [DBTERM_EQV0] THEN MATCH_MP_TAC RSTC_INDUCT THEN
   MESON_TAC [RSTC_RULES; DBTERM_REL0_RULES]);;

let DBTERM_EQV0_SHIFT = prove
  (`!R k n x y. DBTERM_EQV0 R x y
                ==> DBTERM_EQV0 R (SHIFT n k x) (SHIFT n k y)`,
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [DBTERM_EQV0] THEN
   MATCH_MP_TAC RSTC_INDUCT THEN MESON_TAC [RSTC_RULES; DBTERM_REL0_SHIFT]);;

let DBTERM_EQV0_APP_L = prove
  (`!R z x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (APP x z) (APP y z)`,
   GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [DBTERM_EQV0] THEN
   MATCH_MP_TAC RSTC_INDUCT THEN
   MESON_TAC [RSTC_RULES; DBTERM_REL0_RULES; DBTERM_REL0_APP_L]);;

let DBTERM_EQV0_APP_R = prove
  (`!R z x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (APP z x) (APP z y)`,
   GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [DBTERM_EQV0] THEN
   MATCH_MP_TAC RSTC_INDUCT THEN
   MESON_TAC [RSTC_RULES; DBTERM_REL0_RULES; DBTERM_REL0_APP_R]);;

let DBTERM_EQV0_APP = prove
  (`!R x1 y1 x2 y2. DBTERM_EQV0 R x1 y1 /\ DBTERM_EQV0 R x2 y2
                    ==> DBTERM_EQV0 R (APP x1 x2) (APP y1 y2)`,
   MESON_TAC [DBTERM_EQV0_APP_L; DBTERM_EQV0_APP_R; DBTERM_EQV0_TRANS]);;

let DBTERM_EQV0_SUBST_FUN = prove
  (`!R x f g. (?n. DBTERM_EQV0 R (f n) (g n) /\ (!i. i = n \/  f i = g i))
             ==> DBTERM_EQV0 R (SUBST f x) (SUBST g x)`,
   GEN_TAC THEN DBTERM_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC [SUBST] THENL
   [ASM_MESON_TAC [DBTERM_EQV0_REFL];
    MATCH_MP_TAC DBTERM_EQV0_APP THEN ASM_MESON_TAC [];
    MATCH_MP_TAC DBTERM_EQV0_ABS THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `SUC n` THEN CONJ_TAC THENL
    [ASM_SIMP_TAC [SHIFTF; DBTERM_EQV0_SHIFT; TRIVIAL_ARITH];
     NUM_CASES_TAC THEN REWRITE_TAC [SHIFTF; TRIVIAL_ARITH; SHIFT_INJ] THEN
     ASM_MESON_TAC[]]]);;

let DBTERM_EQV0_RULES = MESON [DBTERM_EQV0_INC; DBTERM_EQV0_APP0;
                               DBTERM_EQV0_ABS; DBTERM_EQV0_SUBST_TERM;
 			       DBTERM_EQV0_SUBST_FUN; DBTERM_EQV0_REFL;
 			       DBTERM_EQV0_SYM; DBTERM_EQV0_TRANS]
  `!R. (!x y. R x y ==> DBTERM_EQV0 R x y) /\
       (!x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (ABS x) (ABS y)) /\
       (!x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (APP0 x) (APP0 y)) /\
       (!f x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R (SUBST f x) (SUBST f y)) /\
       (!f g x. (?n. DBTERM_EQV0 R (f n) (g n) /\ (!i. i = n \/  f i = g i))
                ==> DBTERM_EQV0 R (SUBST f x) (SUBST g x)) /\
       (!x. DBTERM_EQV0 R x x) /\
       (!x y. DBTERM_EQV0 R x y ==> DBTERM_EQV0 R y x) /\
       (!x y z. DBTERM_EQV0 R x y /\ DBTERM_EQV0 R y z
                ==> DBTERM_EQV0 R x z)`;;

let DBTERM_EQV0_CASES = prove
  (`!a0 a1.
       DBTERM_EQV0 R a0 a1 <=>
       R a0 a1 \/
       (?x y. a0 = APP0 x /\ a1 = APP0 y /\ DBTERM_EQV0 R x y) \/
       (?x y. a0 = ABS x /\ a1 = ABS y /\ DBTERM_EQV0 R x y) \/
       (?f x y. a0 = SUBST f x /\ a1 = SUBST f y /\ DBTERM_EQV0 R x y) \/
       (?f g x n. a0 = SUBST f x /\ a1 = SUBST g x /\
                  DBTERM_EQV0 R (f n) (g n) /\
		  (!i. n = i \/ f i = g i)) \/
       DBTERM_EQV0 R a1 a0 \/
       (?y. DBTERM_EQV0 R a0 y /\ DBTERM_EQV0 R y a1)`,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC [DBTERM_EQV0] THEN MESON_TAC [RSTC_CASES; RSTC_RULES];
    MESON_TAC [DBTERM_EQV0_RULES]]);;

let BETA_IMP_APP0_ABS_REL = prove
  (`!x y. DBTERM_BETA x y ==> DBTERM_EQV0 APP0_ABS_REL x y`,
   MATCH_MP_TAC DBTERM_BETA_INDUCT THEN
   SIMP_TAC [APP_EQ_APP0; DBTERM_EQV0_SUBST_TERM; DBTERM_EQV0_INC;
             APP0_ABS_REL_CASES]);;

let ETA_IMP_ABS_APP0_REL = prove
  (`!x y. DBTERM_ETA x y ==> DBTERM_EQV0 ABS_APP0_REL x y`,
   MATCH_MP_TAC DBTERM_ETA_INDUCT_ALT THEN
   SIMP_TAC [DBTERM_EQV0_INC; ABS_APP0_REL_CASES]);;

let LC_REL_IMP_APP0_ABS_OR_ABS_APP0 = prove
  (`!x y. x === y
         ==> DBTERM_EQV0 (\x y. APP0_ABS_REL x y \/ ABS_APP0_REL x y) x y`,
   MATCH_MP_TAC LC_REL_INDUCT THEN REPEAT CONJ_TAC THEN
   SIMP_TAC [DBTERM_EQV0_APP; DBTERM_EQV0_ABS; DBTERM_EQV0_SYM] THENL
   [MATCH_MP_TAC DBTERM_BETA_INDUCT THEN
    SIMP_TAC [APP_EQ_APP0; DBTERM_EQV0_SUBST_TERM; DBTERM_EQV0_INC;
              APP0_ABS_REL_CASES];
    MATCH_MP_TAC DBTERM_ETA_INDUCT_ALT THEN
    SIMP_TAC [DBTERM_EQV0_INC; ABS_APP0_REL_CASES];
    MESON_TAC [DBTERM_EQV0_TRANS]]);;

let APP0_ABS_IMP_LC_REL = prove
  (`!x y. APP0_ABS_REL x y ==> x === y`,
   MATCH_MP_TAC APP0_ABS_REL_INDUCT THEN REWRITE_TAC [LC_REL_APP0_ABS]);;

let ABS_APP0_IMP_LC_REL = prove
  (`!x y. ABS_APP0_REL x y ==> x === y`,
   MATCH_MP_TAC ABS_APP0_REL_INDUCT THEN REWRITE_TAC [LC_REL_ABS_APP0]);;

let APP0_ABS_OR_ABS_APP0_IMP_LC_REL = prove
  (`!x y. DBTERM_EQV0 (\x y. APP0_ABS_REL x y \/ ABS_APP0_REL x y) x y
          ==> x === y`,
   REWRITE_TAC [DBTERM_EQV0] THEN MATCH_MP_TAC RSTC_INDUCT THEN
   SIMP_TAC [LC_REL_REFL; LC_REL_SYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DBTERM_REL0_INDUCT THEN
    SIMP_TAC [LC_REL_APP0; LC_REL_ABS; LC_REL_SUBST_TERM] THEN
    CONJ_TAC THENL
    [MESON_TAC [APP0_ABS_IMP_LC_REL; ABS_APP0_IMP_LC_REL];
     REPEAT STRIP_TAC THEN MATCH_MP_TAC LC_REL_SUBST_FUN THEN
     ASM_MESON_TAC [LC_REL_REFL]];
    MESON_TAC [LC_REL_TRANS]]);;

let LC_REL_ALT = MESON [APP0_ABS_OR_ABS_APP0_IMP_LC_REL;
                     LC_REL_IMP_APP0_ABS_OR_ABS_APP0]
   `!x y. x === y <=>
          DBTERM_EQV0 (\x y. APP0_ABS_REL x y \/ ABS_APP0_REL x y) x y`;;
