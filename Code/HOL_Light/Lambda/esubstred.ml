(* ========================================================================= *)
(* Explicit substitution reduction rules.                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Additional lemmas.                                                        *)
(* ------------------------------------------------------------------------- *)

let SHIFTI_0 = prove
 (`!k. SHIFTI k 0 = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; SHIFTI_EQ_REINDEX] THEN
  REWRITE_TAC[REINDEX_ID; ITER_SLIDE] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reduction relation for unary substitution.                                *)
(* ------------------------------------------------------------------------- *)

let ESUBSTRED_RULES,ESUBSTRED_INDUCT,ESUBSTRED_CASES = new_inductive_definition
  `(!k i. ESUBSTRED u k (REF i)
                        (if i = k then SHIFTI 0 k u else
                         if i < k then REF i else REF (i - 1))) /\
   (!k x x' y y'. ESUBSTRED u k x x' /\ ESUBSTRED u k y y'
                  ==> ESUBSTRED u k (APP x y) (APP x' y')) /\
   (!k x x'. ESUBSTRED u (SUC k) x x' ==> ESUBSTRED u k (ABS x) (ABS x'))`;;

let ESUBSTRED_INVERSION = prove
 (`(!k i a. ESUBSTRED u k (REF i) a <=>
           a = (if i = k then SHIFTI 0 k u else
                if i < k then REF i else REF (i - 1))) /\
   (!k x y a. ESUBSTRED u k (APP x y) a <=>
              ?x' y'. a = APP x' y' /\
                      ESUBSTRED u k x x' /\
                      ESUBSTRED u k y y') /\
   (!k x a. ESUBSTRED u k (ABS x) a <=>
            ?x'. a = ABS x' /\ ESUBSTRED u (SUC k) x x')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ESUBSTRED_CASES] THEN
  REWRITE_TAC[injectivity "dblambda"; distinctness "dblambda"; UNWIND_THM1;
              RIGHT_EXISTS_AND_THM; GSYM CONJ_ASSOC]);;

let ESUBSTRED_SUBSTI1 = prove
 (`!u x k. ESUBSTRED u k x (SUBSTI1 k u x)`,
  GEN_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ESUBSTRED_INVERSION; SUBSTI1; injectivity "dblambda";
                  ADD1; UNWIND_THM1; RIGHT_EXISTS_AND_THM; GSYM CONJ_ASSOC]);;

let ESUBSTRED_SUBSTI1_INVERSION = prove
 (`!u k x a. ESUBSTRED u k x a ==> a = SUBSTI1 k u x`,
  GEN_TAC THEN MATCH_MP_TAC ESUBSTRED_INDUCT THEN
  REWRITE_TAC[SUBSTI1; ADD1; injectivity "dblambda"]);;

let ESUBSTRED_SUBSTI1_EQ = prove
 (`!u k x a. ESUBSTRED u k x a <=> a = SUBSTI1 k u x`,
  MESON_TAC[ESUBSTRED_SUBSTI1_INVERSION; ESUBSTRED_SUBSTI1]);;

(* ------------------------------------------------------------------------- *)
(* Compatibility of ESUBSTRED with reindexing and parallel substitution.     *)
(* ------------------------------------------------------------------------- *)

let ESUBSTRED_REINDEX = prove
 (`!u k f x y. ESUBSTRED u k x y
               ==> ESUBSTRED (REINDEX f u) k
                             (REINDEX (ITER (SUC k) SLIDE f) x)
                             (REINDEX (ITER k SLIDE f) y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ESUBSTRED_SUBSTI1_EQ] THEN
  DISCH_THEN SUBST_VAR_TAC THEN REWRITE_TAC[REINDEX_SUBSTI1]);;

let ESUBSTRED_SUBST = prove
 (`!u k f x y. ESUBSTRED u k x y
               ==> ESUBSTRED (SUBST f u) k
                             (SUBST (ITER (SUC k) DERIV f) x)
                             (SUBST (ITER k DERIV f) y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ESUBSTRED_SUBSTI1_EQ] THEN
  DISCH_THEN SUBST_VAR_TAC THEN REWRITE_TAC[SUBST_SUBSTII1]);;
