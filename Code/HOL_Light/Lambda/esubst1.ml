(* ========================================================================= *)
(* Unary explict substitution.                                               *)
(* ========================================================================= *)

(* 
loadt "Lambda/make.ml";;
*)

(* ------------------------------------------------------------------------- *)
(* Datatype for lambda terms with explicit substitution.                     *)
(* ------------------------------------------------------------------------- *)

let eterm_INDUCT,eterm_RECUR = define_type
  "eterm  = EREF num
          | EAPP eterm eterm
          | EABS eterm
          | ESUBST eterm eterm";;

(* ------------------------------------------------------------------------- *)
(* Free references occurring in a lambda term.                               *)
(* ------------------------------------------------------------------------- *)

(*
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
  REWRITE_TAC[distinctness "eterm"; injectivity "eterm"] THEN
  MESON_TAC[]);;

let FREES_CLAUSES = prove
 (`(!i. FREES (REF i) = {i}) /\
   (!x y. FREES (APP x y) = FREES x UNION FREES y) /\
   (!x. FREES (ABS x) = {i | SUC i IN FREES x})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FREES_INVERSION] THEN SET_TAC[]);;
*)

(* ------------------------------------------------------------------------- *)
(* Reindexing operator (functoriality).                                      *)
(* ------------------------------------------------------------------------- *)

let EREINDEX = new_recursive_definition eterm_RECUR
  `(!f i. EREINDEX f (EREF i) = EREF (f i)) /\
   (!f x y. EREINDEX f (EAPP x y) = EAPP (EREINDEX f x) (EREINDEX f y)) /\
   (!f x. EREINDEX f (EABS x) = EABS (EREINDEX (SLIDE f) x)) /\
   (!f x y. EREINDEX f (ESUBST x y) =
            ESUBST (EREINDEX (SLIDE f) x) (EREINDEX f y))`;;

let EREINDEX_I = prove
 (`!x. EREINDEX I x = x`,
  MATCH_MP_TAC eterm_INDUCT THEN
  ASM_REWRITE_TAC[EREINDEX; injectivity "eterm"; SLIDE_I; I_THM]);;

(* 
let EREINDEX_EXTENS = prove
 (`!x f g. (!i. i IN FREES x ==> f i = g i) ==> EREINDEX f x = EREINDEX g x`,
  DBLAMBDA_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[FREES_INVERSION; EREINDEX] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[injectivity "eterm"] THEN ASM_SIMP_TAC[] THENL
  [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; SUC_INJ] THEN ASM_SIMP_TAC[]);;

let EREINDEX_EXTENS_EQ = prove
 (`!x f g. EREINDEX f x = EREINDEX g x <=> (!i. i IN FREES x ==> f i = g i)`,
  SUBGOAL_THEN
    `!x f g i. EREINDEX f x = EREINDEX g x /\ i IN FREES x ==> f i = g i`
    (fun th -> MESON_TAC[th; EREINDEX_EXTENS]) THEN
  DBLAMBDA_INDUCT_TAC THEN
  REWRITE_TAC[EREINDEX; injectivity "eterm"; FREES_INVERSION] THEN
  SIMP_TAC[] THENL [ASM_MESON_TAC[]; REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN `SLIDE f (SUC i) = SLIDE g (SUC i)` MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
   REWRITE_TAC[SLIDE; SUC_INJ]]);;

let EREINDEX_ID = prove
 (`!x f. EREINDEX f x = x <=> (!i. i IN FREES x ==> f i = i)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM EREINDEX_I] THEN
  REWRITE_TAC[EREINDEX_EXTENS_EQ; I_THM]);;
*)

let EREINDEX_EREINDEX = prove
 (`!x f g. EREINDEX g (EREINDEX f x) = EREINDEX (g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EREINDEX; o_THM; injectivity "eterm"] THEN
  REWRITE_TAC[o_DEF; SLIDE_SLIDE; ETA_AX]);;

(*
let EREINDEX_INJ = prove
 (`!x y f. (!i j. f i = f j ==> i = j)
           ==> (EREINDEX f x = EREINDEX f y <=> x = y)`,
  DBLAMBDA_INDUCT_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EREINDEX; distinctness "eterm"] THEN
  REWRITE_TAC[injectivity "eterm"] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[SLIDE_INJ]);;
*)

(* ------------------------------------------------------------------------- *)
(* Derivation operator (needed for the substitution right next).             *)
(* ------------------------------------------------------------------------- *)

let EDERIV = new_recursive_definition num_RECURSION
  `(!f. EDERIV f 0 = EREF 0) /\
   (!f i. EDERIV f (SUC i) = EREINDEX SUC (f i))`;;

let EDERIV_EREF = prove
 (`EDERIV EREF = EREF`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN REWRITE_TAC[EDERIV; EREINDEX]);;

(* 
let EDERIV_EXTENS = prove
 (`!f g i. EDERIV f i = EDERIV g i <=> i = 0 \/ f (PRE i) = g (PRE i)`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; NOT_SUC; PRE] THEN SIMP_TAC[EREINDEX_INJ; SUC_INJ]);;
 *)

let EDERIV_SLIDE = prove
 (`!f g i. EDERIV g (SLIDE f i) = EDERIV (g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; SLIDE; o_THM]);;

let EDERIV_O_SUC = prove
 (`!f. EDERIV f o SUC = EREINDEX SUC o f`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; EDERIV]);;

(* ------------------------------------------------------------------------- *)
(* Parallel capture-avoiding substitution (higher-order style).              *)
(* ------------------------------------------------------------------------- *)

let MSUBST = new_recursive_definition eterm_RECUR
  `(!f i. MSUBST f (EREF i) = f i) /\
   (!f x y. MSUBST f (EAPP x y) = EAPP (MSUBST f x) (MSUBST f y)) /\
   (!f x. MSUBST f (EABS x) = EABS (MSUBST (EDERIV f) x)) /\
   (!f x y. MSUBST f (ESUBST x y) =
            ESUBST (MSUBST (EDERIV f) x) (MSUBST f y))`;;

let MSUBST_EREF = prove
 (`!x. MSUBST EREF x = x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MSUBST; EDERIV_EREF]);;

(* let MSUBST_EXTENS = prove
 (`!x f g. MSUBST f x = MSUBST g x <=> (!i. i IN FREES x ==> f i = g i)`,
  ASM_REWRITE_TAC[MSUBST; FREES_INVERSION; DERIV_EXTENS;
                  injectivity "eterm"; FORALL_UNWIND_THM2] THENL
  [MESON_TAC[]; REPEAT GEN_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_NUM_THM] THEN
  REWRITE_TAC[PRE; NOT_SUC]);;

let SUBST_REF_EQ = prove
 (`!x f. MSUBST f x = x <=> (!i. i IN FREES x ==> f i = REF i)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `MSUBST f x = MSUBST REF x` THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBST_REF]; REWRITE_TAC[SUBST_EXTENS]]);;
*)

let MSUBST_EREINDEX = prove
 (`!x f g. MSUBST g (EREINDEX f x) = MSUBST (g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MSUBST; EREINDEX; o_THM; injectivity "eterm"] THEN
  REWRITE_TAC[o_DEF; EDERIV_SLIDE; ETA_AX]);;

let EREINDEX_SLIDE = prove
 (`!g f i. EREINDEX (SLIDE g) (EDERIV f i) = EDERIV (EREINDEX g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; EREINDEX; SLIDE; o_THM; EREINDEX_EREINDEX] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE]);;

let EREINDEX_MSUBST = prove
 (`!x f g. EREINDEX g (MSUBST f x) = MSUBST (EREINDEX g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EREINDEX; MSUBST; o_THM; injectivity "eterm"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; EREINDEX_SLIDE]);;

let ESUBST_EDERIV = prove
 (`!f g i. MSUBST (EDERIV g) (EDERIV f i) = EDERIV (MSUBST g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; MSUBST; MSUBST_EREINDEX; EREINDEX_MSUBST; o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; EDERIV]);;

let MSUBST_MSUBST = prove
 (`!x f g. MSUBST g (MSUBST f x) = MSUBST (MSUBST g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MSUBST; o_THM; injectivity "eterm"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; ESUBST_EDERIV]);;

let EREINDEX_EQ_SUBST = prove
 (`!f. EREINDEX f = MSUBST (EREF o f)`,
  SUBGOAL_THEN `!x f. EREINDEX f x = MSUBST (EREF o f) x`
    (fun th -> REWRITE_TAC[th; FUN_EQ_THM]) THEN
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EREINDEX; MSUBST; o_THM; injectivity "eterm"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; EDERIV; o_THM; EREINDEX]);;

(* ------------------------------------------------------------------------- *)
(* Classical definition of linear (capture-avoiding) substitution.           *)
(* ------------------------------------------------------------------------- *)

let MSHIFTI = new_recursive_definition eterm_RECUR
  `(!k n i. MSHIFTI k n (EREF i) = EREF (if i < k then i else n + i)) /\
   (!k n x y. MSHIFTI k n (EAPP x y) = EAPP (MSHIFTI k n x) (MSHIFTI k n y)) /\
   (!k n x. MSHIFTI k n (EABS x) = EABS (MSHIFTI (SUC k) n x)) /\
   (!k n x y. MSHIFTI k n (ESUBST x y) =
              ESUBST (MSHIFTI (SUC k) n x) (MSHIFTI k n y))`;;

let MSUBSTI1 = new_recursive_definition eterm_RECUR
  `(!k w i. MSUBSTI1 k w (EREF i) = if i = k then MSHIFTI 0 k w
                                  else if i < k then EREF i
                                  else EREF (i-1)) /\
   (!k w t u. MSUBSTI1 k w (EAPP t u) =
              EAPP (MSUBSTI1 k w t) (MSUBSTI1 k w u)) /\
   (!k w t. MSUBSTI1 k w (EABS t) = EABS (MSUBSTI1 (k+1) w t)) /\
   (!k w t u. MSUBSTI1 k w (ESUBST t u) =
              ESUBST (MSUBSTI1 (k+1) w t) (MSUBSTI1 k w u))`;;

let MSUBST1 = new_definition
  `MSUBST1 u t = MSUBSTI1 0 u t`;;

(* ------------------------------------------------------------------------- *)
(* Link between linear and parallel substitution.                            *)
(* ------------------------------------------------------------------------- *)

let MSHIFTI_EQ_EREINDEX = prove
 (`!n t k. MSHIFTI k n t = EREINDEX (ITER k SLIDE ((+) n)) t`,
  GEN_TAC THEN MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MSHIFTI; EREINDEX; injectivity "eterm"; ITER_SLIDE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; ITER]);;

let MSHIFTI_0 = prove
 (`!x k. MSHIFTI k 0 x = x`,
  MATCH_MP_TAC eterm_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MSHIFTI; injectivity "eterm"] THEN
  ARITH_TAC);;

let ITER_EDERIV = prove
 (`!i a.
     ITER i EDERIV (\i. if i = 0 then u else EREF (i - 1)) a =
     if a = i then MSHIFTI 0 i u else if a < i then EREF a else EREF (a - 1)`,
  INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[ITER] THENL
  [REWRITE_TAC[ARITH_RULE `~(a < 0)`; MSHIFTI_0]; CASES_TAC `a:num`] THEN
  REWRITE_TAC[ARITH_RULE `0 < SUC i`; NOT_SUC; EDERIV] THEN
  ASM_REWRITE_TAC[SUC_INJ; LT_SUC] THEN
  ASM_CASES_TAC `n = i:num` THEN ASM_REWRITE_TAC[MSHIFTI_EQ_EREINDEX] THENL
  [REWRITE_TAC[EREINDEX_EREINDEX; ITER] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; ADD];
   COND_CASES_TAC THEN ASM_REWRITE_TAC[EREINDEX; injectivity "eterm"] THEN
   ASM_ARITH_TAC]);;

let MSUBSTI1_EQ_MSUBST = prove
 (`!u t i. MSUBSTI1 i u t =
           MSUBST (ITER i EDERIV (\i. if i = 0 then u else EREF (i - 1))) t`,
  GEN_TAC THEN MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MSUBST1; MSUBSTI1; MSUBST; injectivity "eterm"] THEN
  REWRITE_TAC[ITER_EDERIV; GSYM ADD1; ITER]);;
(* 
let MSUBST_PUSHENV_LEMMA = prove
 (`!f x i. MSUBST (PUSHENV (MSUBST f y) EREF) (EDERIV f i) =
           MSUBST f (PUSHENV y EREF i)`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[PUSHENV; EDERIV; MSUBST; MSUBST_EREINDEX] THEN
  TRANS_TAC EQ_TRANS `MSUBST EREF (f (n:num))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[MSUBST_EREF]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; MSUBST; PUSHENV]);; *)

let MSUBST1_EQ_MSUBST = prove
 (`!t u. MSUBST1 u t = MSUBST (PUSHENV u EREF) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MSUBST1; MSUBSTI1_EQ_MSUBST; ITER] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN CASES_GEN_TAC THEN
  REWRITE_TAC[NOT_SUC; PUSHENV; injectivity "eterm"] THEN ARITH_TAC);;

let MSUBST1_MSUBST1 = prove
 (`!t u w. MSUBST1 w (MSUBST1 u t) = MSUBST1 (MSUBST1 w u) (MSUBSTI1 1 w t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MSUBST1_EQ_MSUBST; MSUBSTI1_EQ_MSUBST; MSUBST_MSUBST;
              ITER_BINARY; o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[EDERIV; MSUBST; PUSHENV; MSUBST_EREINDEX] THEN
  CASES_TAC `n:num` THEN REWRITE_TAC[PUSHENV; NOT_SUC; MSUBST; o_THM] THENL
  [ALL_TAC; REWRITE_TAC[injectivity "eterm"] THEN ARITH_TAC] THEN
  TRANS_TAC EQ_TRANS `MSUBST EREF w` THEN
  CONJ_TAC THENL [REWRITE_TAC[MSUBST_EREF]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; PUSHENV]);;

(* ------------------------------------------------------------------------- *)
(* Interpretation in standard lambda calculus.                               *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_OF_ETERM = new_recursive_definition eterm_RECUR
  `(!i. DBLAMBDA_OF_ETERM (EREF i) = REF i) /\
   (!x y. DBLAMBDA_OF_ETERM (EAPP x y) =
          APP (DBLAMBDA_OF_ETERM x) (DBLAMBDA_OF_ETERM y)) /\
   (!x. DBLAMBDA_OF_ETERM (EABS x) = ABS (DBLAMBDA_OF_ETERM x)) /\
   (!x y. DBLAMBDA_OF_ETERM (ESUBST x y) =
          SUBST1 (DBLAMBDA_OF_ETERM y) (DBLAMBDA_OF_ETERM x))`;;

let DBLAMBDA_OF_ETERM_EREINDEX = prove
 (`!x f. DBLAMBDA_OF_ETERM (EREINDEX f x) = REINDEX f (DBLAMBDA_OF_ETERM x)`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[DBLAMBDA_OF_ETERM; EREINDEX; REINDEX;
                  injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST1_EQ_SUBST; SUBST_REINDEX; REINDEX_SUBST] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; PUSHENV; REINDEX]);;

let DBLAMBDA_OF_ETERM_MSUBST = prove
 (`!x f. DBLAMBDA_OF_ETERM (MSUBST f x) =
         SUBST (DBLAMBDA_OF_ETERM o f) (DBLAMBDA_OF_ETERM x)`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[DBLAMBDA_OF_ETERM; MSUBST; SUBST; o_THM;
                  injectivity "dblambda"; SUBST1_EQ_SUBST;
                  DBLAMBDA_OF_ETERM_EREINDEX; SUBST_SUBST] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; DERIV; DBLAMBDA_OF_ETERM;
              DBLAMBDA_OF_ETERM_EREINDEX; o_THM] THEN
  REWRITE_TAC[SUBST; PUSHENV; SUBST_REINDEX; o_THM] THEN
  TRANS_TAC EQ_TRANS `SUBST REF (DBLAMBDA_OF_ETERM (f (n:num)))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUBST_REF]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[o_THM; PUSHENV]);;
