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
  "eterm = EREF num
         | EAPP eterm eterm
         | EABS eterm
         | ESUBST num eterm eterm";;

(* ------------------------------------------------------------------------- *)
(* Reindexing operator (functoriality).                                      *)
(* ------------------------------------------------------------------------- *)

let IREINDEX = new_recursive_definition eterm_RECUR
  `(!f i. IREINDEX f (EREF i) = EREF (f i)) /\
   (!f x y. IREINDEX f (EAPP x y) = EAPP (IREINDEX f x) (IREINDEX f y)) /\
   (!f x. IREINDEX f (EABS x) = EABS (IREINDEX (SLIDE f) x)) /\
   (!k f x y. IREINDEX f (ESUBST k x y) =
            ESUBST k (IREINDEX (SLIDE f) x) (IREINDEX f y))`;;

let SLIDE_EXTENS = prove
 (`!f g i. (!i. f i = g i) ==> SLIDE f i = SLIDE g i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN SIMP_TAC[SLIDE]);;

let IREINDEX_I = prove
 (`!x. IREINDEX I x = x`,
  MATCH_MP_TAC eterm_INDUCT THEN
  ASM_REWRITE_TAC[IREINDEX; injectivity "eterm"; SLIDE_I; I_THM]);;

let IREINDEX_SIMPLE_EXTENS = prove
 (`!x f g. (!i. f i = g i) ==> IREINDEX f x = IREINDEX g x`,
  MATCH_MP_TAC eterm_INDUCT THEN REWRITE_TAC[IREINDEX; injectivity "eterm"] THEN
  MESON_TAC[SLIDE_EXTENS]);;

let EREINDEX_EREINDEX = prove
 (`!x f g. IREINDEX g (IREINDEX f x) = IREINDEX (g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IREINDEX; o_THM; injectivity "eterm"] THEN
  MATCH_MP_TAC IREINDEX_SIMPLE_EXTENS THEN REWRITE_TAC[o_THM; SLIDE_SLIDE]);;

let IREINDEX_INJ = prove
 (`!x y f. (!i j. f i = f j ==> i = j)
           ==> (IREINDEX f x = IREINDEX f y <=> x = y)`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT CONJ_TAC THEN FIX_TAC "y" THEN
  CASES_TAC `y:eterm` THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IREINDEX; distinctness "eterm"; injectivity "eterm"] THEN
  ASM_MESON_TAC[SLIDE_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Derivation operator (needed for the substitution right next).             *)
(* ------------------------------------------------------------------------- *)

let EDERIV = new_recursive_definition num_RECURSION
  `(!f. EDERIV f 0 = EREF 0) /\
   (!f i. EDERIV f (SUC i) = IREINDEX SUC (f i))`;;

let EDERIV_EREF = prove
 (`EDERIV EREF = EREF`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN REWRITE_TAC[EDERIV; IREINDEX]);;

let EDERIV_EXTENS = prove
 (`!f g i. EDERIV f i = EDERIV g i <=> i = 0 \/ f (PRE i) = g (PRE i)`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; NOT_SUC; PRE] THEN SIMP_TAC[IREINDEX_INJ; SUC_INJ]);;

let EDERIV_SLIDE = prove
 (`!f g i. EDERIV g (SLIDE f i) = EDERIV (g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; SLIDE; o_THM]);;

let EDERIV_O_SUC = prove
 (`!f. EDERIV f o SUC = IREINDEX SUC o f`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; EDERIV]);;


let SUBDERIV_RULES,SUBDERIV_INDUCT,SUBDERIV_CASES = new_inductive_definition
  `(!k i. SUBDERIV k (EREF i)) /\
   (!k x y. SUBDERIV k x /\ SUBDERIV k y ==> SUBDERIV k (EAPP x y)) /\
   (!k x. SUBDERIV (SUC k) x ==> SUBDERIV k (EABS x)) /\
   (!k x y. SUBDERIV (SUC k) x /\ SUBDERIV k y
            ==> SUBDERIV k (ESUBST k x y))`;;

let esubst_TYBIJ =
  let eth = prove
   (`?p. SUBDERIV (FST p) (SND p)`,
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`0`; `EREF 0`] THEN
    REWRITE_TAC[SUBDERIV_RULES]) in
  new_type_definition "esubst" ("MK_ESUBST","DEST_ESUBST") eth;;



(* ------------------------------------------------------------------------- *)
(* Parallel capture-avoiding substitution (higher-order style).              *)
(* ------------------------------------------------------------------------- *)

let ISUBST = new_recursive_definition eterm_RECUR
  `(!f i. ISUBST f (EREF i) = f i) /\
   (!f x y. ISUBST f (EAPP x y) = EAPP (ISUBST f x) (ISUBST f y)) /\
   (!f x. ISUBST f (EABS x) = EABS (ISUBST (EDERIV f) x)) /\
   (!f x y. ISUBST f (ESUBST k x y) =
            ESUBST k (ISUBST (ITER (SUC K) EDERIV f) x) (ISUBST f y))`;;

let MSUBST_EREF = prove
 (`!x. ISUBST EREF x = x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ISUBST; EDERIV_EREF]);;

(* let MSUBST_EXTENS = prove
 (`!x f g. ISUBST f x = ISUBST g x <=> (!i. i IN FREES x ==> f i = g i)`,
  ASM_REWRITE_TAC[ISUBST; FREES_INVERSION; DERIV_EXTENS;
                  injectivity "eterm"; FORALL_UNWIND_THM2] THENL
  [MESON_TAC[]; REPEAT GEN_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_NUM_THM] THEN
  REWRITE_TAC[PRE; NOT_SUC]);;

let SUBST_REF_EQ = prove
 (`!x f. ISUBST f x = x <=> (!i. i IN FREES x ==> f i = REF i)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `ISUBST f x = ISUBST REF x` THEN CONJ_TAC THENL
  [REWRITE_TAC[SUBST_REF]; REWRITE_TAC[SUBST_EXTENS]]);;
*)

let MSUBST_EREINDEX = prove
 (`!x f g. ISUBST g (IREINDEX f x) = ISUBST (g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ISUBST; IREINDEX; o_THM; injectivity "eterm"] THEN
  REWRITE_TAC[o_DEF; EDERIV_SLIDE; ETA_AX]);;

let EREINDEX_SLIDE = prove
 (`!g f i. IREINDEX (SLIDE g) (EDERIV f i) = EDERIV (IREINDEX g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; IREINDEX; SLIDE; o_THM; EREINDEX_EREINDEX] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE]);;

let EREINDEX_MSUBST = prove
 (`!x f g. IREINDEX g (ISUBST f x) = ISUBST (IREINDEX g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IREINDEX; ISUBST; o_THM; injectivity "eterm"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; EREINDEX_SLIDE]);;

let ESUBST_EDERIV = prove
 (`!f g i. ISUBST (EDERIV g) (EDERIV f i) = EDERIV (ISUBST g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[EDERIV; ISUBST; MSUBST_EREINDEX; EREINDEX_MSUBST; o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; EDERIV]);;

let MSUBST_MSUBST = prove
 (`!x f g. ISUBST g (ISUBST f x) = ISUBST (ISUBST g o f) x`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ISUBST; o_THM; injectivity "eterm"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; ESUBST_EDERIV]);;

let EREINDEX_EQ_SUBST = prove
 (`!f. IREINDEX f = ISUBST (EREF o f)`,
  SUBGOAL_THEN `!x f. IREINDEX f x = ISUBST (EREF o f) x`
    (fun th -> REWRITE_TAC[th; FUN_EQ_THM]) THEN
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IREINDEX; ISUBST; o_THM; injectivity "eterm"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; EDERIV; o_THM; IREINDEX]);;

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
 (`!n t k. MSHIFTI k n t = IREINDEX (ITER k SLIDE ((+) n)) t`,
  GEN_TAC THEN MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MSHIFTI; IREINDEX; injectivity "eterm"; ITER_SLIDE] THEN
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
   COND_CASES_TAC THEN ASM_REWRITE_TAC[IREINDEX; injectivity "eterm"] THEN
   ASM_ARITH_TAC]);;

let MSUBSTI1_EQ_MSUBST = prove
 (`!u t i. MSUBSTI1 i u t =
           ISUBST (ITER i EDERIV (\i. if i = 0 then u else EREF (i - 1))) t`,
  GEN_TAC THEN MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MSUBST1; MSUBSTI1; ISUBST; injectivity "eterm"] THEN
  REWRITE_TAC[ITER_EDERIV; GSYM ADD1; ITER]);;
(* 
let MSUBST_PUSHENV_LEMMA = prove
 (`!f x i. ISUBST (PUSHENV (ISUBST f y) EREF) (EDERIV f i) =
           ISUBST f (PUSHENV y EREF i)`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[PUSHENV; EDERIV; ISUBST; MSUBST_EREINDEX] THEN
  TRANS_TAC EQ_TRANS `ISUBST EREF (f (n:num))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[MSUBST_EREF]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; ISUBST; PUSHENV]);; *)

let MSUBST1_EQ_MSUBST = prove
 (`!t u. MSUBST1 u t = ISUBST (PUSHENV u EREF) t`,
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
  CASES_GEN_TAC THEN REWRITE_TAC[EDERIV; ISUBST; PUSHENV; MSUBST_EREINDEX] THEN
  CASES_TAC `n:num` THEN REWRITE_TAC[PUSHENV; NOT_SUC; ISUBST; o_THM] THENL
  [ALL_TAC; REWRITE_TAC[injectivity "eterm"] THEN ARITH_TAC] THEN
  TRANS_TAC EQ_TRANS `ISUBST EREF w` THEN
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
 (`!x f. DBLAMBDA_OF_ETERM (IREINDEX f x) = REINDEX f (DBLAMBDA_OF_ETERM x)`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[DBLAMBDA_OF_ETERM; IREINDEX; REINDEX;
                  injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST1_EQ_SUBST; SUBST_REINDEX; REINDEX_SUBST] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[SLIDE; PUSHENV; REINDEX]);;

let DBLAMBDA_OF_ETERM_MSUBST = prove
 (`!x f. DBLAMBDA_OF_ETERM (ISUBST f x) =
         SUBST (DBLAMBDA_OF_ETERM o f) (DBLAMBDA_OF_ETERM x)`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[DBLAMBDA_OF_ETERM; ISUBST; SUBST; o_THM;
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
