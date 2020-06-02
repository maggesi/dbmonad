(* ========================================================================= *)
(* Initial semantics for the untyped lambda calculus.                        *)
(* ========================================================================= *)

type_invention_warning := false;;
needs "Library/rstc.ml";;               (* Refl, symm, trans closure.       *)
needs "Library/iter.ml";;               (* Iteration.                       *)
type_invention_warning := true;;

needs "Lambda/lib.ml";;                 (* Misc tactics and theorems        *)
needs "Lambda/dblambda.ml";;
needs "Lambda/new_dbmonad.ml";;
needs "Lambda/new_dbmodule.ml";;

(* ------------------------------------------------------------------------- *)
(* Further lemmas on Lambda Calculus.                                        *)
(* ------------------------------------------------------------------------- *)

let INFINITE_DBLAMBDA = prove
 (`INFINITE (:dblambda)`,
  MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC `IMAGE REF (:num)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  SIMP_TAC[INFINITE_IMAGE_INJ; num_INFINITE; injectivity "dblambda"]);;

(* ------------------------------------------------------------------------- *)
(* DB-monad of lambda calculus.                                              *)
(* ------------------------------------------------------------------------- *)

let IS_DBMONAD_DBLAMBDA = prove
 (`IS_DBMONAD (SUBST,REF)`,
  REWRITE_TAC[IS_DBMONAD; SUBST; SUBST_SUBST; SUBST_REF]);;

let LAMBDA_MONAD = new_definition
  `LAMBDA_MONAD = MK_DBMONAD (SUBST,REF)`;;

let LAMBDA_MONAD_CLAUSES = prove
 (`DBBIND LAMBDA_MONAD = SUBST /\
   DBUNIT LAMBDA_MONAD = REF`,
  REWRITE_TAC[LAMBDA_MONAD] THEN
  SIMP_TAC[DBBIND_MK_DBMONAD; DBUNIT_MK_DBMONAD;
    IS_DBMONAD_IMP_IS_SEMI_DBMONAD; INFINITE_DBLAMBDA; IS_DBMONAD_DBLAMBDA]);;

let DBREINDEX_LAMBDA_MONAD = prove
 (`DBREINDEX LAMBDA_MONAD = REINDEX`,
  REWRITE_TAC[FUN_EQ_THM; DBREINDEX; LAMBDA_MONAD_CLAUSES; REINDEX_EQ_SUBST]);;

let DBSLIDE_LAMBDA_MONAD = prove
 (`!f. DBSLIDE LAMBDA_MONAD f = DERIV f`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[DBSLIDE; DERIV; LAMBDA_MONAD_CLAUSES; DBREINDEX_LAMBDA_MONAD]);;

let APP_MODULE_HOM = prove
 (`UNCURRY APP IN MODULE_HOM
                   (DBMODULE_PRODUCT (SELF_DBMODULE LAMBDA_MONAD,
                                      SELF_DBMODULE LAMBDA_MONAD),
                    SELF_DBMODULE LAMBDA_MONAD)`,
  REWRITE_TAC[MODULE_HOM; IN_ELIM_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[DBMODULE_PRODUCT_CLAUSES; LAMBDA_MONAD_CLAUSES;
    INFINITE_DBLAMBDA; SELF_DBMODULE_CLAUSES; UNCURRY_DEF; SUBST]);;

let ABS_MODULE_HOM = prove
 (`ABS IN MODULE_HOM
            (DBDERIVED (SELF_DBMODULE LAMBDA_MONAD),
             SELF_DBMODULE LAMBDA_MONAD)`,
  REWRITE_TAC[MODULE_HOM; IN_ELIM_THM] THEN
  SIMP_TAC[DBDERIVED_CLAUSES; INFINITE_DBLAMBDA; SELF_DBMODULE_CLAUSES;
           LAMBDA_MONAD_CLAUSES; SUBST; DBSLIDE_LAMBDA_MONAD]);;

let LAMBDA_MODEL = new_definition
  `LAMBDA_MODEL =
   {(m:(A)dbmonad,app:A#A->A,lam:A->A) |
    ((:A) HAS_SIZE 1 \/ INFINITE (:A)) /\
    app IN MODULE_HOM
             (DBMODULE_PRODUCT (SELF_DBMODULE m, SELF_DBMODULE m),
              SELF_DBMODULE m) /\
    lam IN MODULE_HOM (DBDERIVED (SELF_DBMODULE m),SELF_DBMODULE m)}`;;

let IN_LAMBDA_MODEL = prove
 (`!m:(A)dbmonad app:A#A->A lam:A->A.
      (m,app,lam) IN LAMBDA_MODEL <=>
      ((:A) HAS_SIZE 1 \/ INFINITE (:A)) /\
      app IN MODULE_HOM
               (DBMODULE_PRODUCT (SELF_DBMODULE m, SELF_DBMODULE m),
                SELF_DBMODULE m) /\
      lam IN MODULE_HOM (DBDERIVED (SELF_DBMODULE m),SELF_DBMODULE m)`,
  REWRITE_TAC[LAMBDA_MODEL; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let DBSLIDE_LAMBDA_MONAD = prove
 (`DBSLIDE LAMBDA_MONAD = DERIV`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[DBSLIDE; DERIV; LAMBDA_MONAD_CLAUSES; DBREINDEX_LAMBDA_MONAD]);;

let LAMBDA_MONAD_IN_LAMBDA_MODEL = prove
 (`(LAMBDA_MONAD,UNCURRY APP,ABS) IN LAMBDA_MODEL`,
  REWRITE_TAC[IN_LAMBDA_MODEL; MODULE_HOM_CLAUSES; INFINITE_DBLAMBDA] THEN
  SIMP_TAC[SELF_DBMODULE_CLAUSES; DBMODULE_PRODUCT_CLAUSES;
           DBDERIVED_CLAUSES; LAMBDA_MONAD_CLAUSES; INFINITE_DBLAMBDA;
           SUBST; FORALL_PAIR_THM; UNCURRY_DEF; DBSLIDE_LAMBDA_MONAD]);;

let LAMBDA_MODEL_HOM = new_definition
  `!m :(A)dbmonad app :A#A->A lam :A->A
    m':(B)dbmonad app':B#B->B lam':B->B.
    LAMBDA_MODEL_HOM ((m,app,lam),(m',app',lam')) =
    {f:A->B |
     (m, app, lam) IN LAMBDA_MODEL /\
     (m',app',lam') IN LAMBDA_MODEL /\
     f IN DBMONAD_HOM(m,m') /\
     (!x y. f (app (x,y)) = app' (f x,f y)) /\
     (!x. f (lam x) = lam' (f x))}`;;

let LAMBDAREC_DEF = new_recursive_definition dblambda_RECURSION
  `(!i. LAMBDAREC m (REF i) = DBUNIT (FST m) i:A) /\
   (!x y. LAMBDAREC m (APP x y) =
          FST (SND m) (LAMBDAREC m x, LAMBDAREC m y)) /\
   (!x. LAMBDAREC m (ABS x) = SND (SND m) (LAMBDAREC m x))`;;
   
let LAMBDAREC = prove
 (`(!i. LAMBDAREC (m,app,lam) (REF i) = DBUNIT m i:A) /\
   (!x y. LAMBDAREC (m,app,lam) (APP x y) =
          app(LAMBDAREC (m,app,lam) x, LAMBDAREC (m,app,lam) y):A) /\
   (!x. LAMBDAREC (m,app,lam) (ABS x) = lam(LAMBDAREC (m,app,lam) x):A)`,
   REWRITE_TAC[LAMBDAREC_DEF]);;

let LAMBDAREC_REINDEX = prove
 (`!m:A dbmonad app lam x f.
     (m,app,lam) IN LAMBDA_MODEL
     ==> LAMBDAREC (m,app,lam) (REINDEX f x) =
         DBREINDEX m f (LAMBDAREC (m,app,lam) x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IN_LAMBDA_MODEL] THEN
  INTRO_TAC "!m app lam; (size1 | inf) app lam" THEN
  ASM_SIMP_TAC[HAS_SIZE_1_IMP_EQ] THEN
  DBLAMBDA_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[REINDEX; LAMBDAREC] THENL
  [ASM_SIMP_TAC[DBREINDEX_UNIT];
   REMOVE_THEN "app" (MP_TAC o MATCH_MP MODULE_HOM_DBMREINDEX) THEN
   ASM_SIMP_TAC[FORALL_PAIR_THM; DBMREINDEX_DBMODULE_PRODUCT;
                DBMREINDEX_SELF_DBMODULE];
   REMOVE_THEN "lam" (MP_TAC o MATCH_MP MODULE_HOM_DBMREINDEX) THEN
   ASM_SIMP_TAC[DBREINDEX_DBDERIVED; DBMREINDEX_SELF_DBMODULE] THEN
   DISCH_THEN (fun th -> REWRITE_TAC[GSYM th])]);;

let LAMBDAREC_SUBST = prove
 (`!m:A dbmonad app lam x f.
     (m,app,lam) IN LAMBDA_MODEL
     ==> LAMBDAREC (m,app,lam) (SUBST f x) =
         DBBIND m (LAMBDAREC (m,app,lam) o f) (LAMBDAREC (m,app,lam) x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  INTRO_TAC "!m app lam; model" THEN
  HYP_TAC "model->(size1 | inf) app lam" (REWRITE_RULE[IN_LAMBDA_MODEL]) THENL
  [ASM_SIMP_TAC[HAS_SIZE_1_IMP_EQ]; ALL_TAC] THEN
  DBLAMBDA_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[SUBST; LAMBDAREC] THENL
  [ASM_SIMP_TAC[DBBIND_DBUNIT; o_THM];
   REMOVE_THEN "app" MP_TAC THEN
   ASM_SIMP_TAC[MODULE_HOM_CLAUSES; FORALL_PAIR_THM;
                SELF_DBMODULE_CLAUSES; DBMODULE_PRODUCT_CLAUSES];
   REMOVE_THEN "lam" MP_TAC THEN
   ASM_SIMP_TAC[MODULE_HOM_CLAUSES; SELF_DBMODULE_CLAUSES;
                DBDERIVED_CLAUSES] THEN
   DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]) THEN
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CASES_GEN_TAC THEN 
   ASM_SIMP_TAC[DERIV; DBSLIDE; LAMBDAREC; LAMBDAREC_REINDEX; o_THM]]);;

let LAMBDAREC_IN_DBMONAD_HOM = prove
 (`!m:A dbmonad app lam.
     (m,app,lam) IN LAMBDA_MODEL
     ==> LAMBDAREC (m,app,lam) IN DBMONAD_HOM (LAMBDA_MONAD,m)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  REWRITE_TAC[IN_DBMONAD_HOM; LAMBDA_MONAD_CLAUSES; LAMBDAREC] THEN
  ASM_SIMP_TAC[LAMBDAREC_SUBST]);;

let LAMBDAREC_IN_LAMBDA_MODEL_HOM = prove
 (`!m:A dbmonad app lam.
     (m,app,lam) IN LAMBDA_MODEL
     ==> LAMBDAREC (m,app,lam) IN
          LAMBDA_MODEL_HOM ((LAMBDA_MONAD,UNCURRY APP,ABS),(m,app,lam))`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  ASM_REWRITE_TAC[LAMBDA_MODEL_HOM; IN_ELIM_THM; LAMBDA_MONAD_IN_LAMBDA_MODEL;
                  UNCURRY_DEF; LAMBDAREC] THEN
  ASM_SIMP_TAC[LAMBDAREC_IN_DBMONAD_HOM]);;

let LAMBDAREC_UNIQUE = prove
 (`!m:A dbmonad app lam r.
     r IN LAMBDA_MODEL_HOM ((LAMBDA_MONAD,UNCURRY APP,ABS),(m,app,lam))
     ==> r = LAMBDAREC (m,app,lam)`,
  REPEAT GEN_TAC THEN INTRO_TAC "r" THEN
  USE_THEN "r" (MP_TAC o
    REWRITE_RULE[LAMBDA_MODEL_HOM; IN_ELIM_THM; UNCURRY_DEF]) THEN
  INTRO_TAC "_ model r r_app r_lam" THEN REWRITE_TAC[FUN_EQ_THM] THEN
  HYP_TAC "model->(size1|inf) app lam" (REWRITE_RULE[IN_LAMBDA_MODEL]) THENL
  [ASM_MESON_TAC[HAS_SIZE_1_IMP_EQ]; ALL_TAC] THEN
  HYP_TAC "r->r_unit r_bind" (REWRITE_RULE[IN_DBMONAD_HOM; LAMBDA_MONAD_CLAUSES]) THEN
  DBLAMBDA_INDUCT_TAC THEN ASM_REWRITE_TAC[LAMBDAREC]);;

let LAMBDA_INITIAL = prove
 (`!m:(A)dbmonad app lam.
     (m,app,lam) IN LAMBDA_MODEL
     ==> ?!f. f IN LAMBDA_MODEL_HOM
                     ((LAMBDA_MONAD,UNCURRY APP, ABS),(m,app,lam))`,
  MESON_TAC[LAMBDAREC_IN_LAMBDA_MODEL_HOM; LAMBDAREC_UNIQUE]);;
