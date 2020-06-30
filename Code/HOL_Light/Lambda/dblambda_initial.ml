(* ========================================================================= *)
(* Initial semantics for the untyped lambda calculus.                        *)
(*                                                                           *)
(* Content:                                                                  *)
(*   - Preparation.                                                          *)
(*     - Further lemmas on Lambda Calculus.                                  *)
(*     - DB-monad of lambda calculus.                                        *)
(*     - Application and abstraction as module morphisms.                    *)
(*   - Lambda calculus ad initial DB monad.                                  *)
(*     - Category of lambda-calculi models.                                  *)
(*     - Definition of the initial morphism.                                 *)
(*     - Unicity and initiality.                                             *)
(*   - Lambda calculus with beta reduction as initial DB reduction monad.    *)
(* ========================================================================= *)

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

let LAMBDA_DBMONAD = new_definition
  `LAMBDA_DBMONAD = MK_DBMONAD (SUBST,REF)`;;

let LAMBDA_DBMONAD_CLAUSES = prove
 (`DBBIND LAMBDA_DBMONAD = SUBST /\
   DBUNIT LAMBDA_DBMONAD = REF`,
  REWRITE_TAC[LAMBDA_DBMONAD] THEN
  SIMP_TAC[DBBIND_MK_DBMONAD; DBUNIT_MK_DBMONAD;
    IS_DBMONAD_IMP_IS_SEMI_DBMONAD; INFINITE_DBLAMBDA; IS_DBMONAD_DBLAMBDA]);;

let DBREINDEX_LAMBDA_DBMONAD = prove
 (`DBREINDEX LAMBDA_DBMONAD = REINDEX`,
  REWRITE_TAC[FUN_EQ_THM; DBREINDEX; LAMBDA_DBMONAD_CLAUSES;
              REINDEX_EQ_SUBST]);;

let DBDERIV_LAMBDA_DBMONAD = prove
 (`!f. DBDERIV LAMBDA_DBMONAD f = DERIV f`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[DBDERIV; DERIV; LAMBDA_DBMONAD_CLAUSES;
              DBREINDEX_LAMBDA_DBMONAD]);;

(* ------------------------------------------------------------------------- *)
(* Application and abstraction as module morphisms.                          *)
(* ------------------------------------------------------------------------- *)

let APP_DBMODULE_HOM = prove
 (`UNCURRY APP IN DBMODULE_HOM
                   (DBMODULE_PRODUCT (SELF_DBMODULE LAMBDA_DBMONAD,
                                      SELF_DBMODULE LAMBDA_DBMONAD),
                    SELF_DBMODULE LAMBDA_DBMONAD)`,
  REWRITE_TAC[DBMODULE_HOM; IN_ELIM_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[DBMODULE_PRODUCT_CLAUSES; LAMBDA_DBMONAD_CLAUSES;
    INFINITE_DBLAMBDA; SELF_DBMODULE_CLAUSES; UNCURRY_DEF; SUBST]);;

let ABS_DBMODULE_HOM = prove
 (`ABS IN DBMODULE_HOM
            (DBDERIVED (SELF_DBMODULE LAMBDA_DBMONAD),
             SELF_DBMODULE LAMBDA_DBMONAD)`,
  REWRITE_TAC[DBMODULE_HOM; IN_ELIM_THM] THEN
  SIMP_TAC[DBDERIVED_CLAUSES; INFINITE_DBLAMBDA; SELF_DBMODULE_CLAUSES;
           LAMBDA_DBMONAD_CLAUSES; SUBST; DBDERIV_LAMBDA_DBMONAD]);;

(* ------------------------------------------------------------------------- *)
(* Category of lambda-calculi models.                                        *)
(* (I.e., DB-monads endowed with "app" and "abs" morphisms)                  *)
(* Object definition is `LAMBDA_MODEL` and morphism definition               *)
(* is LAMBDA_MODEL_HOM.                                                      *)
(* ------------------------------------------------------------------------- *)

let LAMBDA_MODEL = new_definition
  `LAMBDA_MODEL =
   {(m:(A)dbmonad,app:A#A->A,lam:A->A) |
    ((:A) HAS_SIZE 1 \/ INFINITE (:A)) /\
    app IN DBMODULE_HOM
             (DBMODULE_PRODUCT (SELF_DBMODULE m, SELF_DBMODULE m),
              SELF_DBMODULE m) /\
    lam IN DBMODULE_HOM (DBDERIVED (SELF_DBMODULE m),SELF_DBMODULE m)}`;;

let IN_LAMBDA_MODEL = prove
 (`!m:(A)dbmonad app:A#A->A lam:A->A.
      (m,app,lam) IN LAMBDA_MODEL <=>
      ((:A) HAS_SIZE 1 \/ INFINITE (:A)) /\
      app IN DBMODULE_HOM
               (DBMODULE_PRODUCT (SELF_DBMODULE m, SELF_DBMODULE m),
                SELF_DBMODULE m) /\
      lam IN DBMODULE_HOM (DBDERIVED (SELF_DBMODULE m),SELF_DBMODULE m)`,
  REWRITE_TAC[LAMBDA_MODEL; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let DBDERIV_LAMBDA_DBMONAD = prove
 (`DBDERIV LAMBDA_DBMONAD = DERIV`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[DBDERIV; DERIV; LAMBDA_DBMONAD_CLAUSES;
              DBREINDEX_LAMBDA_DBMONAD]);;

let LAMBDA_DBMONAD_IN_LAMBDA_MODEL = prove
 (`(LAMBDA_DBMONAD,UNCURRY APP,ABS) IN LAMBDA_MODEL`,
  REWRITE_TAC[IN_LAMBDA_MODEL; IN_DBMODULE_HOM; INFINITE_DBLAMBDA] THEN
  SIMP_TAC[SELF_DBMODULE_CLAUSES; DBMODULE_PRODUCT_CLAUSES;
           DBDERIVED_CLAUSES; LAMBDA_DBMONAD_CLAUSES; INFINITE_DBLAMBDA;
           SUBST; FORALL_PAIR_THM; UNCURRY_DEF; DBDERIV_LAMBDA_DBMONAD]);;

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

let IN_LAMBDA_MODEL_HOM = prove
 (`!m :(A)dbmonad app :A#A->A lam :A->A
    m':(B)dbmonad app':B#B->B lam':B->B.
    f:A->B IN LAMBDA_MODEL_HOM ((m,app,lam),(m',app',lam')) <=>
    (m, app, lam) IN LAMBDA_MODEL /\
    (m',app',lam') IN LAMBDA_MODEL /\
    f IN DBMONAD_HOM(m,m') /\
    (!x y. f (app (x,y)) = app' (f x,f y)) /\
    (!x. f (lam x) = lam' (f x))`,
  REWRITE_TAC[LAMBDA_MODEL_HOM; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the initial morphism.                                       *)
(* Construction of the initial morphism `LAMBDAREC` and proof                *)
(* of the compatibility laws.                                                *)
(* ------------------------------------------------------------------------- *)

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
   REMOVE_THEN "app" (MP_TAC o MATCH_MP DBMODULE_HOM_DBMREINDEX) THEN
   ASM_SIMP_TAC[FORALL_PAIR_THM; DBMREINDEX_DBMODULE_PRODUCT;
                DBMREINDEX_SELF_DBMODULE];
   REMOVE_THEN "lam" (MP_TAC o MATCH_MP DBMODULE_HOM_DBMREINDEX) THEN
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
   ASM_SIMP_TAC[IN_DBMODULE_HOM; FORALL_PAIR_THM;
                SELF_DBMODULE_CLAUSES; DBMODULE_PRODUCT_CLAUSES];
   REMOVE_THEN "lam" MP_TAC THEN
   ASM_SIMP_TAC[IN_DBMODULE_HOM; SELF_DBMODULE_CLAUSES;
                DBDERIVED_CLAUSES] THEN
   DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]) THEN
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CASES_GEN_TAC THEN 
   ASM_SIMP_TAC[DERIV; DBDERIV; LAMBDAREC; LAMBDAREC_REINDEX; o_THM]]);;

let LAMBDAREC_IN_DBMONAD_HOM = prove
 (`!m:A dbmonad app lam.
     (m,app,lam) IN LAMBDA_MODEL
     ==> LAMBDAREC (m,app,lam) IN DBMONAD_HOM (LAMBDA_DBMONAD,m)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  REWRITE_TAC[IN_DBMONAD_HOM; LAMBDA_DBMONAD_CLAUSES; LAMBDAREC] THEN
  ASM_SIMP_TAC[LAMBDAREC_SUBST]);;

let LAMBDAREC_IN_LAMBDA_MODEL_HOM = prove
 (`!m:A dbmonad app lam.
     (m,app,lam) IN LAMBDA_MODEL
     ==> LAMBDAREC (m,app,lam) IN
          LAMBDA_MODEL_HOM ((LAMBDA_DBMONAD,UNCURRY APP,ABS),(m,app,lam))`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  ASM_REWRITE_TAC[LAMBDA_MODEL_HOM; IN_ELIM_THM;
                  LAMBDA_DBMONAD_IN_LAMBDA_MODEL;
                  UNCURRY_DEF; LAMBDAREC] THEN
  ASM_SIMP_TAC[LAMBDAREC_IN_DBMONAD_HOM]);;

(* ------------------------------------------------------------------------- *)
(* Unicity and initiality.                                                   *)
(* ------------------------------------------------------------------------- *)

let LAMBDAREC_UNIQUE = prove
 (`!m:A dbmonad app lam r.
     r IN LAMBDA_MODEL_HOM ((LAMBDA_DBMONAD,UNCURRY APP,ABS),(m,app,lam))
     ==> r = LAMBDAREC (m,app,lam)`,
  REPEAT GEN_TAC THEN INTRO_TAC "r" THEN
  USE_THEN "r" (MP_TAC o
    REWRITE_RULE[IN_LAMBDA_MODEL_HOM; UNCURRY_DEF]) THEN
  INTRO_TAC "_ model r r_app r_lam" THEN REWRITE_TAC[FUN_EQ_THM] THEN
  HYP_TAC "model->(size1|inf) app lam" (REWRITE_RULE[IN_LAMBDA_MODEL]) THENL
  [ASM_MESON_TAC[HAS_SIZE_1_IMP_EQ]; ALL_TAC] THEN
  HYP_TAC "r->r_unit r_bind"
    (REWRITE_RULE[IN_DBMONAD_HOM; LAMBDA_DBMONAD_CLAUSES]) THEN
  DBLAMBDA_INDUCT_TAC THEN ASM_REWRITE_TAC[LAMBDAREC]);;

let LAMBDA_INITIAL = prove
 (`!m:(A)dbmonad app lam.
     (m,app,lam) IN LAMBDA_MODEL
     ==> ?!f. f IN LAMBDA_MODEL_HOM
                     ((LAMBDA_DBMONAD,UNCURRY APP, ABS),(m,app,lam))`,
  MESON_TAC[LAMBDAREC_IN_LAMBDA_MODEL_HOM; LAMBDAREC_UNIQUE]);;

(* ------------------------------------------------------------------------- *)
(* Initial semantics for lambda calculus with beta reduction.                *)
(*                                                                           *)
(* We work in the category of the "one-step beta-reduction relations".       *)
(* A full-subcategory of the category of binary relations.                   *)
(* (There is a morphism from `R` to `S when `!x y. R x y ==> S x y)`.)       *)
(* Below we only give the set of objects.                                    *)
(* ------------------------------------------------------------------------- *)

let ONESTEP_BETA_REDUCTION = new_definition
  `ONESTEP_BETA_REDUCTION =
   {R | (!x y f. R x y ==> R (SUBST f x) (SUBST f y)) /\
        (!x y. DBLAMBDA_BETA x y ==> R x y) /\
        (!x1 x2 y. R x1 x2 ==> R (APP x1 y) (APP x2 y)) /\
        (!x y1 y2. R y1 y2 ==> R (APP x y1) (APP x y2)) /\
        (!x y. R x y ==> R (ABS x) (ABS y))}`;;

(* ------------------------------------------------------------------------- *)
(* Initiality of DBLAMBDA_CONG DBLAMBDA_BETA.                                *)
(* ------------------------------------------------------------------------- *)

let BETARED_INITIAL = prove
 (`!R. R IN ONESTEP_BETA_REDUCTION
       ==> (!x y. DBLAMBDA_CONG DBLAMBDA_BETA x y ==> R x y)`,
  GEN_TAC THEN REWRITE_TAC[ONESTEP_BETA_REDUCTION; IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC DBLAMBDA_CONG_INDUCT THEN ASM_REWRITE_TAC[]);;