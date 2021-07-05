(* ========================================================================= *)
(* Proof of the universal property of the syntactic and semantic             *)
(* lambda calculus.                                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* De Bruijn Monads of the syntactic lambda calculus.                        *)
(* ------------------------------------------------------------------------- *)

let SUBST_IN_MONAD = prove
 (`SUBST IN MONAD`,
  REWRITE_TAC[IN_MONAD; SUBST_SUBST; o_DEF] THEN EXISTS_TAC `REF` THEN
  REWRITE_TAC[SUBST; SUBST_REF]);;

let UNIT_SUBST = prove
 (`UNIT SUBST = REF`,
  MATCH_MP_TAC MONAD_UNIT_UNIQUE THEN
  REWRITE_TAC[SUBST_IN_MONAD; SUBST; SUBST_REF]);;

let SUBST_IN_MODULE = prove
 (`SUBST IN MODULE SUBST`,
  REWRITE_TAC[SELF_MODULE; SUBST_IN_MONAD]);;

let FMAP_SUBST = prove
 (`FMAP SUBST = REINDEX`,
  REWRITE_TAC[FUN_EQ_THM; FMAP; REINDEX_EQ_SUBST; UNIT_SUBST]);;

let APP_IN_MODULE_MOR = prove
 (`UNCURRY APP IN MODULE_MOR SUBST (MPROD SUBST SUBST,SUBST)`,
  REWRITE_TAC[IN_MODULE_MOR; SUBST_IN_MODULE] THEN CONJ_TAC THENL
  [MATCH_MP_TAC MPROD_IN_MODULE THEN REWRITE_TAC[SUBST_IN_MODULE];
   REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; MPROD; SUBST]]);;

let ABS_IN_MODULE_MOR = prove
 (`ABS IN MODULE_MOR SUBST (DMOP SUBST SUBST,SUBST)`,
  REWRITE_TAC[IN_MODULE_MOR; SUBST_IN_MODULE] THEN CONJ_TAC THENL
  [MATCH_MP_TAC MODULE_DMOP THEN REWRITE_TAC[SUBST_IN_MODULE]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBST; DMOP; injectivity "dblambda"] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[DERIV; MDERIV; UNIT_SUBST; FMAP_SUBST]);;

(* ------------------------------------------------------------------------- *)
(* Category of models for the syntactic lambda calculus.                     *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_MODEL = new_definition
  `DBLAMBDA_MODEL =
   {(op:(num->A)->A->A,app:A#A->A,lam:A->A) |
      op IN MONAD /\
      app IN MODULE_MOR op (MPROD op op, op) /\
      lam IN MODULE_MOR op (DMOP op op, op)}`;;

let IN_DBLAMBDA_MODEL = prove
 (`!op:(num->A)->A->A app:A#A->A lam:A->A.
   (op,app,lam) IN DBLAMBDA_MODEL <=>
   op IN MONAD /\
   app IN MODULE_MOR op (MPROD op op, op) /\
   lam IN MODULE_MOR op (DMOP op op, op)`,
  REWRITE_TAC[DBLAMBDA_MODEL; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let DBLAMBDA_IN_DBLAMBDA_MODEL = prove
 (`SUBST,UNCURRY APP,ABS IN DBLAMBDA_MODEL`,
  REWRITE_TAC[IN_DBLAMBDA_MODEL; SUBST_IN_MONAD;
              APP_IN_MODULE_MOR; ABS_IN_MODULE_MOR]);;

let DBLAMBDA_MODEL_MOR = new_definition
  `DBLAMBDA_MODEL_MOR ((op,app,lam),(op',app',lam')) =
   {h:A->B | (op, app, lam)  IN DBLAMBDA_MODEL /\
             (op',app',lam') IN DBLAMBDA_MODEL /\
             h IN MONAD_HOM (op,op') /\
             (!x y. h (app (x,y)) = app' (h x,h y)) /\
             (!x. h (lam x) = lam' (h x))}`;;

let IN_DBLAMBDA_MODEL_MOR = prove
 (`!op :(num->A)->A->A app :A#A->A lam :A->A
    op':(num->B)->B->B app':B#B->B lam':B->B
    h:A->B.
     h IN DBLAMBDA_MODEL_MOR ((op,app,lam),(op',app',lam')) <=>
     (op, app, lam)  IN DBLAMBDA_MODEL /\
     (op',app',lam') IN DBLAMBDA_MODEL /\
     h IN MONAD_HOM (op,op') /\
     (!x y. h (app (x,y)) = app' (h x,h y)) /\
     (!x. h (lam x) = lam' (h x))`,
  REWRITE_TAC[DBLAMBDA_MODEL_MOR; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Recursive definition of the initial morphism.                             *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDAINIT_DEF = new_recursive_definition dblambda_RECURSION
  `(!i. DBLAMBDAINIT m (REF i) = UNIT (FST m) i:A) /\
   (!x y. DBLAMBDAINIT m (APP x y) =
          FST (SND m) (DBLAMBDAINIT m x, DBLAMBDAINIT m y)) /\
   (!x. DBLAMBDAINIT m (ABS x) = SND (SND m) (DBLAMBDAINIT m x))`;;

let DBLAMBDAINIT = prove
 (`(!i. DBLAMBDAINIT (op,app,lam) (REF i) = UNIT op i:A) /\
   (!x y. DBLAMBDAINIT (op,app,lam) (APP x y) =
          app(DBLAMBDAINIT (op,app,lam) x, DBLAMBDAINIT (op,app,lam) y):A) /\
   (!x. DBLAMBDAINIT (op,app,lam) (ABS x) =
        lam(DBLAMBDAINIT (op,app,lam) x):A)`,
  REWRITE_TAC[DBLAMBDAINIT_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Compatibility with reindexing and substitution of the initial morphism.   *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDAINIT_REINDEX = prove
 (`!op:(num->A)->A->A app lam x f.
     (op,app,lam) IN DBLAMBDA_MODEL
     ==> DBLAMBDAINIT (op,app,lam) (REINDEX f x) =
         FMAP op f (DBLAMBDAINIT (op,app,lam) x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IN_DBLAMBDA_MODEL] THEN
  INTRO_TAC "!op app lam; op app lam" THEN DBLAMBDA_INDUCT_TAC THEN
  GEN_TAC THEN REWRITE_TAC[REINDEX; DBLAMBDAINIT] THENL
  [ASM_SIMP_TAC[FMAP_UNIT];
   HYP_TAC "app: +" (MATCH_MP MODULE_MOR_MMAP) THEN
   ASM_REWRITE_TAC[FORALL_PAIR_THM; MPROD; GSYM SELF_FMAP] THEN
   DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]) THEN
   REWRITE_TAC[MMAP_MPROD; SELF_FMAP];
   HYP_TAC "lam: +" (MATCH_MP MODULE_MOR_MMAP) THEN
   ASM_REWRITE_TAC[GSYM SELF_FMAP] THEN
   DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]) THEN
   AP_TERM_TAC THEN AP_THM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; FMAP; MMAP; DMOP] THEN
   GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
   INDUCT_TAC THEN REWRITE_TAC[SLIDE; MDERIV; o_THM] THEN
   ASM_SIMP_TAC[FMAP_UNIT]]);;

let DBLAMBDAINIT_SUBST = prove
 (`!op:(num->A)->A->A app lam x f.
     (op,app,lam) IN DBLAMBDA_MODEL
     ==> DBLAMBDAINIT (op,app,lam) (SUBST f x) =
         op (DBLAMBDAINIT (op,app,lam) o f) (DBLAMBDAINIT (op,app,lam) x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN INTRO_TAC "!op app lam; model" THEN
  HYP_TAC "model -> op app lam" (REWRITE_RULE[IN_DBLAMBDA_MODEL]) THEN
  DBLAMBDA_INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[SUBST; DBLAMBDAINIT] THENL
  [ASM_SIMP_TAC[MONAD_RUNIT; o_THM];
   HYP_TAC "app -> _ _ +" (REWRITE_RULE[IN_MODULE_MOR]) THEN
   ASM_REWRITE_TAC[FORALL_PAIR_THM; MPROD] THEN
   DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]);
   HYP_TAC "lam -> _ _ +" (REWRITE_RULE[IN_MODULE_MOR]) THEN
   DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]) THEN AP_TERM_TAC THEN
   ASM_REWRITE_TAC[DMOP] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN INDUCT_TAC THEN
   REWRITE_TAC[MDERIV; DERIV; DBLAMBDAINIT; o_THM] THEN
   ASM_SIMP_TAC[DBLAMBDAINIT_REINDEX]]);;

let DBLAMBDAINIT_IN_MONAD_HOM = prove
 (`!op:(num->A)->A->A app lam.
     (op,app,lam) IN DBLAMBDA_MODEL
     ==> DBLAMBDAINIT (op,app,lam) IN MONAD_HOM (SUBST,op)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  HYP_TAC "model -> op app lam" (REWRITE_RULE[IN_DBLAMBDA_MODEL]) THEN
  ASM_REWRITE_TAC[IN_MONAD_HOM; SUBST_IN_MONAD] THEN
  REWRITE_TAC[DBLAMBDAINIT; UNIT_SUBST] THEN
  ASM_SIMP_TAC[DBLAMBDAINIT_SUBST]);;

(* ------------------------------------------------------------------------- *)
(* Universal property of the syntactic lambda calculus.                      *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDAINIT_IN_DBLAMBDA_MODEL_MOR = prove
 (`!op:(num->A)->A->A app lam.
     (op,app,lam) IN DBLAMBDA_MODEL
     ==> DBLAMBDAINIT (op,app,lam) IN
         DBLAMBDA_MODEL_MOR ((SUBST,UNCURRY APP,ABS),(op,app,lam))`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  ASM_REWRITE_TAC[IN_DBLAMBDA_MODEL_MOR; DBLAMBDA_IN_DBLAMBDA_MODEL] THEN
  ASM_SIMP_TAC[DBLAMBDAINIT_IN_MONAD_HOM] THEN
  REWRITE_TAC[DBLAMBDAINIT; UNCURRY_DEF]);;

let DBLAMBDAINIT_UNIQUE = prove
 (`!op:(num->A)->A->A app lam r.
      r IN DBLAMBDA_MODEL_MOR ((SUBST,UNCURRY APP,ABS),(op,app,lam))
      ==> r = DBLAMBDAINIT (op,app,lam)`,
  REPEAT GEN_TAC THEN INTRO_TAC "r" THEN
  USE_THEN "r" (MP_TAC o REWRITE_RULE[IN_DBLAMBDA_MODEL_MOR; UNCURRY_DEF]) THEN
  INTRO_TAC "_ model r r_app r_lam" THEN REWRITE_TAC[FUN_EQ_THM] THEN
  HYP_TAC "r -> _ _ r_unit r_bind"
    (REWRITE_RULE[IN_MONAD_HOM; UNIT_SUBST]) THEN
  DBLAMBDA_INDUCT_TAC THEN ASM_REWRITE_TAC[DBLAMBDAINIT]);;

(* ------------------------------------------------------------------------- *)
(* De Bruijn Monads of the semantic lambda calculus.                         *)
(* ------------------------------------------------------------------------- *)

let LC_SUBST_IN_MONAD = prove
 (`LC_SUBST IN MONAD`,
  REWRITE_TAC[IN_MONAD; LC_SUBST_SUBST; o_DEF] THEN EXISTS_TAC `LC_REF` THEN
  REWRITE_TAC[LC_SUBST_RUNIT; LC_SUBST_LUNIT]);;

let LC_UNIT = prove
 (`UNIT LC_SUBST = LC_REF`,
  MATCH_MP_TAC MONAD_UNIT_UNIQUE THEN
  REWRITE_TAC[LC_SUBST_IN_MONAD; LC_SUBST_LUNIT; LC_SUBST_RUNIT]);;

(* ------------------------------------------------------------------------- *)
(* Proof that LC is an exponential operad.                                   *)
(* ------------------------------------------------------------------------- *)

let LC_DMOP = prove
 (`!f x. DMOP LC_SUBST LC_SUBST (LC_PROJ o f) (LC_PROJ x) =
         LC_PROJ (DMOP SUBST SUBST f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DMOP; GSYM LC_SUBST_PROJ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  NUM_CASES_TAC THEN
  REWRITE_TAC[MDERIV; UNIT_SUBST; LC_UNIT; LC_REF; o_THM] THEN
  REWRITE_TAC[FMAP; GSYM LC_SUBST_PROJ] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; UNIT_SUBST; LC_UNIT; LC_REF]);;

let LC_REINDEX_EQ_LC_SUBST = prove
 (`!f x. LC_REINDEX f x = LC_SUBST (LC_REF o f) x`,
  REWRITE_TAC[FORALL_LC_THM; FORALL_LC_FUN_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_REINDEX; REINDEX_EQ_SUBST; GSYM LC_SUBST_PROJ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; LC_REF]);;

let LC_ABS_MODULE_MOR = prove
 (`LC_ABS IN MODULE_MOR LC_SUBST (DMOP LC_SUBST LC_SUBST, LC_SUBST)`,
  REWRITE_TAC[IN_MODULE_MOR; SELF_MODULE; LC_SUBST_IN_MONAD] THEN
  SIMP_TAC[MODULE_DMOP; LC_SUBST_IN_MONAD; SELF_MODULE] THEN
  REWRITE_TAC[FORALL_LC_THM; FORALL_LC_FUN_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_SUBST] THEN AP_TERM_TAC THEN REWRITE_TAC[DMOP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  NUM_CASES_TAC THEN REWRITE_TAC[MDERIV; LC_DERIV; LC_UNIT; FMAP] THEN
  REWRITE_TAC[o_THM; LC_REINDEX_EQ_LC_SUBST]);;

let LC_APP0_MODULE_MOR = prove
 (`MODULE_ISOM LC_SUBST (LC_SUBST,DMOP LC_SUBST LC_SUBST) (LC_APP0,LC_ABS)`,
  MESON_TAC[MODULE_ISOM_SYM; LC_APP0_ABS; LC_ABS_APP0;
            MODULE_ISOM; LC_ABS_MODULE_MOR]);;

let LC_EXP = prove
 (`EXP_MONAD LC_SUBST LC_APP0 LC_ABS`,
  REWRITE_TAC[EXP_MONAD; LC_APP0_MODULE_MOR]);;

(* ------------------------------------------------------------------------- *)
(* Proof of the universal property of LC                                     *)
(* ------------------------------------------------------------------------- *)

let EXP_MONAD_UNFOLD = prove
 (`!op h:A->A g.
     EXP_MONAD op h g <=>
     op IN MONAD /\
     (!x. g (h x) = x) /\
     (!y. h (g y) = y) /\
     (!f x. h (op f x) = op (MDERIV op f) (h x)) /\
     (!f x. op f (g x) = g (op (MDERIV op f) x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_MONAD; SELF_MODULE; MODULE_ISOM_UNFOLD;
              IN_MODULE_MOR; DMOP] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MODULE_DMOP; SELF_MODULE]);;

let DBLAMBDA_EXPMAP = new_recursive_definition dblambda_RECURSION
  `(!op h g:A->A i. DBLAMBDA_EXPMAP op h g (REF i) = UNIT op i) /\
   (!op h g x y.
      DBLAMBDA_EXPMAP op h g (APP x y) =
        op (PUSHENV (DBLAMBDA_EXPMAP op h g y) (UNIT op))
           (h (DBLAMBDA_EXPMAP op h g x))) /\
   (!op h g x. DBLAMBDA_EXPMAP op h g (ABS x) =
               g (DBLAMBDA_EXPMAP op h g x))`;;

let DBLAMBDA_EXPMAP_REINDEX = prove
 (`!op h:A->A g x f.
     EXP_MONAD op h g
     ==> DBLAMBDA_EXPMAP op h g (REINDEX f x) =
         op (UNIT op o f) (DBLAMBDA_EXPMAP op h g x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_MONAD_UNFOLD] THEN STRIP_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  GEN_TAC THEN ASM_REWRITE_TAC[REINDEX; DBLAMBDA_EXPMAP] THENL
  [ASM_SIMP_TAC[MONAD_RUNIT; o_THM];
   ASM_SIMP_TAC[MONAD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
   ASM_SIMP_TAC[MDERIV; PUSHENV; o_THM; MONAD_RUNIT; FMAP_UNIT];
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   REWRITE_TAC[MDERIV; SLIDE; o_THM] THEN ASM_SIMP_TAC[FMAP_UNIT]]);;

let FMAP_DBLAMBDA_EXPMAP = prove
 (`!op h g x f.
     EXP_MONAD op h g
     ==> FMAP op f (DBLAMBDA_EXPMAP op h g x) =
         DBLAMBDA_EXPMAP op h g (REINDEX f x):A`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "exp" THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[EXP_MONAD_UNFOLD] THEN STRIP_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  GEN_TAC THEN ASM_REWRITE_TAC[DBLAMBDA_EXPMAP; REINDEX] THENL
  [ASM_SIMP_TAC[FMAP_UNIT];
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; MONAD_ASSOC; FMAP_OP] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
   NUM_CASES_TAC THEN
   ASM_SIMP_TAC[PUSHENV; MDERIV; MONAD_RUNIT; DBLAMBDA_EXPMAP_REINDEX;
                FMAP_UNIT; o_THM];
   ASM_SIMP_TAC[FMAP; DBLAMBDA_EXPMAP_REINDEX] THEN
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   REWRITE_TAC[MDERIV; SLIDE; o_THM] THEN ASM_SIMP_TAC[FMAP_UNIT]]);;

let DBLAMBDA_EXPMAP_SUBST = prove
 (`!op h:A->A g x f.
     EXP_MONAD op h g
     ==> DBLAMBDA_EXPMAP op h g (SUBST f x) =
         op (DBLAMBDA_EXPMAP op h g o f) (DBLAMBDA_EXPMAP op h g x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "exp" THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[EXP_MONAD_UNFOLD] THEN STRIP_TAC THEN DBLAMBDA_INDUCT_TAC THEN
  GEN_TAC THEN ASM_REWRITE_TAC[SUBST; DBLAMBDA_EXPMAP] THENL
  [ASM_SIMP_TAC[MONAD_RUNIT; o_THM];
   ASM_SIMP_TAC[MONAD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   ASM_SIMP_TAC[MONAD_RUNIT; MDERIV; PUSHENV] THEN
   ASM_SIMP_TAC[OP_FMAP; o_THM] THEN MATCH_MP_TAC MONAD_LUNIT_IMP THEN
   ASM_REWRITE_TAC[o_THM; PUSHENV];
   AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
   REWRITE_TAC[DERIV; MDERIV; DBLAMBDA_EXPMAP; o_THM] THEN
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; FMAP_DBLAMBDA_EXPMAP]]);;

let DBLAMBDA_EXPMAP_REL = prove
 (`!op h:A->A g x y.
     EXP_MONAD op h g /\ x === y
     ==> DBLAMBDA_EXPMAP op h g x = DBLAMBDA_EXPMAP op h g y`,
  INTRO_TAC "!op h g" THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  INTRO_TAC "exp" THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[EXP_MONAD_UNFOLD] THEN STRIP_TAC THEN
  MATCH_MP_TAC LC_REL_INDUCT THEN CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_BETA_INDUCT THEN GEN_TAC THEN GEN_TAC THEN
   REWRITE_TAC[DBLAMBDA_EXPMAP; SUBST1_EQ_SUBST] THEN
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_SUBST] THEN AP_THM_TAC THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
   NUM_CASES_TAC THEN REWRITE_TAC[PUSHENV; DBLAMBDA_EXPMAP];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_ETA_INDUCT THEN GEN_TAC THEN
   REWRITE_TAC[DBLAMBDA_EXPMAP] THEN
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; MONAD_ASSOC] THEN
   ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; MONAD_ASSOC] THEN
   SUBGOAL_THEN
     `(op (PUSHENV (UNIT op 0) (UNIT op)) o MDERIV op (UNIT op o SUC)) =
      UNIT (op:(num->A)->A->A)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN NUM_CASES_TAC THEN
    ASM_SIMP_TAC[MDERIV; MONAD_RUNIT; PUSHENV] THEN
    ASM_SIMP_TAC[OP_FMAP; o_THM; MONAD_RUNIT; PUSHENV];
    ASM_SIMP_TAC[MONAD_LUNIT]];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DBLAMBDA_EXPMAP]);;

let LC_EXPMAP = define
  `!op h g:A->A x. LC_EXPMAP op h g x = DBLAMBDA_EXPMAP op h g (LC_LIFT x)`;;

let LC_EXPMAP_FACTOR = prove
 (`!op h:A->A g x.
     EXP_MONAD op h g
     ==> LC_EXPMAP op h g (LC_PROJ x) = DBLAMBDA_EXPMAP op h g x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LC_EXPMAP] THEN
  MATCH_MP_TAC DBLAMBDA_EXPMAP_REL THEN ASM_REWRITE_TAC[LC_LIFT_PROJ]);;

g `!op h:A->A g.
      EXP_MONAD op h g ==> LC_EXPMAP op h g IN MONAD_HOM (LC_SUBST,op)`;;
e (REPEAT STRIP_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_MONAD_UNFOLD]));;
e (ASM_REWRITE_TAC[IN_MONAD_HOM; LC_SUBST_IN_MONAD]);;
e (REWRITE_TAC[LC_UNIT; LC_REF]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR; DBLAMBDA_EXPMAP]);;
e (REWRITE_TAC[LC_SUBST_DEF]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR]);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_SUBST]);;
e (REWRITE_TAC[LC_EXPMAP; o_DEF]);;
let MONAD_HOM_LC_EXPMAP = top_thm ();;

g `!op h:A->A g.
     EXP_MONAD op h g
     ==>
     (!i. DBLAMBDA_EXPMAP op h g (REF i) = UNIT op i) /\
     (!x. DBLAMBDA_EXPMAP op h g (APP0 x) = h (DBLAMBDA_EXPMAP op h g x)) /\
     (!x. DBLAMBDA_EXPMAP op h g (ABS x) = g (DBLAMBDA_EXPMAP op h g x)) /\
     (!t x. DBLAMBDA_EXPMAP op h g (SUBST t x) =
            op (DBLAMBDA_EXPMAP op h g o t) (DBLAMBDA_EXPMAP op h g x))`;;
e (REPEAT GEN_TAC THEN DISCH_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_MONAD_UNFOLD]));;
e (ASM_REWRITE_TAC[APP0; DBLAMBDA_EXPMAP]);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_REINDEX; MONAD_ASSOC]);;
e (MATCH_MP_TAC MONAD_LUNIT_IMP);;
e (ASM_REWRITE_TAC[]);;
e (NUM_CASES_TAC THEN REWRITE_TAC[MDERIV; o_THM] THEN
   ASM_SIMP_TAC[MONAD_RUNIT; FMAP_UNIT; PUSHENV]);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_SUBST]);;
let DBLAMBDA_EXPMAP_ALT = top_thm ();;

g `!op h:A->A g.
      EXP_MONAD op h g
      ==> EXP_MONAD_HOM LC_SUBST LC_APP0 LC_ABS
                          op h g (LC_EXPMAP op h g)`;;
e (REPEAT STRIP_TAC);;
e (FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [EXP_MONAD_UNFOLD]));;
e (ASM_REWRITE_TAC[EXP_MONAD_HOM; LC_EXP]);;
e (ASM_SIMP_TAC[MONAD_HOM_LC_EXPMAP]);;
e (REWRITE_TAC[FORALL_LC_THM]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR; LC_APP0]);;
e (ASM_SIMP_TAC[DBLAMBDA_EXPMAP_ALT]);;
let EXP_MONAD_HOM_LC_EXPMAP = top_thm ();;

g `!op1 h1 g1 op2 h2 g2 f:A->B.
      EXP_MONAD_HOM op1 h1 g1 op2 h2 g2 f
      <=> EXP_MONAD op1 h1 g1 /\
          EXP_MONAD op2 h2 g2 /\
          f IN MONAD_HOM (op1,op2) /\
          (!x. h2 (f x) = f (h1 x)) /\
          (!x. g2 (f x) = f (g1 x))`;;
e (REPEAT GEN_TAC THEN REWRITE_TAC[EXP_MONAD_HOM] THEN
   EQ_TAC THENL [ALL_TAC; MESON_TAC[]]);;
e (DISCH_THEN (fun th -> REWRITE_TAC[th] THEN MP_TAC th));;
e (REWRITE_TAC[EXP_MONAD; MODULE_ISOM_UNFOLD; IN_MODULE_MOR]);;
e (REWRITE_TAC[CONJ_ACI]);;
e (STRIP_TAC THEN GEN_TAC);;
e (SUBGOAL_THEN `!x y : B. h2 x :B = h2 y ==> x = y` MATCH_MP_TAC);;
e (ASM_MESON_TAC[]);;
e (ASM_REWRITE_TAC[]);;
let EXP_MONAD_HOM_FACTS = top_thm ();;

g `!op h:A->A g m.
      EXP_MONAD op h g /\
      EXP_MONAD_HOM LC_SUBST LC_APP0 LC_ABS op h g m
      ==> m = LC_EXPMAP op h g`;;
e (REPEAT STRIP_TAC);;
e (STRIP_ASSUME_TAC
    (REWRITE_RULE [EXP_MONAD_UNFOLD]
                  (ASSUME `EXP_MONAD op (h:A->A) g`)));;
e (STRIP_ASSUME_TAC
     (REWRITE_RULE [EXP_MONAD_HOM_FACTS; LC_EXP]
                   (ASSUME `EXP_MONAD_HOM LC_SUBST LC_APP0 LC_ABS
                                           op (h:A->A) g m`)));;
e (STRIP_ASSUME_TAC
    (REWRITE_RULE [IN_MONAD_HOM; LC_SUBST_IN_MONAD]
                  (ASSUME `m:lc->A IN MONAD_HOM (LC_SUBST,op)`)));;
e (REWRITE_TAC[FUN_EQ_THM]);;
e (REWRITE_TAC[FORALL_LC_THM]);;
e (ASM_SIMP_TAC[LC_EXPMAP_FACTOR]);;
e (DBLAMBDA_INDUCT_TAC);;
e (ASM_REWRITE_TAC[GSYM LC_REF; GSYM LC_UNIT; DBLAMBDA_EXPMAP]);;
e (ASM_REWRITE_TAC[GSYM LC_APP; LC_APP_APP0; DBLAMBDA_EXPMAP]);;
e (SUBGOAL_THEN `m (LC_APP0 (LC_PROJ a0)) :A = h (DBLAMBDA_EXPMAP op h g a0)`
    SUBST1_TAC);;
e (ASM_MESON_TAC[]);;
e (AP_THM_TAC THEN AP_TERM_TAC);;
e (REWRITE_TAC[FUN_EQ_THM; o_THM]);;
e (NUM_CASES_TAC THEN ASM_REWRITE_TAC[PUSHENV; NOT_SUC; PRE]);;
e (ASM_REWRITE_TAC[GSYM LC_UNIT]);;
e (ASM_REWRITE_TAC[GSYM LC_ABS; DBLAMBDA_EXPMAP]);;
e (ASM_MESON_TAC[]);;
let LC_EXPMAP_UNIQUE = top_thm ();;
