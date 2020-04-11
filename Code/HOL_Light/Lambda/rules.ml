let lcrel_INDUCT,lcrel_RECUR = define_type
  "lcrel = LCREL_REFL dblambda
         | LCREL_TRANS lcrel lcrel
         | LCREL_APP lcrel lcrel
         | LCREL_ABS lcrel
         | LCREL_BETA dblambda dblambda
         | LCREL_ETA dblambda";;

let RED_RULES,RED_INDUCT,RED_CASES = new_inductive_definition
  `(!x. RED x x (LCREL_REFL x)) /\
   (!x y z r s. RED x y r /\ RED y z s ==> RED x z (LCREL_TRANS r s)) /\
   (!x1 x2 y1 y2 r1 r2. RED x1 y1 r1 /\ RED x2 y2 r2
      ==> RED (APP x1 x2) (APP y1 y2) (LCREL_APP r1 r2)) /\
   (!x y r. RED x y r ==> RED (ABS x) (ABS y) (LCREL_ABS r)) /\
   (!x y. RED (APP (ABS x) y) (SUBST (PUSHENV y REF) x) (LCREL_BETA x y)) /\
   (!x. RED (ABS (APP (REINDEX SUC x) (REF 0))) x (LCREL_ETA x))`;;

let [RED_REFL;RED_TRANS;RED_APP;RED_ABS;RED_BETA;RED_ETA] =
  CONJUNCTS RED_RULES;;

let RED_INDUCT_STRONG = derive_strong_induction (RED_RULES,RED_INDUCT);;

let RED_IMP_LC_REL = prove
 (`!x y r. RED x y r ==> REDREL x y`,
  MATCH_MP_TAC RED_INDUCT THEN REWRITE_TAC[REDREL_RULES] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
  [MATCH_MP_TAC REDREL_BETA; MATCH_MP_TAC REDREL_ETA] THEN
  REWRITE_TAC[DBLAMBDA_BETA_RULES; DBLAMBDA_ETA_RULES]);;

let REDREL_EQ_RED = prove
 (`!x y. REDREL x y <=> ?r. RED x y r`,
  SUBGOAL_THEN `!x y. REDREL x y ==> ?r. RED x y r`
   (fun th -> MESON_TAC[th; RED_IMP_LC_REL]) THEN
  MATCH_MP_TAC REDREL_INDUCT THEN CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_BETA_INDUCT THEN GEN_TAC THEN GEN_TAC THEN
   EXISTS_TAC `LCREL_BETA x y` THEN REWRITE_TAC[RED_RULES];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_ETA_INDUCT THEN GEN_TAC THEN
   EXISTS_TAC `LCREL_ETA x` THEN REWRITE_TAC[RED_RULES];
   ALL_TAC] THEN
  MESON_TAC[RED_RULES]);;

let RED1 = new_recursive_definition lcrel_RECUR
  `(!x. RED1 (LCREL_REFL x) = x) /\
   (!r s. RED1 (LCREL_TRANS r s) = RED1 r) /\
   (!r s. RED1 (LCREL_APP r s) = APP (RED1 r) (RED1 s)) /\
   (!r. RED1 (LCREL_ABS r) = ABS (RED1 r)) /\
   (!x y. RED1 (LCREL_BETA x y) = APP (ABS x) y) /\
   (!x. RED1 (LCREL_ETA x) = ABS (APP (REINDEX SUC x) (REF 0)))`;;

let RED2 = new_recursive_definition lcrel_RECUR
  `(!x. RED2 (LCREL_REFL x) = x) /\
   (!r s. RED2 (LCREL_TRANS r s) = RED2 s) /\
   (!r s. RED2 (LCREL_APP r s) = APP (RED2 r) (RED2 s)) /\
   (!r. RED2 (LCREL_ABS r) = ABS (RED2 r)) /\
   (!x y. RED2 (LCREL_BETA x y) = SUBST (PUSHENV y REF) x) /\
   (!x. RED2 (LCREL_ETA x) = x)`;;

let RED_PROJECTIONS = prove
 (`!x y r. RED x y r ==> RED1 r = x /\ RED2 r = y`,
  MATCH_MP_TAC RED_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[RED1; RED2]);;

let RFREES_RULES,RFREES_INDUCT,RFREES_CASES = new_inductive_set
  `(!i x. i IN FREES x ==> i IN RFREES (LCREL_REFL x)) /\
   (!i r s. i IN RFREES r ==> i IN RFREES (LCREL_TRANS r s)) /\
   (!i r s. i IN RFREES s ==> i IN RFREES (LCREL_TRANS r s)) /\
   (!i r s. i IN RFREES r ==> i IN RFREES (LCREL_APP r s)) /\
   (!i r s. i IN RFREES s ==> i IN RFREES (LCREL_APP r s)) /\
   (!i r. SUC i IN RFREES r ==> i IN RFREES (LCREL_ABS r)) /\
   (!i x y. SUC i IN FREES x ==> i IN RFREES (LCREL_BETA x y)) /\
   (!i x y. i IN FREES y ==> i IN RFREES (LCREL_BETA x y)) /\
   (!i x. i IN FREES x ==> i IN RFREES (LCREL_ETA x))`;;

let RFREES_INVERSION = prove
 (`(!i x. i IN RFREES (LCREL_REFL x) <=> i IN FREES x) /\
   (!i r s. i IN RFREES (LCREL_TRANS r s) <=>
            i IN RFREES r \/ i IN RFREES s) /\
   (!i r s. i IN RFREES (LCREL_APP r s) <=> i IN RFREES r \/ i IN RFREES s) /\
   (!i r. i IN RFREES (LCREL_ABS r) <=> SUC i IN RFREES r) /\
   (!i r s x. i IN RFREES (LCREL_BETA x y) <=>
              SUC i IN FREES x \/ i IN FREES y) /\
   (!i r s x. i IN RFREES (LCREL_ETA x) <=> i IN FREES x)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RFREES_CASES] THEN
  REWRITE_TAC[distinctness "lcrel"; injectivity "lcrel"; UNWIND_THM1] THEN
  MESON_TAC[]);;

let RFREES_CLAUSES = prove
 (`(!x. RFREES (LCREL_REFL x) = FREES x) /\
   (!r s. RFREES (LCREL_TRANS r s) = RFREES r UNION RFREES s) /\
   (!r s. RFREES (LCREL_APP r s) = RFREES r UNION RFREES s) /\
   (!r. RFREES (LCREL_ABS r) = {i | SUC i IN RFREES r}) /\
   (!r s x. RFREES (LCREL_BETA x y) = {i | SUC i IN FREES x} UNION FREES y) /\
   (!r s x. RFREES (LCREL_ETA x) = FREES x)`,
  REWRITE_TAC[EXTENSION; RFREES_INVERSION] THEN SET_TAC[]);;

let RSUBST = new_recursive_definition lcrel_RECUR
  `(!f x. RSUBST f (LCREL_REFL x) = LCREL_REFL (SUBST f x)) /\
   (!f r s. RSUBST f (LCREL_TRANS r s) =
            LCREL_TRANS (RSUBST f r) (RSUBST f s)) /\
   (!f r s. RSUBST f (LCREL_APP r s) = LCREL_APP (RSUBST f r) (RSUBST f s)) /\
   (!f r. RSUBST f (LCREL_ABS r) = LCREL_ABS (RSUBST (DERIV f) r)) /\
   (!f x y. RSUBST f (LCREL_BETA x y) =
            LCREL_BETA (SUBST (DERIV f) x) (SUBST f y)) /\
   (!f x. RSUBST f (LCREL_ETA x) = LCREL_ETA (SUBST f x))`;;

let RSUBST_EXTENS = prove
 (`!r f g. RSUBST f r = RSUBST g r <=> (!i. i IN RFREES r ==> f i = g i)`,
  MATCH_MP_TAC lcrel_INDUCT THEN
  REWRITE_TAC[RSUBST; RFREES_INVERSION; injectivity "lcrel"; SUBST_EXTENS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DERIV_EXTENS] THEN
  METIS_TAC[PRE; NOT_SUC; cases "num"]);;

let RSUBST_SUBST = prove
 (`!r f g. RSUBST f (RSUBST g r) = RSUBST (SUBST f o g) r`,
  MATCH_MP_TAC lcrel_INDUCT THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[RSUBST; SUBST_SUBST; injectivity "lcrel";
                  RSUBST_EXTENS; SUBST_EXTENS; o_THM; SUBST_DERIV]);;

let RSUBST_REF = prove
 (`!r. RSUBST REF r = r`,
  MATCH_MP_TAC lcrel_INDUCT THEN
  REWRITE_TAC[RSUBST; SUBST_REF; DERIV_REF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBST_RED1 = prove
 (`!r f. SUBST f (RED1 r) = RED1 (RSUBST f r)`,
  MATCH_MP_TAC lcrel_INDUCT THEN REWRITE_TAC[RED1; RSUBST; SUBST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "dblambda"; DERIV] THEN
  REWRITE_TAC[SUBST_REINDEX; REINDEX_SUBST; SUBST_EXTENS; o_THM; DERIV]);;

let SUBST_RED2 = prove
 (`!r f. SUBST f (RED2 r) = RED2 (RSUBST f r)`,
  MATCH_MP_TAC lcrel_INDUCT THEN REWRITE_TAC[RED2; RSUBST; SUBST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST_SUBST; SUBST_EXTENS; o_THM; SUBST_DERIV] THEN
  GEN_TAC THEN DISCH_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[DERIV; PUSHENV; SUBST; SUBST_REINDEX] THEN
  MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC[SUBST_REF_EQ; o_THM; PUSHENV]);;

let MODULE_RSUBST = prove
 (`MODULE SUBST RSUBST`,
  REWRITE_TAC[MODULE_DEF; DBLAMBDA_DBMONAD; DBLAMBDA_DBUNIT;
              RSUBST_REF; RSUBST_SUBST]);;

let MODULE_SUBST = prove
 (`MODULE SUBST SUBST`,
  REWRITE_TAC[MODULE_DEF; DBLAMBDA_DBMONAD; DBLAMBDA_DBUNIT;
              SUBST_REF; SUBST_SUBST]);;

let MODULE_MOR_RED1 = prove
 (`MODULE_MOR SUBST RSUBST SUBST RED1`,
  REWRITE_TAC[MODULE_MOR; MODULE_RSUBST; MODULE_SUBST; SUBST_RED1]);;

let MODULE_MOR_RED2 = prove
 (`MODULE_MOR SUBST RSUBST SUBST RED2`,
  REWRITE_TAC[MODULE_MOR; MODULE_RSUBST; MODULE_SUBST; SUBST_RED2]);;
