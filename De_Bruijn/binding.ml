(* ========================================================================= *)
(* Initial semantics for binding signature.                                  *)
(* ========================================================================= *)

prioritize_num();;

new_type_abbrev("signature",`:num#(num list) -> bool`);;

let LC_SIGNATURE = new_definition
  `LC_SIGNATURE:signature = {(0,[0;0]), (1,[1])}`;;

(* ------------------------------------------------------------------------- *)
(* Term algebra.                                                             *)
(* ------------------------------------------------------------------------- *)

let rterm_INDUCTION,rterm_RECURSION = define_type
  "rterm = TMREF num
         | FN num ((num#rterm) list)";;

let RTERM_INDUCT = prove
 (`!P. (!i. P (TMREF i)) /\
       (!c args. (!k x. MEM (k,x) args ==> P x) ==> P (FN c args))
       ==> (!x. P x)`,
  GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN
    `(!x:rterm. P x) /\
     (!l k x. MEM (k:num,x) l ==> P x) /\
     (!p:num#rterm. P (SND p))`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC rterm_INDUCTION THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let WELLFORMED_RULES,WELLFORMED_INDUCT,WELLFORMED_CASES = new_inductive_set
  `(!i. TMREF i IN WELLFORMED (sig:signature)) /\
   (!c args. (c,MAP FST args) IN sig /\
             (!k x. MEM (k,x) args ==> x IN WELLFORMED sig)
             ==> FN c args IN WELLFORMED sig)`;;

let WELLFORMED_TMREF,WELLFORMED_FN =
  CONJ_PAIR (REWRITE_RULE[FORALL_AND_THM] WELLFORMED_RULES);;

(* ------------------------------------------------------------------------- *)
(* Reindexing.                                                               *)
(* ------------------------------------------------------------------------- *)

let TMSLIDE = new_definition
  `TMSLIDE k f i = if i < k then i else k + f (i - k)`;;

let TMSLIDE_I = prove
 (`!k. TMSLIDE k I = I`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; TMSLIDE; I_THM] THEN ARITH_TAC);;

let TMSLIDE_0 = prove
 (`!f. TMSLIDE 0 f = f`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; TMSLIDE; SUB_0] THEN ARITH_TAC);;

let TMSLIDE_1 = prove
 (`!f. TMSLIDE 1 f = SLIDE f`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; TMSLIDE] THEN
  INDUCT_TAC THEN NUM_REDUCE_TAC THEN
  REWRITE_TAC[SLIDE; ARITH_RULE `~(SUC x < 1) /\ SUC x - 1 = x`] THEN
  ARITH_TAC);;

let TMREINDEX = new_recursive_definition rterm_RECURSION
  `(!f i. TMREINDEX f (TMREF i) = TMREF (f i)) /\
   (!f c args. TMREINDEX f (FN c args) = FN c (TMREINDEX_ARGS f args)) /\
   (!f k x. TMREINDEX_ARG f (k,x) = k,TMREINDEX (TMSLIDE k f) x) /\
   (!f. TMREINDEX_ARGS f [] = []) /\
   (!f p args. TMREINDEX_ARGS f (CONS p args) =
               CONS (TMREINDEX_ARG f p) (TMREINDEX_ARGS f args))`;;

let TMREINDEX_ARGS = prove
 (`!f args. TMREINDEX_ARGS f args =
            MAP (\(k,x). k,TMREINDEX (TMSLIDE k f) x) args`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[TMREINDEX; MAP] THEN
  STRUCT_CASES_TAC (ISPEC `h:num#rterm` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[TMREINDEX]);;

let TMREINDEX_CLAUSES = prove
 (`(!f i. TMREINDEX f (TMREF i) = TMREF (f i)) /\
   (!f c args. TMREINDEX f (FN c args) =
               FN c (MAP (\(k,x). k,TMREINDEX (TMSLIDE k f) x) args))`,
  REWRITE_TAC[TMREINDEX; TMREINDEX_ARGS]);;

let TMREINDEX_I = prove
 (`!x. TMREINDEX I x = x`,
  MATCH_MP_TAC RTERM_INDUCT THEN REWRITE_TAC[TMREINDEX_CLAUSES; I_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[injectivity "rterm"; TMSLIDE_I] THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; PAIR_EQ]);;

let TMREINDEX_IN_WELLFORMED = prove
 (`!sig x f. x IN WELLFORMED sig ==> TMREINDEX f x IN WELLFORMED sig`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  REWRITE_TAC[TMREINDEX_CLAUSES; WELLFORMED_RULES; RIGHT_IMP_FORALL_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WELLFORMED_FN THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MAP_o] THEN SUBGOAL_THEN
     `FST o (\(k,x). k,TMREINDEX (TMSLIDE k f) x) = FST`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
   ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Substitution.                                                             *)
(* ------------------------------------------------------------------------- *)

let TMDERIV = new_definition
  `TMDERIV k f i = if i < k then TMREF i else TMREINDEX ((+) k) (f (i - k))`;;

let TMDERIV_0 = prove
 (`!f. TMDERIV 0 f = f`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; TMDERIV; LT; SUB_0] THEN
  SUBGOAL_THEN `(+) 0 = I` (fun th -> REWRITE_TAC[th; TMREINDEX_I]) THEN
  REWRITE_TAC[FUN_EQ_THM; ADD; I_THM]);;

let TMSUBST = new_recursive_definition rterm_RECURSION
  `(!f i. TMSUBST f (TMREF i) = f i) /\
   (!f c args. TMSUBST f (FN c args) = FN c (TMSUBST_ARGS f args)) /\
   (!f k x. TMSUBST_ARG f (k,x) = k,TMSUBST (TMDERIV k f) x) /\
   (!f. TMSUBST_ARGS f [] = []) /\
   (!f p args. TMSUBST_ARGS f (CONS p args) =
               CONS (TMSUBST_ARG f p) (TMSUBST_ARGS f args))`;;

let TMSUBST_ARGS = prove
 (`!f args. TMSUBST_ARGS f args =
            MAP (\(k,x). k,TMSUBST (TMDERIV k f) x) args`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[TMSUBST; MAP] THEN
  STRUCT_CASES_TAC (ISPEC `h:num#rterm` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[TMSUBST]);;

let TMSUBST_CLAUSES = prove
 (`(!f i. TMSUBST f (TMREF i) = f i) /\
   (!f a args. TMSUBST f (FN a args) =
               FN a (MAP (\(k,x). k,TMSUBST (TMDERIV k f) x) args))`,
  REWRITE_TAC[TMSUBST; TMSUBST_ARGS]);;

let TMREINDEX_EQ_TMSUBST = prove
 (`!x f. TMREINDEX f x = TMSUBST (TMREF o f) x`,
  MATCH_MP_TAC RTERM_INDUCT THEN
  REWRITE_TAC[TMSUBST_CLAUSES; TMREINDEX_CLAUSES; o_THM;
              RIGHT_IMP_FORALL_THM] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; PAIR_EQ] THEN
  INTRO_TAC "![k] [x]; kx" THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `TMSUBST (TMREF o TMSLIDE k f) x` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; TMSLIDE; TMDERIV] THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TMREINDEX_CLAUSES]);;

let TMREINDEX_IN_WELLFORMED = prove
 (`!sig x f. x IN WELLFORMED sig ==> TMREINDEX f x IN WELLFORMED sig`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  REWRITE_TAC[TMREINDEX_CLAUSES; WELLFORMED_RULES; RIGHT_IMP_FORALL_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WELLFORMED_FN THEN CONJ_TAC THENL
  [REWRITE_TAC[GSYM MAP_o] THEN SUBGOAL_THEN
     `FST o (\(k,x). k,TMREINDEX (TMSLIDE k f) x) = FST`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
   ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Category of models.                                                       *)
(* ------------------------------------------------------------------------- *)

let MODEL = new_definition
  `MODEL (sig:signature) =
   {s:A->bool,ref,fn,subst |
    (!i:num. ref i IN s) /\
    (!c args. c,MAP FST args IN sig /\
              (!k x. MEM (k,x) args ==> x IN s) ==> fn c args IN s) /\
    (!f i. (!i. f i IN s) ==> subst f (ref i) = f i) /\
    (!f c args.
       (c,MAP FST args) IN sig
       ==> subst f (fn c args) =
           fn c (MAP (\(k,x). k,subst (\i. if i < k then ref i else
                                           subst (ref o ((+) k)) (f (i-k))) x)
                args))}`;;

let IN_MODEL = prove
 (`!sig s:A->bool ref fn subst.
     (s,ref,fn,subst) IN MODEL (sig:signature) <=>
     (!i:num. ref i IN s) /\
     (!c args. c,MAP FST args IN sig /\
               (!k x. MEM (k,x) args ==> x IN s) ==> fn c args IN s) /\
     (!f i. (!i. f i IN s) ==> subst f (ref i) = f i) /\
     (!f c args.
        (c,MAP FST args) IN sig
        ==> subst f (fn c args) =
              fn c (MAP (\(k,x). k,
                                 subst (\i. if i < k then ref i else
                                            subst (ref o ((+) k)) (f (i-k))) x)
                   args))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MODEL; IN_ELIM_THM; PAIR_EQ] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`s:A->bool`; `ref:num->A`; `fn:num->(num#A)list->A`;
                        `subst:(num->A)->A->A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Morphisms of models.                                                      *)
(* ------------------------------------------------------------------------- *)

let MODEL_MOR = new_definition
  `MODEL_MOR (sig:signature)
             (s1:A->bool,ref1,fn1,subst1)
             (s2:B->bool,ref2,fn2,subst2) =
   {h:A->B |
     (s1,ref1,fn1,subst1) IN MODEL sig /\
     (s2,ref2,fn2,subst2) IN MODEL sig /\
     (!x. x IN s1 ==> h x IN s2) /\
     (!i. h (ref1 i) = ref2 i) /\
     (!c args. c,MAP FST args IN sig
               ==> h (fn1 c args) = fn2 c (MAP (\(k,x). k,h x) args)) /\
     (!f x. x IN s1 /\ (!i. f i IN s1)
            ==> h (subst1 f x) = subst2 (h o f) (h x))}`;;

let o_IN_MODEL_MOR = prove
 (`!sig s1 ref1 fn1 subst1
        s2 ref2 fn2 subst2
        s3 ref3 fn3 subst3
        h1:A->B h2:B->C.
     h1 IN MODEL_MOR sig (s1,ref1,fn1,subst1) (s2,ref2,fn2,subst2) /\
     h2 IN MODEL_MOR sig (s2,ref2,fn2,subst2) (s3,ref3,fn3,subst3)
     ==> (h2 o h1) IN MODEL_MOR sig (s1,ref1,fn1,subst1) (s3,ref3,fn3,subst3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MODEL_MOR; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[o_THM; o_ASSOC] THEN REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[GSYM MAP_o] THEN
  SUBGOAL_THEN `FST o (\(k:num,x:A). k,h1 x:B) = FST`
    (fun th -> ASM_REWRITE_TAC[th]) THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Universal property.                                                       *)
(* ------------------------------------------------------------------------- *)

let RTERM_IN_MODEL = prove
 (`!sig. (WELLFORMED sig, TMREF, FN, TMSUBST) IN MODEL sig `,
  GEN_TAC THEN REWRITE_TAC[IN_MODEL; WELLFORMED_RULES; TMSUBST_CLAUSES] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; TMDERIV; TMREINDEX_EQ_TMSUBST]);;

(* ------------------------------------------------------------------------- *)
(* Initial morphism.                                                         *)
(* ------------------------------------------------------------------------- *)

let INITIAL_MORPHISM =
 (new_specification
    ["INITIAL_MORPHISM"; "INITIAL_MORPHISM_ARG"; "INITIAL_MORPHISM_ARGS"] o
  prove)
 (`?INITIAL_MORPHISM INITIAL_MORPHISM_ARG INITIAL_MORPHISM_ARGS. !ref fn.
     (!i. INITIAL_MORPHISM (ref,fn) (TMREF i) = ref i:A) /\
     (!k x. INITIAL_MORPHISM_ARG (ref,fn) (k,x) =
            k,INITIAL_MORPHISM (ref,fn) x) /\
     (!c args. INITIAL_MORPHISM (ref,fn) (FN c args) =
               fn c (INITIAL_MORPHISM_ARGS (ref,fn) args)) /\
     INITIAL_MORPHISM_ARGS (ref,fn) [] = [] /\
     (!p args. INITIAL_MORPHISM_ARGS (ref,fn) (CONS p args) =
               CONS (INITIAL_MORPHISM_ARG (ref,fn) p)
                    (INITIAL_MORPHISM_ARGS (ref,fn) args))`,
  (STRIP_ASSUME_TAC o prove_recursive_functions_exist rterm_RECURSION)
     `(!m i. INITIAL_MORPHISM m (TMREF i) = FST m i:A) /\
      (!m k:num x. INITIAL_MORPHISM_ARG m (k,x) =
                   k,INITIAL_MORPHISM m x) /\
      (!m c:num args. INITIAL_MORPHISM m (FN c args) =
                      SND m c (INITIAL_MORPHISM_ARGS m args)) /\
      (!m. INITIAL_MORPHISM_ARGS m [] = []) /\
      (!m p args. INITIAL_MORPHISM_ARGS m (CONS p args) =
                  CONS (INITIAL_MORPHISM_ARG m p)
                       (INITIAL_MORPHISM_ARGS m args))` THEN
  MAP_EVERY EXISTS_TAC
    [`INITIAL_MORPHISM:(num->A)#(num->(num#A)list->A)->rterm->A`;
     `INITIAL_MORPHISM_ARG:(num->A)#(num->(num#A)list->A)->num#rterm->num#A`;
     `INITIAL_MORPHISM_ARGS
        :(num->A)#(num->(num#A)list->A)->(num#rterm)list->(num#A)list`] THEN
  ASM_REWRITE_TAC[]);;

let INITIAL_MORPHISM_ARGS = prove
 (`!args. INITIAL_MORPHISM_ARGS (ref,fn) args =
          MAP (\(k,x). k,INITIAL_MORPHISM (ref,fn) x:A) args`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[INITIAL_MORPHISM; MAP; GSYM MAP_o] THEN
  STRUCT_CASES_TAC (ISPEC `h:num#rterm` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[INITIAL_MORPHISM]);;

let INITIAL_MORPHISM_CLAUSES = prove
 (`(!i. INITIAL_MORPHISM (ref,fn) (TMREF i) = ref i:A) /\
   (!c args. INITIAL_MORPHISM (ref,fn) (FN c args) =
             fn c (MAP (\(k,x). k,INITIAL_MORPHISM (ref,fn) x:A) args))`,
  REWRITE_TAC[INITIAL_MORPHISM; INITIAL_MORPHISM_ARGS]);;

let INITIAL_MORPHISM_IN = prove
 (`!sig s ref fn subst.
     (s,ref,fn,subst) IN MODEL sig
     ==> !x. x IN WELLFORMED sig ==> INITIAL_MORPHISM (ref,fn) x:A IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MODEL] THEN STRIP_TAC THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  ASM_REWRITE_TAC[INITIAL_MORPHISM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM MAP_o] THEN
   SUBGOAL_THEN `FST o (\(k:num,x). k,INITIAL_MORPHISM (ref,fn) x:A) = FST`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
  ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let INITIAL_MORPHISM_UNIQUE_SIMPLE = prove
 (`!sig ref fn h.
     (!i. h (TMREF i) = ref i:A) /\
     (!c args. c,MAP FST args IN sig
               ==> h (FN c args) = fn c (MAP ((\(k,x). k,h x)) args))
     ==> (!x. x IN WELLFORMED sig ==> h x = INITIAL_MORPHISM (ref,fn) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WELLFORMED_INDUCT THEN
  ASM_SIMP_TAC[INITIAL_MORPHISM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; PAIR_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Compatibility with the monoidal structure.                                *)
(* ------------------------------------------------------------------------- *)

let INITIAL_MORPHISM_TMREINDEX = prove
 (`!sig s ref fn subst.
     (s,ref,fn,subst) IN MODEL sig
     ==> !x f. x IN WELLFORMED sig
               ==> INITIAL_MORPHISM (ref,fn) (TMREINDEX f x):A =
                   subst (ref o f) (INITIAL_MORPHISM (ref,fn) x)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_MODEL]) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  REWRITE_TAC[TMREINDEX_CLAUSES; INITIAL_MORPHISM_CLAUSES] THEN CONJ_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(ref:num->A o f) (i:num):A` THEN
   CONJ_TAC THENL [REWRITE_TAC[o_THM]; MATCH_MP_TAC EQ_SYM] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[o_THM];
   ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MAP_o] THEN FIRST_X_ASSUM (MP_TAC o
     SPECL [`ref:num->A o f:num->num`; `c:num`;
            `(MAP (\(k:num,x). k,INITIAL_MORPHISM (ref,fn) x:A) args)`]) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN
     `MAP FST (MAP (\(k:num,x). k,INITIAL_MORPHISM (ref,fn) x:A) args) =
      MAP FST args`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   REWRITE_TAC[GSYM MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
  MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; FUN_EQ_THM; o_THM; PAIR_EQ] THEN
  INTRO_TAC "![k] [x]; kx" THEN
  REMOVE_THEN "kx" (fun kx -> FIRST_X_ASSUM (MP_TAC o C MATCH_MP kx)) THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; TMSLIDE] THEN FIX_TAC "[i]" THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(ref o (+) k) (f (i - k)):A` THEN CONJ_TAC THENL
  [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[o_THM]);;

let INITIAL_MORPHISM_TMSUBST = prove
 (`!sig s ref fn subst.
     (s,ref,fn,subst) IN MODEL sig
     ==> !x f. x IN WELLFORMED sig /\ (!i. f i IN WELLFORMED sig)
               ==> INITIAL_MORPHISM (ref,fn) (TMSUBST f x):A =
                   subst (INITIAL_MORPHISM (ref,fn) o f)
                         (INITIAL_MORPHISM (ref,fn) x)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_MODEL]) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  REWRITE_TAC[TMSUBST_CLAUSES; INITIAL_MORPHISM_CLAUSES] THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(INITIAL_MORPHISM (ref,fn) o f) (i:num):A` THEN
   CONJ_TAC THENL [REWRITE_TAC[o_THM]; MATCH_MP_TAC EQ_SYM] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN REWRITE_TAC[o_THM] THEN
   USE_THEN "model" (MATCH_MP_TAC o MATCH_MP INITIAL_MORPHISM_IN) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MAP_o] THEN FIRST_X_ASSUM (MP_TAC o
     SPECL [`INITIAL_MORPHISM (ref,fn):rterm->A o f:num->rterm`; `c:num`;
            `(MAP (\(k:num,x). k,INITIAL_MORPHISM (ref,fn) x:A) args)`]) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN
     `MAP FST (MAP (\(k:num,x). k,INITIAL_MORPHISM (ref,fn) x:A) args) =
      MAP FST args`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   REWRITE_TAC[GSYM MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM MAP_o] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  INTRO_TAC "![k] [x]; kx" THEN REWRITE_TAC[o_THM; PAIR_EQ] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`k:num`; `x:rterm`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `TMDERIV k f`) THEN
  ANTS_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[TMDERIV] THEN COND_CASES_TAC THEN
   REWRITE_TAC[WELLFORMED_RULES] THEN ASM_SIMP_TAC[TMREINDEX_IN_WELLFORMED];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TMDERIV; INITIAL_MORPHISM_CLAUSES] THEN
  USE_THEN "model" (MP_TAC o MATCH_MP INITIAL_MORPHISM_TMREINDEX) THEN
  ASM_SIMP_TAC[]);;

let INITIAL_MORPHISM_IN_MODEL_MOR = prove
 (`!sig s ref:num->A fn subst.
     (s,ref,fn,subst) IN MODEL sig
     ==> INITIAL_MORPHISM (ref,fn) IN
           MODEL_MOR sig (WELLFORMED sig,TMREF,FN,TMSUBST) (s,ref,fn,subst)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  ASM_REWRITE_TAC[MODEL_MOR; IN_ELIM_THM; RTERM_IN_MODEL;
                  INITIAL_MORPHISM_CLAUSES] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[INITIAL_MORPHISM_IN];
   ASM_MESON_TAC[INITIAL_MORPHISM_TMSUBST]]);;

let INITIAL_MORPHISM_UNIQUE = prove
 (`!sig s ref:num->A fn subst h.
     (s,ref,fn,subst) IN MODEL sig /\
     h IN MODEL_MOR sig (WELLFORMED sig,TMREF,FN,TMSUBST) (s,ref,fn,subst)
     ==> (!x. x IN WELLFORMED sig ==> h x = INITIAL_MORPHISM (ref,fn) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MODEL_MOR; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC INITIAL_MORPHISM_UNIQUE_SIMPLE THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Monoidal laws.                                                            *)
(* ------------------------------------------------------------------------- *)

let TMREINDEX_TMREINDEX = prove
 (`!x f g. TMREINDEX f (TMREINDEX g x) = TMREINDEX (f o g) x`,
  MATCH_MP_TAC RTERM_INDUCT THEN REWRITE_TAC[TMREINDEX_CLAUSES; o_THM] THEN
  REWRITE_TAC[injectivity "rterm"; GSYM MAP_o] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; PAIR_EQ] THEN
  SUBGOAL_THEN `!k f g. TMSLIDE k (f o g) = TMSLIDE k f o TMSLIDE k g`
    (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; TMSLIDE] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < k` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(m + n < m) /\ (m + n) - m = n`]);;

let TMSUBST_TMREINDEX = prove
 (`!x f g. TMSUBST f (TMREINDEX g x) = TMSUBST (f o g) x`,
  MATCH_MP_TAC RTERM_INDUCT THEN
  REWRITE_TAC[TMREINDEX_CLAUSES; TMSUBST_CLAUSES; o_THM] THEN
  REWRITE_TAC[injectivity "rterm"; GSYM MAP_o] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; PAIR_EQ] THEN
  SUBGOAL_THEN `!k f g. TMDERIV k (f o g) = TMDERIV k f o TMSLIDE k g`
    (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; TMDERIV; TMSLIDE] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < k` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(m + n < m) /\ (m + n) - m = n`]);;

let TMREINDEX_TMSUBST = prove
 (`!x f g. TMREINDEX f (TMSUBST g x) = TMSUBST (TMREINDEX f o g) x`,
  MATCH_MP_TAC RTERM_INDUCT THEN
  REWRITE_TAC[TMREINDEX_CLAUSES; TMSUBST_CLAUSES; o_THM] THEN
  REWRITE_TAC[injectivity "rterm"; GSYM MAP_o] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; PAIR_EQ;
              TMSUBST_TMREINDEX] THEN
  SUBGOAL_THEN `!k f g. TMDERIV k (TMREINDEX f o g) =
                        TMREINDEX (TMSLIDE k f) o TMDERIV k g`
    (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; TMSLIDE; TMDERIV] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < k` THEN
  ASM_REWRITE_TAC[TMREINDEX; TMSLIDE; TMREINDEX_TMREINDEX;
                  ARITH_RULE `~(m + n < m) /\ (m + n) - m = n`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; TMSLIDE;
              ARITH_RULE `~(m + n < m) /\ (m + n) - m = n`]);;

let TMSUBST_TMSUBST = prove
 (`!x f g. TMSUBST f (TMSUBST g x) = TMSUBST (TMSUBST f o g) x`,
  MATCH_MP_TAC RTERM_INDUCT THEN REWRITE_TAC[TMSUBST_CLAUSES; o_THM] THEN
  REWRITE_TAC[injectivity "rterm"; GSYM MAP_o] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; PAIR_EQ] THEN
  SUBGOAL_THEN `!k f g. TMDERIV k (TMSUBST f o g) =
                        TMSUBST (TMDERIV k f) o TMDERIV k g`
    (fun th -> ASM_MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; TMDERIV] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < k` THEN
  ASM_REWRITE_TAC[o_THM; TMSUBST; TMDERIV; TMREINDEX_TMSUBST;
                  TMSUBST_TMREINDEX;
                  ARITH_RULE `~(m + n < m) /\ (m + n) - m = n`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; TMDERIV] THEN
  X_GEN_TAC `j:num` THEN ASM_CASES_TAC `j < k` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(m + n < m) /\ (m + n) - m = n`]);;

(* ------------------------------------------------------------------------- *)
(* Lambda calculus as initial model.                                         *)
(* ------------------------------------------------------------------------- *)

let MAP_EQ_CONS = prove
 (`!f l h:A t. MAP f l = CONS h t <=>
               ?a m. l = CONS a m /\ h = f a /\ MAP f m = t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let DBFN = define
  `(!x y. DBFN 0 [0,x; 0,y] = APP x y) /\
   (!x. DBFN 1 [1,x] = ABS x)`;;

let DBLAMBDA_IN_MODEL = prove
 (`((:dblambda),REF,DBFN,SUBST) IN MODEL LC_SIGNATURE`,
  REWRITE_TAC[IN_MODEL; IN_UNIV; SUBST; LC_SIGNATURE;
              IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_EQ_CONS; MAP_EQ_NIL; EXISTS_PAIR_THM] THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  REWRITE_TAC[DBFN; MAP; SUBST; injectivity "dblambda";
              SUBST_EXTENS; ARITH_RULE `~(i < 0)`; SUB_0] THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_SYM THEN
   REWRITE_TAC[SUBST_REF_EQ; o_THM; ADD];
   INDUCT_TAC THEN
   REWRITE_TAC[DERIV; ARITH_RULE `0 < 1 /\ ~(SUC i < 1) /\ SUC i - 1 = i`] THEN
   INTRO_TAC "_" THEN
   REWRITE_TAC[REINDEX_EQ_SUBST; SUBST_EXTENS; o_THM;
               ARITH_RULE `1 + i = SUC i`]]);;

(* ------------------------------------------------------------------------- *)
(* Embedding of `:dblambda` in `:rterm`.                                     *)
(* ------------------------------------------------------------------------- *)

let RTERM_OF_DBLAMDBA = new_recursive_definition dblambda_RECURSION
  `(!i. RTERM_OF_DBLAMDBA (REF i) = TMREF i) /\
   (!x y. RTERM_OF_DBLAMDBA (APP x y) =
          FN 0 [0,RTERM_OF_DBLAMDBA x;0,RTERM_OF_DBLAMDBA y]) /\
   (!x. RTERM_OF_DBLAMDBA (ABS x) = FN 1 [1,RTERM_OF_DBLAMDBA x])`;;

let RTERM_OF_DBLAMDBA_IN_WELLFORMED = prove
 (`!x. RTERM_OF_DBLAMDBA x IN WELLFORMED LC_SIGNATURE`,
  DBLAMBDA_INDUCT_TAC THEN
  ASM_REWRITE_TAC[RTERM_OF_DBLAMDBA; WELLFORMED_TMREF] THEN
  MATCH_MP_TAC WELLFORMED_FN THEN
  REWRITE_TAC[MEM; PAIR_EQ; LC_SIGNATURE; IN_INSERT; NOT_IN_EMPTY; MAP_EQ_NIL;
              MAP_EQ_CONS; EXISTS_PAIR_THM; CONS_11; ARITH_EQ] THEN
  ASM_MESON_TAC[LC_SIGNATURE; IN_INSERT; NOT_IN_EMPTY; WELLFORMED_RULES]);;

let RTERM_OF_DBLAMDBA_REINDEX = prove
 (`!x f. RTERM_OF_DBLAMDBA (REINDEX f x) =
         TMREINDEX f (RTERM_OF_DBLAMDBA x)`,
  DBLAMBDA_INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[REINDEX; TMREINDEX_CLAUSES; RTERM_OF_DBLAMDBA; MAP;
    TMSLIDE_0; injectivity "rterm"; CONS_11; PAIR_EQ; TMSLIDE_1]);;

let RTERM_OF_DBLAMDBA_SUBST = prove
 (`!x f. RTERM_OF_DBLAMDBA (SUBST f x) =
         TMSUBST (RTERM_OF_DBLAMDBA o f) (RTERM_OF_DBLAMDBA x)`,
  DBLAMBDA_INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUBST; RTERM_OF_DBLAMDBA; TMSUBST_CLAUSES; o_THM;
    injectivity "rterm"; MAP; CONS_11; PAIR_EQ; TMDERIV_0] THEN
  GEN_TAC THEN SUBGOAL_THEN
    `TMDERIV 1 (RTERM_OF_DBLAMDBA o f) = RTERM_OF_DBLAMDBA o DERIV f`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; DERIV; TMDERIV] THEN INDUCT_TAC THEN
  NUM_REDUCE_TAC THEN REWRITE_TAC[DERIV; RTERM_OF_DBLAMDBA] THEN
  REWRITE_TAC[RTERM_OF_DBLAMDBA_REINDEX;
              ARITH_RULE `~(SUC x < 1) /\ SUC x - 1 = x`] THEN
  SUBGOAL_THEN `(+) 1 = SUC` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC);;

let RTERM_OF_DBLAMDBA_IN_MODEL_MOR = prove
 (`RTERM_OF_DBLAMDBA IN
     MODEL_MOR LC_SIGNATURE
      ((:dblambda),REF,DBFN,SUBST)
      (WELLFORMED LC_SIGNATURE, TMREF, FN, TMSUBST)`,
  REWRITE_TAC[MODEL_MOR; IN_ELIM_THM; IN_UNIV; DBLAMBDA_IN_MODEL;
              RTERM_IN_MODEL; RTERM_OF_DBLAMDBA_IN_WELLFORMED;
              RTERM_OF_DBLAMDBA; RTERM_OF_DBLAMDBA_SUBST] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_SIGNATURE; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ; MAP_EQ_NIL;
              MAP_EQ_CONS; EXISTS_PAIR_THM] THEN
  STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  REWRITE_TAC[DBFN; RTERM_OF_DBLAMDBA; MAP]);;

let RTERM_OF_DBLAMDBA_UNIQUE = prove
 (`!h. h IN MODEL_MOR LC_SIGNATURE
             ((:dblambda),REF,DBFN,SUBST)
             (WELLFORMED LC_SIGNATURE, TMREF, FN, TMSUBST)
       ==> (!x. h x = RTERM_OF_DBLAMDBA x)`,
  INTRO_TAC "!h; h" THEN USE_THEN "h" MP_TAC THEN
  REWRITE_TAC[MODEL_MOR; IN_ELIM_THM; IN_UNIV] THEN
  INTRO_TAC "_ _ wf ref fn subst" THEN
  DBLAMBDA_INDUCT_TAC THEN ASM_REWRITE_TAC[RTERM_OF_DBLAMDBA] THENL
  [TRANS_TAC EQ_TRANS `h (DBFN 0 [0,a0; 0,a1]):rterm` THEN CONJ_TAC THENL
   [REWRITE_TAC[DBFN]; ALL_TAC] THEN
   REMOVE_THEN "fn" (fun th -> IMP_REWRITE_TAC[th]) THEN
   ASM_REWRITE_TAC[LC_SIGNATURE; IN_INSERT; MAP];
   ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `h (DBFN 1 [1,a]):rterm` THEN CONJ_TAC THENL
  [REWRITE_TAC[DBFN]; ALL_TAC] THEN
  REMOVE_THEN "fn" (fun th -> IMP_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[LC_SIGNATURE; IN_INSERT; MAP]);;

(* ------------------------------------------------------------------------- *)
(* The morphisms `RTERM_OF_DBLAMDBA` and `INITIAL_MORPHISM` are reciprocal   *)
(* side inverses.                                                            *)
(* ------------------------------------------------------------------------- *)

let RTERM_OF_DBLAMDBA_INITIAL_MORPHISM = prove
 (`!x. x IN WELLFORMED LC_SIGNATURE
       ==> RTERM_OF_DBLAMDBA (INITIAL_MORPHISM (REF,DBFN) x) = x`,
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  REWRITE_TAC[INITIAL_MORPHISM_CLAUSES; RTERM_OF_DBLAMDBA] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LC_SIGNATURE; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ;
              MAP_EQ_NIL; MAP_EQ_CONS; EXISTS_PAIR_THM] THEN
  STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  REWRITE_TAC[DBFN; MAP; RTERM_OF_DBLAMDBA] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[MEM; PAIR_EQ]) THEN ASM_MESON_TAC[]);;

let INITIAL_MORPHISM_RTERM_OF_DBLAMDBA = prove
 (`!x. INITIAL_MORPHISM (REF,DBFN) (RTERM_OF_DBLAMDBA x) = x`,
  DBLAMBDA_INDUCT_TAC THEN
  ASM_REWRITE_TAC[RTERM_OF_DBLAMDBA; INITIAL_MORPHISM_CLAUSES; MAP; DBFN]);;

let RTERM_OF_DBLAMDBA_INJ = prove
 (`!x y. RTERM_OF_DBLAMDBA x = RTERM_OF_DBLAMDBA y <=> x = y`,
  MESON_TAC[INITIAL_MORPHISM_RTERM_OF_DBLAMDBA]);;

let INITIAL_MORPHISM_SURJ = prove
 (`!x. ?y. y IN WELLFORMED LC_SIGNATURE /\
           x = INITIAL_MORPHISM (REF,DBFN) y`,
  MESON_TAC[INITIAL_MORPHISM_RTERM_OF_DBLAMDBA;
            RTERM_OF_DBLAMDBA_IN_WELLFORMED]);;

let FORALL_DBLAMBDA = prove
 (`(!x. P x) <=>
   (!x. x IN WELLFORMED LC_SIGNATURE ==> P (INITIAL_MORPHISM (REF,DBFN) x))`,
  MESON_TAC[INITIAL_MORPHISM_SURJ]);;

(* ------------------------------------------------------------------------- *)
(* Universal property of the syntactic lambda calculus as special            *)
(* case of the teory of binding signatures.                                  *)
(* ------------------------------------------------------------------------- *)

let DBLAMBDA_UNIVERSAL = prove
 (`!s ref:num->A fn subst.
     (s,ref,fn,subst) IN MODEL LC_SIGNATURE
     ==> ?h. h IN MODEL_MOR LC_SIGNATURE
                    ((:dblambda),REF,DBFN,SUBST) (s,ref,fn,subst) /\
             (!h'. h' IN MODEL_MOR LC_SIGNATURE
                          ((:dblambda),REF,DBFN,SUBST) (s,ref,fn,subst)
                   ==> h'= h)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  EXISTS_TAC `INITIAL_MORPHISM (ref,fn):rterm->A o RTERM_OF_DBLAMDBA` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC o_IN_MODEL_MOR THEN
   ASM_MESON_TAC[INITIAL_MORPHISM_IN_MODEL_MOR;
                 RTERM_OF_DBLAMDBA_IN_MODEL_MOR];
   ALL_TAC] THEN
  INTRO_TAC "!h'; h'" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_DBLAMBDA] THEN
  SIMP_TAC[RTERM_OF_DBLAMDBA_INITIAL_MORPHISM] THEN
  REWRITE_TAC[GSYM (REWRITE_CONV[o_THM]
    `(f o INITIAL_MORPHISM (REF,DBFN)) x:A`)] THEN
  MATCH_MP_TAC INITIAL_MORPHISM_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`s:A->bool`;`subst:(num->A)->A->A`] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC o_IN_MODEL_MOR THEN
  ASM_MESON_TAC[INITIAL_MORPHISM_IN_MODEL_MOR; DBLAMBDA_IN_MODEL]);;

(* ------------------------------------------------------------------------- *)
(* Functoriality of the category of models w.r.t. the signatures.            *)
(* ------------------------------------------------------------------------- *)

let MODEL_MONO = prove
 (`!sig1 sig2. sig1 SUBSET sig2 ==> MODEL sig2 SUBSET MODEL sig1`,
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN INTRO_TAC "!sig1 sig2; sub" THEN
  INTRO_TAC "![s] [ref] [fn] [subst]" THEN REWRITE_TAC[IN_MODEL] THEN
  INTRO_TAC "ref fn s1 s2" THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REMOVE_THEN "fn" MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN REMOVE_THEN "sub" MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN IMP_REWRITE_TAC[]);;

let MODEL_MOR_MONO = prove
 (`!sig1 sig2 s1 ref1 fn1 subst1 s2 ref2 fn2 subst2.
     sig1 SUBSET sig2 /\
     (s1,ref1,fn1,subst1) IN MODEL sig2 /\
     (s2,ref2,fn2,subst2) IN MODEL sig2
     ==> MODEL_MOR sig2 (s1,ref1,fn1,subst1) (s2,ref2,fn2,subst2) SUBSET
          MODEL_MOR sig1 (s1,ref1,fn1,subst1) (s2,ref2,fn2,subst2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN INTRO_TAC "sub m1 m2; ![h]" THEN
  ASM_REWRITE_TAC[MODEL_MOR; IN_ELIM_THM] THEN INTRO_TAC "h href hfn" THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET; MODEL_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Functoriality of the initial semantics w.r.t. signatures.                 *)
(* ------------------------------------------------------------------------- *)

let WELLFORMED_MONO = prove
 (`!sig1 sig2. sig1 SUBSET sig2 ==> WELLFORMED sig1 SUBSET WELLFORMED sig2`,
  INTRO_TAC "!sig1 sig2; sub" THEN REWRITE_TAC[SUBSET] THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN REWRITE_TAC[WELLFORMED_TMREF] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WELLFORMED_FN THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;
