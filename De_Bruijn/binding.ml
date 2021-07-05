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

let MODEL_HOM = new_definition
  `MODEL_HOM (sig:signature)
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

let INITIAL_MORPHISM = new_recursive_definition rterm_RECURSION
  `(!i. INITIAL_MORPHISM ref fn (TMREF i) = ref i:A) /\
   (!k x. INITIAL_MORPHISM_ARG ref fn (k,x) = k,INITIAL_MORPHISM ref fn x) /\
   (!c args. INITIAL_MORPHISM ref fn (FN c args) =
             fn c (INITIAL_MORPHISM_ARGS ref fn args)) /\
   INITIAL_MORPHISM_ARGS ref fn [] = [] /\
   (!p args. INITIAL_MORPHISM_ARGS ref fn (CONS p args) =
             CONS (INITIAL_MORPHISM_ARG ref fn p)
                  (INITIAL_MORPHISM_ARGS ref fn args))`;;

let INITIAL_MORPHISM_ARGS = prove
 (`!args. INITIAL_MORPHISM_ARGS ref fn args =
          MAP (\(k,x). k,INITIAL_MORPHISM ref fn x:A) args`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[INITIAL_MORPHISM; MAP; GSYM MAP_o] THEN
  STRUCT_CASES_TAC (ISPEC `h:num#rterm` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[INITIAL_MORPHISM]);;

let INITIAL_MORPHISM_CLAUSES = prove
 (`(!i. INITIAL_MORPHISM ref fn (TMREF i) = ref i:A) /\
   (!c args. INITIAL_MORPHISM ref fn (FN c args) =
             fn c (MAP (\(k,x). k,INITIAL_MORPHISM ref fn x:A) args))`,
  REWRITE_TAC[INITIAL_MORPHISM; INITIAL_MORPHISM_ARGS]);;

let INITIAL_MORPHISM_IN = prove
 (`!sig s ref fn subst.
     (s,ref,fn,subst) IN MODEL sig
     ==> !x. x IN WELLFORMED sig ==> INITIAL_MORPHISM ref fn x:A IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MODEL] THEN STRIP_TAC THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  ASM_REWRITE_TAC[INITIAL_MORPHISM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM MAP_o] THEN
   SUBGOAL_THEN `FST o (\(k:num,x). k,INITIAL_MORPHISM ref fn x:A) = FST`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
  ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let INITIAL_MORPHISM_UNIQUE_SIMPLE = prove
 (`!sig ref fn h.
     (!i. h (TMREF i) = ref i:A) /\
     (!c args. c,MAP FST args IN sig
               ==> h (FN c args) = fn c (MAP ((\(k,x). k,h x)) args))
     ==> (!x. x IN WELLFORMED sig ==> h x = INITIAL_MORPHISM ref fn x)`,
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
               ==> INITIAL_MORPHISM ref fn (TMREINDEX f x):A =
                   subst (ref o f) (INITIAL_MORPHISM ref fn x)`,
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
            `(MAP (\(k:num,x). k,INITIAL_MORPHISM ref fn x:A) args)`]) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN
     `MAP FST (MAP (\(k:num,x). k,INITIAL_MORPHISM ref fn x:A) args) =
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
               ==> INITIAL_MORPHISM ref fn (TMSUBST f x):A =
                   subst (INITIAL_MORPHISM ref fn o f)
                         (INITIAL_MORPHISM ref fn x)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_MODEL]) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC WELLFORMED_INDUCT THEN
  REWRITE_TAC[TMSUBST_CLAUSES; INITIAL_MORPHISM_CLAUSES] THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(INITIAL_MORPHISM ref fn o f) (i:num):A` THEN
   CONJ_TAC THENL [REWRITE_TAC[o_THM]; MATCH_MP_TAC EQ_SYM] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN REWRITE_TAC[o_THM] THEN
   USE_THEN "model" (MATCH_MP_TAC o MATCH_MP INITIAL_MORPHISM_IN) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MAP_o] THEN FIRST_X_ASSUM (MP_TAC o
     SPECL [`INITIAL_MORPHISM ref fn:rterm->A o f:num->rterm`; `c:num`;
            `(MAP (\(k:num,x). k,INITIAL_MORPHISM ref fn x:A) args)`]) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN
     `MAP FST (MAP (\(k:num,x). k,INITIAL_MORPHISM ref fn x:A) args) =
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

let INITIAL_MORPHISM_IN_MODEL_HOM = prove
 (`!sig s ref:num->A fn subst.
     (s,ref,fn,subst) IN MODEL sig
     ==> INITIAL_MORPHISM ref fn IN MODEL_HOM sig
                                    (WELLFORMED sig,TMREF,FN,TMSUBST)
                                    (s,ref,fn,subst)`,
  REPEAT GEN_TAC THEN INTRO_TAC "model" THEN
  ASM_REWRITE_TAC[MODEL_HOM; IN_ELIM_THM; RTERM_IN_MODEL;
                  INITIAL_MORPHISM_CLAUSES] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[INITIAL_MORPHISM_IN];
   ASM_MESON_TAC[INITIAL_MORPHISM_TMSUBST]]);;

let INITIAL_MORPHISM_UNIQUE = prove
 (`!sig s ref:num->A fn subst h.
     (s,ref,fn,subst) IN MODEL sig /\
     h IN MODEL_HOM sig (WELLFORMED sig,TMREF,FN,TMSUBST) (s,ref,fn,subst)
     ==> (!x. x IN WELLFORMED sig ==> h x = INITIAL_MORPHISM ref fn x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MODEL_HOM; IN_ELIM_THM] THEN STRIP_TAC THEN
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
