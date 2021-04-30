(* ========================================================================= *)
(* Explict substitution lambda-nu (Lascanne)                                 *)
(* ========================================================================= *)

(* 
loadt "Lambda/make.ml";;
*)

let eterm_INDUCT,eterm_RECUR = define_type
  "eterm  = EREF num
          | EAPP eterm eterm
          | EABS eterm
          | ESUBST eterm esubst;
   esubst = ETERM eterm
          | EBUMP
          | EDERIV esubst";;

let eterm_CASES, esubst_CASES = CONJ_PAIR (cases "eterm");;

let aterm_INDUCT,eterm_RECUR = define_type
  "aterm  = AREF num
          | AAPP aterm aterm
          | AABS aterm
          | ASUBST aterm asubst;
   asubst = AFUN (num -> aterm)";;

(* ------------------------------------------------------------------------- *)
(* Intended semantics into the standard lambda calculus.                     *)
(* ------------------------------------------------------------------------- *)

let SEM = new_recursive_definition eterm_RECUR
  `(!i. SEM (EREF i) = REF i) /\
   (!x y. SEM (EAPP x y) = APP (SEM x) (SEM y)) /\
   (!x. SEM (EABS x) = ABS (SEM x)) /\
   (!x s. SEM (ESUBST x s) = SUBST (SEMSUBST s) (SEM x)) /\
   (!u. SEMSUBST (ETERM u) = PUSHENV (SEM u) REF) /\
   (SEMSUBST EBUMP = REF o SUC) /\
   (!s. SEMSUBST (EDERIV s) = DERIV (SEMSUBST s))`;;

(* ------------------------------------------------------------------------- *)
(* Implicit reindexing.                                                      *)
(* ------------------------------------------------------------------------- *)

let IREINDEX = new_recursive_definition eterm_RECUR
  `(!f i. IREINDEX f (EREF i) = EREF (f i)) /\
   (!f x y. IREINDEX f (EAPP x y) = EAPP (IREINDEX f x) (IREINDEX f y)) /\
   (!f x. IREINDEX f (EABS x) = EABS (IREINDEX (SLIDE f) x)) /\
   (!f x s. IREINDEX f (ESUBST x s) =
            ESUBST (IREINDEX (SLIDE f) x) (IREINDEX_SUBST f s)) /\
   (!f u. IREINDEX_SUBST f (ETERM u) = ETERM (IREINDEX f u)) /\
   (!f. IREINDEX_SUBST f EBUMP = EBUMP) /\
   (!f s. IREINDEX_SUBST f (EDERIV s) = EDERIV (IREINDEX_SUBST f s))`;;

let SEM_IREINDEX = prove
 (`(!x f. SEM (IREINDEX f x) = REINDEX f (SEM x)) /\
   (!s f. SEMSUBST (IREINDEX_SUBST f s) = REINDEX f o SEMSUBST s)`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IREINDEX; SEM; REINDEX; FUN_EQ_THM; o_THM;
                  SUBST_REINDEX; REINDEX_SUBST; o_ASSOC]
  REWRITE_TAC[SUBST_EXTENS; o_THM]
  GEN_THEN (fun v -> DISCH_THEN (K ALL_TAC) THEN CASES_TAC v)
  REWRITE_TAC[SLIDE]
  
  );;

let H_SIMPLE_EXTENS = prove
 (`!H:(A->B)->(C->D) x f g. (!i. f i = g i) ==> H f x = H g x`,
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM]);;

let IREINDEX_IREINDEX = prove
 (`(!x f g. IREINDEX f (IREINDEX g x) = IREINDEX (f o g) x) /\
   (!s f g. IREINDEX_SUBST f (IREINDEX_SUBST g s) =
            IREINDEX_SUBST (f o g) s)`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IREINDEX; o_THM; injectivity "eterm"] THEN
  MATCH_MP_TAC H_SIMPLE_EXTENS THEN REWRITE_TAC[o_THM; SLIDE_SLIDE]);;

let IREINDEX_INJ = prove
 (`(!x y f. (!i j. f i = f j ==> i = j)
            ==> (IREINDEX f x = IREINDEX f y <=> x = y)) /\
   (!s t f. (!i j. f i = f j ==> i = j)
            ==> (IREINDEX_SUBST f s = IREINDEX_SUBST f t <=> s = t))`,
  MATCH_MP_TAC eterm_INDUCT THEN REPEAT CONJ_TAC THEN
  ((FIX_TAC "y" THEN STRUCT_CASES_TAC (ISPEC `y:eterm` eterm_CASES)) ORELSE
   (FIX_TAC "t" THEN STRUCT_CASES_TAC (ISPEC `t:esubst` esubst_CASES))) THEN
  ASM_REWRITE_TAC[IREINDEX; injectivity "eterm"; distinctness "eterm"] THEN
  MESON_TAC[SLIDE_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Derivation.                                                               *)
(* ------------------------------------------------------------------------- *)

let IDERIV = new_recursive_definition num_RECURSION
  `(!f. IDERIV f 0 = EREF 0) /\
   (!f i. IDERIV f (SUC i) = IREINDEX SUC (f i))`;;

let IDERIV_EREF = prove
 (`IDERIV EREF = EREF`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN REWRITE_TAC[IDERIV; IREINDEX]);;

let IDERIV_EXTENS = prove
 (`!f g i. IDERIV f i = IDERIV g i <=> i = 0 \/ f (PRE i) = g (PRE i)`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[IDERIV; NOT_SUC; PRE] THEN SIMP_TAC[IREINDEX_INJ; SUC_INJ]);;

let IDERIV_SLIDE = prove
 (`!f g i. IDERIV g (SLIDE f i) = IDERIV (g o f) i`,
  GEN_TAC THEN GEN_TAC THEN CASES_GEN_TAC THEN
  REWRITE_TAC[IDERIV; SLIDE; o_THM]);;

let IDERIV_O_SUC = prove
 (`!f. IDERIV f o SUC = IREINDEX SUC o f`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; IDERIV]);;

(* ------------------------------------------------------------------------- *)
(* Implicit substitution.                                                    *)
(* ------------------------------------------------------------------------- *)

let ISUBST = new_recursive_definition dblambda_RECURSION
  `(!f i. ISUBST f (EREF i) = f i) /\
   (!f x y. ISUBST f (EAPP x y) = EAPP (ISUBST f x) (ISUBST f y)) /\
   (!f x. ISUBST f (EABS x) = EABS (ISUBST (IDERIV f) x)) /\
   (!f x s. ISUBST f (ESUBST x s) =
            ESUBST (ISUBST (IDERIV f) x) (ISUBST_SUBST f s)) /\
   (!f u. ISUBST_SUBST f (ETERM u) = ETERM (ISUBST f u)) /\
   (!f. ISUBST_SUBST f EBUMP = EBUMP)
   `;;
