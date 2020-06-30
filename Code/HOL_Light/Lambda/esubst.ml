(* ========================================================================= *)
(* Lambda calculus with explicit substitutions.                              *)
(* See Abadi et al.                                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Failed attempt: Abandoned!                                                *)
(* We are not able to provide a DB-monad structure.                          *)
(* Laws hold only up to some equivalence relation.                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Datatype for terms and object substitutions.                              *)
(* ------------------------------------------------------------------------- *)

let eterm_INDUCT,eterm_RECUR = define_type
  "eterm  = EREF0
          | EAPP eterm eterm
          | EABS eterm
          | ESUBST eterm esubst;
   esubst = EID
          | ESHIFT1
          | EPUSH eterm esubst
          | ECOMP esubst esubst";;

(* ------------------------------------------------------------------------- *)
(* Reduction relation. (Proof-irrelevant version.)                           *)
(* The constants `ETERMRED` and `ESUBSTRED` denote the one-step              *)
(* reduction relations between eterms and esubstitutions respectively.       *)
(* They are written infix as `>_t1` and `>_s1`).                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(">_t1",(12, "right"));;  (* Reduction for eterms `ETERMRED`   *)
parse_as_infix(">_s1",(12, "right"));;  (* Reduction for esubsts `ESUBSTRED` *)

let ERED1_RULES,ERED1_INDUCT,ERED1_CASES =
  (new_inductive_definition o
   vsubst [`ETERMRED:eterm->eterm->bool`,`(>_t1):eterm->eterm->bool`;
           `ESUBSTRED:esubst->esubst->bool`,`(>_s1):esubst->esubst->bool`])
  `ESUBST EREF0 EID >_t1 EREF0 /\
   (!x s. ESUBST EREF0 (EPUSH x s) >_t1 x) /\
   (!x y s.  ESUBST (EAPP x y) s >_t1 EAPP (ESUBST x s) (ESUBST y s)) /\
   (!x s. ESUBST (EABS x) s >_t1
          EABS (ESUBST x (EPUSH EREF0 (ECOMP s ESHIFT1)))) /\
   (!x s t. ESUBST (ESUBST x s) t >_t1 ESUBST x (ECOMP s t)) /\

   (!x y. EAPP (EABS x) y >_t1 ESUBST x (EPUSH y EID)) /\

   (!s. ECOMP EID s >_s1 s) /\
   ECOMP ESHIFT1 EID >_s1 ESHIFT1 /\
   (!x s. ECOMP ESHIFT1 (EPUSH x s) >_s1 s) /\
   (!x s t. ECOMP (EPUSH x s) t >_s1 EPUSH (ESUBST x t) (ECOMP s t)) /\
   (!r s t. ECOMP (ECOMP r s) t >_s1 ECOMP r (ECOMP s t))`;;

override_interface(">_t1",`ETERMRED`);;
override_interface(">_s1",`ESUBSTRED`);;

let [ERED1_EREF0_EID; ERED1_ESUBST_EREF0_EPUSH; ERED1_ESUBST_EAPP;
     ERED1_ESUBST_EABS; ERED1_ESUBST_ESUBST; ERED1_BETA; ERED1_ECOMP_EID;
     ERED1_ECOMP_ESHIFT1_EID; ECOMP_ESHIFT1_EPUSH; ERED1_ECOMP_EPUSH;
     ERED1_ECOMP_ECOMP] =
  CONJUNCTS ERED1_RULES;;

(* ------------------------------------------------------------------------- *)
(* Congurence closure of a reduction relation.                               *)
(* ------------------------------------------------------------------------- *)

let ETERMCONG_RULES,ETERMCONG_INDUCT,ETERMCONG_CASES = new_inductive_definition
  `(!x x'. R x x' ==> ETERMCONG R S x x') /\
   (!x x' y. ETERMCONG R S x x' ==> ETERMCONG R S (EAPP x y) (EAPP x' y)) /\
   (!x y y'. ETERMCONG R S y y' ==> ETERMCONG R S (EAPP x y) (EAPP x y')) /\
   (!x x'. ETERMCONG R S x x' ==> ETERMCONG R S (EABS x) (EABS x')) /\
   (!x x' s. ETERMCONG R S x x'
             ==> ETERMCONG R S (ESUBST x s) (ESUBST x' s)) /\
   (!x s s'. ESUBSTCONG R S s s'
             ==> ETERMCONG R S (ESUBST x s) (ESUBST x s')) /\
   (!s s'. S s s' ==> ESUBSTCONG R S s s') /\
   (!x x' s. ETERMCONG R S x x'
             ==> ESUBSTCONG R S (EPUSH x s) (EPUSH x' s)) /\
   (!x s s'. ESUBSTCONG R S s s'
             ==> ESUBSTCONG R S (EPUSH x s) (EPUSH x s')) /\
   (!s s' t. ESUBSTCONG R S s s'
             ==> ESUBSTCONG R S (ECOMP s t) (ECOMP s' t)) /\
   (!s t t'. ESUBSTCONG R S t t'
             ==> ESUBSTCONG R S (ECOMP s t) (ECOMP s t'))`;;

(* ------------------------------------------------------------------------- *)
(* Iterated shift.                                                           *)
(* ------------------------------------------------------------------------- *)

let ESHIFT = new_recursive_definition num_RECURSION
  `ESHIFT 0 = EID /\
   (!i. ESHIFT (SUC i) = if i = 0
                         then ESHIFT1
                         else ECOMP ESHIFT1 (ESHIFT i))`;;

let ESHIFT_CLAUSES = prove
 (`ESHIFT 0 = EID /\
   ESHIFT 1 = ESHIFT1 /\
   (!i. ESHIFT (SUC (SUC i)) = ECOMP ESHIFT1 (ESHIFT (SUC i)))`,
  REWRITE_TAC[num_CONV `1`; ESHIFT; NOT_SUC]);;

(* 
(RAND_CONV (TOP_DEPTH_CONV num_CONV) THENC
 REWRITE_CONV[ESHIFT; ARITH]) `ESHIFT 3`;;
*)

(* ------------------------------------------------------------------------- *)
(* References.                                                               *)
(* ------------------------------------------------------------------------- *)

let EREF = new_definition
  `EREF i = if i = 0 then EREF0 else ESUBST EREF0 (ESHIFT i)`;;

(*
(TOP_DEPTH_CONV num_CONV THENC REWRITE_CONV[EREF; ESHIFT; ARITH])
`EREF 3`;;
*)

let PUSHREF = new_recursive_definition num_RECURSION
  `(!s. PUSHREF 0 s = s) /\
   (!k s. PUSHREF (SUC k) s = PUSHREF k (EPUSH (EREF k) s))`;;

(TOP_DEPTH_CONV num_CONV THENC
 REWRITE_CONV[PUSHREF; EREF; SUC_INJ; NOT_SUC] THENC
 NUM_REDUCE_CONV)
`PUSHREF 3 EID`;;

(* ------------------------------------------------------------------------- *)
(* Pure lambda eterms (eterms without esubstitution).                           *)
(* ------------------------------------------------------------------------- *)

let ELAMBDA_RULES,ELAMBDA_INDUCT,ELAMBDA_CASES = new_inductive_definition
  `(!i. ELAMBDA (EREF i)) /\
   (!x y. ELAMBDA x /\ ELAMBDA y ==> ELAMBDA (EAPP x y)) /\
   (!x. ELAMBDA x ==> ELAMBDA (EABS x))`;;

(* ------------------------------------------------------------------------- *)
(* Semantic substitutions.                                                   *)
(* ------------------------------------------------------------------------- *)

let IS_SEMSUBST = new_definition
  `IS_SEMSUBST f <=> ?k. FINITE {i | ~(f i = EREF (i + k))}`;;

let ssubst_TYBIJ =
  (new_type_definition "ssubst" ("SSUBST","SUBSTFUN") o prove)
  (`?f. IS_SEMSUBST f`,
   EXISTS_TAC `EREF` THEN REWRITE_TAC[IS_SEMSUBST] THEN EXISTS_TAC `0` THEN
   REWRITE_TAC[ADD_0; EMPTY_GSPEC; FINITE_EMPTY]);;

parse_as_binder "SSUBST";;

let SSUBST_EQ = prove
 (`!f g. f = g <=> !i. SUBSTFUN f i = SUBSTFUN g i`,
  REPEAT GEN_TAC THEN TRANS_TAC EQ_TRANS `SUBSTFUN f = SUBSTFUN g` THEN
  CONJ_TAC THENL [MESON_TAC[ssubst_TYBIJ]; REWRITE_TAC[FUN_EQ_THM]]);;

let IS_SEMSUBST_SUBSTFUN = prove
 (`!s. IS_SEMSUBST (SUBSTFUN s)`,
  MESON_TAC[ssubst_TYBIJ]);;

let SUBSTFUN_SSUBST = prove
 (`!f. IS_SEMSUBST f ==> SUBSTFUN ((SSUBST) f) = f`,
  MESON_TAC[ssubst_TYBIJ]);;

let SSUBST_ID_DEF = new_definition
  `SSUBST_ID = (SSUBST) EREF`;;

let SSUBST_ID = prove
 (`SUBSTFUN SSUBST_ID = EREF`,
  REWRITE_TAC[SSUBST_ID_DEF; GSYM ssubst_TYBIJ; IS_SEMSUBST] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_0; EMPTY_GSPEC; FINITE_EMPTY]);;

let SSUBST_SHIFT_DEF = new_definition
  `SSUBST_SHIFT = SSUBST i. EREF (SUC i)`;;

let SSUBST_SHIFT = prove
 (`!i. SUBSTFUN SSUBST_SHIFT i = EREF (SUC i)`,
  SUBGOAL_THEN `IS_SEMSUBST (\i. EREF (SUC i))`
  (fun th -> SIMP_TAC[SSUBST_SHIFT_DEF; th; SUBSTFUN_SSUBST]) THEN
  REWRITE_TAC[IS_SEMSUBST] THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[ADD1; EMPTY_GSPEC; FINITE_EMPTY]);;

(* 
let SSUBST_PUSH_DEF = new_definition
  `SSUBST_PUSH x s = SSUBST i. if i = 0 then x else SUBSTFUN f (PRE i)`;;
*)

(*
let EBIND = new_recursive_definition eterm_RECUR
  `(!f. EBIND f EREF0 = SUBSTFUN f 0) /\
   (!f x y. EBIND f (EAPP x y) = EAPP (EBIND f x) (EBIND f y)) /\
   (!f x. EBIND f (EABS x) = EABS (EBIND f x)) /\
   (!f x s. EBIND f (ESUBST x s) = ESUBST (EBIND f x) (EBINDSUBST f s)) /\
   (!f. EBINDSUBST f EID = EID) /\
   (!f. EBINDSUBST f ESHIFT1 = ESHIFT1) /\
   (!f x s. EBINDSUBST (EPUSH x s) = EPUSH (EBIND f x) (EBINDSUBST s)) /\
   (!f t. EBINDSUBST (ECOMP s t) = ECOMP (EBINDSUBST t) (EBINDSUBST s))`;;
*)

(* ------------------------------------------------------------------------- *)
(* Implicit reindexing.                                                      *)
(* ------------------------------------------------------------------------- *)

let EREINDEX = new_recursive_definition eterm_RECUR
  `(!f. EREINDEX f EREF0 = EREF (f 0)) /\
   (!f x y. EREINDEX f (EAPP x y) = EAPP (EREINDEX f x) (EREINDEX f y)) /\
   (!f x. EREINDEX f (EABS x) = EABS (EREINDEX (SLIDE f) x)) /\
   (!f x s. EREINDEX f (ESUBST x s) =  ESUBST x (EREINDEXSUBST f s)) /\
   (!f. EREINDEXSUBST f EID = EID) /\
   (!f. EREINDEXSUBST f ESHIFT1 = ESHIFT1) /\
   (!f x s. EREINDEXSUBST f (EPUSH x s) =
            EPUSH (EREINDEX f x) (EREINDEXSUBST (SLIDE f) s)) /\
   (!f s t. EREINDEXSUBST f (ECOMP s t) = ECOMP s (EREINDEXSUBST f t))`;;

let REINDEX_RID = prove
 (`!f i. EREINDEX f (EREF i) = EREF (f i)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EREF; EREINDEX] THEN
  REWRITE_TAC[NOT_SUC; ESHIFT] THEN CASES_TAC `i:num` THEN
  REWRITE_TAC[NOT_SUC; EREINDEX; ESHIFT] THEN

  COND_CASES_TAC
  
  ;;

let EDERIV = new_recursive_definition num_RECURSION
  `(!f. EDERIV f 0 = EREF0) /\
   (!f i. EDERIV f (SUC i) = EREINDEX SUC (f i))`;;

(* ------------------------------------------------------------------------- *)
(* Implicit substitution.                                                    *)
(* ------------------------------------------------------------------------- *)

let EBIND = new_recursive_definition eterm_RECUR
  `(!f. EBIND f EREF0 = f 0) /\
   (!f x y. EBIND f (EAPP x y) = EAPP (EBIND f x) (EBIND f y)) /\
   (!f x. EBIND f (EABS x) = EABS (EBIND (EDERIV f) x)) /\
   (!f x s. EBIND f (ESUBST x s) = ESUBST x (EBINDSUBST f s)) /\
   (!f. EBINDSUBST f EID = EID) /\
   (!f. EBINDSUBST f ESHIFT1 = ESHIFT1) /\
   (!f x s. EBINDSUBST f (EPUSH x s) =
            EPUSH (EBIND f x) (EBINDSUBST f s)) /\
   (!f s t. EBINDSUBST f (ECOMP s t) =
            ECOMP (EBINDSUBST f s) (EBINDSUBST f t))`;;

(* ------------------------------------------------------------------------- *)
(* DB-monad structure                                                        *)
(* ------------------------------------------------------------------------- *)

let EBIND_RID = prove
 (`!f i. EBIND f (EREF i) = f i`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EREF; EBIND] THEN
  REWRITE_TAC[NOT_SUC; ESHIFT] THEN
  POP_ASSUM MP_TAC THEN CASES_TAC `i:num` THEN

    REWRITE_TAC[EREF; EBIND]
  
  REWRITE_TAC[EBIND]
  COND_CASES_TAC THEN
  POP_ASSUM SUBST_VAR_TAC
  POP_ASSUM MP_TAC
  REWRITE_TAC[EREF; EBIND]
  REWRITE_TAC[EBIND]

let EBIND_EBIND = prove
 (`!x f g. EBIND f (EBIND g x) = EBIND (EBIND f o g) x`,
 );;

let EBIND_LID = prove
 (`!x. EBIND EREF x = x`,
)


let IS_DBMONAD_EBIND = prove
 (`IS_DBMONAD (EBIND,EREF)`,
  REWRITE_TAC[IS_DBMONAD]