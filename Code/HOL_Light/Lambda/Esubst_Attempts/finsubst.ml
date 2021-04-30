(* ========================================================================= *)
(* Restriction to finitary substitutions.                                    *)
(* ========================================================================= *)

(*
needs "Lambda/make.ml";;
loadt "Lambda/finsubst.ml";;
*)

let SHIFTENV = new_definition
  `SHIFTENV k i = REF (k + i)`;;

(* ------------------------------------------------------------------------- *)
(* Degree of "finitary" substitutions.                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("HAS_DEGSUBST",get_infix_status "HAS_SIZE");;

let HAS_DEGSUBST_RULES,HAS_DEGSUBST_INDUCT_GEN,HAS_DEGSUBST_CASES =
  new_inductive_definition
  `(!k. SHIFTENV k HAS_DEGSUBST (0,k)) /\
   (!f m n u. f HAS_DEGSUBST (m,n) ==> PUSHENV u f HAS_DEGSUBST (m+1,n))`;;

let SHIFTENV_HAS_DEGSUBST,PUSHENV_HAS_DEGSUBST = CONJ_PAIR HAS_DEGSUBST_RULES;;

let HAS_DEGSUBST_INDUCT = prove
 (`!P. (!k. P (SHIFTENV k) 0 k) /\
       (!f m n u. P f m n ==> P (PUSHENV u f) (m + 1) n)
       ==> (!f m n. f HAS_DEGSUBST (m,n) ==> P f m n)`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (REWRITE_RULE[FORALL_PAIR_THM]
      (SPEC `\f p. P (f:num->dblambda) (FST p:num) (SND p:num) : bool`
        HAS_DEGSUBST_INDUCT_GEN)) THEN
  ASM_REWRITE_TAC[]);;

let HAS_DEGSUBST = prove
 (`!f m n. f HAS_DEGSUBST (m,n) <=> (!i. m <= i ==> f i = REF ((n + i) - m))`,
  CLAIM_TAC "1"
    `!n m f. (!i. m <= i ==> f i = REF ((n + i) - m))
              ==> f HAS_DEGSUBST (m,n)` THENL
  [GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUB_0; ARITH_RULE `0 <= i`] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `f = SHIFTENV n` SUBST1_TAC THEN
    ASM_REWRITE_TAC[HAS_DEGSUBST_RULES; FUN_EQ_THM; SHIFTENV];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [PUSHENV_EXPAND] THEN
   REWRITE_TAC[ADD1] THEN MATCH_MP_TAC PUSHENV_HAS_DEGSUBST THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[o_THM; LE_SUC] THEN
   REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "2"
    `!f m n. f HAS_DEGSUBST (m,n)
             ==> (!i. m <= i ==> f i = REF ((n + i) - m))` THENL
  [MATCH_MP_TAC HAS_DEGSUBST_INDUCT THEN
   REWRITE_TAC[SUB_0; SHIFTENV] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   CASES_GEN_TAC THEN REWRITE_TAC[PUSHENV] THENL
   [ARITH_TAC; ASM_SIMP_TAC[GSYM ADD1; LE_SUC]] THEN
   DISCH_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
   ASM_MESON_TAC[]]);;

let HAS_DEGSUBST_INC = prove
 (`!f m n. f HAS_DEGSUBST (m,n) ==> f HAS_DEGSUBST (m+1,n+1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_DEGSUBST] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `m + 1 <= i ==> m <= i`] THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let IDSUBST_HAS_DEGSUBST = prove
 (`!m. REF HAS_DEGSUBST (m,m)`,
  REWRITE_TAC[HAS_DEGSUBST; ARITH_RULE `(m + i) - m = i`]);;

let COMP_HAS_DEGSUBST = prove
 (`!f g m n p q. f HAS_DEGSUBST (m,n) /\ g HAS_DEGSUBST (p,q)
                 ==> SUBST g o f HAS_DEGSUBST
                       if n <= p then ((m+p)-n,q) else (m,(q+n)-p)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[HAS_DEGSUBST] THEN
  STRIP_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  (SUBGOAL_THEN `m <= i` (fun th -> ASM_SIMP_TAC[th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[SUBST]] THEN
   SUBGOAL_THEN `p <= (n + i) - m` (fun th -> ASM_SIMP_TAC[th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[SUBST]] THEN
   AP_TERM_TAC THEN ASM_ARITH_TAC));;

let HAS_DEGSUBST_SUBST_SUBST = prove
 (`!f e m n x. e HAS_DEGSUBST (m,n)
               ==> SUBST f (SUBST e x) =
                   SUBST (\i. if i < m
                              then SUBST f (e i)
                              else REF (i - m))
                         (SUBST (ITER m DERIV (f o (+) n)) x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_DEGSUBST; SUBST_SUBST; ADD;
              SUBST_EXTENS; o_THM; ITER_DERIV] THEN
  INTRO_TAC "e; !i; _" THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SUBST; o_THM] THEN
  ASM_SIMP_TAC[GSYM NOT_LT; SUBST; SUBST_REINDEX;
               ARITH_RULE `~(i < m) ==> n + i - m = (n + i) - m`] THEN
  MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC[SUBST_REF_EQ; o_THM] THEN
  INTRO_TAC "![j]; _" THEN ASM_SIMP_TAC[ARITH_RULE `~(m + j < m)`] THEN
  REWRITE_TAC[ARITH_RULE `(m + j) - m = j`]);;

(* ------------------------------------------------------------------------- *)
(* Set of "finitary" substitutions.                                          *)
(* ------------------------------------------------------------------------- *)

let FINSUBST = new_definition
  `FINSUBST = {f:num->dblambda |
               ?d n. !i. n <= i ==> f i = REF ((d + i) - n)}`;;

let IN_FINSUBST = prove
 (`!f. f IN FINSUBST <=> ?d n. !i. n <= i ==> f i = REF ((d + i) - n)`,
  REWRITE_TAC[FINSUBST; IN_ELIM_THM]);;

let FINSUBST_EQ_HAS_DEGSUBST = prove
 (`!f. f IN FINSUBST <=> ?m n. f HAS_DEGSUBST (m,n)`,
  REWRITE_TAC[IN_FINSUBST; HAS_DEGSUBST] THEN MESON_TAC[]);;

let IDSUBST_IN_FINSUBST = prove
 (`REF IN FINSUBST`,
  REWRITE_TAC[FINSUBST_EQ_HAS_DEGSUBST] THEN
  MESON_TAC[IDSUBST_HAS_DEGSUBST]);;

let SHIFTENV_IN_FINSUBST = prove
 (`SHIFTENV d IN FINSUBST`,
  REWRITE_TAC[FINSUBST_EQ_HAS_DEGSUBST] THEN
  MESON_TAC[SHIFTENV_HAS_DEGSUBST]);;

let PUSHENV_IN_FINSUBST = prove
 (`!f u. f IN FINSUBST ==> PUSHENV u f IN FINSUBST`,
  REWRITE_TAC[FINSUBST_EQ_HAS_DEGSUBST] THEN
  MESON_TAC[PUSHENV_HAS_DEGSUBST]);;

let SUBST_o_IN_FINSUBST = prove
 (`!f g. f IN FINSUBST /\ g IN FINSUBST ==> SUBST f o g IN FINSUBST`,
  REWRITE_TAC[FINSUBST_EQ_HAS_DEGSUBST] THEN
  MESON_TAC[COMP_HAS_DEGSUBST]);;

let FINSUBST_INDUCT = prove
 (`!P. (!d. P (SHIFTENV d)) /\
       (!u f. P f ==> P (PUSHENV u f))
       ==> (!f. f IN FINSUBST ==> P f)`,
  INTRO_TAC "!P; 1 2; !f" THEN
  SUBGOAL_THEN `!n f d. (!i. n <= i ==> f i = REF ((d + i) - n)) ==> P f`
    (fun th -> REWRITE_TAC[IN_FINSUBST] THEN REPEAT STRIP_TAC THEN
               MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `0 <= i`; SUB_0] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `f = SHIFTENV d` (fun th -> ASM_REWRITE_TAC[th]) THEN
   ASM_REWRITE_TAC[FUN_EQ_THM; SHIFTENV];
   ALL_TAC] THEN
  INTRO_TAC "!f d; f" THEN
  GEN_REWRITE_TAC RAND_CONV [PUSHENV_EXPAND] THEN
  REMOVE_THEN "2" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[o_THM] THEN EXISTS_TAC `d:num` THEN INTRO_TAC "!i; i" THEN
  ASM_SIMP_TAC[LE_SUC] THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* ENVLIST and SUBSTENV.                                                     *)
(* ------------------------------------------------------------------------- *)

let ENVLIST = new_definition
  `ENVLIST e i = if i < LENGTH e then EL i e else REF (i - LENGTH e)`;;

let ENVLIST_CLAUSES = prove
  (`ENVLIST [] = REF /\
    (!u e. ENVLIST (CONS u e) = PUSHENV u (ENVLIST e))`,
   CONJ_TAC THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[FUN_EQ_THM; ENVLIST; LENGTH; ARITH_RULE `~(x < 0)`; SUB_0] THEN
   CASES_GEN_TAC THEN
   REWRITE_TAC[EL; HD; TL; PUSHENV; ARITH_RULE `0 < SUC n`;
               LT_SUC; SUB_SUC; ENVLIST]);;

let SUBSTENV = new_definition
  `SUBSTENV e = SUBST (ENVLIST e)`;;

let SUBST_SUBSTENV = prove
 (`!x f e. SUBST f (SUBSTENV e x) =
           SUBSTENV (MAP (SUBST f) e) (SUBST (ITER (LENGTH e) DERIV f) x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSTENV; SUBST_SUBST; SUBST_EXTENS; o_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ENVLIST; ITER_DERIV] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SUBST; ENVLIST; LENGTH_MAP; SUBST_REINDEX] THENL
  [ASM_SIMP_TAC[EL_MAP]; MATCH_MP_TAC EQ_SYM] THEN
  REWRITE_TAC[SUBST_REF_EQ; o_THM] THEN INTRO_TAC "![j]; _" THEN
  REWRITE_TAC[ENVLIST; LENGTH_MAP;
              ARITH_RULE `~(m + j < m)`; injectivity "dblambda"] THEN
  ARITH_TAC);;

let ENVLIST_HAS_DEGSUBST = prove
 (`!e. ENVLIST e HAS_DEGSUBST (LENGTH e,0)`,
  GEN_TAC THEN REWRITE_TAC[HAS_DEGSUBST; ADD; ENVLIST] THEN GEN_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE]);;

let ENVLIST_IN_FINSUBST = prove
 (`!e. ENVLIST e IN FINSUBST`,
  REWRITE_TAC[FINSUBST_EQ_HAS_DEGSUBST] THEN
  MESON_TAC[ENVLIST_HAS_DEGSUBST]);;

(* ------------------------------------------------------------------------- *)
(* Syntax for lambda calculus with explicit substitution.                    *)
(* Similar to the one found in Abadi et al.                                  *)
(* ------------------------------------------------------------------------- *)

let eterm_INDUCT,eterm_RECUR = define_type
  "eterm  = EREF num
          | EAPP eterm eterm
          | EABS eterm
          | ESUBST eterm esubst;
   esubst = ESHIFT num
          | ECONS eterm esubst
          | ECOMP esubst esubst";;

let SIMPLE_ESUBST_INDUCT =
  REWRITE_RULE [] (SPEC `\x:eterm. T` eterm_INDUCT);;

let LAMBDALIFT = new_recursive_definition dblambda_RECURSION
  `(!i. LAMBDALIFT (REF i) = EREF i) /\
   (!x y. LAMBDALIFT (APP x y) = EAPP (LAMBDALIFT x) (LAMBDALIFT y)) /\
   (!x. LAMBDALIFT (ABS x) = EABS (LAMBDALIFT x))`;;

(* ------------------------------------------------------------------------- *)
(* Intended semantics into the standard lambda calculus.                     *)
(* ------------------------------------------------------------------------- *)

let SEM = new_recursive_definition eterm_RECUR
  `(!i. SEM (EREF i) = REF i) /\
   (!x y. SEM (EAPP x y) = APP (SEM x) (SEM y)) /\
   (!x. SEM (EABS x) = ABS (SEM x)) /\
   (!x s. SEM (ESUBST x s) = SUBST (SEMSUBST s) (SEM x)) /\
   (!k. SEMSUBST (ESHIFT k) = REF o ((+) k)) /\
   (!u s. SEMSUBST (ECONS u s) = PUSHENV (SEM u) (SEMSUBST s)) /\
   (!s t. SEMSUBST (ECOMP s t) = SUBST (SEMSUBST t) o (SEMSUBST s))`;;

let DEGSUBST = new_recursive_definition eterm_RECUR
  `(!k. DEGSUBST (ESHIFT k) = (0,k)) /\
   (!u s. DEGSUBST (ECONS u s) =
          let (m,n) = DEGSUBST s in (m+1,n)) /\
   (!s t. DEGSUBST (ECOMP s t) =
          let (m,n) = DEGSUBST s in
          let (p,q) = DEGSUBST t in
          if n <= p then (m+p-n,q) else (m,q+n-p))`;;

let SEMSUBST_HAS_DEGSUBST = prove
 (`!s. SEMSUBST s HAS_DEGSUBST DEGSUBST s`,
  MATCH_MP_TAC SIMPLE_ESUBST_INDUCT THEN
  REWRITE_TAC[DEGSUBST; HAS_DEGSUBST; SEM; o_THM; SUB_0] THEN
  CONJ_TAC THENL
  [FIX_TAC "[u] [s]" THEN CLAIM_TAC "@m n. eq" `?m n. DEGSUBST s = m,n` THENL
   [REWRITE_TAC[PAIR_SURJECTIVE]; POP_ASSUM SUBST1_TAC] THEN
   CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[HAS_DEGSUBST] THEN
   DISCH_TAC THEN CASES_GEN_TAC THEN REWRITE_TAC[PUSHENV] THENL
   [ARITH_TAC; ASM_SIMP_TAC[GSYM ADD1; LE_SUC]] THEN
   DISCH_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  FIX_TAC "[s] [t]" THEN
  CLAIM_TAC "@m n. eq" `?m n. DEGSUBST s = m,n` THENL
  [REWRITE_TAC[PAIR_SURJECTIVE]; POP_ASSUM SUBST1_TAC] THEN
  CLAIM_TAC "@p q. eq" `?p q. DEGSUBST t = p,q` THENL
  [REWRITE_TAC[PAIR_SURJECTIVE]; POP_ASSUM SUBST1_TAC] THEN
  CONV_TAC (DEPTH_CONV let_CONV) THEN REWRITE_TAC[HAS_DEGSUBST] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[HAS_DEGSUBST; o_THM] THEN
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `m <= i` (fun th -> ASM_SIMP_TAC[th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[SUBST]] THEN
   SUBGOAL_THEN `p <= (n + i) - m` (fun th -> ASM_SIMP_TAC[th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[SUBST]] THEN AP_TERM_TAC THEN ASM_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

let ADD_HAS_DEGSUBST = prove
 (`!f m n. f HAS_DEGSUBST (m,n) ==> (f o ((+) k)) HAS_DEGSUBST (m,k+n)`,
  REWRITE_TAC[HAS_DEGSUBST; o_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= i ==> m <= k + i`] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let SEM_LAMBDALIFT = prove
 (`!x. SEM (LAMBDALIFT x) = x`,
  DBLAMBDA_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LAMBDALIFT; SEM]);;

let HAS_DEGSUBST_SEM = prove
 (`!f m n. f HAS_DEGSUBST (m,n)
          ==> ?s. f = SEMSUBST s /\ DEGSUBST s = (m,n)`,
  MATCH_MP_TAC HAS_DEGSUBST_INDUCT THEN CONJ_TAC THENL
  [GEN_TAC THEN EXISTS_TAC `ESHIFT k` THEN
   REWRITE_TAC[SEM; DEGSUBST; FUN_EQ_THM; SHIFTENV; o_THM];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "@s. f s" THEN
  EXISTS_TAC `ECONS (LAMBDALIFT u) s` THEN REMOVE_THEN "f" SUBST_VAR_TAC THEN
  REWRITE_TAC[SEM; DEGSUBST; SEM_LAMBDALIFT] THEN POP_ASSUM SUBST1_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN REFL_TAC);;

let SUBSTLIFT = define
  `(!n f. SUBSTLIFT 0 n f = ESHIFT n) /\
   (!m n. SUBSTLIFT (SUC m) n f = ECONS (f 0) (SUBSTLIFT m n (f o SUC)))`;;

let SEMSUBST_SUBSTLIFT = prove
 (`!n m f. f:num->dblambda HAS_DEGSUBST (m,n)
           ==> SEMSUBST (SUBSTLIFT m n (LAMBDALIFT o f)) = f`,
  GEN_TAC THEN REWRITE_TAC[HAS_DEGSUBST] THEN INDUCT_TAC THEN
  REWRITE_TAC[SUBSTLIFT; SEM] THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM; SUB_0; ARITH_RULE `0 <= i`] THEN MESON_TAC[];
   ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[PUSHENV; FUN_EQ_THM; o_THM] THEN
  CASES_GEN_TAC THEN REWRITE_TAC[PUSHENV; SEM_LAMBDALIFT; GSYM o_ASSOC] THEN
  TRANS_TAC EQ_TRANS `(f o SUC) n' : dblambda` THEN CONJ_TAC THENL
  [ALL_TAC; REWRITE_TAC[o_THM]] THEN
  AP_THM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[o_THM; LE_SUC] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let DEGSUBST_SUBSTLIFT = prove
 (`!n m f. f HAS_DEGSUBST (m,n)
           ==> DEGSUBST (SUBSTLIFT m n (LAMBDALIFT o f)) = (m,n)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[SUBSTLIFT; DEGSUBST] THEN
  GEN_TAC THEN REWRITE_TAC[HAS_DEGSUBST] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  SUBGOAL_THEN `f o SUC HAS_DEGSUBST m,n` (fun th -> ASM_SIMP_TAC[th]) THENL
  [ASM_SIMP_TAC[HAS_DEGSUBST; o_THM; LE_SUC] THEN
   GEN_TAC THEN DISCH_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
   CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[ADD1]]);;

(* ------------------------------------------------------------------------- *)
(*                  HIC SUNT LEONES                                          *)
(* ------------------------------------------------------------------------- *)

(* let SUBST_CLAUSES_CHECK = prove
 (`(!f x. SUBST f (SUBST REF x) = SUBST f x) /\
   (!f k x. SUBST f (SUBST (REF o ((+) k)) x) = SUBST (f o (+) k) x) /\
   (!f g x. SUBST f (SUBST g x) = SUBST (SUBST f o g) x)`,
  REWRITE_TAC[SUBST_SUBST; SUBST_EXTENS; o_THM; SUBST]);;

`(!f i. BIND f (EREF i) = EREF (f i)) /\
 (!f x y. BIND f (EAPP x y) = EAPP (BIND f x) (BIND f y)) /\
 (!f . BIND f (EABS x) = EABS (BIND (DERIV f) x)) /\
 (!f x s. BIND f (ESUBST x s) = ESUBST x (BIND_SUBST f s)) /\
 (!f k. BIND f (ESHIFT k) )`
*)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(*
let fsubst_INDUCT,fsubst_RECUR = define_type
  "fsubst = FSHIFT num
          | FPUSH A fsubst
          | FCOMP fsubst fsubst";;

let FSEMSUBST = new_recursive_definition fsubst_RECUR
  `FSEMSUBST r (FSHIFT k) = FST r o ((+) k) /\
   (!u s. FSEMSUBST r (FPUSH u s) = PUSHENV u (FSEMSUBST r s)) /\
   (!s t. FSEMSUBST r (FCOMP s t) =
          SND r (FSEMSUBST r t) o (FSEMSUBST r s))`;;

let FDEGSUBST = new_recursive_definition fsubst_RECUR
  `FDEGSUBST (FSHIFT k) = (0,k) /\
   (!u s. FDEGSUBST (FPUSH u s) =
          let (m,n) = FDEGSUBST s in (m+1,n)) /\
   (!s t. FDEGSUBST (FCOMP s t) =
          let (m,n) = FDEGSUBST s in
          let (p,q) = FDEGSUBST t in
          if n <= p then (m+p-n,q) else (m,q+n-p))`;;

let fterm_INDUCT,fterm_RECUR = define_type
  "fterm = FREF num
         | FAPP fterm fterm
         | FABS fterm
         | FSUBST fterm (fterm fsubst)";;

let IREINDEX = new_recursive_definition eterm_RECUR
  `(!f i. IREINDEX f (EREF i) = EREF (f i)) /\
   (!f x y. IREINDEX f (EAPP x y) = EAPP (IREINDEX f x) (IREINDEX f y)) /\
   (!f x. IREINDEX f (EABS x) = EABS (IREINDEX (SLIDE f) x)) /\
   (!f x s. IREINDEX f (ESUBST x s) =
            ESUBST x (IREINDEX_SUBST f s)) /\
   (!f u s. IREINDEX_SUBST f EID = EID) /\
   (!f. IREINDEX_SUBST f ESHIFT = ESHIFT) /\
   (!f u s. IREINDEX_SUBST f (ECONS u s) =
            let m,n in DEGSUBST s in
            ECONS (IREINDEX f u) (`;;
*)
