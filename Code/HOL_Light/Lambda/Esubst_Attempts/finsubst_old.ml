(* ========================================================================= *)
(* Restriction to finite substitutions.                                      *)
(* ========================================================================= *)

(*
loadt "Lambda/make.ml";;
*)

(* TODO: Sostituire PUSHENV con FCONS. *)

(* Già copiato in dblambda.ml. *)
let PUSHENV_EXPAND = prove
 (`!f. f = PUSHENV (f 0) (f o SUC)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN CASES_GEN_TAC THEN
  REWRITE_TAC[PUSHENV; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Addition of an integer with a natural number with truncation.             *)
(* ------------------------------------------------------------------------- *)

let ADDINT = new_definition
  `ADDINT d i = num_of_int (max (&0) (d + &i))`;;

let INT_OF_NUM_ADDINT = prove
 (`!d i. &(ADDINT d i) = max (&0) (d + &i)`,
  SIMP_TAC[ADDINT; INT_MAX_MAX; INT_OF_NUM_OF_INT]);;

let ADDINT_SUC = prove
 (`!d i. ADDINT (d - &1) (SUC i) = ADDINT d i`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_ADDINT; ADD1; GSYM INT_OF_NUM_ADD] THEN
  AP_TERM_TAC THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Set of "finitary" substitutions.                                          *)
(* ------------------------------------------------------------------------- *)

let FINSUBST = new_definition
  `FINSUBST = {f:num->dblambda |
               ?d n. !i. n <= i ==> f i = REF (ADDINT d i)}`;;

let IN_FINSUBST = prove
 (`!f. f IN FINSUBST <=> ?d n. !i. n <= i ==> f i = REF (ADDINT d i)`,
  REWRITE_TAC[FINSUBST; IN_ELIM_THM]);;

let SHIFTENV = new_definition
  `SHIFTENV d i = REF (ADDINT d i)`;;

let SHIFTENV_IN_FINSUBST = prove
 (`SHIFTENV d IN FINSUBST`,
  REWRITE_TAC[IN_FINSUBST] THEN EXISTS_TAC `d:int` THEN
  REWRITE_TAC[SHIFTENV]);;

let PUSHENV_IN_FINSUBST = prove
 (`!f u. f IN FINSUBST ==> PUSHENV u f IN FINSUBST`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_FINSUBST] THEN INTRO_TAC "@d n. hp" THEN
  MAP_EVERY EXISTS_TAC [`d - &1:int`; `SUC n`] THEN CASES_GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= 0)`; PUSHENV] THEN
  ASM_SIMP_TAC[LE_SUC; injectivity "dblambda"; ADDINT_SUC]);;

let SUBST_o_IN_FINSUBST = prove
 (`!f g. f IN FINSUBST /\ g IN FINSUBST ==> SUBST f o g IN FINSUBST`,
  REWRITE_TAC[IN_FINSUBST; o_THM] THEN
  INTRO_TAC "!f g; (@df nf. f) (@dg ng. g)" THEN
  MAP_EVERY EXISTS_TAC [`df + dg:int`; `MAX ng (ADDINT (--dg) nf)`] THEN
  INTRO_TAC "!i; i" THEN
  SUBGOAL_THEN `g i = REF (ADDINT dg i)` SUBST1_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; REWRITE_TAC[SUBST]] THEN
  TRANS_TAC EQ_TRANS `REF (ADDINT df (ADDINT dg i))` THEN CONJ_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   SUBGOAL_THEN `ADDINT (--dg) nf <= i` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_LE; INT_OF_NUM_ADDINT] THEN
   INT_ARITH_TAC;
   ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_EQ; INT_OF_NUM_ADDINT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM INT_ADD_ASSOC] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `&0 <= dg + &i:int` MP_TAC THENL [ALL_TAC; INT_ARITH_TAC] THEN
  HYP_TAC "i" (REWRITE_RULE[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MAX;
                            INT_OF_NUM_ADDINT]) THEN
  ASM_INT_ARITH_TAC);;

let FINSUBST_INDUCT = prove
 (`!P. (!d. P (SHIFTENV d)) /\
       (!u f. P f ==> P (PUSHENV u f))
       ==> (!f. f IN FINSUBST ==> P f)`,
  INTRO_TAC "!P; 1 2; !f" THEN
  SUBGOAL_THEN `!n f d. (!i. n <= i ==> f i = REF (ADDINT d i)) ==> P f`
    (fun th -> REWRITE_TAC[IN_FINSUBST] THEN REPEAT STRIP_TAC THEN
               MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `0 <= i`] THEN DISCH_TAC THEN
   SUBGOAL_THEN `f = SHIFTENV d` (fun th -> ASM_REWRITE_TAC[th]) THEN
   ASM_REWRITE_TAC[FUN_EQ_THM; SHIFTENV];
   ALL_TAC] THEN
  INTRO_TAC "!f d; f" THEN
  GEN_REWRITE_TAC RAND_CONV [PUSHENV_EXPAND] THEN
  REMOVE_THEN "2" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[o_THM] THEN EXISTS_TAC `d + &1:int` THEN
  INTRO_TAC "!i; i" THEN ASM_SIMP_TAC[LE_SUC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_EQ; INT_OF_NUM_ADDINT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ADD1; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Syntax for lambda calculus with explicit substitution.                    *)
(* Similar to the one found in Abadi et al.                                  *)
(* ------------------------------------------------------------------------- *)

let eterm_INDUCT,eterm_RECUR = define_type
  "eterm  = EREF num
          | EAPP eterm eterm
          | EABS eterm
          | ESUBST eterm esubst;
   esubst = EID
          | ESHIFT
          | ECONS eterm esubst
          | ECOMP esubst esubst";;

let SIMPLE_ESUBST_INDUCT =
  REWRITE_RULE [] (SPEC `\x:eterm. T` eterm_INDUCT);;

(* ------------------------------------------------------------------------- *)
(* Intended semantics into the standard lambda calculus.                     *)
(* ------------------------------------------------------------------------- *)

let SEM = new_recursive_definition eterm_RECUR
  `(!i. SEM (EREF i) = REF i) /\
   (!x y. SEM (EAPP x y) = APP (SEM x) (SEM y)) /\
   (!x. SEM (EABS x) = ABS (SEM x)) /\
   (!x s. SEM (ESUBST x s) = SUBST (SEMSUBST s) (SEM x)) /\
   SEMSUBST EID = REF /\
   SEMSUBST ESHIFT = REF o SUC /\
   (!u s. SEMSUBST (ECONS u s) = PUSHENV (SEM u) (SEMSUBST s)) /\
   (!s t. SEMSUBST (ECOMP s t) = SUBST (SEMSUBST t) o (SEMSUBST s))`;;

let DEGSUBST = new_recursive_definition eterm_RECUR
  `DEGSUBST EID = (0,0) /\
   DEGSUBST ESHIFT = (0,1) /\
   (!u s. DEGSUBST (ECONS u s) =
          let (m,n) = DEGSUBST s in (m+1,n)) /\
   (!s t. DEGSUBST (ECOMP s t) =
          let (m,n) = DEGSUBST s in
          let (p,q) = DEGSUBST t in
          if n <= p then (m+p-n,q) else (m,q+n-p))`;;

let DEGSUBST_SEMSUBST = prove
 (`!s. let (m,n) = DEGSUBST s in
       !i. m <= i ==> SEMSUBST s i = REF (i + n)`,

  MATCH_MP_TAC SIMPLE_ESUBST_INDUCT THEN REWRITE_TAC[DEGSUBST] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SEM; ADD_0; o_THM; ADD1] THEN
  CONJ_TAC THENL

    INTRO_TAC "![u] [s]" THEN
    CLAIM_TAC "@m n. s" `?m n. DEGSUBST s = m,n` THENL
    [MESON_TAC[PAIR_SURJECTIVE];
     ASM_REWRITE_TAC[] THEN CONV_TAC (DEPTH_CONV let_CONV)] THEN
    INTRO_TAC "hp" THEN CASES_GEN_TAC THEN
    REWRITE_TAC[PUSHENV; ARITH_RULE `~(m + 1 <= 0)`] THEN
    ASM_SIMP_TAC[ARITH_RULE `m + 1 <= SUC n <=> m <= n`; injectivity "dblambda"]

    r 1;;

    INTRO_TAC "![s] [t]; s t" THEN
    LET_TAC THEN
    POP_ASSUM MP_TAC THEN LET_TAC
    LET_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT (POP_ASSUM SUBST_VAR_TAC)
    REMOVE_THEN "s" MP_TAC THEN LET_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[PAIR_EQ]
    STRIP_TAC THEN REPEAT (POP_ASSUM SUBST_ALL_TAC)
    INTRO_TAC "s; !i; i"
    SUBGOAL_THEN `m <= i` (fun th -> ASM_SIMP_TAC[th])
     ASM_ARITH_TAC
    REWRITE_TAC[SUBST]
    REMOVE_THEN "t" MP_TAC THEN LET_TAC THEN REWRITE_TAC[PAIR_EQ]
    POP_ASSUM MP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN REPEAT (POP_ASSUM (SUBST_ALL_TAC o GSYM))
    INTRO_TAC "t"
    SUBGOAL_THEN `p <= i + n''` (fun th -> ASM_SIMP_TAC[th])
     ASM_ARITH_TAC

  r 1;;
    POP_ASSUM SUBST_VAR_TAC THEN

let IREINDEX = new_recursive_definition eterm_RECUR
  `(!f i. IREINDEX f (EREF i) = EREF (f i)) /\
   (!f x y. IREINDEX f (EAPP x y) = EAPP (IREINDEX f x) (IREINDEX f y)) /\
   (!f x. IREINDEX f (EABS x) = EABS (IREINDEX (SLIDE f) x)) /\
   (!f x s. IREINDEX f (ESUBST x s) =
            ESUBST x (IREINDEX_SUBST f s)) /\
   (!f u s. IREINDEX_SUBST f (EPUSH u s) = EPUSH (IREINDEX f u) (IREINDEX_SUBST f s)) /\
   (!f. IREINDEX_SUBST f EBUMP = EBUMP) /\
   (!f s. IREINDEX_SUBST f (EDERIV s) = EDERIV (IREINDEX_SUBST f s))`;;
