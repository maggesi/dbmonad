(* ------------------------------------------------------------------------- *)
(* Lambda calculus with explicit substitutions.                              *)
(* Semantic style.                                                           *)
(* ------------------------------------------------------------------------- *)

let ALGTERM_RULES,ALGTERM_INDUCT,ALGTERM_CASES = new_inductive_definition
  `(!i. ALGTERM (REF i)) /\
   (!x y. ALGTERM x /\ ALGTERM y ==> ALGTERM (APP x y)) /\
   (!x. ALGTERM x ==> ALGTERM (ABS x)) /\
   (!x f. ALGTERM x /\ ALGSUBST f ==> ALGTERM (SUBST f x)) /\
   ALGSUBST REF /\
   ALGSUBST (REF o SUC) /\
   (!x f. ALGTERM x /\ ALGSUBST f ==> ALGSUBST (PUSHENV x f)) /\
   (!f g. ALGSUBST f /\ ALGSUBST g ==> ALGSUBST (SUBST f o g))`;;

let etrm_tybij =
  let eth = MESON [ALGTERM_RULES] `?x. ALGTERM x` in
  new_type_definition "etrm" ("MK_ETRM","DEST_ETRM") eth;;

let DEST_MK_ETRM = prove
 (`!x. ALGTERM x ==> DEST_ETRM (MK_ETRM x) = x`,
  MESON_TAC[etrm_tybij]);;

let MK_DEST_ETRM = prove
 (`!x. MK_ETRM (DEST_ETRM x) = x`,
  MESON_TAC[etrm_tybij]);;

let FORALL_ETRM_THM = prove
 (`!P. (!x:etrm. P x) <=> (!x. ALGTERM x ==> P (MK_ETRM x))`,
  MESON_TAC[etrm_tybij]);;

let DEST_ETRM_INJ = prove
 (`!x y. x = y <=> DEST_ETRM x = DEST_ETRM y`,
  MESON_TAC[etrm_tybij]);;

let esbst_tybij =
  let eth = MESON [ALGTERM_RULES] `?x. ALGSUBST x` in
  new_type_definition "esbst" ("MK_ESBST","DEST_ESBST") eth;;

let DEST_MK_ESBST = prove
 (`!f. ALGSUBST f ==> DEST_ESBST (MK_ESBST f) = f`,
  MESON_TAC[esbst_tybij]);;

let MK_DEST_ESBST = prove
 (`!f. MK_ESBST (DEST_ESBST f) = f`,
  MESON_TAC[esbst_tybij]);;

let FORALL_ESBST_THM = prove
 (`!P. (!f:esbst. P f) <=> (!f. ALGSUBST f ==> P (MK_ESBST f))`,
  MESON_TAC[esbst_tybij]);;

let DEST_ESBST_INJ = prove
 (`!f g. f = g <=> DEST_ESBST f = DEST_ESBST g`,
  MESON_TAC[esbst_tybij]);;

let EREFI_DEF = new_definition
  `EREFI i = MK_ETRM (REF i)`;;

let EREF0_DEF = new_definition
  `EREF0 = EREFI 0`;;

let EAPP_DEF = new_definition
  `EAPP x y = MK_ETRM (APP (DEST_ETRM x) (DEST_ETRM y))`;;

let EABS_DEF = new_definition
  `EABS x = MK_ETRM (ABS (DEST_ETRM x))`;;

let ESUBST_DEF = new_definition
  `ESUBST x f = MK_ETRM (SUBST (DEST_ESBST f) (DEST_ETRM x))`;;

let IDSUBST_DEF = new_definition
  `IDSUBST = MK_ESBST REF`;;

let SUCSUBST_DEF = new_definition
  `SUCSUBST = MK_ESBST (REF o SUC)`;;

let PUSHSUBST_DEF = new_definition
  `PUSHSUBST_DEF x f = MK_ESBST (PUSHENV (DEST_ETRM x) (DEST_ESBST f))`;;

let COMPSUBST_DEF = new_definition
  `COMPSUBST f g = MK_ESBST (SUBST (DEST_ESBST f) o DEST_ESBST g)`;;

let EAPP = prove
 (`!x y. ALGTERM x /\ ALGTERM y
         ==> EAPP (MK_ETRM x) (MK_ETRM y) = MK_ETRM (APP x y)`,
  REWRITE_TAC[EAPP_DEF] THEN SIMP_TAC[DEST_MK_ETRM]);;

let ESUBST = prove
 (`!x f. ALGTERM x /\ ALGSUBST f
         ==> ESUBST (MK_ETRM x) (MK_ESBST f) = MK_ETRM (SUBST f x)`,
  REWRITE_TAC[ESUBST_DEF] THEN SIMP_TAC[DEST_MK_ETRM; DEST_MK_ESBST]);;

let COMPSUBST = prove
 (`!f g. ALGSUBST f /\ ALGSUBST g
         ==> COMPSUBST (MK_ESBST f) (MK_ESBST g) = MK_ESBST (SUBST f o g)`,
  REWRITE_TAC[COMPSUBST_DEF] THEN SIMP_TAC[DEST_MK_ESBST]);;

let COMPSUBST_LID = prove
 (`!f. COMPSUBST IDSUBST f = f`,
  REWRITE_TAC[FORALL_ESBST_THM; COMPSUBST; IDSUBST_DEF] THEN
  SIMP_TAC[COMPSUBST; ALGTERM_RULES] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; SUBST_REF]);;