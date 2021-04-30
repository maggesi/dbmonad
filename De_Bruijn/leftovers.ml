(* ------------------------------------------------------------------------- *)
(* Not necessary anymore.                                                    *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_EQ_1 = prove
 (`!s:A->bool. dimindex s = 1 <=> (:A) HAS_SIZE 1 \/ INFINITE (:A)`,
  REWRITE_TAC[dimindex; HAS_SIZE; INFINITE] THEN MESON_TAC[]);;

let HAS_SIZE_1_FUNSPACE_UNIV = prove 
 (`(:B) HAS_SIZE 1 ==> (:A -> B) HAS_SIZE 1`,
  REWRITE_TAC[HAS_SIZE_1_INDISCERNIBLE; FUN_EQ_THM] THEN MESON_TAC[]);;

let HAS_SIZE_2_CASES = prove
 (`!s. s HAS_SIZE 2 <=> ?a b:A. s = {a,b} /\ ~(a = b)`,
  GEN_TAC THEN
  REWRITE_TAC[ONE; TWO; HAS_SIZE_CLAUSES; UNWIND_THM2; NOT_IN_EMPTY] THEN
  EQ_TAC THENL
  [INTRO_TAC "@a t. (@b. t) b s" THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN POP_ASSUM MP_TAC THEN SET_TAC[];
   ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `{b:A}`] THEN POP_ASSUM MP_TAC THEN SET_TAC[]);;

let CARD_UNIV_GE_1 = prove
 (`FINITE (:A) ==> 1 <= CARD (:A)`,
  SUBGOAL_THEN `!s:A->bool. FINITE s ==> ~(s = {}) ==> 1 <= CARD s`
    (fun th -> MESON_TAC[th; UNIV_NOT_EMPTY]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES] THEN ARITH_TAC);;

let CHOICE_SING = prove
 (`!x:A. CHOICE {x} = x`,
  REWRITE_TAC[CHOICE; IN_SING]);;
