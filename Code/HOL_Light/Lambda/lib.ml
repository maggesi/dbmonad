(* -*- holl -*- *)

(* ========================================================================= *)
(*  Additional tactics and theorems about nums, lists, nats...               *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2006                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  Some tactics.                                                            *)
(* ------------------------------------------------------------------------- *)

let TRANS_TAC t =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC t THEN CONJ_TAC;;

let ASM_ARITH_TAC =
  POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN ARITH_TAC;;

let NUM_CASES_TAC =
  let th = prove
    (`!P. P 0 /\ (!n. P (SUC n)) ==> (!n. P n)`,
     GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [])
  in
  MATCH_MP_TAC th THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC];;

let X_INDUCT_TAC tm =
   SPEC_TAC (tm, tm) THEN INDUCT_TAC ;;

let X_NUM_CASES_TAC tm =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (CHOOSE_THEN SUBST_ALL_TAC)
    (SPEC tm num_CASES);;

let X_LIST_INDUCT_TAC tm =
  SPEC_TAC (tm, tm) THEN LIST_INDUCT_TAC;;

(* ------------------------------------------------------------------------- *)
(*  IMAGE.                                                                   *)
(* ------------------------------------------------------------------------- *)

let IMAGE_SING = prove
  (`IMAGE f {x} = {f x}`,
   REWRITE_TAC [IMAGE; EXTENSION; IN_SING; IN_ELIM_THM] THEN MESON_TAC []);;

let IMAGE_EMPTY = prove
  (`IMAGE f {} = {}`,
   REWRITE_TAC [IMAGE; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
   MESON_TAC []);;

(* ------------------------------------------------------------------------- *)
(*  PREIMAGE.                                                                *)
(* ------------------------------------------------------------------------- *)

let PREIMAGE = new_definition
  `PREIMAGE (f:A->B) s = { x:A | f x IN s }`;;

let IN_PREIMAGE = prove
  (`!f s. x IN PREIMAGE f s <=> f x IN s`,
   REWRITE_TAC [PREIMAGE; IN_ELIM_THM]);;

let PREIMAGE_UNION = prove
  (`!(f:A->B) s t. PREIMAGE f (s UNION t) = PREIMAGE f s UNION PREIMAGE f t`,
   REWRITE_TAC [PREIMAGE; UNION; IN_UNION; IN_ELIM_THM]);;

let PREIMAGE_INTER = prove
  (`!(f:A->B) s t. PREIMAGE f (s INTER t) = PREIMAGE f s INTER PREIMAGE f t`,
   REWRITE_TAC [PREIMAGE; INTER; IN_INTER; IN_ELIM_THM]);;

let PREIMAGE_DIFF = prove
  (`!(f:A->B) s t. PREIMAGE f (s DIFF t) = PREIMAGE f s DIFF PREIMAGE f t`,
   REWRITE_TAC [PREIMAGE; DIFF; IN_DIFF; IN_ELIM_THM]);;

let PREIMAGE_EMPTY = prove
  (`!(f:A->B). PREIMAGE f {} = {}`,
   REWRITE_TAC [PREIMAGE; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM]);;

let PREIMAGE_SING = prove
  (`!(f:A->B) a. PREIMAGE f {a} = { x:A | f x = a }`,
   REWRITE_TAC [PREIMAGE; IN_SING]);;

let PREIMAGE_o = prove
  (`!f g s. PREIMAGE (f o g) s = PREIMAGE g (PREIMAGE f s)`,
   REWRITE_TAC [PREIMAGE; o_DEF; EXTENSION; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(*  Misc.                                                                    *)
(* ------------------------------------------------------------------------- *)

let set_of_list_APPEND = prove
  (`!l1 l2. set_of_list (APPEND l1 l2) =
            (set_of_list l1) UNION (set_of_list l2)`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND; set_of_list; UNION] THEN
   SET_TAC []);;

let SING_INJ = prove
  (`!x y. {x} = {y} <=> x = y`,
   GEN_TAC THEN GEN_TAC THEN EQ_TAC THEN
   SIMP_TAC [EXTENSION; IN_SING] THEN MESON_TAC []);;

let IF_DISTRIB = MESON []
  `!f b x y. (if b then f x else f y) = f (if b then x else y)`;;

let TRIVIAL_ARITH = prove
 (`(!n. 0 + n = n) /\
   (!n. n + 0 = n) /\
   (!n. n - 0 = n) /\
   (!n. ~(n < 0)) /\
   (!n. ~(SUC n = 0)) /\
   (!n. 0 < SUC n) /\
   (!m n. SUC m = SUC n <=> m = n) /\
   (!m n. SUC m < SUC n <=> m < n) /\
   (!m n. SUC m - SUC n = m - n) /\
   (!m n. SUC m + n = SUC (m + n)) /\
   (!m n. m + SUC n = SUC (m + n)) /\
   (!n. PRE (SUC n) = n) /\
   (!n. n <= 0 <=> n = 0) /\
   (!n. n < SUC 0 <=> n = 0)`,
   REWRITE_TAC [NOT_SUC; PRE; LE; LT_0; LT; SUC_INJ;
                ADD; ADD_0; ADD_SUC; SUB_0; SUB_SUC; LT_SUC]);;
