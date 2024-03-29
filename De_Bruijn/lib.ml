(* ========================================================================= *)
(* Additional tactics and theorems about nums, lists, nats...                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Some tactics.                                                             *)
(* ------------------------------------------------------------------------- *)

let NUM_CASES_TAC =
  let th = prove
    (`!P. P 0 /\ (!n. P (SUC n)) ==> (!n. P n)`,
     GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[])
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
(* PREIMAGE.                                                                 *)
(* ------------------------------------------------------------------------- *)

let PREIMAGE = new_definition
  `PREIMAGE (f:A->B) s = {x | f x IN s}`;;

let IN_PREIMAGE = prove
 (`!f:A->B s. x IN PREIMAGE f s <=> f x IN s`,
  REWRITE_TAC[PREIMAGE; IN_ELIM_THM]);;

let PREIMAGE_UNION = prove
 (`!f:A->B s t. PREIMAGE f (s UNION t) = PREIMAGE f s UNION PREIMAGE f t`,
  REWRITE_TAC[PREIMAGE; UNION; IN_UNION; IN_ELIM_THM]);;

let PREIMAGE_INTER = prove
 (`!f:A->B s t. PREIMAGE f (s INTER t) = PREIMAGE f s INTER PREIMAGE f t`,
  REWRITE_TAC[PREIMAGE; INTER; IN_INTER; IN_ELIM_THM]);;

let PREIMAGE_DIFF = prove
 (`!f:A->B s t. PREIMAGE f (s DIFF t) = PREIMAGE f s DIFF PREIMAGE f t`,
  REWRITE_TAC[PREIMAGE; DIFF; IN_DIFF; IN_ELIM_THM]);;

let PREIMAGE_EMPTY = prove
 (`!f:A->B. PREIMAGE f {} = {}`,
  REWRITE_TAC[PREIMAGE; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM]);;

let PREIMAGE_SING = prove
 (`!f:A->B a. PREIMAGE f {a} = { x:A | f x = a }`,
  REWRITE_TAC[PREIMAGE; IN_SING]);;

let PREIMAGE_o = prove
 (`!f:B->C g:A->B s. PREIMAGE (f o g) s = PREIMAGE g (PREIMAGE f s)`,
  REWRITE_TAC[PREIMAGE; o_DEF; EXTENSION; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Iteration.                                                                *)
(* ------------------------------------------------------------------------- *)

let ITER_BINARY = prove
 (`(!n f x:A. ITER (NUMERAL n) f x = ITER n f x) /\
   (!f x:A. ITER _0 f x = x) /\
   (!f n x:A. ITER (BIT0 n) f x = ITER n (f o f) x) /\
   (!f n x:A. ITER (BIT1 n) f x = ITER n (f o f) (f x))`,
  CONJ_TAC THENL [REWRITE_TAC[NUMERAL]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[DENUMERAL (CONJUNCT1 ITER)]; ALL_TAC] THEN
  CLAIM_TAC "rmk" `!f n x:A. ITER (n + n) f x = ITER n (f o f) x` THENL
  [GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [NUM_REDUCE_TAC THEN REWRITE_TAC[ITER];
    ASM_REWRITE_TAC[ADD; ADD_SUC; ITER; o_THM]];
   ASM_REWRITE_TAC[BIT0; BIT1; ITER_ALT]]);;

(* ------------------------------------------------------------------------- *)
(* Reflexive, transitive, simmetric closure.                                 *)
(* ------------------------------------------------------------------------- *)

let RTC_MAP = prove
 (`!R f x y:A. (!u v. R u v ==> R (f u) (f v)) /\ RTC R x y
             ==> RTC R (f x) (f y)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN ASM_MESON_TAC[RTC_RULES]);;

let RSTC_MAP = prove
 (`!R f x y:A. (!u v. R u v ==> R (f u) (f v)) /\ RSTC R x y
             ==> RSTC R (f x) (f y)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC RSTC_INDUCT THEN ASM_MESON_TAC[RSTC_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Misc.                                                                     *)
(* ------------------------------------------------------------------------- *)

let IF_DISTRIB = MESON[]
  `!f b x y:A. (if b then f x else f y:B) = f (if b then x else y)`;;

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
   REWRITE_TAC[NOT_SUC; PRE; LE; LT_0; LT; SUC_INJ;
               ADD; ADD_0; ADD_SUC; SUB_0; SUB_SUC; LT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let FORALL_NUM_THM = prove
 (`!P. (!i. P i) <=> P 0 /\ (!i. P (SUC i))`,
  METIS_TAC[cases "num"]);;

(* ------------------------------------------------------------------------- *)
(* Handy tactics for cases analysis on inductive datatypes.                  *)
(* ------------------------------------------------------------------------- *)

let GEN_THEN (vtac:term->tactic) : tactic =
  fun (asl,w) as gl ->
    let x,bod = try dest_forall w with Failure _ ->
                  failwith "GEN_THEN: Not universally quantified" in
    let avoids = itlist (union o thm_frees o snd) asl (frees w) in
    let x' = mk_primed_var avoids x in
    (X_GEN_TAC x' THEN vtac  x') gl;;

let CASES_TAC (tm:term) : tactic =
  let ty = fst(dest_type(type_of tm)) in
  STRUCT_CASES_TAC (ISPEC tm (cases ty));;

let CASES_GEN_TAC : tactic = GEN_THEN CASES_TAC;;
