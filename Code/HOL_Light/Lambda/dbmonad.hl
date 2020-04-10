(* ========================================================================= *)
(*  More definitions and theorems and tactics about lists.                   *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2005 2006 2017, 2020                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* dB monads.                                                                *)
(* ------------------------------------------------------------------------- *)

let DBMONAD_DEF = new_definition
  `!op:(num->A)->A->A.
     DBMONAD op <=>
     (!f g x. op g (op f x) = op (\n. op g (f n)) x) /\
     (?i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`;;

let DBUNIT = new_definition
  `!op:(num->A)->A->A.
     DBUNIT op = (@i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`;;

let DBMONAD = prove
 (`!op. DBMONAD op <=>
        (!f g x:A. op g (op f x) = op (\n. op g (f n)) x) /\
        (!f n. op f (DBUNIT op n) = f n) /\
        (!x. op (DBUNIT op) x = x)`,
  REWRITE_TAC[DBMONAD_DEF; DBUNIT] THEN MESON_TAC[]);;

let DBMONAD_ASSOC = prove
 (`!op. DBMONAD op ==> !f g x:A. op g (op f x) = op (op g o f) x`,
  REWRITE_TAC[DBMONAD; o_DEF] THEN MESON_TAC[]);;

let DBMONAD_RUNIT = prove
 (`!op. DBMONAD op ==> (!f n. op f (DBUNIT op n) = f n:A)`,
  REWRITE_TAC[DBMONAD] THEN MESON_TAC[]);;

let DBMONAD_LUNIT = prove
 (`!op. DBMONAD op ==> (!x:A. op (DBUNIT op) x = x)`,
  REWRITE_TAC[DBMONAD] THEN MESON_TAC[]);;

let DBMONAD_LUNIT_IMP = prove
 (`!op f x:A. DBMONAD op /\ (!i. f i = DBUNIT op i) ==> op f x = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN
  SIMP_TAC[DBMONAD_LUNIT]);;

let DBUNIT_UNIQUE = prove
 (`!op i. DBMONAD op /\ (!f n. op f (i n) = f n:A) /\ (!x. op i x = x)
          ==> DBUNIT op = i`,
  REWRITE_TAC[DBMONAD_DEF; DBUNIT; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

(*
let DBFREES = new_definition
  `DBFREES (op:(num->A)->A->A) x =
   INTERS {s | !f. (!i. i IN s ==> f i = DBUNIT op i) ==> op f x = x}`;;

let DBFREES' = new_definition
  `DBFREES' (op:(num->A)->A->A) x =
   {i | !f. (!j. ~(j = i) ==> f j = DBUNIT op j) ==> op f x = x}`;;

let DBMONAD_LUNIT_FUN = prove
 (`!f x:A. (!i. i IN DBFREES' op x ==> f i = DBUNIT op i) ==> op f x = x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DBFREES'] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  DISCH_TAC THEN

let DBMONAD_EXTENS = prove
 (`!op f g x:A. DBMONAD op /\ (!i. i IN DBFREES' op x ==> f i = g i)
                ==> op f x = op g x`,

  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {i:num | f i:A = g i}`
  CLAIM_TAC "rmk" `s SUBSET DBFREES' op (x:A)`
  REWRITE_TAC[DBFREES'; SUBSET] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  INTRO_TAC "!i; eq" THEN
  REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
  GEN_TAC THEN
  INTRO_TAC "hp" THEN
*)

(* ------------------------------------------------------------------------- *)
(* DBREINDEX                                                                 *)
(* ------------------------------------------------------------------------- *)

let DBREINDEX = new_definition
  `DBREINDEX op f x:A = op (DBUNIT op o f) x`;;

let DBREINDEX_DBREINDEX = prove
 (`!op f g x:A.
     DBMONAD op
     ==> DBREINDEX op g (DBREINDEX op f x) = DBREINDEX op (g o f) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DBREINDEX] THEN
  ASM_SIMP_TAC[DBMONAD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[DBMONAD_RUNIT; FUN_EQ_THM; o_THM]);;

let DBREINDEX_DBUNIT = prove
 (`!op f i. DBMONAD op ==> DBREINDEX op f (DBUNIT op i) = DBUNIT op (f i):A`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DBREINDEX] THEN
  ASM_SIMP_TAC[DBMONAD_RUNIT] THEN REWRITE_TAC[o_THM]);;

let DBREINDEX_DBSUBST = prove
 (`!op f g x:A. DBMONAD op
                ==> DBREINDEX op f (op g x) = op (DBREINDEX op f o g) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[DBREINDEX; DBMONAD_ASSOC; o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; DBREINDEX]);;

let DBSUBST_DBREINDEX = prove
 (`!op f g x:A. DBMONAD op ==> op f (DBREINDEX op g x) = op (f o g) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DBREINDEX] THEN
  ASM_SIMP_TAC[DBMONAD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  ASM_SIMP_TAC[DBMONAD_RUNIT]);;

(* ------------------------------------------------------------------------- *)
(* Morphisms of dB-monads.                                                   *)
(* ------------------------------------------------------------------------- *)

let DBMONAD_MOR = new_definition
  `!op1 op2 h:A->B.
     DBMONAD_MOR op1 op2 h <=>
     DBMONAD op1 /\ DBMONAD op2 /\
     (!n. h (DBUNIT op1 n) = DBUNIT op2 n) /\
     (!f x. h (op1 f x) = op2 (h o f) (h x))`;;

let DBMONAD_MOR_THM = prove
 (`(!op1 op2 h:A->B. DBMONAD_MOR op1 op2 h ==> DBMONAD op1) /\
   (!op1 op2 h:A->B. DBMONAD_MOR op1 op2 h ==> DBMONAD op2) /\
   (!op1 op2 h:A->B. DBMONAD_MOR op1 op2 h
                     ==> (!n. h (DBUNIT op1 n) = DBUNIT op2 n)) /\
   (!op1 op2 h:A->B. DBMONAD_MOR op1 op2 h
                     ==> (!f x. h (op1 f x) = op2 (h o f) (h x)))`,
  REWRITE_TAC[DBMONAD_MOR] THEN MESON_TAC[]);;

let DBMONAD_MOR_ID = prove
 (`!op:(num->A)->A->A. DBMONAD op ==> DBMONAD_MOR op op I`,
  REWRITE_TAC[DBMONAD_MOR; I_THM; I_O_ID]);;

let DBMONAD_MOR_o = prove
 (`!op1 op2 op3 h:A->B g:B->C.
     DBMONAD_MOR op1 op2 h /\ DBMONAD_MOR op2 op3 g
     ==> DBMONAD_MOR op1 op3 (g o h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DBMONAD_MOR] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[o_THM; o_ASSOC]);;

let DBMONAD_MOR_IMP = MATCH_MP EQ_IMP (SPEC_ALL DBMONAD_MOR);;

(* ------------------------------------------------------------------------- *)
(*  Modules.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MODULE_DEF = new_definition
  `!op mop:(num->A)->B->B.
     MODULE op mop <=> DBMONAD op /\
                       (!x. mop (DBUNIT op) x = x) /\
                       (!f g x. mop g (mop f x) = mop (op g o f) x)`;;

let SELF_MODULE = prove
 (`!op:(num->A)->A->A. MODULE op op <=> DBMONAD op`,
  REWRITE_TAC[DBMONAD; MODULE_DEF; o_DEF] THEN MESON_TAC[]);;

let MODULE_MOR = new_definition
  `!op mop1 mop2 h.
     MODULE_MOR op mop1 mop2 h <=>
     MODULE op mop1 /\
     MODULE op mop2 /\
     (!f:num->A x:M. h (mop1 f x) = mop2 f (h x):N)`;;

let MODULE_MOR_ID = prove
 (`!op mop:(num->A)->B->B. MODULE op mop <=> MODULE_MOR op mop mop I`,
  REWRITE_TAC[MODULE_MOR; I_THM]);;

let MODULE_MOR_o = prove
 (`!op:(num->A)->A->A mop1 mop2 g:N->L h:M->N.
     MODULE_MOR op mop1 mop2 h /\ MODULE_MOR op mop2 mop3 g
     ==> MODULE_MOR op mop1 mop3 (g o h)`,
  REWRITE_TAC[MODULE_MOR] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* ------------------------------------------------------------------------- *)
(*  Pull-back modules.                                                       *)
(* ------------------------------------------------------------------------- *)

let PBMOP = new_definition
  `!op':(num->A')->A'->A' op:(num->A)->A->A h:A'->A mop:(num->A)->M->M f.
     PBMOP op' op h mop f = mop (h o f)`;;

let PB_MODULE = prove
 (`!op' op h:A'->A mop:(num->A)->M->M.
      DBMONAD_MOR op' op h /\ MODULE op mop
      ==> MODULE op' (PBMOP op' op h mop)`,
  REWRITE_TAC[DBMONAD_MOR; MODULE_DEF; PBMOP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(*  Derived Modules.                                                         *)
(* ------------------------------------------------------------------------- *)

let DBDERIV = new_recursive_definition num_RECURSION
  `(!op f. DBDERIV op f 0 = DBUNIT op 0:A) /\
   (!op f i. DBDERIV op f (SUC i) = DBREINDEX op SUC (f i))`;;

let DBDERIV_DBUNIT = prove
 (`!op. DBMONAD op ==> DBDERIV op (DBUNIT op) = DBUNIT op:num->A`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  REWRITE_TAC[DBDERIV] THEN ASM_SIMP_TAC[DBREINDEX_DBUNIT]);;

let DMOP = new_definition
  `!op:(num->A)->A->A mop:(num->A)->M->M f:num->A x:M.
     DMOP op mop f x = mop (DBDERIV op f) x:M`;;

let MODULE_DMOP = prove
 (`!op mop:(num->A)->M->M. MODULE op mop ==> MODULE op (DMOP op mop)`,
  REPEAT GEN_TAC THEN INTRO_TAC "mod" THEN
  HYP_TAC "mod -> mnd munit massoc" (REWRITE_RULE[MODULE_DEF]) THEN
  ASM_REWRITE_TAC[MODULE_DEF] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[DMOP] THEN ASM_SIMP_TAC[DBDERIV_DBUNIT] THEN
  REWRITE_TAC[o_THM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  ASM_SIMP_TAC[DBDERIV; DBMONAD_RUNIT; o_THM] THEN
  ASM_SIMP_TAC[DBSUBST_DBREINDEX; DBREINDEX_DBSUBST] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; DBDERIV]);;

let MODULE_DMOP_MOR = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N.
     MODULE_MOR op mop1 mop2 h
     ==> MODULE_MOR op (DMOP op mop1) (DMOP op mop2) h`,
  SIMP_TAC[MODULE_MOR; MODULE_DMOP; DMOP]);;

let MODULE_MOR_INV = prove
 (`!op:(num->A)->A->A mop1 mop2 g:M->N h:N->M.
     MODULE_MOR op mop1 mop2 h /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)
     ==> MODULE_MOR op mop2 mop1 g`,
  REWRITE_TAC[MODULE_MOR] THEN MESON_TAC[]);;

let MODULE_ISOM = new_definition
  `!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     MODULE_ISOM op mop1 mop2 h g <=>
       MODULE_MOR op mop1 mop2 h /\
       (!x. g (h x) = x) /\ (!y. h (g y) = y)`;;

let MODULE_ISOM_SYM = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     MODULE_ISOM op mop1 mop2 h g
     ==> MODULE_ISOM op mop2 mop1 g h`,
  REWRITE_TAC[MODULE_ISOM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MODULE_MOR_INV THEN
  ASM_MESON_TAC[]);;

let MODULE_ISOM_UNFOLD = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g.
     MODULE_ISOM op mop1 mop2 h g <=>
     MODULE op mop1 /\
     MODULE op mop2 /\
     MODULE_MOR op mop1 mop2 h /\
     MODULE_MOR op mop2 mop1 g /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [ALL_TAC; ASM_REWRITE_TAC[MODULE_ISOM]] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP MODULE_ISOM_SYM) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [MODULE_ISOM]) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [MODULE_MOR]) THEN
  ASM_REWRITE_TAC[]);;

let EXP_DBMONAD = new_definition
  `!op:(num->A)->A->A h g.
     EXP_DBMONAD op h g <=> MODULE_ISOM op op (DMOP op op) h g`;;

let EXP_DBMONAD_MOR = new_definition
  `!op1 h1 g1 op2 h2 g2 f:A->B.
     EXP_DBMONAD_MOR op1 h1 g1 op2 h2 g2 f <=>
     EXP_DBMONAD op1 h1 g1 /\
     EXP_DBMONAD op2 h2 g2 /\
     DBMONAD_MOR op1 op2 f /\
      (!x. h2 (f x) = f (h1 x))`;;
