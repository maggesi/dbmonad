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
(* Substoids (De Bruijn monads).                                             *)
(* ------------------------------------------------------------------------- *)

let SUBSTOID_DEF = new_definition
  `!op:(num->A)->A->A.
     SUBSTOID op <=>
     (!f g x. op g (op f x) = op (\n. op g (f n)) x) /\
     (?i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`;;

let SBUNIT = new_definition
  `!op:(num->A)->A->A.
     SBUNIT op = (@i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`;;

let SUBSTOID = prove
 (`!op. SUBSTOID op <=>
        (!f g x:A. op g (op f x) = op (\n. op g (f n)) x) /\
        (!f n. op f (SBUNIT op n) = f n) /\
        (!x. op (SBUNIT op) x = x)`,
  REWRITE_TAC[SUBSTOID_DEF; SBUNIT] THEN MESON_TAC[]);;

let SUBSTOID_ASSOC = prove
 (`!op. SUBSTOID op ==> !f g x:A. op g (op f x) = op (op g o f) x`,
  REWRITE_TAC[SUBSTOID; o_DEF] THEN MESON_TAC[]);;

let SUBSTOID_RUNIT = prove
 (`!op. SUBSTOID op ==> (!f n. op f (SBUNIT op n) = f n:A)`,
  REWRITE_TAC[SUBSTOID] THEN MESON_TAC[]);;

let SUBSTOID_LUNIT = prove
 (`!op. SUBSTOID op ==> (!x:A. op (SBUNIT op) x = x)`,
  REWRITE_TAC[SUBSTOID] THEN MESON_TAC[]);;

let SUBSTOID_LUNIT_IMP = prove
 (`!op f x:A. SUBSTOID op /\ (!i. f i = SBUNIT op i) ==> op f x = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN
  SIMP_TAC[SUBSTOID_LUNIT]);;

let SBUNIT_UNIQUE = prove
 (`!op i. SUBSTOID op /\ (!f n. op f (i n) = f n:A) /\ (!x. op i x = x)
          ==> SBUNIT op = i`,
  REWRITE_TAC[SUBSTOID_DEF; SBUNIT; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

(*
let SBFREE = new_definition
  `SBFREE (op:(num->A)->A->A) x =
   INTERS {s | !f. (!i. i IN s ==> f i = SBUNIT op i) ==> op f x = x}`;;

let SBFREE' = new_definition
  `SBFREE' (op:(num->A)->A->A) x =
   {i | !f. (!j. ~(j = i) ==> f j = SBUNIT op j) ==> op f x = x}`;;

let SUBSTOID_LUNIT_FUN = prove
 (`!f x:A. (!i. i IN SBFREE' op x ==> f i = SBUNIT op i) ==> op f x = x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SBFREE'] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  DISCH_TAC THEN

let SUBSTOID_EXTENS = prove
 (`!op f g x:A. SUBSTOID op /\ (!i. i IN SBFREE' op x ==> f i = g i)
                ==> op f x = op g x`,

  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {i:num | f i:A = g i}`
  CLAIM_TAC "rmk" `s SUBSET SBFREE' op (x:A)`
  REWRITE_TAC[SBFREE'; SUBSET] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  INTRO_TAC "!i; eq" THEN
  REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
  GEN_TAC THEN
  INTRO_TAC "hp" THEN
*)

(* ------------------------------------------------------------------------- *)
(* SBREINDEX                                                                 *)
(* ------------------------------------------------------------------------- *)

let SBREINDEX = new_definition
  `SBREINDEX op f x:A = op (SBUNIT op o f) x`;;

let SBREINDEX_SBREINDEX = prove
 (`!op f g x:A.
     SUBSTOID op
     ==> SBREINDEX op g (SBREINDEX op f x) = SBREINDEX op (g o f) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SBREINDEX] THEN
  ASM_SIMP_TAC[SUBSTOID_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[SUBSTOID_RUNIT; FUN_EQ_THM; o_THM]);;

let SBREINDEX_SBUNIT = prove
 (`!op f i. SUBSTOID op ==> SBREINDEX op f (SBUNIT op i) = SBUNIT op (f i):A`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SBREINDEX] THEN
  ASM_SIMP_TAC[SUBSTOID_RUNIT] THEN REWRITE_TAC[o_THM]);;

let SBREINDEX_DBSUBST = prove
 (`!op f g x:A. SUBSTOID op
                ==> SBREINDEX op f (op g x) = op (SBREINDEX op f o g) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SBREINDEX; SUBSTOID_ASSOC; o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; SBREINDEX]);;

let DBSUBST_SBREINDEX = prove
 (`!op f g x:A. SUBSTOID op ==> op f (SBREINDEX op g x) = op (f o g) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SBREINDEX] THEN
  ASM_SIMP_TAC[SUBSTOID_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  ASM_SIMP_TAC[SUBSTOID_RUNIT]);;

(* ------------------------------------------------------------------------- *)
(* Morphisms of dB-monads.                                                   *)
(* ------------------------------------------------------------------------- *)

let SUBSTOID_MOR = new_definition
  `!op1 op2 h:A->B.
     SUBSTOID_MOR op1 op2 h <=>
     SUBSTOID op1 /\ SUBSTOID op2 /\
     (!n. h (SBUNIT op1 n) = SBUNIT op2 n) /\
     (!f x. h (op1 f x) = op2 (h o f) (h x))`;;

let SUBSTOID_MOR_THM = prove
 (`(!op1 op2 h:A->B. SUBSTOID_MOR op1 op2 h ==> SUBSTOID op1) /\
   (!op1 op2 h:A->B. SUBSTOID_MOR op1 op2 h ==> SUBSTOID op2) /\
   (!op1 op2 h:A->B. SUBSTOID_MOR op1 op2 h
                     ==> (!n. h (SBUNIT op1 n) = SBUNIT op2 n)) /\
   (!op1 op2 h:A->B. SUBSTOID_MOR op1 op2 h
                     ==> (!f x. h (op1 f x) = op2 (h o f) (h x)))`,
  REWRITE_TAC[SUBSTOID_MOR] THEN MESON_TAC[]);;

let SUBSTOID_MOR_ID = prove
 (`!op:(num->A)->A->A. SUBSTOID op ==> SUBSTOID_MOR op op I`,
  REWRITE_TAC[SUBSTOID_MOR; I_THM; I_O_ID]);;

let SUBSTOID_MOR_o = prove
 (`!op1 op2 op3 h:A->B g:B->C.
     SUBSTOID_MOR op1 op2 h /\ SUBSTOID_MOR op2 op3 g
     ==> SUBSTOID_MOR op1 op3 (g o h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSTOID_MOR] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[o_THM; o_ASSOC]);;

let SUBSTOID_MOR_IMP = MATCH_MP EQ_IMP (SPEC_ALL SUBSTOID_MOR);;

(* ------------------------------------------------------------------------- *)
(*  Substoid modules.                                                        *)
(* ------------------------------------------------------------------------- *)

let SBMODULE_DEF = new_definition
  `!op mop:(num->A)->B->B.
     SBMODULE op mop <=> SUBSTOID op /\
                       (!x. mop (SBUNIT op) x = x) /\
                       (!f g x. mop g (mop f x) = mop (op g o f) x)`;;

let SELF_SBMODULE = prove
 (`!op:(num->A)->A->A. SBMODULE op op <=> SUBSTOID op`,
  REWRITE_TAC[SUBSTOID; SBMODULE_DEF; o_DEF] THEN MESON_TAC[]);;

let SBMODULE_MOR = new_definition
  `!op mop1 mop2 h.
     SBMODULE_MOR op mop1 mop2 h <=>
     SBMODULE op mop1 /\
     SBMODULE op mop2 /\
     (!f:num->A x:M. h (mop1 f x) = mop2 f (h x):N)`;;

let SBMODULE_MOR_ID = prove
 (`!op mop:(num->A)->B->B. SBMODULE op mop <=> SBMODULE_MOR op mop mop I`,
  REWRITE_TAC[SBMODULE_MOR; I_THM]);;

let SBMODULE_MOR_o = prove
 (`!op:(num->A)->A->A mop1 mop2 g:N->L h:M->N.
     SBMODULE_MOR op mop1 mop2 h /\ SBMODULE_MOR op mop2 mop3 g
     ==> SBMODULE_MOR op mop1 mop3 (g o h)`,
  REWRITE_TAC[SBMODULE_MOR] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* ------------------------------------------------------------------------- *)
(*  Pull-back module.                                                        *)
(* ------------------------------------------------------------------------- *)

let PBMOP = new_definition
  `!op':(num->A')->A'->A' op:(num->A)->A->A h:A'->A mop:(num->A)->M->M f.
     PBMOP op' op h mop f = mop (h o f)`;;

let PB_SBMODULE = prove
 (`!op' op h:A'->A mop:(num->A)->M->M.
      SUBSTOID_MOR op' op h /\ SBMODULE op mop
      ==> SBMODULE op' (PBMOP op' op h mop)`,
  REWRITE_TAC[SUBSTOID_MOR; SBMODULE_DEF; PBMOP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(*  Derived module.                                                          *)
(* ------------------------------------------------------------------------- *)

let SBDERIV = new_recursive_definition num_RECURSION
  `(!op f. SBDERIV op f 0 = SBUNIT op 0:A) /\
   (!op f i. SBDERIV op f (SUC i) = SBREINDEX op SUC (f i))`;;

let SBDERIV_SBUNIT = prove
 (`!op. SUBSTOID op ==> SBDERIV op (SBUNIT op) = SBUNIT op:num->A`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  REWRITE_TAC[SBDERIV] THEN ASM_SIMP_TAC[SBREINDEX_SBUNIT]);;

let DMOP = new_definition
  `!op:(num->A)->A->A mop:(num->A)->M->M f:num->A x:M.
     DMOP op mop f x = mop (SBDERIV op f) x:M`;;

let SBMODULE_DMOP = prove
 (`!op mop:(num->A)->M->M. SBMODULE op mop ==> SBMODULE op (DMOP op mop)`,
  REPEAT GEN_TAC THEN INTRO_TAC "mod" THEN
  HYP_TAC "mod -> mnd munit massoc" (REWRITE_RULE[SBMODULE_DEF]) THEN
  ASM_REWRITE_TAC[SBMODULE_DEF] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[DMOP] THEN ASM_SIMP_TAC[SBDERIV_SBUNIT] THEN
  REWRITE_TAC[o_THM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  ASM_SIMP_TAC[SBDERIV; SUBSTOID_RUNIT; o_THM] THEN
  ASM_SIMP_TAC[DBSUBST_SBREINDEX; SBREINDEX_DBSUBST] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; SBDERIV]);;

let SBMODULE_DMOP_MOR = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N.
     SBMODULE_MOR op mop1 mop2 h
     ==> SBMODULE_MOR op (DMOP op mop1) (DMOP op mop2) h`,
  SIMP_TAC[SBMODULE_MOR; SBMODULE_DMOP; DMOP]);;

let SBMODULE_MOR_INV = prove
 (`!op:(num->A)->A->A mop1 mop2 g:M->N h:N->M.
     SBMODULE_MOR op mop1 mop2 h /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)
     ==> SBMODULE_MOR op mop2 mop1 g`,
  REWRITE_TAC[SBMODULE_MOR] THEN MESON_TAC[]);;

let SBMODULE_ISOM = new_definition
  `!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     SBMODULE_ISOM op mop1 mop2 h g <=>
       SBMODULE_MOR op mop1 mop2 h /\
       (!x. g (h x) = x) /\ (!y. h (g y) = y)`;;

let SBMODULE_ISOM_SYM = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     SBMODULE_ISOM op mop1 mop2 h g
     ==> SBMODULE_ISOM op mop2 mop1 g h`,
  REWRITE_TAC[SBMODULE_ISOM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SBMODULE_MOR_INV THEN
  ASM_MESON_TAC[]);;

let SBMODULE_ISOM_UNFOLD = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g.
     SBMODULE_ISOM op mop1 mop2 h g <=>
     SBMODULE op mop1 /\
     SBMODULE op mop2 /\
     SBMODULE_MOR op mop1 mop2 h /\
     SBMODULE_MOR op mop2 mop1 g /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [ALL_TAC; ASM_REWRITE_TAC[SBMODULE_ISOM]] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP SBMODULE_ISOM_SYM) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SBMODULE_ISOM]) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SBMODULE_MOR]) THEN
  ASM_REWRITE_TAC[]);;

let EXP_SUBSTOID = new_definition
  `!op:(num->A)->A->A h g.
     EXP_SUBSTOID op h g <=> SBMODULE_ISOM op op (DMOP op op) h g`;;

let EXP_SUBSTOID_MOR = new_definition
  `!op1 h1 g1 op2 h2 g2 f:A->B.
     EXP_SUBSTOID_MOR op1 h1 g1 op2 h2 g2 f <=>
     EXP_SUBSTOID op1 h1 g1 /\
     EXP_SUBSTOID op2 h2 g2 /\
     SUBSTOID_MOR op1 op2 f /\
      (!x. h2 (f x) = f (h1 x))`;;
