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
(* De Bruijn monads.                                                         *)
(* ------------------------------------------------------------------------- *)

let SUBSTOID_DEF = new_definition
  `!op:(num->A)->A->A.
     SUBSTOID op <=>
     (!f g x. op g (op f x) = op (\n. op g (f n)) x) /\
     (?i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`;;

let UNIT = new_definition
  `!op:(num->A)->A->A.
     UNIT op = (@i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`;;

let SUBSTOID = prove
 (`!op. SUBSTOID op <=>
        (!f g x:A. op g (op f x) = op (\n. op g (f n)) x) /\
        (!f n. op f (UNIT op n) = f n) /\
        (!x. op (UNIT op) x = x)`,
  REWRITE_TAC[SUBSTOID_DEF; UNIT] THEN MESON_TAC[]);;

let SUBSTOID_ASSOC = prove
 (`!op. SUBSTOID op ==> !f g x:A. op g (op f x) = op (op g o f) x`,
  REWRITE_TAC[SUBSTOID; o_DEF] THEN MESON_TAC[]);;

let SUBSTOID_RUNIT = prove
 (`!op. SUBSTOID op ==> (!f n. op f (UNIT op n) = f n:A)`,
  REWRITE_TAC[SUBSTOID] THEN MESON_TAC[]);;

let SUBSTOID_LUNIT = prove
 (`!op. SUBSTOID op ==> (!x:A. op (UNIT op) x = x)`,
  REWRITE_TAC[SUBSTOID] THEN MESON_TAC[]);;

let SUBSTOID_LUNIT_IMP = prove
 (`!op f x:A. SUBSTOID op /\ (!i. f i = UNIT op i) ==> op f x = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN
  SIMP_TAC[SUBSTOID_LUNIT]);;

let UNIT_UNIQUE = prove
 (`!op i. SUBSTOID op /\ (!f n. op f (i n) = f n:A) /\ (!x. op i x = x)
          ==> UNIT op = i`,
  REWRITE_TAC[SUBSTOID_DEF; UNIT; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* SBREINDEX                                                                 *)
(* ------------------------------------------------------------------------- *)

let SBREINDEX = new_definition
  `SBREINDEX op f x:A = op (UNIT op o f) x`;;

let SBREINDEX_SBREINDEX = prove
 (`!op f g x:A.
     SUBSTOID op
     ==> SBREINDEX op g (SBREINDEX op f x) = SBREINDEX op (g o f) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SBREINDEX] THEN
  ASM_SIMP_TAC[SUBSTOID_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[SUBSTOID_RUNIT; FUN_EQ_THM; o_THM]);;

let SBREINDEX_UNIT = prove
 (`!op f i. SUBSTOID op ==> SBREINDEX op f (UNIT op i) = UNIT op (f i):A`,
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

let SUBSTOID_MOR = define
  `SUBSTOID_MOR (op1,op2) =
   {h:A->B | SUBSTOID op1 /\ SUBSTOID op2 /\
             (!n. h (UNIT op1 n) = UNIT op2 n) /\
             (!f x. h (op1 f x) = op2 (h o f) (h x))}`;;

let IN_SUBSTOID_MOR = prove
 (`!op1 op2 h:A->B.
     h IN SUBSTOID_MOR (op1,op2) <=>
     SUBSTOID op1 /\ SUBSTOID op2 /\
     (!n. h (UNIT op1 n) = UNIT op2 n) /\
     (!f x. h (op1 f x) = op2 (h o f) (h x))`,
  REWRITE_TAC[SUBSTOID_MOR; IN_ELIM_THM]);;

(*
let SUBSTOID_MOR_THM = prove
 (`(!op1 op2 h:A->B. h IN SUBSTOID_MOR (op1,op2) ==> SUBSTOID op1) /\
   (!op1 op2 h:A->B. h IN SUBSTOID_MOR (op1,op2) ==> SUBSTOID op2) /\
   (!op1 op2 h:A->B. h IN SUBSTOID_MOR (op1,op2)
                     ==> (!n. h (UNIT op1 n) = UNIT op2 n)) /\
   (!op1 op2 h:A->B. h IN SUBSTOID_MOR (op1,op2)
                     ==> (!f x. h (op1 f x) = op2 (h o f) (h x)))`,
  REWRITE_TAC[IN_SUBSTOID_MOR] THEN MESON_TAC[]);;
*)

let SUBSTOID_MOR_ID = prove
 (`!op:(num->A)->A->A. SUBSTOID op ==> I IN SUBSTOID_MOR (op,op)`,
  REWRITE_TAC[IN_SUBSTOID_MOR; I_THM; I_O_ID]);;

let SUBSTOID_MOR_o = prove
 (`!op1 op2 op3 h:A->B g:B->C.
     h IN SUBSTOID_MOR (op1,op2) /\ g IN SUBSTOID_MOR (op2,op3)
     ==> g o h IN SUBSTOID_MOR (op1,op3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SUBSTOID_MOR] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[o_THM; o_ASSOC]);;

(* let SUBSTOID_MOR_IMP = MATCH_MP EQ_IMP (SPEC_ALL SUBSTOID_MOR);; *)

(* ------------------------------------------------------------------------- *)
(*  Substoid modules.                                                        *)
(* ------------------------------------------------------------------------- *)

let SBMODULE = new_definition
  `SBMODULE (op:(num->A)->A->A) =
   {mop:(num->A)->B->B | SUBSTOID op /\
                         (!x. mop (UNIT op) x = x) /\
                         (!f g x. mop g (mop f x) = mop (op g o f) x)}`;;

let IN_SBMODULE = prove
 (`mop:(num->A)->B->B IN SBMODULE (op:(num->A)->A->A) <=>
   SUBSTOID op /\
   (!x. mop (UNIT op) x = x) /\
   (!f g x. mop g (mop f x) = mop (op g o f) x)`,
  REWRITE_TAC[SBMODULE; IN_ELIM_THM]);;

let MODREINDEX = new_definition
  `MODREINDEX (op,mop:(num->A)->B->B) f = mop (UNIT op o f)`;;

let SELF_SBMODULE = prove
 (`!op:(num->A)->A->A. op IN SBMODULE op <=> SUBSTOID op`,
  REWRITE_TAC[SUBSTOID; IN_SBMODULE; o_DEF] THEN MESON_TAC[]);;

let SELF_SBREINDEX = prove
 (`!op:(num->A)->A->A. SBREINDEX op = MODREINDEX (op,op)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; SBREINDEX; MODREINDEX]);;

let SBMODULE_MOR = new_definition
  `SBMODULE_MOR op (mop1,mop2) =
   {h:B->C | mop1 IN SBMODULE op /\
             mop2 IN SBMODULE op /\
             (!f:num->A x. h (mop1 f x) = mop2 f (h x))}`;;

let IN_SBMODULE_MOR = prove
 (`!op mop1 mop2 h:B->C.
     h IN SBMODULE_MOR op (mop1,mop2) <=>
     mop1 IN SBMODULE op /\
     mop2 IN SBMODULE op /\
     (!f:num->A x. h (mop1 f x) = mop2 f (h x))`,
  REWRITE_TAC[SBMODULE_MOR; IN_ELIM_THM]);;

let SBMODULE_MOR_MODREINDEX = prove
 (`!op:(num->A)->A->A mop1 mop2 h:B->C f x.
     h IN SBMODULE_MOR op (mop1,mop2)
     ==> h (MODREINDEX (op,mop1) f x) = MODREINDEX (op,mop2) f (h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SBMODULE_MOR] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MODREINDEX]);;

let SBMODULE_MOR_ID = prove
 (`!op mop:(num->A)->B->B.
     I IN SBMODULE_MOR op (mop,mop) <=> mop IN SBMODULE op`,
  REWRITE_TAC[IN_SBMODULE_MOR; I_THM]);;

let SBMODULE_MOR_o = prove
 (`!op:(num->A)->A->A mop1 mop2 g:N->L h:M->N.
     h IN SBMODULE_MOR op (mop1,mop2) /\
     g IN SBMODULE_MOR op (mop2,mop3)
     ==> g o h IN SBMODULE_MOR op (mop1,mop3)`,
  REWRITE_TAC[IN_SBMODULE_MOR] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* ------------------------------------------------------------------------- *)
(*  Pull-back module.                                                        *)
(* ------------------------------------------------------------------------- *)

let PBMOP = new_definition
  `!op':(num->A')->A'->A' op:(num->A)->A->A h:A'->A mop:(num->A)->M->M f.
     PBMOP op' op h mop f = mop (h o f)`;;

let PB_SBMODULE = prove
 (`!op' op h:A'->A mop:(num->A)->M->M.
      h IN SUBSTOID_MOR (op',op) /\ mop IN SBMODULE op
      ==> PBMOP op' op h mop IN SBMODULE op'`,
  REWRITE_TAC[IN_SUBSTOID_MOR; IN_SBMODULE; PBMOP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(*  Derived module.                                                          *)
(* ------------------------------------------------------------------------- *)

let SBDERIV = new_recursive_definition num_RECURSION
  `(!op f. SBDERIV op f 0 = UNIT op 0:A) /\
   (!op f i. SBDERIV op f (SUC i) = SBREINDEX op SUC (f i))`;;

let SBDERIV_UNIT = prove
 (`!op. SUBSTOID op ==> SBDERIV op (UNIT op) = UNIT op:num->A`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  REWRITE_TAC[SBDERIV] THEN ASM_SIMP_TAC[SBREINDEX_UNIT]);;

let DMOP = new_definition
  `!op:(num->A)->A->A mop:(num->A)->M->M f:num->A x:M.
     DMOP op mop f x = mop (SBDERIV op f) x:M`;;

let SBMODULE_DMOP = prove
 (`!op mop:(num->A)->M->M.
     mop IN SBMODULE op ==> DMOP op mop IN SBMODULE op`,
  REPEAT GEN_TAC THEN INTRO_TAC "mod" THEN
  HYP_TAC "mod -> mnd munit massoc" (REWRITE_RULE[IN_SBMODULE]) THEN
  ASM_REWRITE_TAC[IN_SBMODULE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[DMOP] THEN ASM_SIMP_TAC[SBDERIV_UNIT] THEN
  REWRITE_TAC[o_THM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  ASM_SIMP_TAC[SBDERIV; SUBSTOID_RUNIT; o_THM] THEN
  ASM_SIMP_TAC[DBSUBST_SBREINDEX; SBREINDEX_DBSUBST] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; SBDERIV]);;

let SBMODULE_DMOP_MOR = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N.
     h IN SBMODULE_MOR op (mop1,mop2)
     ==> h IN SBMODULE_MOR op (DMOP op mop1,DMOP op mop2)`,
  SIMP_TAC[IN_SBMODULE_MOR; SBMODULE_DMOP; DMOP]);;

let SBMODULE_MOR_INV = prove
 (`!op:(num->A)->A->A mop1 mop2 g:M->N h:N->M.
     h IN SBMODULE_MOR op (mop1,mop2) /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)
     ==> g IN SBMODULE_MOR op (mop2,mop1)`,
  REWRITE_TAC[IN_SBMODULE_MOR] THEN MESON_TAC[]);;

let SBMODULE_ISOM = new_definition
  `!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     SBMODULE_ISOM op (mop1,mop2) (h,g) <=>
       h IN SBMODULE_MOR op (mop1,mop2) /\
       (!x. g (h x) = x) /\ (!y. h (g y) = y)`;;

let SBMODULE_ISOM_SYM = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     SBMODULE_ISOM op (mop1,mop2) (h,g)
     ==> SBMODULE_ISOM op (mop2,mop1) (g,h)`,
  REWRITE_TAC[SBMODULE_ISOM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SBMODULE_MOR_INV THEN
  ASM_MESON_TAC[]);;

let SBMODULE_ISOM_UNFOLD = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g.
     SBMODULE_ISOM op (mop1,mop2) (h,g) <=>
     mop1 IN SBMODULE op /\
     mop2 IN SBMODULE op /\
     h IN SBMODULE_MOR op (mop1,mop2) /\
     g IN SBMODULE_MOR op (mop2,mop1) /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [ALL_TAC; ASM_REWRITE_TAC[SBMODULE_ISOM]] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP SBMODULE_ISOM_SYM) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [SBMODULE_ISOM]) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IN_SBMODULE_MOR]) THEN
  ASM_REWRITE_TAC[]);;

let EXP_SUBSTOID = new_definition
  `!op:(num->A)->A->A h g.
     EXP_SUBSTOID op h g <=> SBMODULE_ISOM op (op,DMOP op op) (h,g)`;;

let EXP_SUBSTOID_MOR = new_definition
  `!op1 h1 g1 op2 h2 g2 f:A->B.
     EXP_SUBSTOID_MOR op1 h1 g1 op2 h2 g2 f <=>
     EXP_SUBSTOID op1 h1 g1 /\
     EXP_SUBSTOID op2 h2 g2 /\
     f IN SUBSTOID_MOR (op1,op2) /\
      (!x. h2 (f x) = f (h1 x))`;;
