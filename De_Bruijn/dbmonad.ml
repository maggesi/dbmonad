(* ========================================================================= *)
(*  De Bruijn monads and modules.                                            *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2005 2006 2017, 2020, 2021          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* De Bruijn monads.                                                         *)
(* ------------------------------------------------------------------------- *)

let MONAD_DEF = new_definition
  `MONAD =
   {op:(num->A)->A->A |
     (!f g x. op g (op f x) = op (\n. op g (f n)) x) /\
     (?i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))}`;;

let IN_MONAD = prove
 (`!op:(num->A)->A->A.
     op IN MONAD <=>
     (!f g x. op g (op f x) = op (\n. op g (f n)) x) /\
     (?i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`,
  REWRITE_TAC[MONAD_DEF; IN_ELIM_THM]);;

let UNIT = new_definition
  `!op:(num->A)->A->A.
     UNIT op = (@i. (!f n. op f (i n) = f n) /\ (!x. op i x = x))`;;

let MONAD = prove
 (`!op. op IN MONAD <=>
        (!f g x:A. op g (op f x) = op (\n. op g (f n)) x) /\
        (!f n. op f (UNIT op n) = f n) /\
        (!x. op (UNIT op) x = x)`,
  REWRITE_TAC[IN_MONAD; UNIT] THEN MESON_TAC[]);;

let MONAD_ASSOC = prove
 (`!op. op IN MONAD ==> !f g x:A. op g (op f x) = op (op g o f) x`,
  REWRITE_TAC[MONAD; o_DEF] THEN MESON_TAC[]);;

let MONAD_RUNIT = prove
 (`!op. op IN MONAD ==> (!f n. op f (UNIT op n) = f n:A)`,
  REWRITE_TAC[MONAD] THEN MESON_TAC[]);;

let MONAD_LUNIT = prove
 (`!op. op IN MONAD ==> (!x:A. op (UNIT op) x = x)`,
  REWRITE_TAC[MONAD] THEN MESON_TAC[]);;

let MONAD_LUNIT_IMP = prove
 (`!op f x:A. op IN MONAD /\ (!i. f i = UNIT op i) ==> op f x = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN
  SIMP_TAC[MONAD_LUNIT]);;

let MONAD_UNIT_UNIQUE = prove
 (`!op i. op IN MONAD /\ (!f n. op f (i n) = f n:A) /\ (!x. op i x = x)
          ==> UNIT op = i`,
  REWRITE_TAC[IN_MONAD; UNIT; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reindexing: functoriality of De Bruijn monads.                            *)
(* ------------------------------------------------------------------------- *)

let FMAP = new_definition
  `FMAP op f x:A = op (UNIT op o f) x`;;

let FMAP_FMAP = prove
 (`!op f g x:A.
     op IN MONAD
     ==> FMAP op g (FMAP op f x) = FMAP op (g o f) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FMAP] THEN
  ASM_SIMP_TAC[MONAD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[MONAD_RUNIT; FUN_EQ_THM; o_THM]);;

let FMAP_UNIT = prove
 (`!op f i. op IN MONAD ==> FMAP op f (UNIT op i) = UNIT op (f i):A`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FMAP] THEN
  ASM_SIMP_TAC[MONAD_RUNIT] THEN REWRITE_TAC[o_THM]);;

let FMAP_OP = prove
 (`!op f g x:A. op IN MONAD
                ==> FMAP op f (op g x) = op (FMAP op f o g) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[FMAP; MONAD_ASSOC; o_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FMAP]);;

let OP_FMAP = prove
 (`!op f g x:A. op IN MONAD ==> op f (FMAP op g x) = op (f o g) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FMAP] THEN
  ASM_SIMP_TAC[MONAD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN ASM_SIMP_TAC[MONAD_RUNIT]);;

(* ------------------------------------------------------------------------- *)
(* Morphisms of De Bruijn monads.                                            *)
(* ------------------------------------------------------------------------- *)

let MONAD_HOM = define
  `MONAD_HOM (op1,op2) =
   {h:A->B | op1 IN MONAD /\ op2 IN MONAD /\
             (!n. h (UNIT op1 n) = UNIT op2 n) /\
             (!f x. h (op1 f x) = op2 (h o f) (h x))}`;;

let IN_MONAD_HOM = prove
 (`!op1 op2 h:A->B.
     h IN MONAD_HOM (op1,op2) <=>
     op1 IN MONAD /\ op2 IN MONAD /\
     (!n. h (UNIT op1 n) = UNIT op2 n) /\
     (!f x. h (op1 f x) = op2 (h o f) (h x))`,
  REWRITE_TAC[MONAD_HOM; IN_ELIM_THM]);;

let MONAD_HOM_I = prove
 (`!op:(num->A)->A->A. op IN MONAD ==> I IN MONAD_HOM (op,op)`,
  REWRITE_TAC[IN_MONAD_HOM; I_THM; I_O_ID]);;

let MONAD_HOM_o = prove
 (`!op1 op2 op3 h:A->B g:B->C.
     h IN MONAD_HOM (op1,op2) /\ g IN MONAD_HOM (op2,op3)
     ==> g o h IN MONAD_HOM (op1,op3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MONAD_HOM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[o_THM; o_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Modules over De Bruijn monads                                             *)
(* ------------------------------------------------------------------------- *)

let MODULE = new_definition
  `MODULE (op:(num->A)->A->A) =
   {mop:(num->A)->B->B | op IN MONAD /\
                         (!x. mop (UNIT op) x = x) /\
                         (!f g x. mop g (mop f x) = mop (op g o f) x)}`;;

let IN_MODULE = prove
 (`mop:(num->A)->B->B IN MODULE (op:(num->A)->A->A) <=>
   op IN MONAD /\
   (!x. mop (UNIT op) x = x) /\
   (!f g x. mop g (mop f x) = mop (op g o f) x)`,
  REWRITE_TAC[MODULE; IN_ELIM_THM]);;

let MMAP = new_definition
  `MMAP (op,mop:(num->A)->B->B) f = mop (UNIT op o f)`;;

(* ------------------------------------------------------------------------- *)
(* Tautological module over a De Bruijn monad.                               *)
(* ------------------------------------------------------------------------- *)

let SELF_MODULE = prove
 (`!op:(num->A)->A->A. op IN MODULE op <=> op IN MONAD`,
  REWRITE_TAC[MONAD; IN_MODULE; o_DEF] THEN MESON_TAC[]);;

let SELF_FMAP = prove
 (`!op:(num->A)->A->A. FMAP op = MMAP (op,op)`,
  REWRITE_TAC[FUN_EQ_THM; FMAP; MMAP]);;

(* ------------------------------------------------------------------------- *)
(* Product of modules.                                                       *)
(* ------------------------------------------------------------------------- *)

let MPROD = new_definition
  `MPROD (mop1:(num->A)->B->B) (mop2:(num->A)->C->C)
           (f:num->A) (x:B,y:C) : B#C = mop1 f x,mop2 f y`;;

let MPROD_IN_MODULE = prove
 (`!op mod1:(num->A)->B->B mod2:(num->A)->C->C.
     mod1 IN MODULE op /\ mod2 IN MODULE op
     ==> MPROD mod1 mod2 IN MODULE op`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MODULE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; MPROD]);;

let MMAP_MPROD = prove
 (`!op:(num->A)->A->A f x:B y:C.
     MMAP (op,MPROD mop1 mop2) f (x,y) =
     MMAP (op,mop1) f x, MMAP (op,mop2) f y`,
  REWRITE_TAC[MMAP; MPROD]);;

(* ------------------------------------------------------------------------- *)
(* Morphisms of modules over the same De Bruijn monad.                       *)
(* ------------------------------------------------------------------------- *)

let MODULE_MOR = new_definition
  `MODULE_MOR op (mop1,mop2) =
   {h:B->C | mop1 IN MODULE op /\
             mop2 IN MODULE op /\
             (!f:num->A x. h (mop1 f x) = mop2 f (h x))}`;;

let IN_MODULE_MOR = prove
 (`!op mop1 mop2 h:B->C.
     h IN MODULE_MOR op (mop1,mop2) <=>
     mop1 IN MODULE op /\
     mop2 IN MODULE op /\
     (!f:num->A x. h (mop1 f x) = mop2 f (h x))`,
  REWRITE_TAC[MODULE_MOR; IN_ELIM_THM]);;

let MODULE_MOR_MMAP = prove
 (`!op:(num->A)->A->A mop1 mop2 h:B->C f x.
     h IN MODULE_MOR op (mop1,mop2)
     ==> h (MMAP (op,mop1) f x) = MMAP (op,mop2) f (h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MODULE_MOR] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MMAP]);;

let MODULE_MOR_ID = prove
 (`!op mop:(num->A)->B->B.
     I IN MODULE_MOR op (mop,mop) <=> mop IN MODULE op`,
  REWRITE_TAC[IN_MODULE_MOR; I_THM]);;

let MODULE_MOR_o = prove
 (`!op:(num->A)->A->A mop1 mop2 g:N->L h:M->N.
     h IN MODULE_MOR op (mop1,mop2) /\
     g IN MODULE_MOR op (mop2,mop3)
     ==> g o h IN MODULE_MOR op (mop1,mop3)`,
  REWRITE_TAC[IN_MODULE_MOR] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Pull-back module along a module morphism.                                 *)
(* ------------------------------------------------------------------------- *)

let PBMOP = new_definition
  `!h:A'->A mop:(num->A)->M->M f.
     PBMOP h mop f = mop (h o f)`;;

let PBMOP_IN_MODULE = prove
 (`!op' op h:A'->A mop:(num->A)->M->M.
      h IN MONAD_HOM (op',op) /\ mop IN MODULE op
      ==> PBMOP h mop IN MODULE op'`,
  REWRITE_TAC[IN_MONAD_HOM; IN_MODULE; PBMOP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Derived module.                                                           *)
(* ------------------------------------------------------------------------- *)

let MDERIV = new_recursive_definition num_RECURSION
  `(!op f. MDERIV op f 0 = UNIT op 0:A) /\
   (!op f i. MDERIV op f (SUC i) = FMAP op SUC (f i))`;;

let MDERIV_UNIT = prove
 (`!op. op IN MONAD ==> MDERIV op (UNIT op) = UNIT op:num->A`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  REWRITE_TAC[MDERIV] THEN ASM_SIMP_TAC[FMAP_UNIT]);;

let DMOP = new_definition
  `!op:(num->A)->A->A mop:(num->A)->M->M f:num->A x:M.
     DMOP op mop f x = mop (MDERIV op f) x:M`;;

let MODULE_DMOP = prove
 (`!op mop:(num->A)->M->M.
     mop IN MODULE op ==> DMOP op mop IN MODULE op`,
  REPEAT GEN_TAC THEN INTRO_TAC "mod" THEN
  HYP_TAC "mod -> mnd munit massoc" (REWRITE_RULE[IN_MODULE]) THEN
  ASM_REWRITE_TAC[IN_MODULE] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[DMOP] THEN
  ASM_SIMP_TAC[MDERIV_UNIT] THEN REWRITE_TAC[o_THM] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN NUM_CASES_TAC THEN
  ASM_SIMP_TAC[MDERIV; MONAD_RUNIT; o_THM; OP_FMAP; FMAP_OP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; MDERIV]);;

let DMOP_IN_MODULE_MOR = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N.
     h IN MODULE_MOR op (mop1,mop2)
     ==> h IN MODULE_MOR op (DMOP op mop1,DMOP op mop2)`,
  SIMP_TAC[IN_MODULE_MOR; MODULE_DMOP; DMOP]);;

(* ------------------------------------------------------------------------- *)
(* Isomorphisms of modules over a De Bruijn monad.                           *)
(* ------------------------------------------------------------------------- *)

let MODULE_MOR_INV = prove
 (`!op:(num->A)->A->A mop1 mop2 g:M->N h:N->M.
     h IN MODULE_MOR op (mop1,mop2) /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)
     ==> g IN MODULE_MOR op (mop2,mop1)`,
  REWRITE_TAC[IN_MODULE_MOR] THEN MESON_TAC[]);;

let MODULE_ISOM = new_definition
  `!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     MODULE_ISOM op (mop1,mop2) (h,g) <=>
       h IN MODULE_MOR op (mop1,mop2) /\
       (!x. g (h x) = x) /\ (!y. h (g y) = y)`;;

let MODULE_ISOM_SYM = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g:N->M.
     MODULE_ISOM op (mop1,mop2) (h,g)
     ==> MODULE_ISOM op (mop2,mop1) (g,h)`,
  REWRITE_TAC[MODULE_ISOM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MODULE_MOR_INV THEN ASM_MESON_TAC[]);;

let MODULE_ISOM_UNFOLD = prove
 (`!op:(num->A)->A->A mop1 mop2 h:M->N g.
     MODULE_ISOM op (mop1,mop2) (h,g) <=>
     mop1 IN MODULE op /\
     mop2 IN MODULE op /\
     h IN MODULE_MOR op (mop1,mop2) /\
     g IN MODULE_MOR op (mop2,mop1) /\
     (!x. g (h x) = x) /\ (!y. h (g y) = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [ALL_TAC; ASM_REWRITE_TAC[MODULE_ISOM]] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP MODULE_ISOM_SYM) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [MODULE_ISOM]) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [IN_MODULE_MOR]) THEN ASM_REWRITE_TAC[]);;

let EXP_MONAD = new_definition
  `!op:(num->A)->A->A h g.
     EXP_MONAD op h g <=> MODULE_ISOM op (op,DMOP op op) (h,g)`;;

let EXP_MONAD_HOM = new_definition
  `!op1 h1 g1 op2 h2 g2 f:A->B.
     EXP_MONAD_HOM op1 h1 g1 op2 h2 g2 f <=>
     EXP_MONAD op1 h1 g1 /\
     EXP_MONAD op2 h2 g2 /\
     f IN MONAD_HOM (op1,op2) /\
      (!x. h2 (f x) = f (h1 x))`;;
