(* -*- holl -*- *)

(* ========================================================================= *)
(*  More definitions and theorems and tactics about lists.                   *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  Operads.                                                                 *)
(* ------------------------------------------------------------------------- *)

let OPERAD_DEF = new_definition
  `!(op:(num->A)->A->A).
     OPERAD op <=>
       (!f g x. op g (op f x) = op (\n. op g (f n)) x) /\
       (?i. (!f n. op f (i n) = f n) /\
            (!x. op i x = x))`;;

let OPERAD_UNIT = new_definition
  `!(op:(num->A)->A->A).
      OPERAD_UNIT op = (@i. (!f n. op f (i n) = f n) /\
                            (!x. op i x = x))`;;

let OPERAD = prove
  (`!op:(num->A)->A->A. OPERAD op <=>
      (!f g x. op g (op f x) = op (\n. op g (f n)) x) /\
      (!f n. op f (OPERAD_UNIT op n) = f n) /\
      (!x. op (OPERAD_UNIT op) x = x)`,
   REWRITE_TAC [OPERAD_DEF; OPERAD_UNIT] THEN MESON_TAC []);;

let OPERAD_ASSOC = prove
  (`!op. OPERAD op ==>
      (!f g x. op g (op f x) = op (\n. op g (f n)) x)`,
  REWRITE_TAC [OPERAD] THEN MESON_TAC[]);;

let OPERAD_RUNIT = prove
  (`!op. OPERAD op ==> (!f n. op f (OPERAD_UNIT op n) = f n)`,
  REWRITE_TAC [OPERAD] THEN MESON_TAC[]);;

let OPERAD_LUNIT = prove
  (`!op. OPERAD op ==> (!x. op (OPERAD_UNIT op) x = x)`,
  REWRITE_TAC [OPERAD] THEN MESON_TAC[]);;

let OPERAD_LUNIT_IMP = prove
  (`!op f x. OPERAD op /\ (!i. f i = OPERAD_UNIT op i) ==> op f x = x`,
   REWRITE_TAC [GSYM FUN_EQ_THM; ETA_AX] THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [OPERAD_LUNIT]);;

(* Example: operad of lists. *)
(***********************************
needs "/home/maggesi/Trees/HOL/hol_light/Permutation/morelist.ml";;

g `OPERAD FLATMAP (\n:num. [n])`;;
e (REWRITE_TAC [OPERAD_DEF; FLATMAP; APPEND_NIL]);;
e (CONJ_TAC);;
e (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [FLATMAP; APPEND]);;
e (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [FLATMAP; FLATMAP_APPEND]);;
let LIST_OPERAD = top_thm ();;
*************************************)

let OPERAD_UNIT_UNIQUE = prove
  (`!op i. OPERAD op /\ (!f n. op f (i n) = f n) /\ (!x. op i x = x)
           ==> OPERAD_UNIT op = i`,
   REWRITE_TAC [OPERAD_DEF; OPERAD_UNIT; FUN_EQ_THM] THEN MESON_TAC []);;

let OPERAD_SHIFT = new_definition
  `!op k n x. OPERAD_SHIFT op k n x =
                op (\i. if i < k
 		        then OPERAD_UNIT op i
 			else OPERAD_UNIT op (n + i))
                   x`;;

let OPERAD_OP_SHIFT = prove
  (`!op f k n x. OPERAD op
                 ==> op f (OPERAD_SHIFT op k n x) =
                     op (\i. f (if i < k then i else n + i)) x`,
   REWRITE_TAC [OPERAD] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [OPERAD_SHIFT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC []);;

let OPERAD_SHIFT_OP = prove
  (`!op f k n x. OPERAD op
                 ==> OPERAD_SHIFT op k n (op f x) =
                     op (OPERAD_SHIFT op k n o f) x`,
   REWRITE_TAC [OPERAD] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [OPERAD_SHIFT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; o_THM; OPERAD_SHIFT] THEN GEN_TAC);;

let OPERAD_MOR = new_definition
  `!op1 op2 h. OPERAD_MOR op1 op2 h <=>
     OPERAD op1 /\ OPERAD op2 /\
     (!n. h (OPERAD_UNIT op1 n) = OPERAD_UNIT op2 n) /\
     (!f x. h (op1 f x) = op2 (h o f) (h x))`;;

let OPERAD_MOR_THM = prove
  (`(!op1 op2 h. OPERAD_MOR op1 op2 h ==> OPERAD op1) /\
    (!op1 op2 h. OPERAD_MOR op1 op2 h ==> OPERAD op2) /\
    (!op1 op2 h. OPERAD_MOR op1 op2 h ==>
                 (!n. h (OPERAD_UNIT op1 n) = OPERAD_UNIT op2 n)) /\
    (!op1 op2 h. OPERAD_MOR op1 op2 h ==>
                 (!f x. h (op1 f x) = op2 (h o f) (h x)))`,
   REWRITE_TAC [OPERAD_MOR] THEN MESON_TAC []);;

let OPERAD_MOR_SRC_THM = prove
  (`(!op1 op2 h. OPERAD_MOR op1 op2 h ==> OPERAD op1)`,
   REWRITE_TAC [OPERAD_MOR] THEN MESON_TAC []);;

let OPERAD_MOR_ID = prove
  (`!op. OPERAD op ==> OPERAD_MOR op op I`,
   REWRITE_TAC [OPERAD_MOR; I_THM; I_O_ID]);;

let OPERAD_MOR_o = prove
  (`!op1 op2 op3 h g.
    OPERAD_MOR op1 op2 h /\
    OPERAD_MOR op2 op3 g ==>
    OPERAD_MOR op1 op3 (g o h)`,
   REWRITE_TAC [OPERAD_MOR] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [o_THM; o_ASSOC]);;

let OPERAD_MOR_IMP = (MATCH_MP EQ_IMP (SPEC_ALL OPERAD_MOR));;

(* ------------------------------------------------------------------------- *)
(*  Modules.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MODULE_DEF = new_definition
  `!(op:(num->A)->A->A) (mop:(num->A)->B->B).
     MODULE op mop <=>
       OPERAD op /\
       (!x. mop (OPERAD_UNIT op) x = x) /\
       (!f g x. mop g (mop f x) = mop (\n. op g (f n)) x)`;;

let SELF_MODULE = prove
  (`!op mop. MODULE op op <=> OPERAD op`,
   REWRITE_TAC [OPERAD; MODULE_DEF] THEN MESON_TAC []);;

let MODULE_MOR = new_definition
  `!op mop1 mop2 h. MODULE_MOR op mop1 mop2 h <=>
    MODULE op mop1 /\
    MODULE op mop2 /\
    (!f x. h (mop1 f x) = mop2 f (h x))`;;

let MODULE_MOR_ID = prove
  (`!op mop. MODULE op mop <=> MODULE_MOR op mop mop I`,
    REWRITE_TAC [MODULE_MOR; I_THM]);;

let MODULE_MOR_o = prove
  (`!op mop1 mop2 h.
      MODULE_MOR op mop1 mop2 h /\ MODULE_MOR op mop2 mop3 g
      ==> MODULE_MOR op mop1 mop3 (g o h)`,
   REWRITE_TAC [MODULE_MOR] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [o_DEF]);;

(* ------------------------------------------------------------------------- *)
(*  Pull-back modules.                                                       *)
(* ------------------------------------------------------------------------- *)

let PBMOP = new_definition
  `!op' op h mop f. PBMOP op' op h mop f = mop (h o f)`;;

let PB_MODULE = prove
  (`!op' op h mop.
      OPERAD_MOR op' op h /\ MODULE op mop
      ==> MODULE op' (PBMOP op' op h mop)`,
   REWRITE_TAC [OPERAD_MOR; MODULE_DEF; PBMOP] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [o_DEF; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(*  Derived Modules.                                                         *)
(* ------------------------------------------------------------------------- *)

let DMOP = new_definition
  `!k op mop f x.
     DMOP k op mop f x =
       mop (\n. if n < k then OPERAD_UNIT op n else
                op (\n. OPERAD_UNIT op (k + n)) (f (n - k))) x`;;

let DMOP_0 = prove
  (`!op i mop. OPERAD op ==> DMOP 0 op mop = mop`,
   REWRITE_TAC [OPERAD] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [FUN_EQ_THM; DMOP; LT; ADD; SUB_0; ETA_AX]);;

let MODULE_DMOP = prove
  (`!(op:(num->A)->A->A) mop k.
      MODULE op mop ==> MODULE op (DMOP k op mop)`,
   ASM_REWRITE_TAC [OPERAD; MODULE_DEF; DMOP] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THENL
   [SUBGOAL_THEN `(\n. if n < k then OPERAD_UNIT op n else
                       OPERAD_UNIT op (k + n - k)) = OPERAD_UNIT op :num->A`
      SUBST1_TAC THEN ASM_REWRITE_TAC [FUN_EQ_THM] THEN
    MESON_TAC [ARITH_RULE `~(x < k) ==> k + x - k = x`];
    AP_THM_TAC  THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [ARITH_RULE `~(k + x' < k) /\ (k + n) - k = n`]]);;

let MODULE_DMOP_MOR = prove
  (`!op mop1 mop2 h.
      MODULE_MOR op mop1 mop2 h
      ==> MODULE_MOR op (DMOP k op mop1) (DMOP k op mop2) h`,
   SIMP_TAC [MODULE_MOR; MODULE_DMOP; DMOP]);;

let MODULE_MOR_INV = prove
  (`!op mop1 mop2 g h.
      MODULE_MOR op mop1 mop2 h /\
      (!x:A. g (h x) = x) /\ (!y:B. h (g y) = y)
      ==> MODULE_MOR op mop2 mop1 g`,
   REWRITE_TAC [MODULE_MOR] THEN MESON_TAC []);;

let MODULE_ISOM = new_definition
  `!op mop1 mop2 h g.
     MODULE_ISOM op mop1 mop2 h g <=>
       MODULE_MOR op mop1 mop2 h /\
       (!x:A. g (h x) = x) /\ (!y:B. h (g y) = y)`;;

let MODULE_ISOM_SYM = prove
  (`!op mop1 mop2 (h:C->B) g.
      MODULE_ISOM op mop1 mop2 h g
      ==> MODULE_ISOM op mop2 mop1 g h`,
   REWRITE_TAC [MODULE_ISOM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MODULE_MOR_INV THEN
   ASM_MESON_TAC []);;

let MODULE_ISOM_UNFOLD = prove
  (`!(op:(num->T)->T->T) mop1 mop2 (h:A->B) g.
     MODULE_ISOM op mop1 mop2 h g <=>
       MODULE op mop1 /\
       MODULE op mop2 /\
       MODULE_MOR op mop1 mop2 h /\
       MODULE_MOR op mop2 mop1 g /\
       (!x:A. g (h x) = x) /\ (!y:B. h (g y) = y)`,
   REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC [MODULE_ISOM]] THEN
   FIRST_ASSUM (ASSUME_TAC o MATCH_MP MODULE_ISOM_SYM) THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MODULE_ISOM]) THEN
   ASM_REWRITE_TAC [] THEN
   RULE_ASSUM_TAC (REWRITE_RULE [MODULE_MOR]) THEN
   ASM_REWRITE_TAC []);;

let EXP_OPERAD = new_definition
  `!op h g.
     EXP_OPERAD op h g <=> MODULE_ISOM op op (DMOP (SUC 0) op op) h g`;;

let EXP_OPERAD_MOR = new_definition
  `!op1 h1 g1 op2 h2 g2 f.
      EXP_OPERAD_MOR op1 h1 g1 op2 h2 g2 f
      <=> EXP_OPERAD op1 h1 g1 /\
          EXP_OPERAD op2 h2 g2 /\
      	  OPERAD_MOR op1 op2 f /\
      	  (!x. h2 (f x) = f (h1 x))`;;
