(* ========================================================================= *)
(* Basic category theory.                                                    *)
(*                                                                           *)
(* Notes:                                                                    *)
(*   - We use diagrammatic order in compositions.                            *)
(*   - We use "protocategories" (i.e., homs spaces are not disjoint).        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Notations:                                                                *)
(*                                                                           *)
(* `x IN OBJ C`        `x` is an objects of the category`C`                  *)
(* `f IN HOM C (x,y)`  `f` is an arrows from `x` to `y` in `C`               *)
(* `IDT C x`           identity of object `x` in `C`                         *)
(* `COMP C (f,g)`      composition of arrows `f` and `g` in `C`              *)
(*                     (diagrammatic order!)                                 *)
(* ------------------------------------------------------------------------- *)

needs "misc.ml";;

(* ------------------------------------------------------------------------- *)
(* We introduce a new datatype for categories.                               *)
(* ------------------------------------------------------------------------- *)

let IS_CATEGORY = new_definition
  `IS_CATEGORY (ob,hom,idt,comp) <=>
   (!x y:O f:A. f IN hom(x,y) ==> x IN ob /\ y IN ob) /\
   (!x. x IN ob ==> idt x IN hom(x,x)) /\
   (!x y z f g. f IN hom(x,y) /\ g IN hom(y,z) ==> comp(f,g) IN hom(x,z)) /\
   (!x y f. f IN hom(x,y) ==> comp(idt x,f) = f /\ comp(f,idt y) = f) /\
   (!w x y z f g h. f IN hom(w,x) /\ g IN hom(x,y) /\ h IN hom(y,z)
                    ==> comp(f,comp(g,h)) = comp(comp(f,g),h))`;;

(* ------------------------------------------------------------------------- *)
(* In the following definition, we use types A, B instead                    *)
(* of O,A (Objects, Arrows) in order to enforce the right order for the      *)
(* type parameters in the type expression `:(O,A)category`.                  *)
(* ------------------------------------------------------------------------- *)

let category_TYBIJ =
  (new_type_definition "category" ("MK_CATEGORY","DEST_CATEGORY") o prove)
  (`?C:(A->bool)#(A#A->B->bool)#(A->B)#(B#B->B). IS_CATEGORY C`,
   REWRITE_TAC[EXISTS_PAIR_THM] THEN MAP_EVERY EXISTS_TAC
     [`{}:A->bool`;
      `\(x:A,y:A). {}:B->bool`;
      `\x:A. ARB:B`;
      `\(f:B,g:B). ARB:B`] THEN
   REWRITE_TAC[IS_CATEGORY; NOT_IN_EMPTY]);;

let OBJ = new_definition
  `OBJ (C:(O,A)category) = FST (DEST_CATEGORY C)`;;

let HOM = new_definition
  `HOM (C:(O,A)category) = FST (SND (DEST_CATEGORY C))`;;

let IDT = new_definition
  `IDT (C:(O,A)category) = FST (SND (SND (DEST_CATEGORY C)))`;;

let COMP = new_definition
  `COMP (C:(O,A)category) = SND (SND (SND (DEST_CATEGORY C)))`;;

let CATEGORY_CLAUSES = prove
 (`(!x y f. f IN HOM (C:(O,A)category) (x,y) ==> x IN OBJ C /\ y IN OBJ C) /\
   (!x. x IN OBJ C ==> IDT C x IN HOM C (x,x)) /\
   (!x y z f g.
      f IN HOM C (x,y) /\ g IN HOM C (y,z) ==> COMP C (f,g) IN HOM C (x,z)) /\
   (!x y f.
      f IN HOM C (x,y) ==> COMP C (IDT C x,f) = f /\ COMP C (f,IDT C y) = f) /\
   (!w x y z f g h.
      f IN HOM C (w,x) /\ g IN HOM C (x,y) /\ h IN HOM C (y,z)
      ==> COMP C (f, COMP C (g,h)) = COMP C (COMP C (f,g),h))`,
   SUBGOAL_THEN `IS_CATEGORY (OBJ C, HOM C, IDT C:O->A, COMP C)` MP_TAC THENL
   [C SUBGOAL_THEN SUBST1_TAC
       `(OBJ C, HOM C, IDT C:O->A, COMP C) = DEST_CATEGORY C` THENL
    [REWRITE_TAC[OBJ; HOM; IDT; COMP]; MESON_TAC[category_TYBIJ]];
    REWRITE_TAC[IS_CATEGORY]]);;

let CATEGORY_HOM = prove
 (`!x y f. f IN HOM (C:(O,A)category) (x,y) ==> x IN OBJ C /\ y IN OBJ C`,
  REWRITE_TAC[CATEGORY_CLAUSES]);;

let CATEGORY_IDT = prove
 (`!x. x IN OBJ C ==> IDT C x IN HOM C (x,x)`,
  REWRITE_TAC[CATEGORY_CLAUSES]);;

let CATEGORY_COMP = prove
 (`!x y z f g. f IN HOM C (x,y) /\ g IN HOM C (y,z)
               ==> COMP C (f,g) IN HOM C (x,z)`,
  REWRITE_TAC[CATEGORY_CLAUSES]);;

let CATEGORY_LID = prove
 (`!x y f. f IN HOM C (x,y) ==> COMP C (IDT C x,f) = f`,
  MESON_TAC[CATEGORY_CLAUSES]);;

let CATEGORY_RID = prove
 (`!x y f. f IN HOM C (x,y) ==> COMP C (f,IDT C y) = f`,
  MESON_TAC[CATEGORY_CLAUSES]);;

let CATEGORY_ASSOC = prove
 (`!w x y z f g h.
     f IN HOM C (w,x) /\ g IN HOM C (x,y) /\ h IN HOM C (y,z)
     ==> COMP C (f, COMP C (g,h)) = COMP C (COMP C (f,g),h)`,
  REWRITE_TAC[CATEGORY_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Helper theorem to define a category using the function specify.           *)
(* ------------------------------------------------------------------------- *)

let EXISTS_CATEGORY = prove
 (`!obj hom idt comp.
   (!x y f. f IN hom x y ==> x IN obj /\ y IN obj) /\
   (!x. x IN obj ==> idt x IN hom x x) /\
   (!x y z f g. f IN hom x y /\ g IN hom y z ==> comp f g IN hom x z) /\
   (!x y f. f IN hom x y ==> comp (idt x) f = f /\ comp f (idt y) = f) /\
   (!w x y z f g h. f IN hom w x /\ g IN hom x y /\ h IN hom y z
                    ==> comp f (comp g h) = comp (comp f g) h)
   ==> ?C:(O,A)category.
         (OBJ C = obj) /\
         (!x y. HOM C (x,y) = hom x y) /\
         (!x. IDT C x = idt x) /\
         (!f g. COMP C (f,g) = comp f g)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
    `MK_CATEGORY(obj,(\(x,y). hom x y),(idt:O->A),(\(f,g). comp f g))` THEN
  CLAIM_TAC "cat"
    `IS_CATEGORY (obj,(\(x,y). hom x y),idt:O->A,(\(f,g). comp f g))` THENL
  [ASM_REWRITE_TAC[IS_CATEGORY];
   HYP_TAC "cat" (REWRITE_RULE[category_TYBIJ])] THEN
  ASM_REWRITE_TAC[OBJ; HOM; IDT; COMP]);;

(* ------------------------------------------------------------------------- *)
(* Basic categorical constructions.                                          *)
(* ------------------------------------------------------------------------- *)

let EMPTY_CATEGORY = (specify o prove)
 (`?EMPTY_CATEGORY.
     OBJ EMPTY_CATEGORY = {} /\
     (!x y. HOM EMPTY_CATEGORY (x,y) = {}) /\
     (!x. IDT EMPTY_CATEGORY (x:O) = ARB:A) /\
     (!f g. COMP EMPTY_CATEGORY (f,g) = f)`,
  MATCH_MP_TAC EXISTS_CATEGORY THEN REWRITE_TAC[NOT_IN_EMPTY]);;

let DUAL_CATEGORY = (specify o prove)
 (`!C. ?DUAL_CATEGORY.
     OBJ DUAL_CATEGORY = OBJ C /\
     (!x y. HOM DUAL_CATEGORY (x,y) = HOM C (y,x)) /\
     (!x:O. IDT DUAL_CATEGORY x = IDT C x) /\
     (!f g:A. COMP DUAL_CATEGORY (f,g) = COMP C (g,f))`,
  GEN_TAC THEN MATCH_MP_TAC EXISTS_CATEGORY THEN
  SIMP_TAC[CATEGORY_CLAUSES] THEN MESON_TAC[CATEGORY_CLAUSES]);;

let DISCRETE_CATEGORY = (specify o prove)
 (`!s:O->bool i:O->A. ?DISCRETE_CATEGORY.
     OBJ DISCRETE_CATEGORY = s /\
     (!x y. HOM DISCRETE_CATEGORY (x,y) =
        GSPEC (\a. SETSPEC a (x IN s /\ x = y) (i x))) /\
     (!x. IDT DISCRETE_CATEGORY x = i x) /\
     (!f g. COMP DISCRETE_CATEGORY (f,g) = f)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC EXISTS_CATEGORY THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Functors.                                                                 *)
(* ------------------------------------------------------------------------- *)

let functor_INDUCT,functor_RECUR = define_type
  "functor = MK_FUNCTOR ((A,C)category) ((B,D)category) (A->B) (C->D)";;

let FUNCTOR_SRC = new_recursive_definition functor_RECUR
  `FUNCTOR_SRC (MK_FUNCTOR C1 C2 (h0:O->O') (h1:A->A')) = C1`;;

let FUNCTOR_TRG = new_recursive_definition functor_RECUR
  `FUNCTOR_TRG (MK_FUNCTOR C1 C2 (h0:O->O') (h1:A->A')) = C2`;;

let ONOBJS = new_recursive_definition functor_RECUR
  `ONOBJS (MK_FUNCTOR C1 C2 (h0:O->O') (h1:A->A')) = h0`;;

let ONARRS = new_recursive_definition functor_RECUR
  `ONARRS (MK_FUNCTOR C1 C2 (h0:O->O') (h1:A->A')) = h1`;;

let FUNCTOR_EXTENS = prove
 (`!h k. h = k <=>
           FUNCTOR_SRC h = FUNCTOR_SRC k /\
           FUNCTOR_TRG h = FUNCTOR_TRG k /\
           ONOBJS h:O->O' = ONOBJS k /\
           ONARRS h:A->A' = ONARRS k`,
  MATCH_MP_TAC functor_INDUCT THEN INTRO_TAC "![C1] [C2] [h0] [h1]" THEN
  MATCH_MP_TAC functor_INDUCT THEN INTRO_TAC "![D1] [D2] [k0] [k1]" THEN
  EQ_TAC THENL
  [DISCH_TAC THEN ASM_REWRITE_TAC[];
   SIMP_TAC[FUNCTOR_SRC; FUNCTOR_TRG; ONOBJS; ONARRS]]);;

let FUNCTOR = new_definition
  `FUNCTOR (C1,C2) =
   {h | FUNCTOR_SRC h = C1 /\
        FUNCTOR_TRG h = C2 /\
        (!x:O. x IN OBJ C1 ==> ONOBJS h x:O' IN OBJ C2) /\
        (!x y f:A. f IN HOM C1 (x,y)
                   ==> ONARRS h f:A' IN HOM C2 (ONOBJS h x,ONOBJS h y)) /\
        (!x. x IN OBJ C1 ==> ONARRS h (IDT C1 x) = IDT C2 (ONOBJS h x)) /\
        (!x y z f g.
           f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
           ==> ONARRS h (COMP C1 (f,g)) = COMP C2 (ONARRS h f, ONARRS h g))}`;;

let IN_FUNCTOR = prove
 (`!h:(O,0',A,A')functor.
     h IN FUNCTOR (C1,C2) <=>
     (!x. x IN OBJ C1 ==> ONOBJS h x IN OBJ C2) /\
     (!x y f. f IN HOM C1 (x,y)
              ==> ONARRS h f IN HOM C2 (ONOBJS h x,ONOBJS h y)) /\
     (!x. x IN OBJ C1 ==> ONARRS h (IDT C1 x) = IDT C2 (ONOBJS h x)) /\
     (!x y z f g.
        f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
        ==> ONARRS h (COMP C1 (f,g)) = COMP C2 (ONARRS h f, ONARRS h g))`,
  MATCH_MP_TAC functor_INDUCT THEN REWRITE_TAC[FUNCTOR; IN_ELIM_THM]);;

let FUNCTOR_CLAUSES = prove
 (`!h:(O,0',A,A')functor.
     h IN FUNCTOR (C1,C2)
     ==> (!x. x IN OBJ C1 ==> ONOBJS h x IN OBJ C2) /\
         (!x y f. f IN HOM C1 (x,y)
                  ==> ONARRS h f IN HOM C2 (ONOBJS h x,ONOBJS h y)) /\
         (!x. x IN OBJ C1 ==> ONARRS h (IDT C1 x) = IDT C2 (ONOBJS h x)) /\
         (!x y z f g.
            f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
            ==> ONARRS h (COMP C1 (f,g)) = COMP C2 (ONARRS h f, ONARRS h g))`,
  REWRITE_TAC[IN_FUNCTOR]);;

let FUNCTOR_ONOBJS = prove
 (`!h:(O,0',A,A')functor x.
     h IN FUNCTOR (C1,C2) /\ x IN OBJ C1 ==> ONOBJS h x IN OBJ C2`,
  REWRITE_TAC[IN_FUNCTOR] THEN MESON_TAC[]);;

let FUNCTOR_ONARRS = prove
 (`!h:(O,0',A,A')functor x y f.
     h IN FUNCTOR (C1,C2) /\ f IN HOM C1 (x,y)
     ==> ONARRS h f IN HOM C2 (ONOBJS h x,ONOBJS h y)`,
  REWRITE_TAC[IN_FUNCTOR] THEN MESON_TAC[]);;

let FUNCTOR_IDT = prove
 (`!h:(O,0',A,A')functor x.
     h IN FUNCTOR (C1,C2) /\ x IN OBJ C1
     ==> ONARRS h (IDT C1 x) = IDT C2 (ONOBJS h x)`,
  REWRITE_TAC[IN_FUNCTOR] THEN MESON_TAC[]);;

let FUNCTOR_COMP = prove
 (`!h:(O,0',A,A')functor x y z f g.
     h IN FUNCTOR (C1,C2) /\ f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
     ==> ONARRS h (COMP C1 (f,g)) = COMP C2 (ONARRS h f, ONARRS h g)`,
  REWRITE_TAC[IN_FUNCTOR] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helper theorem for defining functors.                                     *)
(* ------------------------------------------------------------------------- *)

let EXISTS_FUNCTOR = prove
 (`!C1 C2 h0:O->O' h1:A->A'.
     (!x. x IN OBJ C1 ==> h0 x IN OBJ C2) /\
     (!x y f. f IN HOM C1 (x,y) ==> h1 f IN HOM C2 (h0 x,h0 y)) /\
     (!x. x IN OBJ C1 ==> h1 (IDT C1 x) = IDT C2 (h0 x)) /\
     (!x y z f g. f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
                  ==> h1 (COMP C1 (f,g)) = COMP C2 (h1 f, h1 g))
     ==> ?h:(O,O',A,A')functor. (ONOBJS h = h0) /\
                                (ONARRS h = h1) /\
                                h IN FUNCTOR (C1,C2)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `MK_FUNCTOR h0 h1:(O,O',A,A')functor` THEN
  ASM_REWRITE_TAC[ONOBJS; ONARRS; IN_FUNCTOR]);;

let IDT_FUNCTOR = (specify o prove)
 (`?IDT_FUNCTOR.
     (ONOBJS IDT_FUNCTOR = I:O->O) /\
     (ONARRS IDT_FUNCTOR = I:A->A) /\
     (!C. IDT_FUNCTOR IN FUNCTOR (C,C))`,
  EXISTS_TAC `MK_FUNCTOR I I:(O,O,A,A)functor` THEN
  REWRITE_TAC[ONOBJS; ONARRS; IN_FUNCTOR; I_THM]);;

let COMP_FUNCTOR = (specify o prove)
 (`?COMP_FUNCTOR. !h1 h2.
     ONOBJS (COMP_FUNCTOR (h1,h2)) = ONOBJS h2 o ONOBJS h1 /\
     ONARRS (COMP_FUNCTOR (h1,h2)) = ONARRS h2 o ONARRS h1 /\
     (!C1:(O1,A1)category C2:(O2,A2)category C3:(O3,A3)category.
        h1 IN FUNCTOR (C1,C2) /\ h2 IN FUNCTOR (C2,C3)
        ==> COMP_FUNCTOR (h1,h2) IN FUNCTOR (C1,C3))`,
  EXISTS_TAC
    `\(h1:(O1,O2,A1,A2)functor,h2:(O2,O3,A2,A3)functor).
       MK_FUNCTOR (ONOBJS h2 o ONOBJS h1) (ONARRS h2 o ONARRS h1)` THEN
  REWRITE_TAC[IN_FUNCTOR; o_THM; ONOBJS; ONARRS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

let COMP_IDT_FUNCTOR = prove
 (`(!h:(O,O',A,A')functor. COMP_FUNCTOR (IDT_FUNCTOR,h) = h) /\
   (!h:(O,O',A,A')functor. COMP_FUNCTOR (h,IDT_FUNCTOR) = h)`,
  REWRITE_TAC[FUNCTOR_EXTENS; COMP_FUNCTOR; IDT_FUNCTOR; I_O_ID]);;

let COMP_FUNCTOR_ASSOC = prove
 (`!f g:(O2,O3,A2,A3)functor h.
     COMP_FUNCTOR (f,COMP_FUNCTOR (g,h)):(O1,O4,A1,A4)functor =
     COMP_FUNCTOR (COMP_FUNCTOR (f,g),h)`,
  REWRITE_TAC[FUNCTOR_EXTENS; COMP_FUNCTOR; o_ASSOC]);;

let CATEGORY = (specify o prove)
 (`?CATEGORY.
     OBJ CATEGORY = (:(O,A)category) /\
     (!C1 C2. HOM CATEGORY (C1,C2) = FUNCTOR (C1,C2)) /\
     (!C. IDT CATEGORY C = IDT_FUNCTOR) /\
     (!h1 h2. COMP CATEGORY (h1,h2) = COMP_FUNCTOR (h1,h2))`,
  MATCH_MP_TAC EXISTS_CATEGORY THEN
  REWRITE_TAC[IS_CATEGORY; IN_UNIV; IDT_FUNCTOR;
              COMP_IDT_FUNCTOR; COMP_FUNCTOR_ASSOC] THEN
  MESON_TAC[COMP_FUNCTOR]);;

(* ------------------------------------------------------------------------- *)
(* Natural transformations.                                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*   h x ---> k x                                                            *)
(*    |        |                                                             *)
(*    V        V                                                             *)
(*   h y ---> k y                                                            *)
(* ------------------------------------------------------------------------- *)

let NATTRANS = new_definition
  `NATTRANS (C1:(O,A)category,C2:(O',A')category) (h,k) =
   {n | h IN FUNCTOR (C1,C2) /\
        k IN FUNCTOR (C1,C2) /\
        (!x. x IN OBJ C1 ==> n x IN HOM C2 (ONOBJS h x, ONOBJS k x)) /\
        (!x y f. f IN HOM C1 (x,y)
                 ==> COMP C2 (n x, ONARRS k f) = COMP C2 (ONARRS h f, n y))}`;;

let IN_NATTRANS = prove
 (`!C1:(O,A)category C2:(O',A')category h k n.
     n IN NATTRANS (C1,C2) (h,k) <=>
     h IN FUNCTOR (C1,C2) /\
     k IN FUNCTOR (C1,C2) /\
     (!x. x IN OBJ C1 ==> n x IN HOM C2 (ONOBJS h x, ONOBJS k x)) /\
     (!x y f. f IN HOM C1 (x,y)
              ==> COMP C2 (n x, ONARRS k f) = COMP C2 (ONARRS h f, n y))`,
  REWRITE_TAC[NATTRANS; IN_ELIM_THM]);;

let IDT_NATTRANS = new_definition
  `IDT_NATTRANS C2 (h:(O,O',A,A')functor) x = IDT C2 (ONOBJS h x):A'`;;

let IDT_NATTRANS_IN_NATTRANS = prove
 (`!C1:(O,A)category C2:(O',A')category h.
     h IN FUNCTOR (C1,C2) ==> IDT_NATTRANS C2 h IN NATTRANS (C1,C2) (h,h)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_NATTRANS; IDT_NATTRANS] THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE[IN_FUNCTOR]) THEN CONJ_TAC THENL
  [ASM_MESON_TAC[CATEGORY_IDT];
   ASM_MESON_TAC[CATEGORY_LID; CATEGORY_RID]]);;

let COMP_NATTRANS = new_definition
 `COMP_NATTRANS (C2:(O',A')category) (n1,n2) (x:O) = COMP C2 (n1 x,n2 x)`;;

let COMP_NATTRANS_IN_NATTRANS = prove
 (`!C1:(O,A)category C2:(O',A')category h k j n1 n2.
     n1 IN NATTRANS (C1,C2) (h,k) /\
     n2 IN NATTRANS (C1,C2) (k,j)
     ==> COMP_NATTRANS C2 (n1,n2) IN NATTRANS (C1,C2) (h,j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NATTRANS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMP_NATTRANS] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[CATEGORY_COMP]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
    `COMP (C2:(O',A')category)
       (n1 (x:O),COMP C2 (n2 x,ONARRS (j:(O,O',A,A')functor) f))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC CATEGORY_ASSOC THEN
   ASM_MESON_TAC[FUNCTOR_ONARRS; CATEGORY_HOM];
   ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
    `COMP (C2:(O',A')category)
      (n1 (x:O),COMP C2 (ONARRS (k:(O,O',A,A')functor) f,n2 (y:O)))` THEN
  CONJ_TAC THEN ASM_SIMP_TAC[] THEN
  TRANS_TAC EQ_TRANS
    `COMP (C2:(O',A')category)
       (COMP C2 (n1 (x:O),ONARRS (k:(O,O',A,A')functor) f),n2 (y:O))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CATEGORY_ASSOC THEN
   ASM_MESON_TAC[FUNCTOR_ONARRS; CATEGORY_HOM];
   ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
    `COMP (C2:(O',A')category)
       (COMP C2 (ONARRS (h:(O,O',A,A')functor) f,n1 (y:O)),n2 (y:O))` THEN
  CONJ_TAC THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC CATEGORY_ASSOC THEN
  ASM_MESON_TAC[FUNCTOR_ONARRS; CATEGORY_HOM]);;

(* ------------------------------------------------------------------------- *)
(* Monads.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*
let POINTED_FUNCTOR = new_definition
  `POINTED_FUNCTOR C (h,n) <=>
   h IN FUNCTOR (C,C) /\
   n IN NATTRANS (C,C) (IDT_FUNCTOR,h)`;;

let MONAD = new_definition
  `MONAD (C:(O,A)category) (M,join,unit) <=>
   M IN FUNCTOR (C,C) /\
   join IN NATTRANS (C,C) (COMP_FUNCTOR (M,M), M) /\
   unit IN NATTRANS (C,C) (IDT_FUNCTOR, M) /\
   `;;
 *)
