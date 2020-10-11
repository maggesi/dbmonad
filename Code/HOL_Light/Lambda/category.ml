(* ========================================================================= *)
(* Basic category theory.                                                    *)
(*                                                                           *)
(* Notes:                                                                    *)
(*   - Use diagrammatic order in compositions.                               *)
(*   - Use protoctegory defifinition (homs are not disjoint).                *)
(*   - Identity is abbreviated idt.                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Handy wrapper function around new_specification.                          *)
(* ------------------------------------------------------------------------- *)

let specify th =
  let vars = fst (strip_forall (concl th)) in
  let th = GEN_REWRITE_RULE TRY_CONV [RIGHT_IMP_EXISTS_THM] (SPEC_ALL th) in
  let names = map name_of (fst(strip_exists (concl th))) in
  let th = GEN_REWRITE_RULE DEPTH_CONV [SKOLEM_THM] (GENL vars th) in
  new_specification names th;;

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

(* In the following definition, we use types A, B instead
   of O,A (Objects, Arrows) in order to enforce the right order for the
   type parameters in the type expression `:(O,A)category`.  *)

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

(* ------------------------------------------------------------------------- *)
(* Helper theorem to define a category using the function specify.           *)
(* ------------------------------------------------------------------------- *)

let EXISTS_CATEGORY = prove
 (`IS_CATEGORY (obj,(\(x,y). hom x y),(idt:OO->AA),(\(f,g). comp f g))
   ==> ?C:(OO,AA)category.
         (OBJ C = obj) /\
         (!x y. HOM C (x,y) = hom x y) /\
         (!x. IDT C x = idt x) /\
         (!f g. COMP C (f,g) = comp f g)`,
  REWRITE_TAC[category_TYBIJ] THEN DISCH_TAC THEN
  EXISTS_TAC
    `MK_CATEGORY(obj,(\(x,y). hom x y),(idt:OO->AA),(\(f,g). comp f g))` THEN
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
  MATCH_MP_TAC EXISTS_CATEGORY THEN REWRITE_TAC[IS_CATEGORY; NOT_IN_EMPTY]);;

let DUAL_CATEGORY = (specify o prove)
 (`!C. ?DUAL_CATEGORY.
     OBJ DUAL_CATEGORY = OBJ C /\
     (!x y. HOM DUAL_CATEGORY (x,y) = HOM C (y,x)) /\
     (!x:O. IDT DUAL_CATEGORY x = IDT C x) /\
     (!f g:A. COMP DUAL_CATEGORY (f,g) = COMP C (g,f))`,
  GEN_TAC THEN MATCH_MP_TAC EXISTS_CATEGORY THEN
  SIMP_TAC[IS_CATEGORY; CATEGORY_CLAUSES] THEN MESON_TAC[CATEGORY_CLAUSES]);;

let DISCRETE_CATEGORY = (specify o prove)
 (`!s:O->bool i:O->A. ?DISCRETE_CATEGORY.
     OBJ DISCRETE_CATEGORY = s /\
     (!x y. HOM DISCRETE_CATEGORY (x,y) =
        GSPEC (\a. SETSPEC a (x IN s /\ x = y) (i x))) /\
     (!x. IDT DISCRETE_CATEGORY x = i x) /\
     (!f g. COMP DISCRETE_CATEGORY (f,g) = f)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC EXISTS_CATEGORY THEN
  REWRITE_TAC[IS_CATEGORY] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Functors.                                                                 *)
(* ------------------------------------------------------------------------- *)

let FUNCTOR = new_definition
  `FUNCTOR (C1,C2) =
     {(h0,h1) | (!x:O. x IN OBJ C1 ==> h0 x:O' IN OBJ C2) /\
                (!x y f:A. f IN HOM C1 (x,y)
                           ==> h1 f:A' IN HOM C2 (h0 x,h0 y)) /\
                (!x. x IN OBJ C1 ==> h1 (IDT C1 x) = IDT C2 (h0 x)) /\
                (!x y z f g. f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
                             ==> h1 (COMP C1 (f,g)) = COMP C2 (h1 f, h1 g))}`;;

let IN_FUNCTOR_ALT = prove
 (`!h0:O->O' h1:A->A'.
     (h0,h1) IN FUNCTOR (C1,C2) <=>
     (!x. x IN OBJ C1 ==> h0 x IN OBJ C2) /\
     (!x y f. f IN HOM C1 (x,y) ==> h1 f IN HOM C2 (h0 x,h0 y)) /\
     (!x. x IN OBJ C1 ==> h1 (IDT C1 x) = IDT C2 (h0 x)) /\
     (!x y z f g. f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
                  ==> h1 (COMP C1 (f,g)) = COMP C2 (h1 f, h1 g))`,
  REWRITE_TAC[FUNCTOR; IN_ELIM_THM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`h0:O->O'`;`h1:A->A'`] THEN
  ASM_REWRITE_TAC[]);;

let ONOBJS = new_definition
  `ONOBJS (h0:O->O',h1:A->A') = h0`;;

let ONARRS = new_definition
  `ONARRS (h0:O->O',h1:A->A') = h1`;;

let FUNCTOR_EXTENS = prove
 (`!h1 h2. h1 = h2 <=> ONOBJS h1:O->O' = ONOBJS h2 /\ ONARRS h1:A->A' = ONARRS h2`,
  REWRITE_TAC[FORALL_PAIR_THM; ONOBJS; ONARRS; PAIR_EQ]);;

let IN_FUNCTOR = prove
 (`!h:(O->O')#(A->A').
     h IN FUNCTOR (C1,C2) <=>
     (!x. x IN OBJ C1 ==> ONOBJS h x IN OBJ C2) /\
     (!x y f. f IN HOM C1 (x,y)
              ==> ONARRS h f IN HOM C2 (ONOBJS h x,ONOBJS h y)) /\
     (!x. x IN OBJ C1 ==> ONARRS h (IDT C1 x) = IDT C2 (ONOBJS h x)) /\
     (!x y z f g.
        f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
        ==> ONARRS h (COMP C1 (f,g)) = COMP C2 (ONARRS h f, ONARRS h g))`,
  REWRITE_TAC[FORALL_PAIR_THM; GSYM IN_FUNCTOR_ALT; ONOBJS; ONARRS; ETA_AX]);;

(* Helper theorem for defining functors. *)
let EXISTS_FUNCTOR = prove
 (`!C1 C2 h0:O->O' h1:A->A'.
     (!x. x IN OBJ C1 ==> h0 x IN OBJ C2) /\
     (!x y f. f IN HOM C1 (x,y) ==> h1 f IN HOM C2 (h0 x,h0 y)) /\
     (!x. x IN OBJ C1 ==> h1 (IDT C1 x) = IDT C2 (h0 x)) /\
     (!x y z f g. f IN HOM C1 (x,y) /\ g IN HOM C1 (y,z)
                  ==> h1 (COMP C1 (f,g)) = COMP C2 (h1 f, h1 g))
     ==> ?F. (ONOBJS F = h0) /\
             (ONARRS F = h1) /\
             F IN FUNCTOR (C1,C2)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `(h0:O->O',h1:A->A')` THEN
  ASM_REWRITE_TAC[ONOBJS; ONARRS; IN_FUNCTOR_ALT]);;

let IDT_FUNCTOR = (specify o prove)
 (`?IDT_FUNCTOR.
     (ONOBJS IDT_FUNCTOR = I:O->O) /\
     (ONARRS IDT_FUNCTOR = I:A->A) /\
     (!C. IDT_FUNCTOR IN FUNCTOR (C,C))`,
  EXISTS_TAC `(I:O->O,I:A->A)` THEN
  REWRITE_TAC[ONOBJS; ONARRS; IN_FUNCTOR; I_THM]);;

let COMP_FUNCTOR = (specify o prove)
 (`!h1 h2. ?COMP_FUNCTOR.
     ONOBJS COMP_FUNCTOR = ONOBJS h2 o ONOBJS h1 /\
     ONARRS COMP_FUNCTOR = ONARRS h2 o ONARRS h1 /\
     (!C1:(O1,A1)category C2:(O2,A2)category C3:(O3,A3)category.
        h1 IN FUNCTOR (C1,C2) /\ h2 IN FUNCTOR (C2,C3)
        ==> COMP_FUNCTOR IN FUNCTOR (C1,C3))`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC
    `(ONOBJS (h2:(O2->O3)#(A2->A3)) o ONOBJS (h1:(O1->O2)#(A1->A2))),
     (ONARRS (h2:(O2->O3)#(A2->A3)) o ONARRS (h1:(O1->O2)#(A1->A2)))` THEN
  REWRITE_TAC[IN_FUNCTOR; o_THM; ONOBJS; ONARRS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

let COMP_IDT_FUNCTOR = prove
 (`(!h. COMP_FUNCTOR IDT_FUNCTOR h = h:(O->O')#(A->A')) /\
   (!h. COMP_FUNCTOR h IDT_FUNCTOR = h:(O->O')#(A->A'))`,
  REWRITE_TAC[FUNCTOR_EXTENS; COMP_FUNCTOR; IDT_FUNCTOR; I_O_ID]);;

let COMP_FUNCTOR_ASSOC = prove
 (`!f g h. COMP_FUNCTOR f (COMP_FUNCTOR g h) =
           COMP_FUNCTOR (COMP_FUNCTOR f g) h`,
  REWRITE_TAC[FUNCTOR_EXTENS; COMP_FUNCTOR; o_ASSOC]);;

let CATEGORY = (specify o prove)
 (`?CATEGORY.
     OBJ CATEGORY = (:(O,A)category) /\
     (!C1 C2. HOM CATEGORY (C1,C2) = FUNCTOR (C1,C2)) /\
     (!C. IDT CATEGORY C = IDT_FUNCTOR) /\
     (!h1 h2. COMP CATEGORY (h1,h2) = COMP_FUNCTOR h1 h2)`,
  MATCH_MP_TAC EXISTS_CATEGORY THEN
  REWRITE_TAC[IS_CATEGORY; IN_UNIV; IDT_FUNCTOR;
              COMP_IDT_FUNCTOR; COMP_FUNCTOR_ASSOC] THEN
  MESON_TAC[COMP_FUNCTOR]);;
