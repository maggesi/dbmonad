(* ------------------------------------------------------------------------- *)
(* Mischellanea.                                                             *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_1_CASES = prove
 (`!s. s HAS_SIZE 1 <=> ?a:A. s = {a}`,
  REWRITE_TAC[ONE; HAS_SIZE_CLAUSES; UNWIND_THM2; NOT_IN_EMPTY]);;

let HAS_SIZE_1_INDISCERNIBLE = prove
 (`(:A) HAS_SIZE 1 <=> (!x y:A. x = y)`,
  REWRITE_TAC[ONE; HAS_SIZE_CLAUSES; UNWIND_THM2; NOT_IN_EMPTY] THEN
  REWRITE_TAC[EXTENSION; IN_SING; IN_UNIV] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Definition of De Brujin monad structure.                                  *)
(* ------------------------------------------------------------------------- *)

let IS_DBMONAD = new_definition
  `IS_DBMONAD (bind:(num->A)->A->A,unit:num->A) <=>
   (!f g x. bind f (bind g x) = bind (bind f o g) x) /\
   (!x. bind unit x = x) /\
   (!f i. bind f (unit i) = f i)`;;

(* ------------------------------------------------------------------------- *)
(* Given an injective map `unit:num ->A`, there is a trivial "bind" operator *)
(* so that `(bind,unit)` is a DB-monad on `:A`.   The idea is to consider    *)
(* every term outside of the image of `unit` as "constants" (i.e., terms     *)
(* where the `bind` acts trivially).                                         *)
(* This is implemented by the following operator `CONSTANT_DBBIND`.          *)
(* ------------------------------------------------------------------------- *)

let CONSTANT_DBBIND = new_definition
  `CONSTANT_DBBIND (unit:num->A) (f:num->A) (x:A) =
   if x IN IMAGE unit (:num) then f (@i. x = unit i) else x`;;

let CONSTANT_DBBIND_CLAUSES = prove
 (`(!unit f i. (!i j. unit i = unit j ==> i = j)
               ==> CONSTANT_DBBIND unit f (unit i) = f i:A) /\
   (!unit f x. ~(x:A IN IMAGE unit (:num))
              ==> CONSTANT_DBBIND unit f x = x)`,
  SIMP_TAC[CONSTANT_DBBIND; FUN_IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

let IS_DBMONAD_CONSTANT_DBBIND = prove
 (`!unit:num->A. (!i j. unit i = unit j ==> i = j)
                 ==> IS_DBMONAD (CONSTANT_DBBIND unit,unit)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IS_DBMONAD] THEN
  SUBGOAL_THEN
    `!P. (!x:A. P x) <=>
         (!i:num. P (unit i)) /\ (!x. ~(x IN IMAGE unit (:num)) ==> P x)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
  [GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; STRIP_TAC THEN GEN_TAC] THEN
   ASM_CASES_TAC `x:A IN IMAGE unit (:num)` THENL
   [POP_ASSUM MP_TAC; ASM_MESON_TAC[]] THEN
   REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
   ASM_SIMP_TAC[CONSTANT_DBBIND_CLAUSES] THEN
   POP_ASSUM (fun th ->
     SIMP_TAC[o_THM; MATCH_MP (CONJUNCT1 CONSTANT_DBBIND_CLAUSES) th])]);;

(* ------------------------------------------------------------------------- *)
(* A singleton type has a trivial structure of DB-monad.                     *)
(* ------------------------------------------------------------------------- *)

let IS_DBMONAD_SING = prove
 (`(:A) HAS_SIZE 1 
   ==> (!m:((num->A)->A->A)#(num->A). IS_DBMONAD m) /\
       (?!m:((num->A)->A->A)#(num->A). IS_DBMONAD m)`,
  REWRITE_TAC[HAS_SIZE_1_INDISCERNIBLE] THEN DISCH_TAC THEN
  MATCH_MP_TAC (MESON[] `P /\ (P ==> Q) ==> P /\ Q`) THEN
  CONJ_TAC THENL
  [REWRITE_TAC[FORALL_PAIR_THM; IS_DBMONAD] THEN
   ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM];
   ALL_TAC] THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th; EXISTS_UNIQUE_THM]) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The unit of a DB-monad over a type with two distincts inhabitants is      *)
(* injective.                                                                *)
(* ------------------------------------------------------------------------- *)

let DBMONAD_UNIT_INJ = prove
 (`(?a b:A. ~(a = b))
   ==> !bind unit:num->A.
         IS_DBMONAD (bind,unit) ==> (!i j. unit i = unit j ==> i = j)`,
  REWRITE_TAC[IS_DBMONAD] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o
    AP_TERM `bind (\k:num. if k = i then a else b:A):A->A`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A type `:A` allows a DB-monad structure if and only if is infinite or a   *)
(* singleton.                                                                *)
(* ------------------------------------------------------------------------- *)

let EXISTS_DBMONAD = prove
 (`(?m:((num->A)->A->A)#(num->A). IS_DBMONAD m) <=>
   INFINITE (:A) \/ (:A) HAS_SIZE 1`,
  ASM_CASES_TAC `(:A) HAS_SIZE 1` THEN ASM_REWRITE_TAC[] THENL
  [ASM_MESON_TAC[IS_DBMONAD_SING]; ALL_TAC] THEN
  ASM_CASES_TAC `INFINITE (:A)` THEN ASM_REWRITE_TAC[] THENL
  [POP_ASSUM MP_TAC THEN REWRITE_TAC[INFINITE_ENUMERATE_SUBSET; IN_UNIV] THEN
   INTRO_TAC "@unit. inj" THEN
   EXISTS_TAC `CONSTANT_DBBIND unit,unit:num->A` THEN
   ASM_MESON_TAC[IS_DBMONAD_CONSTANT_DBBIND];
  REWRITE_TAC[EXISTS_PAIR_THM] THEN INTRO_TAC "@DBBIND unit. +"] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[CONTRAPOS_THM; INFINITE_ENUMERATE_SUBSET; IN_UNIV] THEN
  SUBGOAL_THEN `?x y:A. ~(x = y)`
    (fun th -> MESON_TAC[th; DBMONAD_UNIT_INJ]) THEN
  MP_TAC (ASSUME `~((:A) HAS_SIZE 1)`) THEN
  MP_TAC (MESON [UNIV_NOT_EMPTY] `~((:A)={})`) THEN
  STRUCT_CASES_TAC (SPEC `(:A)` SET_CASES) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; HAS_SIZE_1_CASES] THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* We now define a type for DB-monads.  Because of the above theorem,        *)
(* we cannot define a type in bijection with IS_DBMONAD.  We hack the        *)
(* definition of DB-monad to obtain the best approximation.                  *)
(* We thus give the following notion of semi-DB-monad.                       *)
(* ------------------------------------------------------------------------- *)

let IS_SEMI_DBMONAD = new_definition
  `IS_SEMI_DBMONAD (bind:(num->A)->A->A,unit:num->A) <=>
   (!f g x. bind f (bind g x) = bind (bind f o g) x) /\
   (!x. bind unit x = x) /\
   (!f i. bind f (unit i) = if FINITE (:A) then ARB else f i)`;;

(* ------------------------------------------------------------------------- *)
(* Semi-DB-monad are monads, whenever the associated type allows it          *)
(* (see theorem EXISTS_DBMONAD).                                             *)
(* ------------------------------------------------------------------------- *)

let IS_DBMONAD_IMP_IS_SEMI_DBMONAD = prove
 (`(INFINITE (:A) \/ (:A) HAS_SIZE 1)
   ==> !m:((num->A)->A->A)#(num->A). IS_SEMI_DBMONAD m = IS_DBMONAD m`,
  REWRITE_TAC[FORALL_PAIR_THM; IS_SEMI_DBMONAD; IS_DBMONAD] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[MESON [INFINITE] `FINITE (:A) <=> ~INFINITE (:A)`] THEN
  ASM_MESON_TAC[HAS_SIZE_1_INDISCERNIBLE]);;

(* ------------------------------------------------------------------------- *)
(* Every type allows a semi-DB-monad.                                        *)
(* ------------------------------------------------------------------------- *)

let EXISTS_SEMI_DBMONAD = prove
 (`?m:((num->A)->A->A)#(num->A). IS_SEMI_DBMONAD m`,
  ASM_CASES_TAC `FINITE (:A)` THENL
  [ASM_REWRITE_TAC[EXISTS_PAIR_THM; IS_SEMI_DBMONAD] THEN
   MAP_EVERY EXISTS_TAC [`\f:(num->A) x:A. x`; `\i:num. ARB:A`] THEN
   REWRITE_TAC[];
   ASM_MESON_TAC[INFINITE; IS_DBMONAD_IMP_IS_SEMI_DBMONAD; EXISTS_DBMONAD]]);;

(* ------------------------------------------------------------------------- *)
(* A data type for DB-monads.                                                *)
(* We define a datatype for semi-DB-monad, this will be the "right type"     *)
(* when `:A` is infinite (or a singleton).                                   *)
(* ------------------------------------------------------------------------- *)

let dbmonad_tybij =
  new_type_definition "dbmonad" ("MK_DBMONAD","DEST_DBMONAD")
    EXISTS_SEMI_DBMONAD;;

let MK_DEST_DBMONAD = prove
 (`!m:A dbmonad. MK_DBMONAD (DEST_DBMONAD m) = m`,
  REWRITE_TAC[dbmonad_tybij]);;

let DEST_MK_DBMONAD = prove
 (`!m. IS_SEMI_DBMONAD m ==> DEST_DBMONAD (MK_DBMONAD m:A dbmonad) = m`,
  REWRITE_TAC[GSYM dbmonad_tybij] THEN MESON_TAC[]);;

let DBBIND = new_definition
  `DBBIND (m:A dbmonad) = FST (DEST_DBMONAD m)`;;

let DBBIND_MK_DBMONAD = prove
 (`!bind:(num->A)->A->A unit:num->A.
     IS_SEMI_DBMONAD (bind,unit) ==> DBBIND (MK_DBMONAD (bind,unit)) = bind`,
  SIMP_TAC[DBBIND; DEST_MK_DBMONAD]);;

let DBUNIT = new_definition
  `DBUNIT (m:A dbmonad) = SND (DEST_DBMONAD m)`;;

let DBUNIT_MK_DBMONAD = prove
 (`!bind:(num->A)->A->A unit:num->A.
     IS_SEMI_DBMONAD (bind,unit) ==> DBUNIT (MK_DBMONAD (bind,unit)) = unit`,
  SIMP_TAC[DBUNIT; DEST_MK_DBMONAD]);;

let dbmonad_CASES_GEN = prove
 (`!m:A dbmonad. ?bind unit.
     m = MK_DBMONAD (bind,unit) /\
     (!f g x. bind f (bind g x) = bind (bind f o g) x) /\
     (!x. bind unit x = x) /\
     (!f i. bind f (unit i) = (if FINITE (:A) then ARB else f i))`,
  let th =
    `!m:A dbmonad. ?w. m = MK_DBMONAD w /\ IS_SEMI_DBMONAD w`
    |> METIS [dbmonad_tybij]
    |> REWRITE_RULE[EXISTS_PAIR_THM; IS_SEMI_DBMONAD]
    |> SPEC `m:A dbmonad` in
  GEN_TAC THEN STRIP_ASSUME_TAC th THEN ASM_MESON_TAC[]);;

let FORALL_DBMONAD_THM = prove
 (`!P. (!m:A dbmonad. P (DBBIND m) (DBUNIT m)) <=>
       (!bind unit.
          (!f g x. bind f (bind g x) = bind (bind f o g) x) /\
          (!x. bind unit x = x) /\
          (!f i. bind f (unit i) = (if FINITE (:A) then ARB else f i))
          ==> P bind unit)`,
  let th =
    `!P. (!m:A dbmonad. P m) <=> (!w. IS_SEMI_DBMONAD w ==> P (MK_DBMONAD w))`
    |> METIS [dbmonad_tybij]
    |> REWRITE_RULE[FORALL_PAIR_THM]
    |> SPEC `\m:A dbmonad. P (DBBIND m) (DBUNIT m):bool`
    |> BETA_RULE
    |> SIMP_RULE [DBBIND_MK_DBMONAD; DBUNIT_MK_DBMONAD]
    |> REWRITE_RULE[IS_SEMI_DBMONAD] in
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [th] THEN MESON_TAC[]);;

let DBMONAD_CLAUSES_GEN = prove
 (`!m:A dbmonad.
     (!f g x. DBBIND m f (DBBIND m g x) = DBBIND m (DBBIND m f o g) x) /\
     (!x. DBBIND m (DBUNIT m) x = x) /\
     (!f i. DBBIND m f (DBUNIT m i) = if FINITE (:A) then ARB else f i)`,
  REWRITE_TAC[FORALL_DBMONAD_THM]);;

let DBMONAD_CLAUSES = prove
 (`!m:A dbmonad.
     (!f g x. DBBIND m f (DBBIND m g x) = DBBIND m (DBBIND m f o g) x) /\
     (!x. DBBIND m (DBUNIT m) x = x) /\
     (!f i. INFINITE (:A) ==> DBBIND m f (DBUNIT m i) = f i)`,
  SIMP_TAC[FORALL_DBMONAD_THM; INFINITE]);;

let DBMONAD_IS_DBMONAD = prove
 (`!m:A dbmonad. INFINITE (:A) ==> IS_DBMONAD (DBBIND m, DBUNIT m)`,
  SIMP_TAC[FORALL_DBMONAD_THM; IS_DBMONAD; DBMONAD_CLAUSES; INFINITE]);;

let [DBBIND_DBBIND;DBUNIT_DBBIND;DBBIND_DBUNIT] =
  CONJUNCTS (REWRITE_RULE[FORALL_AND_THM] DBMONAD_CLAUSES);;

let DBREINDEX = new_definition
  `DBREINDEX (m:A dbmonad) f = DBBIND m (DBUNIT m o f)`;;

let DBREINDEX_UNIT_GEN = prove
 (`!m:A dbmonad f i. DBREINDEX m f (DBUNIT m i) =
                     if FINITE (:A) then ARB else DBUNIT m (f i)`,
  REWRITE_TAC[DBREINDEX; DBMONAD_CLAUSES_GEN; o_THM]);;

let DBREINDEX_UNIT = prove
 (`!m:A dbmonad f i.
     INFINITE(:A) ==> DBREINDEX m f (DBUNIT m i) = DBUNIT m (f i)`,
  SIMP_TAC[DBREINDEX_UNIT_GEN; INFINITE]);;

let DBBIND_DBREINDEX = prove
 (`INFINITE (:A)
   ==> !m:A dbmonad f g x. DBBIND m f (DBREINDEX m g x) = DBBIND m (f o g) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DBREINDEX; DBBIND_DBBIND] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  ASM_SIMP_TAC[DBBIND_DBUNIT]);;

let DBREINDEX_DBBIND = prove
 (`!m:A dbmonad f g x.
     DBREINDEX m f (DBBIND m g x) = DBBIND m (DBREINDEX m f o g) x`,
  REWRITE_TAC[DBREINDEX; DBBIND_DBBIND]);;

(* ------------------------------------------------------------------------- *)
(* Homomorphisms of DB-monads.                                               *)
(* ------------------------------------------------------------------------- *)

let DBMONAD_HOM = new_definition
  `DBMONAD_HOM (m:A dbmonad) (n:B dbmonad) =
   {h:A->B | (!i. h (DBUNIT m i) = DBUNIT n i) /\
             (!f x. h (DBBIND m f x) = DBBIND n (h o f) (h x))}`;;

let IN_DBMONAD_HOM = prove
 (`!m n h:A->B. h IN DBMONAD_HOM m n <=>
                (!i. h (DBUNIT m i) = DBUNIT n i) /\
                (!f x. h (DBBIND m f x) = DBBIND n (h o f) (h x))`,
  REWRITE_TAC[DBMONAD_HOM; IN_ELIM_THM]);;
