(* ========================================================================= *)
(* De Bruijn modules.                                                        *)
(* ========================================================================= *)

needs "Lambda/new_dbmonad.ml";;

(* ------------------------------------------------------------------------- *)
(* Modules.                                                                  *)
(* ------------------------------------------------------------------------- *)

let IS_DBMODULE = new_definition
  `!t:A dbmonad mbind:(num->A)->B->B.
     IS_DBMODULE (t,mbind) <=>
     (!x. mbind (DBUNIT t) x = x) /\
     (!f g x. mbind g (mbind f x) = mbind (DBBIND t g o f) x)`;;

let EXISTS_DBMODULE = prove
 (`?m:A dbmonad#((num->A)->B->B). IS_DBMODULE m`,
  EXISTS_TAC `(ARB:A dbmonad), (\ (f:num->A) (x:B). x)` THEN
  REWRITE_TAC[IS_DBMODULE]);;

let dbmodule_tybij =
  new_type_definition "dbmodule" ("MK_DBMODULE","DEST_DBMODULE")
    EXISTS_DBMODULE;;

let MK_DEST_DBMODULE = prove
 (`!m:(A,B)dbmodule. MK_DBMODULE (DEST_DBMODULE m) = m`,
  REWRITE_TAC[dbmodule_tybij]);;

let DEST_MK_DBMODULE = prove
 (`!m. IS_DBMODULE m ==> DEST_DBMODULE (MK_DBMODULE m:(A,B)dbmodule) = m`,
  REWRITE_TAC[GSYM dbmodule_tybij] THEN MESON_TAC[]);;

let DBBASE = new_definition
  `DBBASE (m:(A,B)dbmodule) = FST (DEST_DBMODULE m)`;;

let DBMBIND = new_definition
  `DBMBIND (m:(A,B)dbmodule) = SND (DEST_DBMODULE m)`;;

let DBBASE_MK_DBMODULE = prove
 (`!t:A dbmonad mbind:(num->A)->B->B.
     IS_DBMODULE (t,mbind) ==> DBBASE (MK_DBMODULE (t,mbind)) = t`,
  SIMP_TAC[DBBASE; DEST_MK_DBMODULE]);;

let DBMBIND_MK_DBMODULE = prove
 (`!t:A dbmonad mbind:(num->A)->B->B.
     IS_DBMODULE (t,mbind) ==> DBMBIND (MK_DBMODULE (t,mbind)) = mbind`,
  SIMP_TAC[DBMBIND; DEST_MK_DBMODULE]);;

let dbmodule_CASES = prove
 (`!m:(A,B)dbmodule. ?t mbind.
     m = MK_DBMODULE (t,mbind) /\
     (!f g x. mbind f (mbind g x) = mbind (DBBIND t f o g) x) /\
     (!x. mbind (DBUNIT t) x = x)`,
  let th =
    `!m:(A,B)dbmodule.
       ?w. m = MK_DBMODULE w /\ IS_DBMODULE w`
    |> METIS [dbmodule_tybij]
    |> REWRITE_RULE[EXISTS_PAIR_THM; IS_DBMODULE]
    |> SPEC `m:(A,B)dbmodule` in
  GEN_TAC THEN STRIP_ASSUME_TAC th THEN ASM_MESON_TAC[]);;

let FORALL_DBMODULE_THM = prove
 (`!P. (!m:(A,B)dbmodule. P (DBBASE m) (DBMBIND m)) <=>
       (!t mbind.
          (!f g x. mbind f (mbind g x) = mbind (DBBIND t f o g) x) /\
          (!x. mbind (DBUNIT t) x = x)
          ==> P t mbind)`,
  let th =
    `!P. (!m:(A,B)dbmodule. P m) <=> (!w. IS_DBMODULE w ==> P (MK_DBMODULE w))`
    |> METIS [dbmodule_tybij]
    |> REWRITE_RULE[FORALL_PAIR_THM]
    |> SPEC `\m:(A,B)dbmodule. P (DBBASE m) (DBMBIND m):bool`
    |> BETA_RULE
    |> SIMP_RULE [DBBASE_MK_DBMODULE; DBMBIND_MK_DBMODULE]
    |> REWRITE_RULE[IS_DBMODULE] in
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [th] THEN MESON_TAC[]);;

let DBMODULE_CLAUSES = prove
 (`!m:(A,B)dbmodule.
     (!f g x. DBMBIND m f (DBMBIND m g x) = DBMBIND m (DBBIND (DBBASE m) f o g) x) /\
     (!x. DBMBIND m (DBUNIT (DBBASE m)) x = x)`,
  REWRITE_TAC[FORALL_DBMODULE_THM]);;

let DBMODULE_IS_DBMODULE = prove
 (`!m:(A,B)dbmodule. IS_DBMODULE (DBBASE m, DBMBIND m)`,
  SIMP_TAC[FORALL_DBMODULE_THM; IS_DBMODULE; DBMODULE_CLAUSES]);;

let [DBMBIND_DBMBIND;DBUNIT_DBMBIND] =
  CONJUNCTS (REWRITE_RULE[FORALL_AND_THM] DBMODULE_CLAUSES);;

(* ------------------------------------------------------------------------- *)
(* Tautological module.                                                      *)
(* ------------------------------------------------------------------------- *)

let SELF_DBMODULE = new_definition
  `SELF_DBMODULE t = MK_DBMODULE (t,DBBIND t)`;;

let SELF_DBMODULE_CLAUSES = prove
 (`(!t:A dbmonad. DBBASE (SELF_DBMODULE t) = t) /\
   (!t:A dbmonad. DBMBIND (SELF_DBMODULE t) = DBBIND t)`,
  REWRITE_TAC[SELF_DBMODULE] THEN
  CLAIM_TAC "rmk" `!t:A dbmonad. IS_DBMODULE (t,DBBIND t)` THENL
  [REWRITE_TAC[IS_DBMODULE; DBMONAD_CLAUSES]; ALL_TAC] THEN
  ASM_SIMP_TAC[DBBASE_MK_DBMODULE; DBMBIND_MK_DBMODULE]);;

(* ------------------------------------------------------------------------- *)
(*  Product module.                                                          *)
(* ------------------------------------------------------------------------- *)

let DBMODULE_PRODUCT = new_definition
  `DBMODULE_PRODUCT (l:(A,B)dbmodule,m:(A,C)dbmodule) : (A,B#C)dbmodule =
   MK_DBMODULE (DBBASE l, 
                (\f (x,y). (DBMBIND l f x, DBMBIND m f y)))`;;

let DBMODULE_PRODUCT_CLAUSES = prove
 (`!l:(A,B)dbmodule m:(A,C)dbmodule.
     INFINITE (:A) /\ DBBASE l = DBBASE m
     ==> DBBASE (DBMODULE_PRODUCT(l,m)) = DBBASE l /\
         (!f x y. DBMBIND (DBMODULE_PRODUCT(l,m)) f (x,y) =
                  (DBMBIND l f x, DBMBIND m f y))`,
  INTRO_TAC "!l m; infty dbase_eq" THEN
  C SUBGOAL_THEN
    (fun th -> SIMP_TAC[DBMODULE_PRODUCT; DBBASE_MK_DBMODULE; DBMBIND_MK_DBMODULE; th])
    `IS_DBMODULE (DBBASE l, 
                  (\f (x,y). (DBMBIND (l:(A,B)dbmodule) f x,
                              DBMBIND (m:(A,C)dbmodule) f y)))` THEN
  REWRITE_TAC[IS_DBMODULE; FORALL_PAIR_THM; PAIR_EQ; DBMODULE_CLAUSES] THEN
  ASM_REWRITE_TAC[DBMODULE_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(*  Derived module.                                                          *)
(* ------------------------------------------------------------------------- *)

let DBSLIDE = new_recursive_definition num_RECURSION
  `(!t f. DBSLIDE t f 0 = DBUNIT t 0:A) /\
   (!t f i. DBSLIDE t f (SUC i) = DBREINDEX t SUC (f i))`;;

let DBDERIVED = new_definition
  `DBDERIVED (m:(A,B)dbmodule) =
   MK_DBMODULE (DBBASE m,\f. DBMBIND m (DBSLIDE (DBBASE m) f))`;;

let DBDERIVED_CLAUSES = prove
 (`INFINITE (:A)
   ==> (!m:(A,B)dbmodule. DBBASE (DBDERIVED m) = DBBASE m) /\
       (!m:(A,B)dbmodule f.
          DBMBIND (DBDERIVED m) f = DBMBIND m (DBSLIDE (DBBASE m) f))`,
  DISCH_TAC THEN CLAIM_TAC "rmk"
    `!m:(A,B)dbmodule.
       IS_DBMODULE (DBBASE m,\f. DBMBIND m (DBSLIDE (DBBASE m) f))` THENL
  [REWRITE_TAC[IS_DBMODULE; DBMODULE_CLAUSES] THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
      `DBSLIDE (DBBASE (m:(A,B)dbmodule)) (DBUNIT (DBBASE m)) =
       DBUNIT (DBBASE m)`
      (fun th -> ASM_SIMP_TAC[th; DBMODULE_CLAUSES]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN REWRITE_TAC[DBSLIDE] THEN
    ASM_SIMP_TAC[DBREINDEX_UNIT];
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
    ASM_SIMP_TAC[DBSLIDE; o_THM; DBMONAD_CLAUSES] THEN
    ASM_SIMP_TAC[DBBIND_DBREINDEX; DBREINDEX_DBBIND] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; DBSLIDE]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[DBDERIVED; DBBASE_MK_DBMODULE; DBMBIND_MK_DBMODULE]);;

(* ------------------------------------------------------------------------- *)
(* Morphisms of modules (over the same base DB-monad).                       *)
(* ------------------------------------------------------------------------- *)

let MODULE_HOM = new_definition
  `!m1:(A,M)dbmodule m2:(A,N)dbmodule.
     MODULE_HOM (m1,m2) =
     {h | DBBASE m1 = DBBASE m2 /\
          (!f:num->A x. h (DBMBIND m1 f x) = DBMBIND m2 f (h x))}`;;

let MODULE_HOM_CLAUSES = prove
 (`!m1:(A,M)dbmodule m2:(A,N)dbmodule h:M->N.
     h IN MODULE_HOM (m1,m2)
     <=> DBBASE m1 = DBBASE m2 /\
         (!f:num->A x. h (DBMBIND m1 f x) = DBMBIND m2 f (h x))`,
 REWRITE_TAC[MODULE_HOM; IN_ELIM_THM] THEN MESON_TAC[]);;

let MODULE_HOM_ID = prove
 (`!m:(A,M)dbmodule. I IN MODULE_HOM (m,m)`,
  REWRITE_TAC[MODULE_HOM_CLAUSES; I_THM]);;

let MODULE_HOM_o = prove
 (`!m1:(A,L)dbmodule m2:(A,M)dbmodule m3:(A,N)dbmodule g:L->M h:M->N.
     g IN MODULE_HOM (m1,m2) /\ h IN MODULE_HOM (m2,m3)
     ==> h o g IN MODULE_HOM (m1,m3)`,
  REWRITE_TAC[MODULE_HOM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* ------------------------------------------------------------------------- *)
(*  Pull-back module.                                                        *)
(* ------------------------------------------------------------------------- *)

let PULLBACK_DBMODULE = new_definition
  `PULLBACK_DBMODULE (t:A dbmonad) (h:A->B) (m:(B,M)dbmodule) =
   MK_DBMODULE (t,\f:(num->A). DBMBIND m (h o f))`;;

let PULLBACK_DBMODULE_CLAUSES = prove
 (`!t:A dbmonad h:A->B m:(B,M)dbmodule.
     h IN DBMONAD_HOM (t,DBBASE m)
     ==> (DBBASE (PULLBACK_DBMODULE t h m) = t) /\
         (!f. DBMBIND (PULLBACK_DBMODULE t h m) f = DBMBIND m (h o f))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DBMONAD_HOM] THEN STRIP_TAC THEN
  CLAIM_TAC "rmk"
    `IS_DBMODULE (t:A dbmonad,
                  \f:(num->A). DBMBIND (m:(B,M)dbmodule) (h o f))` THENL
  [REWRITE_TAC[IS_DBMODULE] THEN
   SUBGOAL_THEN `h:A->B o DBUNIT t = DBUNIT (DBBASE (m:(B,M)dbmodule))`
     SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
   REWRITE_TAC[DBMODULE_CLAUSES] THEN REPEAT STRIP_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM; o_THM];
   ALL_TAC] THEN
  ASM_SIMP_TAC[PULLBACK_DBMODULE; DBBASE_MK_DBMODULE; DBMBIND_MK_DBMODULE]);;

(* ------------------------------------------------------------------------- *)
(* Big Morphisms of modules (over different base DB-monad).                  *)
(* ------------------------------------------------------------------------- *)

let BIG_MODULE_HOM = new_definition
  `!m1:(A,M)dbmodule m2:(B,N)dbmodule.
     BIG_MODULE_HOM (m1,m2) =
     {(h:A->B,k:M->N) |
        h IN DBMONAD_HOM (DBBASE m1,DBBASE m2) /\
        (!f:num->A x. k (DBMBIND m1 f x) = DBMBIND m2 (h o f) (k x))}`;;

let IN_BIG_MODULE_HOM = prove
 (`!m1:(A,M)dbmodule m2:(B,N)dbmodule h:A->B k:M->N.
     (h,k) IN BIG_MODULE_HOM (m1,m2)
     <=> h IN DBMONAD_HOM (DBBASE m1,DBBASE m2) /\
         (!f:num->A x. k (DBMBIND m1 f x) = DBMBIND m2 (h o f) (k x))`,
 REWRITE_TAC[BIG_MODULE_HOM; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let BIG_MODULE_HOM_ID = prove
 (`!m:(A,M)dbmodule. (I,I) IN BIG_MODULE_HOM (m,m)`,
  REWRITE_TAC[IN_BIG_MODULE_HOM; I_THM; I_O_ID; DBMONAD_HOM_ID]);;

let BIG_MODULE_HOM_o = prove
 (`!m1:(A,L)dbmodule m2:(B,M)dbmodule m3:(C,N)dbmodule
     h1:A->B h2:B->C k1:L->M k2:M->N.
     (h1,k1) IN BIG_MODULE_HOM (m1,m2) /\ (h2,k2) IN BIG_MODULE_HOM (m2,m3)
     ==> (h2 o h1,k2 o k1) IN BIG_MODULE_HOM (m1,m3)`,
  REWRITE_TAC[IN_BIG_MODULE_HOM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_THM; o_ASSOC] THEN ASM_MESON_TAC[DBMONAD_HOM_o]);;

let SMALL_MODULE = prove
 (`!m1:(A,M)dbmodule m2:(A,N)dbmodule h:M->N.
     h IN MODULE_HOM (m1,m2) <=>
     DBBASE m1 = DBBASE m2 /\
     (I,h) IN BIG_MODULE_HOM (m1,m2)`,
  REWRITE_TAC[MODULE_HOM_CLAUSES; IN_BIG_MODULE_HOM; I_O_ID] THEN
  MESON_TAC[DBMONAD_HOM_ID]);;

let SELF_MODULE_HOM = prove
 (`!m1 m2 h:A->B.
     h IN DBMONAD_HOM (m1,m2)
     ==> (h,h) IN BIG_MODULE_HOM (SELF_DBMODULE m1, SELF_DBMODULE m2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_DBMONAD_HOM; IN_BIG_MODULE_HOM; SELF_DBMODULE_CLAUSES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let BIG_MODULE_HOM_ALT = prove
 (`!m1 m2 h:A->B k:M->N.
     (h,k) IN BIG_MODULE_HOM (m1,m2) <=>
     h IN DBMONAD_HOM (DBBASE m1,DBBASE m2) /\
     k IN MODULE_HOM (m1,PULLBACK_DBMODULE (DBBASE m1) h m2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BIG_MODULE_HOM; MODULE_HOM_CLAUSES] THEN
  ASM_CASES_TAC `h:A->B IN DBMONAD_HOM
    (DBBASE (m1:(A,M)dbmodule),DBBASE (m2:(B,N)dbmodule))` THEN
  ASM_SIMP_TAC[PULLBACK_DBMODULE_CLAUSES]);;
