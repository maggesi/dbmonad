(* ========================================================================= *)
(* Axiomatic Set Theory in HOL Light.                                        *)
(*                                                                           *)
(* Copyright (c) 2020 Marco Maggesi                                          *)
(* ========================================================================= *)

(* load_path := "/Users/maggesi/Devel/dbmonad/Code/HOL_Light" :: !load_path;; *)
(* loadt "/Users/maggesi/Devel/dbmonad/Code/HOL_Light/Lambda/misc.ml";; *)

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(",,",get_infix_status ",");;            (* Pairs             *)
parse_as_infix("=>",get_infix_status ",");;            (* Function space    *)
parse_as_infix("~~>",get_infix_status "=>");;          (* Partial fun space *)
parse_as_infix("AP",get_infix_status "$");;            (* Funct application *)
parse_as_infix("CROSSSET",get_infix_status "CROSS");;  (* Cartesian prod    *)
parse_as_infix("FUNCTIONAL_ON",(12, "right"));;        (* Funct with domain *)
parse_as_infix("KCROSS",get_infix_status "CROSS");;    (* Kuratowski prod   *)
parse_as_infix("RELSET",get_infix_status "CROSS");;    (* Binary relations  *)

parse_as_binder "FUNC";;                               (* Funct abstraction *)

(* ------------------------------------------------------------------------- *)
(* Universe of sets.                                                         *)
(* ------------------------------------------------------------------------- *)

new_type("elem",0);;
new_type_abbrev("class",`:elem->bool`);;
new_constant("UNPACK",`:elem->class`);;

let UU = new_definition
  `UU = IMAGE UNPACK (:elem)`;;

let IN_UU = prove
 (`!s. s IN UU <=> (?t. s = UNPACK t)`,
  REWRITE_TAC[UU; IN_IMAGE; IN_UNIV]);;

let PACK = new_definition
  `PACK s = @x. s = UNPACK x`;;

(* ------------------------------------------------------------------------- *)
(* Empty set and von Neumann ordinals.                                       *)
(* ------------------------------------------------------------------------- *)

let ZERO_ELEM = new_definition
  `ZERO_ELEM = PACK {}`;;

let SUC_ELEM = new_definition
  `SUC_ELEM x = PACK (x INSERT UNPACK x)`;;

let ORDINAL_ELEM = new_recursive_definition num_RECURSION
  `ORDINAL_ELEM 0 = ZERO_ELEM /\
   (!n. ORDINAL_ELEM (SUC n) = SUC_ELEM (ORDINAL_ELEM n))`;;

let NATSET = new_definition
  `NATSET = {ORDINAL_ELEM n | n IN (:num)}`;;

(* ------------------------------------------------------------------------- *)
(* Axioms.                                                                   *)
(* ------------------------------------------------------------------------- *)

let EMPTY_IN_UU = new_axiom
  `{} IN UU`;;

let UNPACK_INJ = new_axiom
  `!s t. UNPACK s = UNPACK t ==> s = t`;;

let SUBSET_IN_UU = new_axiom
  `!s t. s IN UU /\ t SUBSET s ==> t IN UU`;;

let UNIONS_IN_UU = new_axiom
  `!u. u IN UU ==> UNIONS (IMAGE UNPACK u) IN UU`;;

let IMAGE_IN_UU = new_axiom
  `!f s. s IN UU ==> IMAGE f s IN UU`;;

let POWERSET_IN_UU = new_axiom
  `!s. s IN UU ==> {PACK t | t SUBSET s} IN UU`;;

let FOUNDATION_AX = new_axiom
  `!s. s IN UU /\ ~(s = {}) ==> ?x. x IN s /\ DISJOINT (UNPACK x) s`;;

let NATSET_IN_UU = new_axiom
  `NATSET IN UU`;;



(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* The foundation of Set Theory in HOL ends here.                            *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(* Russell's paradox.                                                        *)
(* ------------------------------------------------------------------------- *)

let RUSSELL_PARADOX = prove
 (`~({s | ~(s IN UNPACK s)} IN UU)`,
  REWRITE_TAC[IN_UU] THEN INTRO_TAC "@u. u" THEN
  SUBGOAL_THEN `u IN UNPACK u <=> ~(u IN UNPACK u)`
    (fun th -> MESON_TAC[th]) THEN
  POP_ASSUM (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[IN_ELIM_THM]);;

let UNIV_IN_UU = prove
 (`~((:elem) IN UU)`,
  INTRO_TAC "hp" THEN SUBGOAL_THEN `{s | ~(s IN UNPACK s)} IN UU`
    (fun th -> MESON_TAC[th; RUSSELL_PARADOX]) THEN
  MATCH_MP_TAC SUBSET_IN_UU THEN EXISTS_TAC `(:elem)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

let IN_UU_NOT_UNIV = prove
 (`!s. s IN UU ==> ?x. ~(x IN s)`,
  GEN_TAC THEN DISCH_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `s = (:elem)` SUBST_VAR_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIV] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_UNIV] THEN ASM_MESON_TAC[UNIV_IN_UU]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties about packing and unpacking.                             *)
(* ------------------------------------------------------------------------- *)

let UNPACK_EQ = prove
 (`!x y. UNPACK x = UNPACK y <=> x = y`,
  MESON_TAC[UNPACK_INJ]);;

let UNPACK_IN_UU = prove
 (`!x. UNPACK x IN UU`,
  REWRITE_TAC[IN_UU; UNPACK_EQ] THEN MESON_TAC[]);;

let PACK_UNPACK = prove
 (`!x. PACK (UNPACK x) = x`,
  REWRITE_TAC[PACK; UNPACK_EQ] THEN MESON_TAC[]);;

let UNPACK_PACK = prove
 (`!s. s IN UU ==> UNPACK (PACK s) = s`,
  REWRITE_TAC[UU; PACK; FORALL_IN_IMAGE; IN_UNIV;  UNPACK_EQ] THEN
  MESON_TAC[]);;

let PACK_INJ = prove
 (`!s t. s IN UU /\ t IN UU /\ PACK s = PACK t ==> s = t`,
  REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o AP_TERM `UNPACK`) THEN
  ASM_SIMP_TAC[UNPACK_PACK]);;

let PACK_EQ = prove
 (`!s t. s IN UU /\ t IN UU ==> (PACK s = PACK t <=> s = t)`,
  MESON_TAC[PACK_INJ]);;

let PACK_UNIQUE = prove
 (`!s x. s IN UU /\ UNPACK x = s ==> PACK s = x`,
  MESON_TAC[PACK_UNPACK]);;

let EXISTS_UNPACK = prove
 (`!s. (?x. UNPACK x = s) <=> s IN UU`,
  REWRITE_TAC[IN_UU] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic set constructions.                                                  *)
(* ------------------------------------------------------------------------- *)

let INTER_IN_UU = prove
 (`!s t. s IN UU \/ t IN UU ==> s INTER t IN UU`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_IN_UU THENL
  [EXISTS_TAC `s:elem->bool` THEN ASM SET_TAC[];
   EXISTS_TAC `t:elem->bool` THEN ASM SET_TAC[]]);;

let SING_IN_UU = prove
 (`!x. {x} IN UU`,
  GEN_TAC THEN SUBGOAL_THEN
    `{x:elem} = IMAGE (\a. x) {PACK t | t SUBSET {}}` SUBST1_TAC THENL
  [SUBGOAL_THEN `{PACK t | t SUBSET {}} = {PACK {}}`
      (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]) THEN
   REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC;
               FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SING] THEN AP_TERM_TAC THEN
    POP_ASSUM MP_TAC THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `{}:class` THEN
    REWRITE_TAC[NOT_IN_EMPTY]];
   ALL_TAC] THEN
  SIMP_TAC[IMAGE_IN_UU; POWERSET_IN_UU; EMPTY_IN_UU]);;

let UNIONS_IN_UU_EQ = prove
 (`!u. UNIONS (IMAGE UNPACK u) IN UU <=> u IN UU`,
  SUBGOAL_THEN `!u. UNIONS (IMAGE UNPACK u) IN UU ==> u IN UU`
    (fun th -> MESON_TAC[th; UNIONS_IN_UU]) THEN
  INTRO_TAC "!u; u" THEN MATCH_MP_TAC SUBSET_IN_UU THEN EXISTS_TAC
    `{PACK t | t SUBSET UNIONS (IMAGE UNPACK u)}` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[POWERSET_IN_UU]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN INTRO_TAC "!x; x" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `UNPACK x` THEN
  REWRITE_TAC[PACK_UNPACK] THEN ASM SET_TAC[]);;

let POWERSET_IN_UU_EQ = prove
 (`!s. {PACK t | t SUBSET s} IN UU <=> s IN UU`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POWERSET_IN_UU] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `UNIONS (IMAGE UNPACK {PACK t | t SUBSET s})` THEN
  ASM_SIMP_TAC[UNIONS_IN_UU_EQ] THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `{x:elem}` THEN
  REWRITE_TAC[IN_SING; IN_IMAGE] THEN EXISTS_TAC `PACK {x}` THEN
  SIMP_TAC[UNPACK_PACK; SING_IN_UU] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `{x:elem}` THEN ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let INSERT_IN_UU = prove
 (`!x s. s IN UU ==> x INSERT s IN UU`,
  INTRO_TAC "!x s; s" THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `UNIONS (IMAGE UNPACK
                            (IMAGE (\a. if a = PACK {} then PACK {x} else a)
                                   {PACK t | t SUBSET s}))` THEN
  ASM_SIMP_TAC[UNIONS_IN_UU; IMAGE_IN_UU; POWERSET_IN_UU_EQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_INSERT; GSYM IMAGE_o] THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{x}:class` THEN
   REWRITE_TAC[IN_INSERT; IN_IMAGE; o_THM] THEN EXISTS_TAC `PACK {}` THEN
   ASM_SIMP_TAC[UNPACK_PACK; SING_IN_UU; IN_ELIM_THM] THEN
   EXISTS_TAC `{}:class` THEN REWRITE_TAC[NOT_IN_EMPTY];
   ALL_TAC] THEN
  INTRO_TAC "![y]; y" THEN REWRITE_TAC[IN_UNIONS] THEN
  EXISTS_TAC `s:class` THEN ASM_REWRITE_TAC[IN_IMAGE; o_THM] THEN
  EXISTS_TAC `PACK s` THEN ASM_SIMP_TAC[PACK_EQ; EMPTY_IN_UU] THEN
  COND_CASES_TAC THENL
  [POP_ASSUM SUBST_VAR_TAC THEN POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC[NOT_IN_EMPTY];
   ALL_TAC] THEN
  ASM_SIMP_TAC[UNPACK_PACK] THEN SET_TAC[]);;

let UNION_IN_UU = prove
 (`!s t. s IN UU /\ t IN UU ==> s UNION t IN UU`,
  REPEAT STRIP_TAC THEN C SUBGOAL_THEN SUBST1_TAC
    `s UNION t : class =
     UNIONS (IMAGE UNPACK {PACK s, PACK t})` THENL
  [ASM_SIMP_TAC[IMAGE_CLAUSES; UNPACK_PACK] THEN SET_TAC[];
   ASM_SIMP_TAC[UNIONS_IN_UU; INSERT_IN_UU; EMPTY_IN_UU]]);;

let UNION_IN_UU_EQ = prove
 (`!s t. s UNION t IN UU <=> s IN UU /\ t IN UU`,
  SUBGOAL_THEN `!s t. s UNION t IN UU ==> s IN UU /\ t IN UU`
    (fun th -> MESON_TAC[th; UNION_IN_UU]) THEN
  INTRO_TAC "!s t; hp" THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `s UNION t:class` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let INSERT_IN_UU_EQ = prove
 (`!x s. x INSERT s IN UU <=> s IN UU`,
  ONCE_REWRITE_TAC[SET_RULE `!x:elem s. x INSERT s = {x} UNION s`] THEN
  REWRITE_TAC[UNION_IN_UU_EQ; SING_IN_UU]);;

let INTERS_IN_UU = prove
 (`!u. ~(u = {}) ==> INTERS (IMAGE UNPACK u) IN UU`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_IN_UU THEN EXISTS_TAC `UNPACK x` THEN
  REWRITE_TAC[UNPACK_IN_UU] THEN ASM SET_TAC[]);;

let DIFF_IN_UU = prove
 (`!s t. s IN UU ==> s DIFF t IN UU`,
  MESON_TAC[SET_RULE `s DIFF t SUBSET s:class`; SUBSET_IN_UU]);;

let DELETE_IN_UU = prove
 (`!s x. s IN UU ==> s DELETE x IN UU`,
  MESON_TAC[SET_RULE `s DELETE x SUBSET s:class`; SUBSET_IN_UU]);;

let DELETE_IN_UU_EQ = prove
 (`!s x. s DELETE x IN UU <=> s IN UU`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[DELETE_IN_UU] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `x:elem INSERT (s DELETE x)` THEN
  ASM_REWRITE_TAC[INSERT_IN_UU_EQ] THEN SET_TAC[]);;

let GEN_UNIONS_IN_UU = prove
 (`!s f. s IN UU /\ (!x. x IN s ==> f x IN UU) ==> UNIONS (IMAGE f s) IN UU`,
  REPEAT STRIP_TAC THEN C SUBGOAL_THEN SUBST1_TAC
    `IMAGE (f:elem->class) s = IMAGE (UNPACK o PACK o f) s` THENL
  [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[o_THM; UNPACK_PACK]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[IMAGE_o] THEN ASM_SIMP_TAC[UNIONS_IN_UU_EQ; IMAGE_IN_UU]);;

(* ------------------------------------------------------------------------- *)
(* Simple consequences of the axiom of foundations.                          *)
(* ------------------------------------------------------------------------- *)

let INTER_SING_DISJOINT = prove
 (`!s. s IN UU ==> DISJOINT s {PACK s}`,
  INTRO_TAC "!s; s" THEN MP_TAC (SPEC `{PACK s}` FOUNDATION_AX) THEN
  REWRITE_TAC[SING_IN_UU] THEN ASM SET_TAC[UNPACK_PACK]);;

let IN_IRREFLEXIVE = prove
 (`!x. ~(x IN UNPACK x)`,
  SET_TAC[INTER_SING_DISJOINT; UNPACK_IN_UU; PACK_UNPACK]);;

let IN_IRRIFLEXIVE_ALT = prove
 (`!s. s IN UU ==> ~(PACK s IN s)`,
  MESON_TAC[UNPACK_PACK; IN_IRREFLEXIVE]);;

let SINGLETON_SUBSET_REFL = prove
 (`!x. ~({x} SUBSET UNPACK x)`,
  SET_TAC[IN_IRREFLEXIVE]);;

let UNPACK_SUC_ELEM = prove
 (`!n. UNPACK (SUC_ELEM n) = n INSERT UNPACK n`,
  SIMP_TAC[SUC_ELEM; UNPACK_PACK; INSERT_IN_UU; UNPACK_IN_UU]);;

(* ------------------------------------------------------------------------- *)
(* About von Neumann ordinals.                                               *)
(* ------------------------------------------------------------------------- *)

let ORDINAL_ELEM_IN_NATSET = prove
 (`!n. ORDINAL_ELEM n IN NATSET`,
  REWRITE_TAC[NATSET] THEN SET_TAC[]);;

let FORALL_IN_NATSET = prove
 (`(!n. n IN NATSET ==> P n) <=> (!n. P (ORDINAL_ELEM n))`,
  REWRITE_TAC[NATSET] THEN SET_TAC[]);;

let EXISTS_IN_NATSET = prove
 (`(?n. n IN NATSET /\ P n) <=> (?n. P (ORDINAL_ELEM n))`,
  REWRITE_TAC[NATSET] THEN SET_TAC[]);;

let UNPACK_ZERO_ELEM = prove
 (`UNPACK ZERO_ELEM = {}`,
  REWRITE_TAC[ZERO_ELEM] THEN SIMP_TAC[UNPACK_PACK; EMPTY_IN_UU]);;

let NOT_SUC_ZERO_ELEM = prove
 (`!n. ~(SUC_ELEM n = ZERO_ELEM)`,
  REWRITE_TAC[GSYM UNPACK_EQ; UNPACK_ZERO_ELEM;
              UNPACK_SUC_ELEM; NOT_INSERT_EMPTY]);;

let PRED_ELEM = (specify o prove)
 (`!x. ?PRED_ELEM. UNPACK PRED_ELEM = UNIONS (IMAGE UNPACK (UNPACK x))`,
  REWRITE_TAC[EXISTS_UNPACK; UNIONS_IN_UU_EQ; UNPACK_IN_UU]);;

let PRED_SUC_ELEM_IFF_TRANSITIVE = prove
 (`!x. PRED_ELEM (SUC_ELEM x) = x <=>
       (!a b. a IN UNPACK b /\ b IN UNPACK x ==> a IN UNPACK x)`,
  REWRITE_TAC[GSYM UNPACK_EQ; PRED_ELEM; UNPACK_SUC_ELEM; IMAGE_CLAUSES] THEN
  SET_TAC[]);;

let TRANSITIVE_SUC_ELEM = prove
 (`!x. (!a b. a IN UNPACK b /\ b IN UNPACK x ==> a IN UNPACK x)
       ==> (!a b. a IN UNPACK b /\ b IN UNPACK (SUC_ELEM x)
                  ==> a IN UNPACK (SUC_ELEM x))`,
  INTRO_TAC "!x; x" THEN REWRITE_TAC[UNPACK_SUC_ELEM] THEN
  REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[]);;

let TRANSITIVE_ORDINAL_ELEM = prove
 (`!n a b. a IN UNPACK b /\ b IN UNPACK (ORDINAL_ELEM n)
           ==> a IN UNPACK (ORDINAL_ELEM n)`,
  INDUCT_TAC THEN REWRITE_TAC[ORDINAL_ELEM] THENL
  [REWRITE_TAC[UNPACK_ZERO_ELEM; NOT_IN_EMPTY];
   ASM_MESON_TAC[TRANSITIVE_SUC_ELEM]]);;

let PRED_SUC_ELEM = prove
 (`!n. n IN NATSET ==> PRED_ELEM (SUC_ELEM n) = n`,
  REWRITE_TAC[FORALL_IN_NATSET] THEN
  MESON_TAC[PRED_SUC_ELEM_IFF_TRANSITIVE; TRANSITIVE_ORDINAL_ELEM]);;

let SUC_ELEM_INJ = prove
 (`!m n. m IN NATSET /\ n IN NATSET /\ SUC_ELEM m = SUC_ELEM n ==> m = n`,
  MESON_TAC[PRED_SUC_ELEM]);;

let SUC_ELEM_EQ = prove
 (`!m n. m IN NATSET /\ n IN NATSET
         ==> (SUC_ELEM m = SUC_ELEM n <=> m = n)`,
  MESON_TAC[SUC_ELEM_INJ]);;

let ORDINAL_ELEM_INJ = prove
 (`!m n. ORDINAL_ELEM m = ORDINAL_ELEM n ==> m = n`,
  INDUCT_TAC THEN (INDUCT_TAC THENL [ALL_TAC; POP_ASSUM (K ALL_TAC)]) THEN
  REWRITE_TAC[ORDINAL_ELEM; NOT_SUC_ZERO_ELEM] THEN
  ASM_SIMP_TAC[SUC_ELEM_EQ; SUC_INJ; ORDINAL_ELEM_IN_NATSET]);;

let ORDINAL_ELEM_EQ = prove
 (`!m n. ORDINAL_ELEM m = ORDINAL_ELEM n <=> m = n`,
  MESON_TAC[ORDINAL_ELEM_INJ]);;

let UNPACK_ORDINAL_ELEM = prove
 (`!n. UNPACK (ORDINAL_ELEM n) = {ORDINAL_ELEM i | i < n}`,
  INDUCT_TAC THEN REWRITE_TAC[ORDINAL_ELEM] THENL
  [REWRITE_TAC[UNPACK_ZERO_ELEM; ARITH_RULE `!n. ~(n < 0)`] THEN SET_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[UNPACK_SUC_ELEM; GSYM SUBSET_ANTISYM_EQ; SUBSET;
                  FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM; ORDINAL_ELEM_EQ] THEN
  ASM_MESON_TAC[ARITH_RULE `i < SUC n <=> i = n \/ i < n`]);;

(* ------------------------------------------------------------------------- *)
(* Natural numbers.                                                          *)
(* ------------------------------------------------------------------------- *)

let [NAT_IN_UU; NAT_OF_NUM_IN_NAT; NAT_OF_NUM_INJ; NAT_OF_NUM_SURJ;
     NAT_OF_NUM_0; NAT_OF_NUM_SUC] =
 (CONJUNCTS o specify o prove)
 (`?nat nat_of_num natzero:elem natsuc.
     nat IN UU /\
     (!n:num. nat_of_num n IN nat) /\
     (!m n. nat_of_num m = nat_of_num n ==> m = n) /\
     (!n. n IN nat ==> ?m. n = nat_of_num m) /\
     (nat_of_num 0 = natzero) /\
     (!n. nat_of_num (SUC n) = natsuc (nat_of_num n))`,
  MAP_EVERY EXISTS_TAC [`NATSET`; `ORDINAL_ELEM`; `ZERO_ELEM`; `SUC_ELEM`] THEN
  REWRITE_TAC[NATSET_IN_UU; ORDINAL_ELEM_IN_NATSET; ORDINAL_ELEM;
              FORALL_IN_NATSET; ORDINAL_ELEM_EQ] THEN
  MESON_TAC[]);;

let NAT_OF_NUM_CLAUSES = CONJ NAT_OF_NUM_0 NAT_OF_NUM_SUC;;

overload_interface("&",`nat_of_num`);;

(* ------------------------------------------------------------------------- *)
(* Further properties of `nat_of_num` and `num_of_nat`.                      *)
(* ------------------------------------------------------------------------- *)

let NAT_OF_NUM_EQ_ZERO = prove
 (`!n. &n:elem = natzero <=> n = 0`,
  MESON_TAC[NAT_OF_NUM_CLAUSES; NAT_OF_NUM_INJ]);;

let NAT_OF_NUM_EQ = prove
 (`!m n. &m = &n <=> m = n`,
  MESON_TAC[NAT_OF_NUM_INJ]);;

let FORALL_IN_NAT = prove
 (`(!n. n IN nat ==> P n) <=> (!n. P (&n))`,
  MESON_TAC[NAT_OF_NUM_IN_NAT; NAT_OF_NUM_SURJ]);;

let NUM_OF_NAT_OF_NUM = (specify o prove)
 (`?num_of_nat. !n. num_of_nat(&n) = n`,
  EXISTS_TAC `\n. @m. nat_of_num m = n` THEN MESON_TAC[NAT_OF_NUM_INJ]);;

let NAT_OF_NUM_OF_NAT = prove
 (`!n. n IN nat ==> &(num_of_nat n) = n`,
  REWRITE_TAC[FORALL_IN_NAT; NUM_OF_NAT_OF_NUM]);;

let NUM_OF_NAT_INJ = prove
 (`!m n. m IN nat /\ n IN nat /\ num_of_nat m = num_of_nat n ==> m = n`,
  REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o AP_TERM `nat_of_num`) THEN
  ASM_SIMP_TAC[NAT_OF_NUM_OF_NAT]);;

let NUM_OF_NAT_SURJ = prove
 (`!n. ?m. m IN nat /\ n = num_of_nat m`,
  GEN_TAC THEN EXISTS_TAC `nat_of_num n` THEN
  REWRITE_TAC[NAT_OF_NUM_IN_NAT; NUM_OF_NAT_OF_NUM]);;

let FORALL_NAT = prove
 (`!P. (!n. n IN nat ==> P n) <=> (!n. P (&n))`,
  MESON_TAC[NAT_OF_NUM_OF_NAT; NAT_OF_NUM_IN_NAT]);;

let NAT_EQ = prove
 (`!m n. m IN nat /\ n IN nat ==> (m = n <=> num_of_nat m = num_of_nat n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_NAT;
              NUM_OF_NAT_OF_NUM; NAT_OF_NUM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Contable set are in correspondece with axiomatic sets.                    *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_IMP_EXISTS_SET = prove
 (`!s:A->bool. COUNTABLE s
               ==> ?t:class f g. t IN UU /\
                                 (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
                                 (!y. y IN t ==> g y IN s /\ f (g y) = y)`,
  GEN_TAC THEN REWRITE_TAC[COUNTABLE; ge_c; le_c; IN_UNIV] THEN
  INTRO_TAC "@i. inj" THEN MAP_EVERY EXISTS_TAC
    [`{nat_of_num (i x) | x | x:A IN s}`;
     `\x:A. nat_of_num (i x)`;
     `\y:elem. @x:A. x IN s /\ y = nat_of_num (i x)`] THEN
  BETA_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[NAT_OF_NUM_EQ]] THEN
  MATCH_MP_TAC SUBSET_IN_UU THEN EXISTS_TAC `nat` THEN CONJ_TAC THENL
  [REWRITE_TAC[NAT_IN_UU]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; NAT_OF_NUM_IN_NAT]);;

(* ------------------------------------------------------------------------- *)
(* Kuratowski pairs.                                                         *)
(* ------------------------------------------------------------------------- *)

let UNPACK_KPAIR = (specify o prove)
 (`!x y. ?KPAIR. UNPACK KPAIR = {PACK {x}, PACK {x,y}}`,
  REWRITE_TAC[EXISTS_UNPACK; INSERT_IN_UU_EQ; SING_IN_UU]);;

let KFST = new_definition
  `KFST p = PACK (UNIONS (IMAGE UNPACK (INTERS (IMAGE UNPACK (UNPACK p)))))`;;

let UNPACK_KFST = prove
 (`!p. ~(UNPACK p = {})
       ==> UNPACK (KFST p) =
           UNIONS (IMAGE UNPACK (INTERS (IMAGE UNPACK (UNPACK p))))`,
  SIMP_TAC[KFST; UNPACK_PACK; UNIONS_IN_UU_EQ; INTERS_IN_UU]);;

let KFST_KPAIR = prove
 (`!x y. KFST (KPAIR x y) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM UNPACK_EQ] THEN
  CLAIM_TAC "nempty" `~(UNPACK (KPAIR x y) = {})` THENL
  [REWRITE_TAC[UNPACK_KPAIR; NOT_INSERT_EMPTY];
   ASM_SIMP_TAC[UNPACK_KFST; UNPACK_KPAIR]] THEN
  REWRITE_TAC[IMAGE_CLAUSES; INTERS_2] THEN
  SIMP_TAC[UNPACK_PACK; SING_IN_UU; INSERT_IN_UU_EQ; EMPTY_IN_UU] THEN
  SET_TAC[]);;

let KSND = new_definition
  `KSND p = let u = IMAGE UNPACK (UNPACK p) in
            let s = UNIONS u DIFF INTERS u in
            PACK (UNIONS (IMAGE UNPACK (if s = {} then UNIONS u else s)))`;;

let UNPACK_KSND = prove
 (`!p. UNPACK (KSND p) =
       let u = IMAGE UNPACK (UNPACK p) in
       let s = UNIONS u DIFF INTERS u in
       UNIONS (IMAGE UNPACK (if s = {} then UNIONS u else s))`,
  GEN_TAC THEN REWRITE_TAC[KSND] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN MATCH_MP_TAC UNPACK_PACK THEN
  REWRITE_TAC[UNIONS_IN_UU_EQ] THEN COND_CASES_TAC THEN
  SIMP_TAC[DIFF_IN_UU; UNIONS_IN_UU_EQ; UNPACK_IN_UU]);;

let KSND_KPAIR = prove
 (`!x y. KSND (KPAIR x y) = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM UNPACK_EQ; UNPACK_KSND] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[UNPACK_KPAIR; IMAGE_CLAUSES; UNIONS_2; INTERS_2] THEN
  SIMP_TAC[UNPACK_PACK; SING_IN_UU; INSERT_IN_UU_EQ; FORALL_IN_UNION;
           FORALL_IN_INSERT; NOT_IN_EMPTY;
           SET_RULE `!s t. s DIFF t = {} <=>
                           (!x:elem. x IN s ==> x IN t)`] THEN
  REWRITE_TAC[IN_INSERT; IN_INTER; NOT_IN_EMPTY] THEN
  COND_CASES_TAC THENL [POP_ASSUM SUBST1_TAC THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INSERT_UNION; UNION_EMPTY; IN_INSERT; NOT_IN_EMPTY;
                  IN_INTER; INSERT_DIFF; EMPTY_DIFF] THEN
  ASM SET_TAC[]);;

let KPAIR_EQ = prove
 (`!x1 x2 y1 y2. KPAIR x1 y1 = KPAIR x2 y2 <=> x1 = x2 /\ y1 = y2`,
  MESON_TAC[KFST_KPAIR; KSND_KPAIR]);;

let KCROSS = new_definition
  `!s t. s KCROSS t = {KPAIR x y | x IN s /\ y IN t}`;;

let KPAIR_IN_KCROSS = prove
 (`!x y s t. KPAIR x y IN s KCROSS t <=> x IN s /\ y IN t`,
  REWRITE_TAC[KCROSS; IN_ELIM_THM; KPAIR_EQ] THEN MESON_TAC[]);;

let FORALL_IN_KCROSS = prove
 (`!s t. (!p. p IN s KCROSS t ==> P p) <=>
         (!x y. x IN s /\ y IN t ==> P (KPAIR x y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KCROSS; IN_ELIM_THM] THEN
  MESON_TAC[KPAIR_EQ]);;

let KCROSS_IN_UU = prove
 (`!s t. s IN UU /\ t IN UU ==> s KCROSS t IN UU`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `{PACK q | q SUBSET {PACK p | p SUBSET (s UNION t)}}` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[POWERSET_IN_UU_EQ; UNION_IN_UU]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_KCROSS] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `{PACK {x}, PACK {x,y}}` THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY;
              GSYM UNPACK_EQ; UNPACK_KPAIR] THEN
  SIMP_TAC[UNPACK_PACK; INSERT_IN_UU_EQ; SING_IN_UU;
           IN_ELIM_THM; IN_UNION] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
  EXISTS_TAC `{x,y:elem}` THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Abstract cartesian product.                                               *)
(* ------------------------------------------------------------------------- *)

let [CROSSSET_IN_UU; PAIRSET_IN_CROSSSET; PROJ1_IN; PROJ2_IN; PAIRSET_EQ;
     IN_CROSSSET_CASES; PROJ1_PAIRSET; PROJ2_PAIRSET] =
 (CONJUNCTS o specify o prove)
 (`?(CROSSSET) (,,) PROJ1 PROJ2.
     (!s t. s IN UU /\ t IN UU ==> s CROSSSET t IN UU) /\
     (!x y s t. x IN s /\ y IN t ==> x,,y IN s CROSSSET t) /\
     (!s t p. p IN s CROSSSET t ==> PROJ1 p IN s) /\
     (!s t p. p IN s CROSSSET t ==> PROJ2 p IN t) /\
     (!x1 x2 y1 y2. x1,,y1 = x2,,y2 <=> x1 = x2 /\ y1 = y2) /\
     (!s t p. p IN s CROSSSET t ==> ?x y. x IN s /\ y IN t /\ p = x,,y) /\
     (!x y. PROJ1 (x,,y) = x) /\
     (!x y. PROJ2 (x,,y) = y)`,
  MAP_EVERY EXISTS_TAC [`KCROSS`; `KPAIR`; `KFST`; `KSND`] THEN
  REWRITE_TAC[KCROSS_IN_UU; KPAIR_IN_KCROSS; KFST_KPAIR; KSND_KPAIR;
              FORALL_IN_KCROSS; KPAIR_EQ] THEN
  MESON_TAC[]);;

let PAIRSET_IN_CROSSSET_EQ = prove
 (`!x y s t. x,,y IN s CROSSSET t <=> x IN s /\ y IN t`,
  REPEAT GEN_TAC THEN SUBGOAL_THEN `x,,y IN s CROSSSET t ==> x IN s /\ y IN t`
    (fun th -> MESON_TAC[th; PAIRSET_IN_CROSSSET]) THEN
  MESON_TAC[IN_CROSSSET_CASES; PROJ1_PAIRSET; PROJ2_PAIRSET]);;

let IN_CROSSSET_CASES_EQ = prove
 (`!s t p. p IN s CROSSSET t <=> ?x y. x IN s /\ y IN t /\ p = x,,y`,
  MESON_TAC[IN_CROSSSET_CASES; PAIRSET_IN_CROSSSET]);;

(* ------------------------------------------------------------------------- *)
(* Set of booleans.                                                          *)
(* ------------------------------------------------------------------------- *)

let [BOOL_IN_UU; TRUE_IN_BOOL; FALSE_IN_BOOL; BOOL_DISTINCTNESS; BOOL_CASES] =
 (CONJUNCTS o specify o prove)
 (`?bool true false.
     bool IN UU /\
     true IN bool /\
     false IN bool /\
     ~(true = false) /\
     (!x. x IN bool ==> x = true \/ x = false)`,
  MAP_EVERY EXISTS_TAC [`{&0,&1}`; `&0`; `&1`] THEN
  REWRITE_TAC[INSERT_IN_UU_EQ; EMPTY_IN_UU; IN_INSERT; NOT_IN_EMPTY;
              NAT_OF_NUM_EQ; ARITH_EQ]);;

let FORALL_IN_BOOL = prove
 (`!P. (!b. b IN bool ==> P b) <=> P true /\ P false`,
  MESON_TAC[BOOL_CASES; TRUE_IN_BOOL; FALSE_IN_BOOL]);;

let EXISTS_IN_BOOL = prove
 (`!P. (?b. b IN bool /\ P b) <=> P true \/ P false`,
  MESON_TAC[BOOL_CASES; TRUE_IN_BOOL; FALSE_IN_BOOL]);;

(* ------------------------------------------------------------------------- *)
(* Set of binary relations.                                                  *)
(* ------------------------------------------------------------------------- *)

let IN_RELSET = (specify o prove)
 (`!s t. ?(RELSET). !r. r IN (RELSET) <=> UNPACK r SUBSET s CROSSSET t`,
  REPEAT GEN_TAC THEN EXISTS_TAC `{r | UNPACK r SUBSET s CROSSSET t}` THEN
  REWRITE_TAC[IN_ELIM_THM]);;

let RELSET_IN_UU = prove
 (`!s t. s IN UU /\ t IN UU ==> s RELSET t IN UU`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `{PACK r | r SUBSET s CROSSSET t}` THEN
  ASM_SIMP_TAC[POWERSET_IN_UU_EQ; CROSSSET_IN_UU] THEN
  REWRITE_TAC[SUBSET; IN_RELSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[PACK_UNPACK]);;

let RELSET_IN_UU_EQ = prove
 (`!s t. ~(s = {}) /\ ~(t = {})
         ==> (s RELSET t IN UU <=> s IN UU /\ t IN UU)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  INTRO_TAC "(@a. a) (@b. b)" THEN
  SUBGOAL_THEN `s RELSET t IN UU ==> s IN UU /\ t IN UU`
    (fun th -> MESON_TAC[th; RELSET_IN_UU]) THEN
  INTRO_TAC "hp" THEN CONJ_TAC THENL
  [MATCH_MP_TAC SUBSET_IN_UU THEN
   EXISTS_TAC `UNIONS (IMAGE (IMAGE PROJ1 o UNPACK) (s RELSET t))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GEN_UNIONS_IN_UU THEN ASM_REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[IMAGE_IN_UU; UNPACK_IN_UU];
    ALL_TAC] THEN
   REWRITE_TAC[SUBSET] THEN INTRO_TAC "!x; x" THEN REWRITE_TAC[IN_UNIONS] THEN
   EXISTS_TAC `{x:elem}` THEN REWRITE_TAC[IN_SING; IN_IMAGE] THEN
   EXISTS_TAC `PACK {x,,b}` THEN CONJ_TAC THENL
   [SIMP_TAC[o_THM; UNPACK_PACK; SING_IN_UU; IMAGE_CLAUSES; PROJ1_PAIRSET];
    SIMP_TAC[IN_RELSET; UNPACK_PACK; SING_IN_UU] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[PAIRSET_IN_CROSSSET]]
   ;
   MATCH_MP_TAC SUBSET_IN_UU THEN
   EXISTS_TAC `UNIONS (IMAGE (IMAGE PROJ2 o UNPACK) (s RELSET t))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GEN_UNIONS_IN_UU THEN ASM_REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[IMAGE_IN_UU; UNPACK_IN_UU];
    ALL_TAC] THEN
   REWRITE_TAC[SUBSET] THEN INTRO_TAC "![y]; y" THEN
   REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{y:elem}` THEN
   REWRITE_TAC[IN_SING; IN_IMAGE] THEN EXISTS_TAC `PACK {a,,y}` THEN
   CONJ_TAC THENL
   [SIMP_TAC[o_THM; UNPACK_PACK; SING_IN_UU; IMAGE_CLAUSES; PROJ2_PAIRSET];
    SIMP_TAC[IN_RELSET; UNPACK_PACK; SING_IN_UU] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[PAIRSET_IN_CROSSSET]]]);;

(* ------------------------------------------------------------------------- *)
(* Set functions.                                                            *)
(* ------------------------------------------------------------------------- *)

let FUNCSET = new_definition
  `s => t = {f | s IN UU /\ t IN UU /\
                 !x. if x IN s then f x IN t else f x = PACK t}`;;

let IN_FUNCSET = prove
 (`!f s t. f IN s => t <=>
           s IN UU /\ t IN UU /\
           !x. if x IN s then f x IN t else f x = PACK t`,
  REWRITE_TAC[FUNCSET; IN_ELIM_THM]);;

let DOMAIN_CODOMAIN_UNIQUE = prove
 (`!f s s' t t'. f IN s => t /\ f IN s' => t' ==> s = s' /\ t = t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_FUNCSET] THEN
  INTRO_TAC "(s t f) (s' t' f')" THEN
  SUBGOAL_THEN `t' = t:class` SUBST_ALL_TAC THENL
  [CLAIM_TAC "@z. z z'" `?z:elem. ~(z IN s) /\ ~(z IN s')` THENL
   [SUBGOAL_THEN `?z:elem. ~(z IN s UNION s')`  (fun th -> SET_TAC[th]) THEN
    HYP MESON_TAC "s s'" [IN_UU_NOT_UNIV; UNION_IN_UU];
    ALL_TAC] THEN
   MATCH_MP_TAC PACK_INJ THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   REWRITE_TAC[]] THEN
  SUBGOAL_THEN `s = {x:elem | f x:elem IN t}` SUBST1_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[IN_IRRIFLEXIVE_ALT]);;

let DOM_DEF = new_definition
  `DOM f = @s. ?t. f IN s => t`;;

let COD_DEF = new_definition
  `COD f = @t. ?s. f IN s => t`;;

let DOM_EXPLICIT = prove
 (`!f. f IN s => t ==> DOM f = s`,
  REWRITE_TAC[DOM_DEF] THEN MESON_TAC[DOMAIN_CODOMAIN_UNIQUE]);;

let COD_EXPLICIT = prove
 (`!f. f IN s => t ==> COD f = t`,
  REWRITE_TAC[COD_DEF] THEN MESON_TAC[DOMAIN_CODOMAIN_UNIQUE]);;

let FUNC = (specify o prove)
 (`?(FUNC) FDOM FCOD FGRAPH. !f s t.
     f IN s => t
     ==> FDOM ((FUNC) f s t) = s /\
         FCOD ((FUNC) f s t) = t /\
         FGRAPH ((FUNC) f s t) = IMAGE (\x. x,,f x) s`,
  MAP_EVERY EXISTS_TAC
    [`\f s t. PACK (IMAGE (\x. x,,f x) s),,PACK t`]
     `PACK s`;
     `PACK t`;
     `PROJ1`]
  EXISTS_TAC `\f s t. 
 );;

let FUNC = (specify o prove)
 (`?(FUNC). !f s. (FUNC) f (UNPACK s) =
                  s,,PACK (IMAGE (\x. x,,f x) (UNPACK s))`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `\f s. PACK s,,PACK (IMAGE (\x. x,,f x) s)` THEN
  REWRITE_TAC[PAIRSET_EQ; PACK_UNPACK]);;

let FUNC_ALT = prove
 (`!f s. s IN UU ==> (FUNC) f s = PACK s,,PACK (IMAGE (\x. x,,f x) s)`,
  REPEAT STRIP_TAC THEN DESTRUCT_TAC "@t. t"
    (MESON [ASSUME `s IN UU`; UNPACK_PACK] `?t. s = UNPACK t`) THEN
  ASM_REWRITE_TAC[FUNC; PACK_UNPACK]);;

let FUNCTIONS = new_definition
  `FUNCTIONS = {(FUNC) f s | f IN (:elem->elem) /\ s IN UU}`;;

let IN_FUNCTIONS = prove
 (`!f. f IN FUNCTIONS <=>
       (?s g. f = s,,g /\
              (!p. p IN UNPACK g ==> ?x y. x IN UNPACK s /\ p = x,,y) /\
              (!x y y'. x,,y IN UNPACK g /\ x,,y' IN UNPACK g ==> y = y'))`,
  REWRITE_TAC[FUNCTIONS; GSYM IMP_ANTISYM_EQ; FORALL_IN_GSPEC; IMP_CONJ;
              FORALL_AND_THM; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN
   EXISTS_TAC `PACK s` THEN
   ASM_SIMP_TAC[UNPACK_PACK] THEN
   EXISTS_TAC `PACK (IMAGE (\x. x,, f x) s)` THEN
   CONJ_TAC THENL
    ASM_SIMP_TAC[FUNC_ALT; IMAGE_IN_UU; UNPACK_PACK] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; PAIRSET_EQ] THEN
    REWRITE_TAC[IN_IMAGE; PAIRSET_EQ] THEN MESON_TAC[]
   ;
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`\x. @y. x,,y IN UNPACK g`; `UNPACK s`] THEN
    REWRITE_TAC[UNPACK_IN_UU; FUNC] THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC[PAIRSET_EQ] THEN MATCH_MP_TAC UNPACK_INJ THEN
    SIMP_TAC[UNPACK_PACK; IMAGE_IN_UU; UNPACK_IN_UU] THEN
    REWRITE_TAC[EXTENSION_ALT; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     INTRO_TAC "![p]; p" THEN FIRST_X_ASSUM
       (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `p IN UNPACK g`)) THEN
     POP_ASSUM SUBST_VAR_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
     ASM_MESON_TAC[]
    ;
     REPEAT STRIP_TAC THEN


  );;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)



let FUNC = new_definition
  `(FUNC) f s = PACK s,,(IMAGE (\x. x,,f x) s)`

let ELEFUN = new_definition
  `s => t =
   {f | s IN UU /\
        t IN UU /\
        IMAGE f s SUBSET t /\
        (!x. ~(x IN s) ==> f x = PACK (IMAGE f s))}`;;

let IN_ELEFUN = prove
 (`!f s t. f IN s => t <=>
           s IN UU /\
           t IN UU /\
           IMAGE f s SUBSET t /\
           (!x. ~(x IN s) ==> f x = PACK (IMAGE f s))`,
  REWRITE_TAC[ELEFUN; IN_ELIM_THM]);;

let FUNPACK = new_definition
 (`FUNPACK g x =
   @y. x,,y IN UNPACK g /\
       `);;


(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(* Domain and codomain (defined for all binary relations)                    *)
(* ------------------------------------------------------------------------- *)

let DOMAIN = new_definition
  `!r. DOMAIN r = {x | ?y. x,,y IN UNPACK r}`;;

let DOMAIN_IN_UU = prove
 (`!r. DOMAIN r IN UU`,
  GEN_TAC THEN REWRITE_TAC[DOMAIN] THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `IMAGE PROJ1 (UNPACK r)` THEN
  SIMP_TAC[IMAGE_IN_UU; UNPACK_IN_UU] THEN SET_TAC[PROJ1_PAIRSET]);;

let IN_DOMAIN = prove
 (`!r x. x IN DOMAIN r <=> ?y. (x,,y) IN UNPACK r`,
  REWRITE_TAC[DOMAIN; GSYM IMP_ANTISYM_EQ; FORALL_AND_THM] THEN
  SET_TAC[]);;

let FORALL_IN_DOMAIN = prove
 (`!r. (!x. x IN DOMAIN r ==> P x) <=> (!x y. x,,y IN UNPACK r ==> P x)`,
  REWRITE_TAC[IN_DOMAIN] THEN MESON_TAC[]);;

let DOMAIN_SUBSET_EQ = prove
 (`!r s t. DOMAIN r SUBSET s <=> (!x y. x,,y IN UNPACK r ==> x IN s)`,
  REWRITE_TAC[SUBSET; FORALL_IN_DOMAIN]);;

let DOMAIN_SUBSET = prove
 (`!r s t. r IN s RELSET t ==> DOMAIN r SUBSET s`,
  REWRITE_TAC[IN_RELSET; DOMAIN_SUBSET_EQ] THEN
  SET_TAC[PAIRSET_IN_CROSSSET_EQ]);;

let DOMAIN_EQ = prove
 (`!f s. DOMAIN f = s <=> (!x. x IN s <=> ?y. x,,y IN UNPACK f)`,
  REWRITE_TAC[EXTENSION; IN_DOMAIN] THEN MESON_TAC[]);;

let CODOMAIN = new_definition
  `!r. CODOMAIN r = {y | ?x. x,,y IN UNPACK r}`;;

let CODOMAIN_IN_UU = prove
 (`!r. CODOMAIN r IN UU`,
  GEN_TAC THEN REWRITE_TAC[CODOMAIN] THEN MATCH_MP_TAC SUBSET_IN_UU THEN
  EXISTS_TAC `IMAGE PROJ2 (UNPACK r)` THEN
  SIMP_TAC[IMAGE_IN_UU; UNPACK_IN_UU] THEN SET_TAC[PROJ2_PAIRSET]);;

let IN_CODOMAIN = prove
 (`!r y. y IN CODOMAIN r <=> ?x. (x,,y) IN UNPACK r`,
  REWRITE_TAC[CODOMAIN; GSYM IMP_ANTISYM_EQ; FORALL_AND_THM] THEN SET_TAC[]);;

let FORALL_IN_CODOMAIN = prove
 (`!r. (!y. y IN CODOMAIN r ==> P y) <=> (!x y. x,,y IN UNPACK r ==> P y)`,
  REWRITE_TAC[IN_CODOMAIN] THEN MESON_TAC[]);;

let CODOMAIN_SUBSET_EQ = prove
 (`!r s t. CODOMAIN r SUBSET t <=> (!x y. x,,y IN UNPACK r ==> y IN t)`,
  REWRITE_TAC[SUBSET; FORALL_IN_CODOMAIN]);;

let CODOMAIN_SUBSET = prove
 (`!r s t. r IN s RELSET t ==> CODOMAIN r SUBSET t`,
  REWRITE_TAC[IN_RELSET; CODOMAIN_SUBSET_EQ] THEN
  SET_TAC[PAIRSET_IN_CROSSSET_EQ]);;

let CODOMAIN_EQ = prove
 (`!f t. CODOMAIN f = t <=> (!y. y IN t <=> ?x. x,,y IN UNPACK f)`,
  REWRITE_TAC[EXTENSION; IN_CODOMAIN] THEN MESON_TAC[]);;



(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)




(* ------------------------------------------------------------------------- *)
(* Functional relations.                                                     *)
(* ------------------------------------------------------------------------- *)

let FUNCTIONAL = new_definition
  `FUNCTIONAL f <=> (!p. p IN UNPACK f ==> ?x y. p = x,,y) /\
                    (!x y1 y2. x,,y1 IN UNPACK f /\ x,,y2 IN UNPACK f
                               ==> y1 = y2)`;;

let FUNCTIONAL_IN_RELSET = prove
 (`!f. FUNCTIONAL f ==> f IN DOMAIN f RELSET CODOMAIN f`,
  GEN_TAC THEN REWRITE_TAC[FUNCTIONAL] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_RELSET; SUBSET] THEN INTRO_TAC "![p]; p" THEN
  USE_THEN "p" MP_TAC THEN REMOVE_THEN "p"
    (fun th -> FIRST_X_ASSUM (STRUCT_CASES_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[PAIRSET_IN_CROSSSET_EQ; IN_DOMAIN; IN_CODOMAIN] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set of partial functions.                                                 *)
(* ------------------------------------------------------------------------- *)

let IN_PFUNCSET = (specify o prove)
 (`!s t. ?(~~>). !f.
     f IN (~~>) <=>
     FUNCTIONAL f /\ DOMAIN f SUBSET s /\ CODOMAIN f SUBSET t`,
  REPEAT GEN_TAC THEN EXISTS_TAC
    `{r | r IN s RELSET t /\
          (!x y1 y2. x,,y1 IN UNPACK r /\ x,,y2 IN UNPACK r ==> y1 = y2)}` THEN
  REWRITE_TAC[IN_RELSET; DOMAIN_SUBSET_EQ; CODOMAIN_SUBSET_EQ; SUBSET;
              IN_CROSSSET_CASES_EQ; FUNCTIONAL; IN_ELIM_THM] THEN
  MESON_TAC[PAIRSET_EQ]);;

let DOMAIN_PFUNCSET = prove
 (`!f s t. f IN s ~~> t ==> DOMAIN f SUBSET s`,
  SIMP_TAC[IN_PFUNCSET]);;

let CODOMAIN_PFUNCSET = prove
 (`!f s t. f IN s ~~> t ==> CODOMAIN f SUBSET t`,
  SIMP_TAC[IN_PFUNCSET]);;

let PFUNCSET_SUBSET_RELSET = prove
 (`!s t. s ~~> t SUBSET s RELSET t`,
  REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[IN_PFUNCSET; IN_RELSET; DOMAIN_SUBSET_EQ;
              CODOMAIN_SUBSET_EQ; FUNCTIONAL] THEN
  REWRITE_TAC[SUBSET; IN_CROSSSET_CASES_EQ] THEN MESON_TAC[]);;

(* 
let PFUNCSET_TARGET_SUPERSET = prove
 (`!f s t t'. f IN s ~~> t /\ t SUBSET t' ==> f IN s ~~> t'`,
  REWRITE_TAC[IN_PFUNCSET] THEN MESON_TAC[SUBSET_TRANS]);;

let PFUNCSET_TARGET_SUPERSET = prove
 (`!f s t t'. f IN s ~~> t /\ t SUBSET t' ==> f IN s ~~> t'`,
  REWRITE_TAC[IN_PFUNCSET] THEN MESON_TAC[SUBSET_TRANS]);;
*)

(* ------------------------------------------------------------------------- *)
(* Set of functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let IN_FUNCSET = (specify o prove)
 (`!s t. ?(=>).
     !f. f IN (=>) <=> FUNCTIONAL f /\ DOMAIN f = s /\ CODOMAIN f SUBSET t`,
  REPEAT GEN_TAC THEN EXISTS_TAC `{f | f IN s ~~> t /\ DOMAIN f = s}` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_PFUNCSET] THEN  MESON_TAC[SUBSET_REFL]);;

let FUNCTIONAL_FUNCSET = prove
 (`!f s t. f IN s => t ==> FUNCTIONAL f`,
  SIMP_TAC[IN_FUNCSET]);;

let DOMAIN_FUNCSET = prove
 (`!f s t. f IN s => t ==> DOMAIN f = s`,
  SIMP_TAC[IN_FUNCSET]);;

let CODOMAIN_FUNCSET = prove
 (`!f s t. f IN s => t ==> CODOMAIN f SUBSET t`,
  SIMP_TAC[IN_FUNCSET]);;

(*
let FUNCSET_TARGET_SUPERSET = prove
 (`!f s t t'. f IN s => t /\ t SUBSET t' ==> f IN s => t'`,
  REWRITE_TAC[IN_FUNCSET; SUBSET; IN_CROSSSET_CASES] THEN MESON_TAC[]);;
*)

let FUNCSET_CODOMAIN_SUPERSET = prove
 (`!f s t t'. f IN s => t /\ CODOMAIN f SUBSET t' ==> f IN s => t'`,
  REWRITE_TAC[IN_FUNCSET; SUBSET; IN_CROSSSET_CASES; IN_CODOMAIN] THEN
  MESON_TAC[]);;

let FUNSEC_SUBSET_PFUNCSET = prove
 (`!s t. s => t SUBSET s ~~> t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [SUBSET] THEN GEN_TAC THEN
  REWRITE_TAC[IN_FUNCSET] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_PFUNCSET; SUBSET_REFL]);;

let FUNCSET_SUBSET_RELSET = prove
 (`!s t. s => t SUBSET s RELSET t`,
  MESON_TAC[SUBSET_TRANS; PFUNCSET_SUBSET_RELSET; FUNSEC_SUBSET_PFUNCSET]);;

let FUNCTIONAL_IFF_FUNCSET = prove
 (`!f. FUNCTIONAL f <=> f IN DOMAIN f => CODOMAIN f`,
  GEN_TAC THEN
  REWRITE_TAC[FUNCTIONAL; IN_FUNCSET; SUBSET; IN_CROSSSET_CASES;
              IN_DOMAIN; IN_CODOMAIN] THEN
  EQ_TAC THEN STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  INTRO_TAC "!x y1 y2; y1 y2" THEN
  USE_THEN "y2" (fun th -> FIRST_ASSUM (MP_TAC o C MATCH_MP th)) THEN
  USE_THEN "y1" (fun th -> FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[PAIRSET_EQ] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Functional relation with specified domain.                                *)
(* ------------------------------------------------------------------------- *)

let FUNCTIONAL_ON = new_definition
  `!f s. f FUNCTIONAL_ON s <=> FUNCTIONAL f /\ DOMAIN f = s`;;

let FUNCTIONAL_ON_EXPLICIT = prove
 (`!f s. f FUNCTIONAL_ON s <=> (!p. p IN UNPACK f ==> ?x y. p = x,,y) /\
                               (!x y. x,,y IN UNPACK f ==> x IN s) /\
                               (!x. x IN s ==> ?!y. x,,y IN UNPACK f)`,
  REWRITE_TAC[FUNCTIONAL_ON; FUNCTIONAL; DOMAIN_EQ] THEN ASM_MESON_TAC[]);;

let FUNCTIONAL_IFF_FUNCTIONAL_ON = prove
 (`!f. FUNCTIONAL f <=> f FUNCTIONAL_ON DOMAIN f`,
  REWRITE_TAC[FUNCTIONAL_ON] THEN MESON_TAC[]);;

let DOMAIN_FUNCTIONAL_ON = prove
 (`!f s. f FUNCTIONAL_ON s ==> DOMAIN f = s`,
  REWRITE_TAC[FUNCTIONAL_ON] THEN MESON_TAC[]);;

let FUNCTIONAL_ON_IFF_FUNCSET = prove
 (`!f s. f FUNCTIONAL_ON s <=> f IN s => CODOMAIN f`,
  REWRITE_TAC[FUNCTIONAL_ON; IN_FUNCSET; SUBSET_REFL]);;

let FUNCSET_IFF_FUNCTIONAL_ON = prove
 (`!f s t. f IN s => t <=> f FUNCTIONAL_ON s /\ CODOMAIN f SUBSET t`,
  REWRITE_TAC[FUNCTIONAL_ON_IFF_FUNCSET] THEN
  MESON_TAC[CODOMAIN_FUNCSET; SUBSET_REFL; FUNCSET_CODOMAIN_SUPERSET]);;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)





(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)




(* ------------------------------------------------------------------------- *)
(* Objects.                                                                  *)
(* ------------------------------------------------------------------------- *)

let SENDMSG = new_definition
  `obj $$ s = obj AP (str s)`;;

let CARRIER = new_definition
  `CARRIER X = UNPACK (X$$"carrier")`;;

let obj_add = new_definition
  `obj_add X a b = (X$$"+") AP (a,,b)`;;

let obj_neg = new_definition
  `obj_neg X a = (X$$"--") AP a`;;

let obj_mul = new_definition
  `obj_mul X a b = (X$$"*") AP (a,,b)`;;

let obj_inv = new_definition
  `obj_inv X a = (X$$"inv") AP a`;;

let obj_unit = new_definition
  `obj_unit X = X$$"unit"`;;

let GEN_MONOID = new_definition
  `GEN_MONOID M op unit <=>
   (!x y. x IN M /\ y IN M ==> op x y IN M) /\
   unit IN M /\
   (!x y z. op x (op y z) = op (op x y) z) /\
   (!x. op unit x = x) /\
   (!x. op x unit = x)`;;

let SETUNCURRY = (specify o prove)
 (`!f. ?SETUNCURRY. !x y. SETUNCURRY (x,,y) :elem = f x y`,
  GEN_TAC THEN EXISTS_TAC `\p. f (PROJ1 p) (PROJ2 p) : elem` THEN
  REWRITE_TAC[PROJ1_PAIRSET; PROJ2_PAIRSET]);;

parse_as_infix("BINARY_OPERATOR_ON",get_infix_status "HAS_SIZE");;

let BINARY_OPERATOR_ON = new_definition
  `op BINARY_OPERATOR_ON s <=> op IN s PAIRSET s => s`

let SET_CARRIER = new_definition
  `SET_CARRIER X <=> str"carrier" X`


let SET_MONOID = new_definition
  `SET_MONOID M <=>
   {str"carrier",str"*",str"unit",str"inv"} SUBSET DOM M /\
   M$$"*" IN (CARRIER M PAIRSET CARRIER M) => CARRIER M /\
   obj_unit M IN CARRIER M /\
   obj_mul M

   GEN_MONOID (CARRIER M) (obj_mul M) (obj_unit M)`;;



(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)


(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)


(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)








(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)





(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)




(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)






(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)




(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)





(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

show_goal_variables ();;


(* ------------------------------------------------------------------------- *)
(* Function abstraction.                                                     *)
(* ------------------------------------------------------------------------- *)

let new_definition =

let UNPACK_FUNC = (specify o prove)
 (`!f s. s IN UU ==> ?(FUNC). UNPACK (FUNC) = {x,,f x | x | x IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNPACK] THEN
  MATCH_MP_TAC SUBSET_IN_UU THEN EXISTS_TAC `s CROSSSET IMAGE f s` THEN
  ASM_SIMP_TAC[CROSSSET_IN_UU; IMAGE_IN_UU] THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  SIMP_TAC[PAIRSET_IN_CROSSSET_EQ; FUN_IN_IMAGE]);;

let DOMAIN_FUNC = prove
 (`!f s. s IN UU ==> DOMAIN ((FUNC) f s) = s`,
  SIMP_TAC[DOMAIN_EQ; UNPACK_FUNC; IN_ELIM_THM; PAIRSET_EQ] THEN MESON_TAC[]);;

let IN_FUNC_CASES = prove
 (`!f s p. s IN UU
           ==> (p IN UNPACK ((FUNC) f s) <=> ?x. x IN s /\ p = x,,f x)`,
  SIMP_TAC[UNPACK_FUNC; IN_ELIM_THM]);;

let FORALL_IN_FUNC = prove
 (`!P f s. s IN UU ==> ((!p. p IN UNPACK ((FUNC) f s) ==> P p) <=>
                        (!x. x IN s ==> P (x,,f x)))`,
  SIMP_TAC[IN_FUNC_CASES] THEN MESON_TAC[]);;

let EXISTS_IN_FUNC = prove
 (`!P f s. s IN UU
           ==> ((?p. p IN UNPACK ((FUNC) f s) /\ P p) <=>
                (?x. x IN s /\ P (x,,f x)))`,
  SIMP_TAC[IN_FUNC_CASES] THEN MESON_TAC[]);;

let FUNCTIONAL_FUNC = prove
 (`!f s. FUNCTIONAL ((FUNC) f s)`,
  REWRITE_TAC[FUNCTIONAL; UNPACK_FUNC]
 )


let FUNC_IN_FUNCSET = prove
 (`!f s t. (FUNC) f s IN s => t <=> (!x. x IN s ==> f x IN t)`,
  REWRITE_TAC[IN_FUNCSET]

  REWRITE_TAC[IN_FUNCSET; DOMAIN_EQ; CODOMAIN_SUBSET; FUNCTIONAL;
              IN_FUNC; FORALL_IN_FUNC; PAIRSET_EQ] THEN
  MESON_TAC[]);;

let FUNC_FUNCTIONAL_ON = prove
 (`!f s. (FUNC) f s FUNCTIONAL_ON s`,
  REWRITE_TAC[FUNCTIONAL_ON; IN_FUNC; FORALL_IN_FUNC; PAIRSET_PROJ] THEN
  MESON_TAC[]);;

let DOMAIN_FUNC = prove
 (`!f s. DOMAIN ((FUNC) f s) = s`,
  REWRITE_TAC[DOMAIN_EQ; IN_FUNC] THEN MESON_TAC[]);;

let CODOMAIN_FUNC = prove
 (`!f s. CODOMAIN ((FUNC) f s) = Replacement f s`,
  REWRITE_TAC[CODOMAIN_EQ; IN_FUNC; IN_REPLACEMENT]);;

(* ------------------------------------------------------------------------- *)
(* Function application.                                                     *)
(* ------------------------------------------------------------------------- *)

let AP = new_definition
  `f AP x = @y. x,,y IN f`;;

let AP_UNIQUE = prove
 (`!f s x y. f FUNCTIONAL_ON s /\ x IN s /\ x,,y IN f ==> f AP x = y`,
  REWRITE_TAC[FUNCTIONAL_ON; AP] THEN MESON_TAC[]);;

let FUNC_AP = prove
 (`!x s. x IN s ==> (FUNC) f s AP x = f x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AP_UNIQUE THEN
  ASM_MESON_TAC[FUNC_FUNCTIONAL_ON; IN_FUNC]);;

let FUNCSET_AP_UNIQUE = time prove
 (`!f s t x y. f IN s => t /\ x IN s /\ x,,y IN f ==> f AP x = y`,
  REWRITE_TAC[FUNCSET_IFF_FUNCTIONAL_ON] THEN MESON_TAC[AP_UNIQUE]);;

let FUNCTIONAL_EXTENSIONALITY = prove
 (`!f g. FUNCTIONAL f /\
         FUNCTIONAL g /\
         DOMAIN f = DOMAIN g /\
         (!x. x IN DOMAIN f ==> f AP x = g AP x)
         ==> f = g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUNCTIONAL] THEN
  INTRO_TAC "(f1 f2) (g1 g2) eq1 eq2" THEN
  GEN_REWRITE_TAC I [SET_EQ] THEN FIX_TAC "[p]" THEN
  ASM_CASES_TAC `p IN f`  THEN ASM_REWRITE_TAC[] THEN
   REMOVE_THEN "f1" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `p IN f`))
   POP_ASSUM SUBST_VAR_TAC THEN
   CLAIM_TAC "x1" `x IN DOMAIN f` THEN
   [REWRITE_TAC[IN_DOMAIN] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   CLAIM_TAC "fx" `f AP x = y` THENL
   [
     MATCH_MP_TAC AP_UNIQUE
   ]
  );;

(* ------------------------------------------------------------------------- *)
(* Product set (i.e., dependent product).                                    *)
(* ------------------------------------------------------------------------- *)

let PRODSET_DEF = new_definition
  `Prodset s t =
   Separation (s => Unionset(Replacement t s))
              (\f. !x. x IN s ==> f AP x IN t x)`;;

let IN_PRODSET = prove
 (`!f. f IN Prodset s t <=>
       f FUNCTIONAL_ON s /\
       (!x. x IN s ==> f AP x IN t x)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[PRODSET_DEF; IN_SEPARATION] THENL
  [REWRITE_TAC[IN_SEPARATION; FUNCSET_IFF_FUNCTIONAL_ON] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "f fx" THEN ASM_REWRITE_TAC[FUNCSET_IFF_FUNCTIONAL_ON] THEN
  REWRITE_TAC[SUBSET; IN_CODOMAIN; IN_UNIONSET; IN_REPLACEMENT] THEN
  INTRO_TAC "![y]; @x. xy" THEN EXISTS_TAC `t (x:set):set` THEN
  CLAIM_TAC "x" `x IN s` THENL [ASM_MESON_TAC[FUNCTIONAL_ON]; ALL_TAC] THEN
  USE_THEN "x" (HYP_TAC "fx" o C MATCH_MP) THEN
  SUBGOAL_THEN `f AP x = y` SUBST_ALL_TAC THENL
  [MATCH_MP_TAC AP_UNIQUE THEN ASM_MESON_TAC[FUNCTIONAL_ON];
   ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Grothendieck universes.                                                   *)
(* ------------------------------------------------------------------------- *)

let GROTHENDIECK_UNIVERSE = new_definition
  `GROTHENDIECK_UNIVERSE u <=>
   (!x s. x IN s /\ s IN u ==> x IN u) /\
   (!x y. x IN u /\ y IN u ==> {x,y} IN u) /\
   (!x. x IN u ==> Powerset x IN u) /\
   (!s t. s IN u /\ (!x. x IN s ==> t x IN u)
          ==> Unionset (Replacement t s) IN u)`;;

let GUNIV_IN_TRANS = prove
 (`!u x s. GROTHENDIECK_UNIVERSE u /\ x IN s /\ s IN u ==> x IN u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

let GUNIV_2 = prove
 (`!u x y.
         GROTHENDIECK_UNIVERSE u /\ x IN u /\ y IN u
         ==> x INSERT y INSERT {} IN u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

let GUNIV_POWERSET = prove
 (`!u x. GROTHENDIECK_UNIVERSE u /\ x IN u ==> Powerset x IN u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

let GUNIV_UNIONFAM = prove
 (`!u s t.
         GROTHENDIECK_UNIVERSE u /\ s IN u /\ (!x. x IN s ==> t x IN u)
         ==> Unionset (Replacement t s) IN u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Axiomatic sets associated to HOL sets (predicates).                       *)
(* ------------------------------------------------------------------------- *)

let IS_SETOF = new_definition
  `IS_SETOF (s:A->bool, t:set, enc:A->set, dec:set->A) <=>
   (!x. x IN s ==> enc x IN t /\ dec (enc x) = x) /\
   (!y. y IN t ==> dec y IN s /\ enc (dec y) = y)`;;

(* prioritize_hol_set();;
prioritize_axset();; *)

let setof_tybij =
  (new_type_definition "setof" ("mk_setof","dest_setof") o prove)
  (`?p:(A->bool)#set#(A->set)#(set->A). IS_SETOF p`,
   EXISTS_TAC `({}:A->bool),{}:set,(\x:A.{}),(\y:set. ARB:A)` THEN
   REWRITE_TAC[IS_SETOF; NOT_IN_EMPTY; IN_EMPTYSET]);;

let holset = new_definition
  `holset (p:A setof) = FST (dest_setof p)`;;

let setof = new_definition
  `setof (p:A setof) = FST (SND (dest_setof p))`;;

let setencode = new_definition
  `setencode (p:A setof) = FST (SND (SND (dest_setof p)))`;;

let setdecode = new_definition
  `setdecode (p:A setof) = SND (SND (SND (dest_setof p)))`;;

let SETOF_CASES = prove
 (`!p:A setof. ?q.
     p = mk_setof q /\ IS_SETOF q`,
  MESON_TAC[setof_tybij]);;

let FORALL_SETOF = prove
 (`!P. (!p:A setof. P p) <=> (!q. IS_SETOF q ==> P (mk_setof q))`,
  MESON_TAC[setof_tybij]);;

let EXISTS_SETOF = prove
 (`!P. (?p:A setof. P p) <=> (?q. IS_SETOF q /\ P (mk_setof q))`,
  MESON_TAC[setof_tybij]);;

let SETDECODE_SETENCODE,SETENCODE_SETDECODE = (CONJ_PAIR o prove)
 (`(!p x:A. x IN holset p
            ==> setencode p x IN setof p /\
                setdecode p (setencode p x) = x) /\
   (!p:A setof y. y IN setof p
                  ==> setdecode p y IN holset p /\
                      setencode p (setdecode p y) = y)`,
  REWRITE_TAC[GSYM FORALL_AND_THM] THEN
  REWRITE_TAC[FORALL_SETOF; FORALL_PAIR_THM] THEN
  INTRO_TAC "![s] [t] [enc] [dec]; p" THEN
  HYP_TAC "p -> p'" (REWRITE_RULE[setof_tybij]) THEN
  ASM_REWRITE_TAC[holset; setof; setencode; setdecode] THEN
  HYP_TAC "p: p1 p2" (REWRITE_RULE[IS_SETOF]) THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* De Bruijn monads in set theory.                                           *)
(* ------------------------------------------------------------------------- *)

let IS_DBMONADSET = new_definition
  `IS_DBMONADSET (t,unit,bind) <=>
     unit IN nat => t /\
     bind IN (nat => t) Crossset t => t /\
     (!f g x. f IN nat => t /\ g IN nat => t /\ x IN t
              ==> bind AP (f,, bind AP (g,, x)) =
                  bind AP ((FUNC i. bind AP (f,, g AP i)) nat,, x)) /\
     (!f i. f IN nat => t /\ i IN nat
            ==> bind AP (f,,unit AP i) = f AP i) /\
     (!x. x IN t ==> bind AP (unit,, x) = x)`;;

let DBMONADSET = (new_specification ["DBMONADSET"] o prove)
 (`?DBMONADSET. !t unit bind.
     DBMONADSET (t,, unit,, bind) <=> IS_DBMONADSET (t, unit, bind)`,
  EXISTS_TAC
    `\m. ?t unit bind.
       m = (t,, unit,, bind) /\ IS_DBMONADSET (t, unit, bind)` THEN
  REWRITE_TAC[PAIRSET_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint union of axiomatic sets.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("Amalg",get_infix_status "UNION");;

let [IN_AMALG_RULES; AMALG_DISTINCTNESS; AMALG_INJECTIVITY], IN_AMALG_CASES =
 (splitlist CONJ_PAIR o new_specification ["Amalg";"Inl";"Inr"] o prove)
 (`?(Amalg) Inl Inr.
     ((!s t x. Inl x IN s Amalg t <=> x IN s) /\
      (!s t y. Inr y IN s Amalg t <=> y IN t)) /\
     (!x y. ~(Inl x = Inr y)) /\
     ((!x1 x2. Inl x1 = Inl x2 ==> x1 = x2) /\
      (!y1 y2. Inr y1 = Inr y2 ==> y1 = y2)) /\
     (!s t z. z IN s Amalg t <=>
               (?x. x IN s /\ z = Inl x) \/
               (?y. y IN t /\ z = Inr y))`,
  EXISTS_TAC
    `\s t. Separation (bool Crossset (s Un t))
            (\z. SNDSET z IN (if FSTSET z = true then s else t))` THEN
  EXISTS_TAC `\x. (true,,x)` THEN
  EXISTS_TAC `\x. (false,,x)` THEN
  REWRITE_TAC[IN_SEPARATION; PAIRSET_IN_CROSSSET; PAIRSET_PROJ;
              PAIRSET_EQ; BOOL_RULES; BOOL_DISTINCTNESS] THEN
  CONJ_TAC THENL [ST_TAC[]; REPEAT GEN_TAC] THEN
  REWRITE_TAC[IN_CROSSSET_CASES; IN_BOOL] THEN EQ_TAC THENL
  [REWRITE_TAC[IMP_CONJ]; ALL_TAC] THEN
  STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  ASM_REWRITE_TAC[PAIRSET_PROJ; PAIRSET_EQ; BOOL_DISTINCTNESS] THEN
  ASM_ST_TAC[]);;

let [IN_MAYBE_RULES; MAYBE_DISTINCTNESS; MAYBE_INJECTIVITY], IN_MAYBE_CASES =
 (splitlist CONJ_PAIR o new_specification ["Maybe";"Just";"Nothing"] o prove)
 (`?(Maybe:set->set) Just Nothing.
    ((!A x. x IN A ==> Just x IN Maybe A) /\
      (!A. Nothing IN Maybe A)) /\
    (!x. ~(Just x = Nothing)) /\
    (!x1 x2. Just x1 = Just x2 ==> x1 = x2) /\
    (!A y. y IN Maybe A <=> y = Nothing \/ ?x. x IN A /\ y = Just x)`,
  EXISTS_TAC `\A. A Amalg Singleton natzero` THEN
  EXISTS_TAC `Inl` THEN
  EXISTS_TAC `Inr natzero` THEN
  REWRITE_TAC[IN_AMALG_RULES; IN_SINGLETON; AMALG_DISTINCTNESS;
              AMALG_INJECTIVITY] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [IN_AMALG_CASES] THEN
  REWRITE_TAC[IN_SINGLETON] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

let [SET_OF_STRING_IN_STRINGSET;
     STRING_OF_SET_OF_STRING;
     SET_OF_STRING_OF_SET] = (CONJUNCTS o specify o prove)
 (`?stringset set_of_string string_of_set.
     (!s:string. set_of_string s IN stringset) /\
     (!s. string_of_set (set_of_string s) = s) /\
     (!s. s IN stringset ==> set_of_string (string_of_set s) = s)`,
  CHEAT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Objects.                                                                  *)
(* ------------------------------------------------------------------------- *)

let OBJSET = new_definition
  `OBJSET uu = stringset ~~> uu`;;

let METHOD = new_definition
  `ob>-s = ob AP set_of_string s`;;

let OBJ_EQ = prove
 (`!o1 o2.
     o1 = o2 <=>
     DOMAIN o1 = DOMAIN o2 /\
     (!s. s IN DOMAIN o1 ==> o1>-s = o2>-s)`,
  );;

(* ------------------------------------------------------------------------- *)
(* Lambda calculus.                                                          *)
(* ------------------------------------------------------------------------- *)

(*
let [IN_LTERM_RULES; LTERM_DISTINCTNESS; LTERM_INJECTIVITY], IN_LTERM_CASES =
 (splitlist CONJ_PAIR o
  new_specification ["LTerm";"LVar";"LApp";"LAbs"] o prove)
 (`?(LTerm:set->set) LVar LApp LAbs.
     ((!A x. x IN A ==> LVar x IN LTerm A) /\
      (!A s t. s IN LTerm A /\ t IN LTerm A ==> LApp s t IN LTerm A) /\
      (!A t. t IN LTerm (Maybe A) ==> LAbs t IN LTerm A)) /\
     ((!x s t. ~(LVar x = LApp s t)) /\
      (!x t. ~(LVar x = LAbs t)) /\
      (!s t u. ~(LApp s t = LAbs u))) /\
     ((!x1 x2. LVar x1 = LVar x2 ==> x1 = x2) /\
      (!s1 s2 t1 t2. LApp s1 t1 = LApp s2 t2 ==> s1 = s2 /\ t1 = t2) /\
      (!t1 t2. LAbs t1 = LAbs t2 ==> t1 = t2)) /\
     (!A u. u IN LTerm A <=>
            (?x. x IN A /\ u = LVar A) \/
            (?s t. s IN LTerm A /\ t IN LTerm A /\ u = LApp s t) \/
            (?t. t IN LTerm (Maybe A) /\ u = LAbs t))`,
  CHEAT_TAC);;
*)

(* ------------------------------------------------------------------------- *)
(* Monads.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*
let IS_MONADSET = new_definition
  `IS_MONADSET (M:set->set,unit,bind) <=>
     (!A a. a IN A ==> unit a IN M A) /\
     (!A B f. (!a. a In))
     unit IN nat => t /\
     bind IN (nat => t) Crossset t => t /\
     (!f g x. f IN nat => t /\ g IN nat => t /\ x IN t
              ==> bind AP (f,, bind AP (g,, x)) =
                  bind AP ((FUNC i. bind AP (f,, g AP i)) nat,, x)) /\
     (!f i. f IN nat => t /\ i IN nat
            ==> bind AP (f,,unit AP i) = f AP i) /\
     (!x. x IN t ==> bind AP (unit,, x) = x)`;;
 *)
(*
let MONAD = (new_specification ["MONAD"] o prove)
 (`?MONAD. !t unit bind.
     MONAD (t,, unit,, bind) <=>
     `,
  EXISTS_TAC
    `\m. ?t unit bind.
       m = (t,, unit,, bind) /\ IS_MONAD (t, unit, bind)` THEN
  REWRITE_TAC[PAIRSET_EQ] THEN MESON_TAC[]);;
*)

(* objects, arrows, source, target, identity, composition *)
let SETCATEGORY = new_definition
 (`SETCATEGORY uu =
     Separation (uu Crossset
                 uu Crossset
                 uu Crossset
                 uu Crossset
                 uu Crossset
                 uu)
       (\C. let obj = FSTSET C in
            let arr = FSTSET (SNDSET C) in
            let src = FSTSET (SNDSET (SNDSET C)) in
            let trg = FSTSET (SNDSET (SNDSET (SNDSET C))) in
            let idt = FSTSET (SNDSET (SNDSET (SNDSET (SNDSET C)))) in
            let comp = FSTSET (SNDSET (SNDSET (SNDSET (SNDSET (SNDSET C))))) in
            let hom = Separation (arr Crossset arr) (\p. trg (FSTSET p) )
            src IN arr => obj /\
            trg IN arr => obj /\
            idt IN obj => arr /\
            comp In

            `,)