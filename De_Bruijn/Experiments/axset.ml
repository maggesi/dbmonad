(* ========================================================================= *)
(* Axiomatic Set Theory in HOL Light.                                        *)
(*                                                                           *)
(* Copyright (c) 2020 Marco Maggesi                                          *)
(* ========================================================================= *)

needs "misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("In",get_infix_status "IN");;           (* Membership rel    *)
parse_as_infix("Sbset",get_infix_status "SUBSET");;    (* Subset rel        *)
parse_as_infix("Un",get_infix_status "UNION");;        (* Union             *)
parse_as_infix("Int",get_infix_status "INTER");;       (* Intersection      *)
parse_as_infix("Diffset",get_infix_status "DIFF");;    (* Difference        *)
parse_as_infix(",,",get_infix_status ",");;            (* Pairs             *)
parse_as_infix("Crossset",get_infix_status "CROSS");;  (* Cartesian product *)
parse_as_infix("Relset",get_infix_status "CROSS");;    (* Binary relations  *)
parse_as_infix("=>",get_infix_status ",");;            (* Function space    *)
parse_as_infix("~~>",get_infix_status "=>");;          (* Partial fun space *)
parse_as_infix("FUNCTIONAL_ON",(12, "right"));;        (* Functional rels   *)
parse_as_infix("AP",get_infix_status "$");;            (* Funct application *)
parse_as_infix(">-",get_infix_status "$");;            (* Methods           *)
parse_as_binder "FUNC";;                               (* Funct abstraction *)

(* ------------------------------------------------------------------------- *)
(* Universe of sets.                                                         *)
(* ------------------------------------------------------------------------- *)

new_type("set",0);;

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

new_constant("In",`:set->set->bool`);;
new_constant("Emptyset",`:set`);;
new_constant("Unionset",`:set->set`);;
new_constant("Powerset",`:set->set`);;
new_constant("Separation",`:set->(set->bool)->set`);;
new_constant("Replacement",`:(set->set)->set->set`);;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let SBSET = new_definition
  `s Sbset t <=> (!x. x In s ==> x In t)`;;

let INTERSET_DEF = new_definition
  `s Int t = Separation s (\x. x In t)`;;

let SINGLETON_DEF = new_definition
  `Singleton s = Replacement (\x. s) (Powerset Emptyset)`;;

let UN_DEF = new_definition
  `s Un t = Unionset (Replacement (\x. if x = Emptyset then s else t)
                                  (Powerset (Singleton Emptyset)))`;;

(* ------------------------------------------------------------------------- *)
(* Axioms.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SET_EQ = new_axiom
  `!s t. s = t <=> (!x. x In s <=> x In t)`;;

let IN_EMPTYSET = new_axiom
  `!x. ~(x In Emptyset)`;;

let IN_UNIONSET = new_axiom
  `!s x. x In Unionset s <=> ?t. x In t /\ t In s`;;

let IN_POWERSET = new_axiom
  `!s x. x In Powerset s <=> x Sbset s`;;

let IN_SEPARATION = new_axiom
  `!s p x. x In Separation s p <=> x In s /\ p x`;;

let IN_REPLACEMENT = new_axiom
  `!f s y. y In Replacement f s <=> ?x. x In s /\ y = f x`;;

let FOUNDATION_AX = new_axiom
  `!s. ~(s = Emptyset) ==> ?x. x In s /\ x Int s = Emptyset`;;

let INFINITY_SET = new_axiom
  `?s. Emptyset In s /\ !x. x In s ==> x Un Singleton x In s`;;

(* ------------------------------------------------------------------------- *)
(* Syntax for the empty set, insertion and set enumeration.                  *)
(* ------------------------------------------------------------------------- *)

make_overloadable "EMPTY" `:A`;;
make_overloadable "INSERT" `:A->B->B`;;

let prioritize_hol_set() =
  overload_interface("EMPTY",mk_mconst("EMPTY",`:A->bool`));
  overload_interface("INSERT",mk_mconst("INSERT",`:A->(A->bool)->(A->bool)`));;

prioritize_hol_set();;

overload_interface("EMPTY",`Emptyset:set`);;
overload_interface("INSERT",`Insset:set->set->set`);;

(* ------------------------------------------------------------------------- *)
(* Basic properties about the subset relation.                               *)
(* ------------------------------------------------------------------------- *)

let SBSET_REFL = prove
 (`!s. s Sbset s`,
  REWRITE_TAC[SBSET]);;

let SBSET_TRANS = prove
 (`!r s t. r Sbset s /\ s Sbset t ==> r Sbset t`,
  REWRITE_TAC[SBSET] THEN MESON_TAC[]);;

let SBSET_ANTISYM = prove
 (`!s t. s Sbset t /\ t Sbset s ==> s = t`,
  REWRITE_TAC[SBSET; SET_EQ] THEN MESON_TAC[]);;

let SBSET_ANTISYM_EQ = prove
 (`!s t. s = t <=> s Sbset t /\ t Sbset s`,
  MESON_TAC[SBSET_REFL; SBSET_ANTISYM]);;

let EMPTYSET_SBSET = prove
 (`!s. {} Sbset s`,
  REWRITE_TAC[SBSET; IN_EMPTYSET ]);;

let SBSET_EMPTYSET = prove
 (`!s. s Sbset {} <=> s = {}`,
  REWRITE_TAC[SBSET; IN_EMPTYSET ; SET_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties about singletons.                                        *)
(* ------------------------------------------------------------------------- *)

let IN_SINGLETON = prove
 (`!s x. x In Singleton s <=> x = s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SINGLETON_DEF; IN_REPLACEMENT] THEN
  SUBGOAL_THEN `!x. x In Powerset {} <=> x = {}`
    (fun th -> REWRITE_TAC[th; UNWIND_THM2]) THEN
  REWRITE_TAC[IN_POWERSET; SBSET_EMPTYSET]);;

let SINGLETON_NOT_EMPTY = prove
 (`~(Singleton s = {})`,
  GEN_REWRITE_TAC RAND_CONV [SET_EQ] THEN
  REWRITE_TAC[IN_SINGLETON; IN_EMPTYSET] THEN MESON_TAC[]);;

let SBSET_SINGLETON = prove
 (`!s x. s Sbset Singleton x <=> s = {} \/ s = Singleton x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [REWRITE_TAC[SBSET; IN_SINGLETON] THEN INTRO_TAC "hp" THEN
   ASM_CASES_TAC `x In s` THENL
   [DISJ2_TAC THEN ONCE_REWRITE_TAC[SET_EQ] THEN
    REWRITE_TAC[IN_SINGLETON] THEN ASM_MESON_TAC[];
    DISJ1_TAC THEN REWRITE_TAC[SET_EQ; IN_EMPTYSET] THEN ASM_MESON_TAC[]];
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC[EMPTYSET_SBSET; SBSET_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Characterization of intersection and union of sets.                       *)
(* ------------------------------------------------------------------------- *)

let IN_INT = prove
 (`!x s t. x In s Int t <=> x In s /\ x In t`,
  REWRITE_TAC[INTERSET_DEF; IN_SEPARATION]);;

let IN_UN = prove
 (`!x s t. x In s Un t <=> x In s \/ x In t`,
  REWRITE_TAC[UN_DEF; IN_UNIONSET; IN_REPLACEMENT;
              IN_POWERSET; SBSET_SINGLETON] THEN
  MESON_TAC[SINGLETON_NOT_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Global choice, derived as a consequence of the Hilbert choice operator    *)
(* of the ambient HOL Logic.                                                 *)
(* ------------------------------------------------------------------------- *)

let SETCHOICE =
  (new_specification ["SETCHOICE"] o REWRITE_RULE[SKOLEM_THM] o prove)
   (`!s. ?x. ~(s = {}) ==> x In s`,
    REWRITE_TAC[SET_EQ; IN_EMPTYSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Existence of an universe leads to Russell's paradox.                      *)
(* ------------------------------------------------------------------------- *)

let NOT_UNIVSET = prove
 (`~(?u. !s. s In u)`,
  REFUTE_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `?d. !s. s In d <=> ~(s In s)` (fun th -> MESON_TAC[th]) THEN
  EXISTS_TAC `Separation u (\s. ~(s In s))` THEN
  ASM_REWRITE_TAC[IN_SEPARATION]);;


(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* The foundation of Set Theory in HOL ends here.                            *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Overloading.                                                              *)
(* ------------------------------------------------------------------------- *)

let prioritize_axset() =
  prioritize_overload `:set`;;

prioritize_axset();;

(* ------------------------------------------------------------------------- *)
(* Basic automation procedure for set theory based on meson.                 *)
(* ------------------------------------------------------------------------- *)

let set_axset_rewrites,extend_axset_rewrites,axset_rewrites,axset_net =
  let rewrites = ref ([]:thm list)
  and conv_net = ref (empty_net: gconv net) in
  let rehash_convnet() =
    conv_net := itlist (net_of_thm true) (!rewrites) empty_net in
  let set_axset_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl; rehash_convnet())
  and extend_axset_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := union canon_thl !rewrites; rehash_convnet())
  and axset_rewrites() = !rewrites
  and axset_net() = !conv_net in
  set_axset_rewrites,extend_axset_rewrites,axset_rewrites,axset_net;;

extend_axset_rewrites
  [SBSET; SBSET_REFL; SBSET_EMPTYSET; EMPTYSET_SBSET; SBSET_SINGLETON;
   IN_EMPTYSET; IN_SEPARATION; IN_POWERSET; IN_UNIONSET; IN_REPLACEMENT;
   IN_SINGLETON; IN_UN; IN_INT];;

let ONCE_PURE_AXSET_REWRITE_CONV thl =
  GENERAL_REWRITE_CONV true ONCE_DEPTH_CONV (axset_net()) thl;;

let AXSET_RW_CONV thl =
  let net = merge_nets(basic_net(),axset_net()) in
  GENERAL_REWRITE_CONV true I net thl;;

let EXT_CONV : conv =
  let SET_EQ_CONV = GEN_REWRITE_CONV I [SET_EQ] in
  fun th ->
    (SET_EQ_CONV THENC CHANGED_CONV (ONCE_PURE_AXSET_REWRITE_CONV[])) th;;

let PRE_ST_CONV : conv =
  fun tm -> TOP_DEPTH_CONV (EXT_CONV ORELSEC AXSET_RW_CONV[]) tm;;

let ST_TAC =
  let LIST_MP_TAC thl =
    if thl = [] then ALL_TAC else MP_TAC (end_itlist CONJ thl) in
  fun thl ->
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    ASM LIST_MP_TAC thl THEN CONV_TAC PRE_ST_CONV THEN MESON_TAC[];;

let ASM_ST_TAC = ASM ST_TAC;;

let ST_RULE tm = prove(tm,ST_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Further basic properties and identities.                                  *)
(* ------------------------------------------------------------------------- *)

let UN_EMPTYSET = ST_RULE
  `(!s. s Un {} = s) /\ (!s. {} Un s = s)`;;

let UN_ACI = ST_RULE
  `p Un q = q Un p /\
   (p Un q) Un r = p Un q Un r /\
   p Un q Un r = q Un p Un r /\
   p Un p = p /\
   p Un p Un q = p Un q`;;

let UN_EQ_EMPTYSET = ST_RULE
  `!s t. s Un t = {} <=> s = {} /\ t = {}`;;

let FORALL_IN_UN = ST_RULE
  `!P s t. (!x. x In s Un t ==> P x) <=>
           (!x. x In s ==> P x) /\ (!x. x In t ==> P x)`;;

let EXISTS_IN_UN = ST_RULE
  `!P s t. (?x. x In s Un t /\ P x) <=>
           (?x. x In s /\ P x) \/ (?x. x In t /\ P x)`;;

let UN_SYM,UN_ASSOC,UN_IDEMP =
  let [UN_SYM; UN_ASSOC; _; UN_IDEMP; _] = CONJUNCTS UN_ACI in
  UN_SYM,GSYM UN_ASSOC,UN_IDEMP;;

let INT_EMPTYSET = ST_RULE
  `(!s. s Int {} = {}) /\ (!s. {} Int s = {})`;;

let INT_ACI = ST_RULE
  `p Int q = q Int p /\
   (p Int q) Int r = p Int q Int r /\
   p Int q Int r = q Int p Int r /\
   p Int p = p /\
   p Int p Int q = p Int q`;;

let INT_SYM,INT_ASSOC,INT_IDEMP =
  let [INT_SYM; INT_ASSOC; _; INT_IDEMP; _] = CONJUNCTS INT_ACI in
  INT_SYM,GSYM INT_ASSOC,INT_IDEMP;;

extend_axset_rewrites
  [UN_EMPTYSET; UN_IDEMP; UN_EQ_EMPTYSET; FORALL_IN_UN; EXISTS_IN_UN;
   INT_EMPTYSET; INT_IDEMP];;

let FORALL_IN_UNIONSET = ST_RULE
  `!P s. (!x. x In Unionset s ==> P x) <=>
         (!t. t In s ==> !x. x In t ==> P x)`;;

let EXISTS_IN_UNIONSET = ST_RULE
  `!P s. (?x. x In Unionset s /\ P x) <=>
         (?t. t In s /\ ?x. x In t /\ P x)`;;

let FORALL_IN_REPLACEMENT = ST_RULE
  `!P s f. (!y. y In Replacement f s ==> P y) <=>
           (!x. x In s ==> P (f x))`;;

let EXISTS_IN_REPLACEMENT = ST_RULE
  `!P s f. (?y. y In Replacement f s /\ P y) <=>
           (?x. x In s /\ P (f x))`;;

extend_axset_rewrites
  [FORALL_IN_UNIONSET; EXISTS_IN_UNIONSET;
   FORALL_IN_REPLACEMENT; EXISTS_IN_REPLACEMENT];;

(* ------------------------------------------------------------------------- *)
(* Simple consequences of the axiom of foundations.                          *)
(* ------------------------------------------------------------------------- *)

let INT_SINGLETON_DISJOINT = prove
 (`!s. s Int Singleton s = {}`,
  GEN_TAC THEN MP_TAC (SPEC `Singleton s` FOUNDATION_AX) THEN ST_TAC[]);;

let IN_REFL = prove
 (`!s. ~(s In s)`,
  ST_TAC[INT_SINGLETON_DISJOINT]);;

let SINGLETON_SBSET_REFL = prove
 (`!s. ~(Singleton s Sbset s)`,
  ST_TAC[IN_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Set insertion (i.e., adding one an element to a set).                     *)
(* ------------------------------------------------------------------------- *)

let INSSET_DEF = new_definition
  `x INSERT s = Singleton x Un s`;;

(* Workaround for a bug?  See INSSET_SYM *)
overload_interface("EMPTY",`Emptyset:set`);;
overload_interface("INSERT",`Insset`);;
(* prioritize_axset();; *)

let IN_INSSET = prove
 (`!x y s. x In y INSERT s <=> x = y \/ x In s`,
  REWRITE_TAC[INSSET_DEF; IN_UN; IN_SINGLETON]);;

extend_axset_rewrites [IN_INSSET];;

let INSSET_ABSORPTION_IFF = ST_RULE
  `!x s. x INSERT s = s <=> x In s`;;

let INSSET_ABSORPTION = prove
 (`!x s. x In s ==> x INSERT s = s`,
  REWRITE_TAC[INSSET_ABSORPTION_IFF]);;

let INSSET_SYM = ST_RULE
  `!x y s. x INSERT y INSERT s = y INSERT x INSERT s`;;

let INSSET_IDEMP = ST_RULE
  `!x s. x INSERT x INSERT s = x INSERT s`;;

let INSSET_NOT_EMPTY = ST_RULE
  `!x s. ~(x INSERT s = {})`;;

extend_axset_rewrites [COND_RAND; COND_EXPAND];;

let INSSET_INT = ST_RULE
  `!a s t. a INSERT s Int t = if a In t then a INSERT (s Int t) else s Int t`;;

let INSSET_UN = ST_RULE
  `!a s t. a INSERT s Un t = if a In t then s Un t else a INSERT (s Un t)`;;

let FORALL_IN_INSSET = ST_RULE
  `!P a s. (!x. x In a INSERT s ==> P x) <=> P a /\ (!x. x In s ==> P x)`;;

let EXISTS_IN_INSSET = ST_RULE
  `!P a s. (?x. x In a INSERT s /\ P x) <=> P a \/ (?x. x In s /\ P x)`;;

let UNIONSET_CLAUSES = ST_RULE
  `Unionset {} = {} /\
   (!a s. Unionset (a INSERT s) = a Un Unionset s)`;;

let UNIONSET_EMPTYSET,UNIONSET_INSSET = CONJ_PAIR UNIONSET_CLAUSES;;

let UNIONSET_SINGLETON = ST_RULE
  `!x. Unionset (Singleton x) = x`;;

let UNIONSET_UN = ST_RULE
  `!s t. Unionset (s Un t) = Unionset s Un Unionset t`;;

extend_axset_rewrites
  [INSSET_ABSORPTION_IFF; INSSET_SYM; INSSET_IDEMP; INSSET_NOT_EMPTY;
   FORALL_IN_INSSET; EXISTS_IN_INSSET; UNIONSET_EMPTYSET; UNIONSET_SINGLETON;
   UNIONSET_UN];;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let DIFFSET_DEF = new_definition
  `s Diffset t = Separation s (\x. ~(x In t))`;;

let IN_DIFFSET = prove
 (`!s t x. x In s Diffset t <=> x In s /\ ~(x In t)`,
  REWRITE_TAC[DIFFSET_DEF; IN_SEPARATION]);;

extend_axset_rewrites [IN_DIFFSET];;

let DIFFSET_CLAUSES = ST_RULE
  `(!s. {} Diffset s = {}) /\
   (!a s. a INSERT s Diffset t =
          if a In t then s Diffset t else a INSERT (s Diffset t))`;;

let DIFFSET_REFL = ST_RULE
  `!s. s Diffset s = {}`;;

let DIFFSET_EQ_EMPTYSET = ST_RULE
  `!s t. s Diffset t = {} <=> s Sbset t`;;

extend_axset_rewrites [DIFFSET_CLAUSES; DIFFSET_REFL; DIFFSET_EQ_EMPTYSET];;

(* ------------------------------------------------------------------------- *)
(* Finite sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let FINSET_RULES,FINSET_INDUCT,FINSET_CASES = new_inductive_definition
  `FINSET {} /\
   (!x s. FINSET s ==> FINSET (x INSERT s))`;;

let FINSET_INDUCT_STRONG =
  derive_strong_induction (FINSET_RULES,FINSET_INDUCT);;

(* ------------------------------------------------------------------------- *)
(* Intersection of a family.                                                 *)
(* ------------------------------------------------------------------------- *)

let IN_INTSET =
 (new_specification ["Intset"] o REWRITE_RULE[SKOLEM_THM] o prove)
 (`!s. ?r. ~(s = {}) ==> (!x. x In r <=> !t. t In s ==> x In t)`,
  REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN
  CLAIM_TAC "@t0. t0" `?t0. t0 In s` THENL
  [POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[SET_EQ] THEN
   REWRITE_TAC[IN_EMPTYSET] THEN MESON_TAC[];
   EXISTS_TAC `Separation t0 (\x. !t. t In s ==> x In t)`] THEN
   REWRITE_TAC[IN_SEPARATION] THEN ASM_MESON_TAC[]);;

let INTSET_SINGLETON = prove
 (`!x. Intset (Singleton x) = x`,
  ONCE_REWRITE_TAC[SET_EQ] THEN
  SIMP_TAC[IN_INTSET; SINGLETON_NOT_EMPTY] THEN
  REWRITE_TAC[IN_SINGLETON; FORALL_UNWIND_THM2]);;

let INTSET_INSSET = prove
 (`!s u. Intset(s INSERT u) = if u = {} then s else s Int Intset u`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [SET_EQ] THEN
  GEN_TAC THEN SIMP_TAC[IN_INTSET; INSSET_NOT_EMPTY] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[FORALL_IN_INSSET; IN_EMPTYSET; IN_INT] THEN
  ASM_SIMP_TAC[IN_INTSET]);;

extend_axset_rewrites[IN_INTSET; INTSET_SINGLETON];;

(* ------------------------------------------------------------------------- *)
(* Cartesian product and pairs.                                              *)
(* ------------------------------------------------------------------------- *)

let PAIRSET_DEF = new_definition
  `x,,y = {{x},{x,y}}`;;

let FSTSET_DEF = new_definition
  `FSTSET p = Unionset(Intset p)`;;

let SNDSET_DEF = new_definition
  `SNDSET p =
     let u = Unionset p Diffset Intset p in
     Unionset(if u = {} then Unionset p else u)`;;

let PAIRSET_PROJ = prove
 (`(!x y. FSTSET (x,,y) = x) /\
   (!x y. SNDSET (x,,y) = y)`,
  REWRITE_TAC[PAIRSET_DEF; FSTSET_DEF; SNDSET_DEF;
    UNIONSET_INSSET; UNIONSET_EMPTYSET; INTSET_INSSET;
    INSSET_UN; UN_EMPTYSET; INSSET_INT; INT_EMPTYSET; DIFFSET_CLAUSES;
    IN_INSSET; IN_EMPTYSET; INSSET_NOT_EMPTY] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[UNIONSET_CLAUSES; UN_EMPTYSET; UN_IDEMP; INSSET_NOT_EMPTY]);;

let PAIRSET_EQ = prove
 (`!x1 x2 y1 y2. x1,,y1 = x2,,y2 <=> x1 = x2 /\ y1 = y2`,
  MESON_TAC[PAIRSET_PROJ]);;

let CROSSSET_DEF = new_definition
  `s Crossset t = Separation (Powerset (Powerset (s Un t)))
                             (\p. ?x y. p = x,,y /\ x In s /\ y In t)`;;

let CROSSSET_PROJ_IN = prove
 (`!p s t. p In s Crossset t ==> FSTSET p In s /\ SNDSET p In t`,
  REWRITE_TAC[CROSSSET_DEF; IN_SEPARATION; IN_POWERSET] THEN
  REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  ASM_REWRITE_TAC[PAIRSET_PROJ]);;

let IN_CROSSSET_CASES = prove
 (`!p s t. p In s Crossset t <=> ?x y. x In s /\ y In t /\ p = x,,y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CROSSSET_DEF; IN_SEPARATION; IN_POWERSET] THEN
  EQ_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[PAIRSET_DEF] THEN ASM_ST_TAC[];
   REWRITE_TAC[PAIRSET_EQ] THEN ASM_MESON_TAC[]]);;

let PAIRSET_IN_CROSSSET = prove
 (`!s t x y. x,,y In s Crossset t <=> x In s /\ y In t`,
  REWRITE_TAC[IN_CROSSSET_CASES; PAIRSET_EQ] THEN MESON_TAC[]);;

let FORALL_IN_CROSSSET = prove
 (`!P s t. (!p. p In s Crossset t ==> P p) <=>
           (!x y. x In s /\ y In t ==> P(x,,y))`,
  REWRITE_TAC[IN_CROSSSET_CASES] THEN ASM_MESON_TAC[]);;

let EXISTS_IN_CROSSSET = prove
 (`!P s t. (?p. p In s Crossset t /\ P p) <=>
           (?x y. x In s /\ y In t /\ P(x,,y))`,
  REWRITE_TAC[IN_CROSSSET_CASES] THEN ASM_MESON_TAC[]);;

extend_axset_rewrites [PAIRSET_PROJ; PAIRSET_EQ; PAIRSET_IN_CROSSSET;
  FORALL_IN_CROSSSET; EXISTS_IN_CROSSSET];;

(*
let IS_PAIRSET_RULES,IS_PAIRSET_INDUCT,IS_PAIRSET_CASES =
  new_inductive_definition
  `!x y. IS_PAIRSET (x,, y)`;;

let IN_CROSSET_IS_PAIRSET = prove
 (`!p s t. p In s Crossset t ==> IS_PAIRSET p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_CROSSSET_CASES] THEN
  DISCH_THEN STRUCT_CASES_TAC THEN REWRITE_TAC[IS_PAIRSET_RULES]);;

let CARTESIAN_RULES,CARTESIAN_INDUCT,CARTESIAN_CASES = new_inductive_definition
  `!s t. CARTESIAN (s Crossset t)`;;
*)

(* ------------------------------------------------------------------------- *)
(* Set of natural numbers.                                                   *)
(* ------------------------------------------------------------------------- *)

let NAT_EXIST = prove
 (`?nat inc zero suc.
     (!n:num. inc n In nat) /\
     (!m n. inc m = inc n ==> m = n) /\
     (!n. n In nat ==> ?m. n = inc m) /\
     (inc 0 = zero) /\
     (!n. inc (SUC n) = suc (inc n))`,
  DESTRUCT_TAC "@u. u0 u1" INFINITY_SET THEN
  (DESTRUCT_TAC "@N. Nrules Nind Ncases" o prove_inductive_relations_exist)
    `N Emptyset /\
     (!n. N n ==> N (n Un Singleton n))` THEN
  USE_THEN "Nrules" (fun th1 -> USE_THEN "Nind"
    (fun th2 -> LABEL_TAC "Nind'" (derive_strong_induction(th1,th2)))) THEN
  HYP_TAC "Nrules:zero suc" I THEN
  CLAIM_TAC "N" `!n. N n ==> n In u` THENL
  [REMOVE_THEN "Nind" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (DESTRUCT_TAC "@inc. inc0 inc1" o
   prove_recursive_functions_exist num_RECURSION)
    `inc 0 = Emptyset /\ (!n. inc (SUC n) = inc n Un Singleton (inc n))` THEN
  MAP_EVERY EXISTS_TAC
    [`Separation u N`; `inc:num->set`; `{}`; `\n. n Un Singleton n`] THEN
  HYP REWRITE_TAC "inc0 inc1" [] THEN
  CONJ_TAC THENL
  [LABEL_INDUCT_TAC THEN
   HYP REWRITE_TAC "inc0 inc1 u0 zero" [IN_SEPARATION] THEN ASM_ST_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "pre"
    `!n:num. Unionset (inc n Un Singleton (inc n)) = inc n` THENL
  [REWRITE_TAC[UNIONSET_UN; UNIONSET_SINGLETON] THEN
   LABEL_INDUCT_TAC THEN HYP REWRITE_TAC "inc0 inc1" [] THENL
   [ST_TAC[];
    HYP REWRITE_TAC "n_ind" [UNIONSET_UN; UNIONSET_SINGLETON; UN_ACI]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [LABEL_INDUCT_TAC THEN HYP REWRITE_TAC "inc0 inc1" [] THEN INDUCT_TAC THEN
   HYP REWRITE_TAC "inc0 inc1" [UN_EQ_EMPTYSET; SINGLETON_NOT_EMPTY] THENL
   [MESON_TAC[UN_EQ_EMPTYSET; SINGLETON_NOT_EMPTY]; ALL_TAC] THEN
   DISCH_THEN (MP_TAC o AP_TERM `Unionset`) THEN
   HYP REWRITE_TAC "pre m_ind" [SUC_INJ];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. n In Separation u N <=> N n`
    (fun th -> REWRITE_TAC[th]) THENL
  [HYP MESON_TAC "N" [IN_SEPARATION];
   REMOVE_THEN "Nind" MATCH_MP_TAC THEN HYP MESON_TAC "inc0 inc1" []]);;

(* ------------------------------------------------------------------------- *)
(* Injection of `:num` in sets.                                              *)
(* ------------------------------------------------------------------------- *)

let NAT_OF_NUM_IN_NAT,NAT_OF_NUM_INJ,NAT_OF_NUM_SURJ,NAT_OF_NUM_CLAUSES =
  let NAT_THM =
    new_specification ["nat"; "nat_of_num"; "Zero"; "Succ"] NAT_EXIST in
  let NAT_OF_NUM_IN_NAT,pth1 = CONJ_PAIR NAT_THM in
  let NAT_OF_NUM_INJ,pth2 = CONJ_PAIR pth1 in
  let NAT_OF_NUM_SURJ,NAT_OF_NUM_CLAUSES = CONJ_PAIR pth2 in
  NAT_OF_NUM_IN_NAT,NAT_OF_NUM_INJ,NAT_OF_NUM_SURJ,NAT_OF_NUM_CLAUSES;;

overload_interface("&",`nat_of_num`);;

let NAT_OF_NUM_EQ_ZERO = prove
 (`!n. &n = Zero <=> n = 0`,
  MESON_TAC[NAT_OF_NUM_CLAUSES; NAT_OF_NUM_INJ]);;

let NAT_OF_NUM_EQ = prove
 (`!m n. &m = &n <=> m = n`,
  MESON_TAC[NAT_OF_NUM_INJ]);;

(* ------------------------------------------------------------------------- *)
(* num_of_nat.                                                               *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_NAT_OF_NUM,NAT_OF_NUM_OF_NAT =
 (CONJ_PAIR o new_specification ["num_of_nat"] o prove)
 (`?num_of_nat. (!n. num_of_nat (nat_of_num n) = n) /\
                (!n. n In nat ==> nat_of_num (num_of_nat n) = n)`,
  EXISTS_TAC `\n. @m. n = nat_of_num m` THEN BETA_TAC THEN
  MESON_TAC[NAT_OF_NUM_INJ; NAT_OF_NUM_SURJ]);;

let NUM_OF_NAT_INJ = prove
 (`!m n. m In nat /\ n In nat /\ num_of_nat m = num_of_nat n ==> m = n`,
  REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o AP_TERM `nat_of_num`) THEN
  ASM_SIMP_TAC[NAT_OF_NUM_OF_NAT]);;

let NUM_OF_NAT_SURJ = prove
 (`!n. ?m. m In nat /\ n = num_of_nat m`,
  GEN_TAC THEN EXISTS_TAC `nat_of_num n` THEN
  REWRITE_TAC[NAT_OF_NUM_IN_NAT; NUM_OF_NAT_OF_NUM]);;

let FORALL_NAT = prove
 (`!P. (!n. n In nat ==> P n) <=> (!n. P (&n))`,
  MESON_TAC[NAT_OF_NUM_OF_NAT; NAT_OF_NUM_IN_NAT]);;

let NAT_EQ = prove
 (`!m n. m In nat /\ n In nat ==> (m = n <=> num_of_nat m = num_of_nat n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_NAT;
              NUM_OF_NAT_OF_NUM; NAT_OF_NUM_EQ]);;

let FORALL_NUM_OF_NAT = prove
 (`!P. (!n. P n) <=> (!n. n In nat ==> P (num_of_nat n))`,
  REWRITE_TAC[FORALL_NAT; NUM_OF_NAT_OF_NUM]);;

let NUM_OF_NAT_EQ_0 = prove
 (`!n. n In nat ==> (num_of_nat n = 0 <=> n = Zero)`,
  REWRITE_TAC[FORALL_NAT; NUM_OF_NAT_OF_NUM; NAT_OF_NUM_EQ_ZERO]);;

let COUNTABLE_IMP_EXISTS_SET = prove
 (`!s:A->bool. COUNTABLE s
               ==> ?t f g. (!x. x IN s ==> f x In t /\ g (f x) = x) /\
                           (!y. y In t ==> g y IN s /\ f (g y) = y)`,
  GEN_TAC THEN REWRITE_TAC[COUNTABLE; ge_c; le_c; IN_UNIV] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`Separation nat (\y. ?x:A. x IN s /\ y = nat_of_num(f x))`;
    `\x:A. nat_of_num(f x)`;
    `\y. @x:A. x IN s /\ y = nat_of_num(f x)`] THEN
  REWRITE_TAC[IN_SEPARATION; NAT_OF_NUM_IN_NAT; NAT_OF_NUM_EQ] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set of booleans.                                                          *)
(* ------------------------------------------------------------------------- *)

let BOOLSET_THM = (new_specification ["boolset";"True";"False"] o prove)
 (`?b t f. t In b /\
           f In b /\
           ~(t = f) /\
           (!x. x In b ==> x = t \/ x = f)`,
  EXISTS_TAC `Separation nat (\n. n = nat_of_num 0 \/ n = nat_of_num 1)` THEN
  EXISTS_TAC `nat_of_num 0` THEN
  EXISTS_TAC `nat_of_num 1` THEN
  REWRITE_TAC[IN_SEPARATION; NAT_OF_NUM_IN_NAT; NAT_OF_NUM_EQ; ARITH_EQ] THEN
  MESON_TAC[]);;

let BOOLSET_RULES = prove
 (`True In boolset /\ False In boolset`,
  MESON_TAC[BOOLSET_THM]);;

let BOOLSET_DISTINCTNESS = prove
 (`~(True = False)`,
  MESON_TAC[BOOLSET_THM]);;

let IN_BOOLSET = prove
 (`!b. b In boolset <=> b = True \/ b = False`,
  MESON_TAC[BOOLSET_THM]);;

let BOOLSET_CASES = prove
 (`!b. b In boolset ==> b = True \/ b = False`,
  REWRITE_TAC[IN_BOOLSET]);;

let FORALL_IN_BOOLSET = prove
 (`!P. (!b. b In boolset ==> P b) <=> P True /\ P False`,
  REWRITE_TAC[IN_BOOLSET] THEN MESON_TAC[]);;

let EXISTS_IN_BOOLSET = prove
 (`!P. (?b. b In boolset /\ P b) <=> P True \/ P False`,
  REWRITE_TAC[IN_BOOLSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Binary relations.                                                         *)
(* ------------------------------------------------------------------------- *)

let RELSET_DEF = new_definition
  `s Relset t = Powerset (s Crossset t)`;;

let IN_RELSET = prove
 (`!r s t. r In s Relset t <=> r Sbset s Crossset t`,
  REWRITE_TAC[RELSET_DEF; IN_POWERSET]);;

(* ------------------------------------------------------------------------- *)
(* Functional relations.                                                     *)
(* ------------------------------------------------------------------------- *)

let DOMAIN = new_definition
  `DOMAIN r = Separation (Replacement FSTSET r) (\x. ?y. x,,y In r)`;;

let IN_DOMAIN = prove
 (`!x r. x In DOMAIN r <=> ?y. x,,y In r`,
  REWRITE_TAC[DOMAIN; IN_SEPARATION; IN_REPLACEMENT] THEN
  MESON_TAC[PAIRSET_PROJ]);;

let CODOMAIN = new_definition
  `CODOMAIN r = Separation (Replacement SNDSET r) (\y. ?x. x,,y In r)`;;

let IN_CODOMAIN = prove
 (`!y r. y In CODOMAIN r <=> ?x. x,,y In r`,
  REWRITE_TAC[CODOMAIN; IN_SEPARATION; IN_REPLACEMENT] THEN
  MESON_TAC[PAIRSET_PROJ]);;

let DOMAIN_SBSET = prove
 (`!f s. DOMAIN f Sbset s <=> (!x y. x,,y In f ==> x In s)`,
  REWRITE_TAC[SBSET; IN_DOMAIN] THEN MESON_TAC[]);;

let CODOMAIN_SBSET = prove
 (`!f t. CODOMAIN f Sbset t <=> (!x y. x,,y In f ==> y In t)`,
  REWRITE_TAC[SBSET; IN_CODOMAIN] THEN MESON_TAC[]);;

let DOMAIN_EQ = prove
 (`!f s. DOMAIN f = s <=> (!x. x In s <=> ?y. x,,y In f)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SET_EQ] THEN
  REWRITE_TAC[IN_DOMAIN] THEN MESON_TAC[]);;

let CODOMAIN_EQ = prove
 (`!f t. CODOMAIN f = t <=> (!y. y In t <=> ?x. x,,y In f)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SET_EQ] THEN
  REWRITE_TAC[IN_CODOMAIN] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Functional relations.                                                     *)
(* ------------------------------------------------------------------------- *)

let FUNCTIONAL = new_definition
  `FUNCTIONAL f <=> (!p. p In f ==> ?x y. p = x,,y) /\
                    (!x y1 y2. x,,y1 In f /\ x,,y2 In f ==> y1 = y2)`;;

let FUNCTIONAL_IN_RELSET = prove
 (`!f. FUNCTIONAL f ==> f In DOMAIN f Relset CODOMAIN f`,
  GEN_TAC THEN REWRITE_TAC[FUNCTIONAL] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_RELSET; SBSET] THEN INTRO_TAC "![p]; p" THEN
  USE_THEN "p" MP_TAC THEN REMOVE_THEN "p"
    (fun th -> FIRST_X_ASSUM (STRUCT_CASES_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[PAIRSET_IN_CROSSSET; IN_DOMAIN; IN_CODOMAIN] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set of partial functions.                                                 *)
(* ------------------------------------------------------------------------- *)

let IN_PFUNCSET = (specify o prove)
 (`?(~~>). !f s t.
     f In s ~~> t <=>
     FUNCTIONAL f /\ DOMAIN f Sbset s /\ CODOMAIN f Sbset t`,
  EXISTS_TAC `\s t.
    Separation (s Relset t)
               (\r. !x y1 y2. x,,y1 In r /\ x,,y2 In r ==> y1 = y2)` THEN
  REWRITE_TAC[DOMAIN_SBSET; CODOMAIN_SBSET; IN_SEPARATION; IN_RELSET] THEN
  REWRITE_TAC[SBSET; IN_CROSSSET_CASES; FUNCTIONAL] THEN
  MESON_TAC[PAIRSET_EQ]);;

let DOMAIN_PFUNCSET = prove
 (`!f s t. f In s ~~> t ==> DOMAIN f Sbset s`,
  SIMP_TAC[IN_PFUNCSET]);;

let CODOMAIN_PFUNCSET = prove
 (`!f s t. f In s ~~> t ==> CODOMAIN f Sbset t`,
  SIMP_TAC[IN_PFUNCSET]);;

let PFUNCSET_TARGET_SUPERSET = prove
 (`!f s t t'. f In s ~~> t /\ t Sbset t' ==> f In s ~~> t'`,
  REWRITE_TAC[IN_PFUNCSET] THEN MESON_TAC[SBSET_TRANS]);;

let PFUNCSET_TARGET_SUPERSET = prove
 (`!f s t t'. f In s ~~> t /\ t Sbset t' ==> f In s ~~> t'`,
  REWRITE_TAC[IN_PFUNCSET] THEN MESON_TAC[SBSET_TRANS]);;

let PFUNCSET_SBSET_RELSET = prove
 (`!s t. s ~~> t Sbset s Relset t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [SBSET] THEN
  REWRITE_TAC[IN_PFUNCSET; IN_RELSET; DOMAIN_SBSET; CODOMAIN_SBSET;
              SBSET; IN_CROSSSET_CASES; FUNCTIONAL] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set of functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let IN_FUNCSET = (specify o prove)
 (`?(=>). !f s t.
     f In s => t <=>
     FUNCTIONAL f /\ DOMAIN f = s /\ CODOMAIN f Sbset t`,
  EXISTS_TAC `\s t. Separation (s ~~> t) (\f. DOMAIN f = s)` THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEPARATION; IN_PFUNCSET] THEN
  MESON_TAC[SBSET_REFL]);;

let FUNCTIONAL_FUNCSET = prove
 (`!f s t. f In s => t ==> FUNCTIONAL f`,
  SIMP_TAC[IN_FUNCSET]);;

let DOMAIN_FUNCSET = prove
 (`!f s t. f In s => t ==> DOMAIN f = s`,
  SIMP_TAC[IN_FUNCSET]);;

let CODOMAIN_FUNCSET = prove
 (`!f s t. f In s => t ==> CODOMAIN f Sbset t`,
  SIMP_TAC[IN_FUNCSET]);;

let FUNCSET_TARGET_SUPERSET = prove
 (`!f s t t'. f In s => t /\ t Sbset t' ==> f In s => t'`,
  REWRITE_TAC[IN_FUNCSET; SBSET; IN_CROSSSET_CASES] THEN MESON_TAC[]);;

let FUNCSET_CODOMAIN_SUPERSET = prove
 (`!f s t t'. f In s => t /\ CODOMAIN f Sbset t' ==> f In s => t'`,
  REWRITE_TAC[IN_FUNCSET; SBSET; IN_CROSSSET_CASES; IN_CODOMAIN] THEN
  MESON_TAC[]);;

let FUNSEC_SBSET_PFUNCSET = prove
 (`!s t. s => t Sbset s ~~> t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [SBSET] THEN GEN_TAC THEN
  REWRITE_TAC[IN_FUNCSET] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_PFUNCSET; SBSET_REFL]);;

let FUNCSET_SBSET_RELSET = prove
 (`!s t. s => t Sbset s Relset t`,
  MESON_TAC[SBSET_TRANS; PFUNCSET_SBSET_RELSET; FUNSEC_SBSET_PFUNCSET]);;

let FUNCTIONAL_IFF_FUNCSET = prove
 (`!f. FUNCTIONAL f <=> f In DOMAIN f => CODOMAIN f`,
  GEN_TAC THEN
  REWRITE_TAC[FUNCTIONAL; IN_FUNCSET; SBSET; IN_CROSSSET_CASES;
              IN_DOMAIN; IN_CODOMAIN] THEN
  EQ_TAC THEN STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  INTRO_TAC "!x y1 y2; y1 y2" THEN
  USE_THEN "y2" (fun th -> FIRST_ASSUM (MP_TAC o C MATCH_MP th)) THEN
  USE_THEN "y1" (fun th -> FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[PAIRSET_EQ] THEN ASM_MESON_TAC[]);;

let FUNCTIONAL_ON = new_definition
  `!f s. f FUNCTIONAL_ON s <=> (!p. p In f ==> ?x y. p = x,,y) /\
                               (!x y. x,,y In f ==> x In s) /\
                               (!x. x In s ==> ?!y. x,,y In f)`;;

let FUNCTIONAL_ON_IFF_FUNCTIONAL = prove
 (`!f s. f FUNCTIONAL_ON s <=> FUNCTIONAL f /\ DOMAIN f = s`,
  REWRITE_TAC[SET_EQ] THEN
  REWRITE_TAC[FUNCTIONAL_ON; FUNCTIONAL; IN_DOMAIN] THEN MESON_TAC[]);;

let FUNCTIONAL_IFF_FUNCTIONAL_ON = prove
 (`!f. FUNCTIONAL f <=> f FUNCTIONAL_ON DOMAIN f`,
  MESON_TAC[FUNCTIONAL_ON_IFF_FUNCTIONAL]);;

let DOMAIN_FUNCTIONAL_ON = prove
 (`!f s. f FUNCTIONAL_ON s ==> DOMAIN f = s`,
  MESON_TAC[FUNCTIONAL_ON_IFF_FUNCTIONAL]);;

let FUNCTIONAL_ON_IFF_FUNCSET = prove
 (`!f s. f FUNCTIONAL_ON s <=> f In s => CODOMAIN f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUNCTIONAL_ON; IN_FUNCSET; DOMAIN_EQ;
              SBSET_REFL; FUNCTIONAL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let FUNCSET_IFF_FUNCTIONAL_ON = prove
 (`!f s t. f In s => t <=> f FUNCTIONAL_ON s /\ CODOMAIN f Sbset t`,
  REWRITE_TAC[FUNCTIONAL_ON_IFF_FUNCSET] THEN
  MESON_TAC[CODOMAIN_FUNCSET; SBSET_REFL; FUNCSET_CODOMAIN_SUPERSET]);;

(* ------------------------------------------------------------------------- *)
(* Function abstraction.                                                     *)
(* ------------------------------------------------------------------------- *)

let FUNC_DEF = new_definition
  `(FUNC) f s = Separation (s Crossset Replacement f s)
                           (\p. ?x. x In s /\ p = (x,,f x))`;;

let IN_FUNC_CASES = prove
 (`!f s p. p In (FUNC) f s <=> ?x. x In s /\ p = x,,f x`,
  REWRITE_TAC[FUNC_DEF; IN_SEPARATION; IN_CROSSSET_CASES; IN_REPLACEMENT] THEN
  MESON_TAC[PAIRSET_EQ]);;

let IN_FUNC = prove
 (`!f s x y. x,,y In (FUNC) f s <=> x In s /\ y = f x`,
  REWRITE_TAC[FUNC_DEF; IN_SEPARATION; PAIRSET_IN_CROSSSET;
              IN_REPLACEMENT; PAIRSET_EQ] THEN
  MESON_TAC[]);;

let FORALL_IN_FUNC = prove
 (`!P f s. (!p. p In (FUNC) f s ==> P p) <=> (!x. x In s ==> P (x,,f x))`,
  REWRITE_TAC[IN_FUNC_CASES] THEN MESON_TAC[]);;

let EXISTS_IN_FUNC = prove
 (`!P f s. (?p. p In (FUNC) f s /\ P p) <=> (?x. x In s /\ P (x,,f x))`,
  REWRITE_TAC[IN_FUNC_CASES] THEN MESON_TAC[]);;

let FUNC_IN_FUNCSET = prove
 (`!f s t. (FUNC) f s In s => t <=> (!x. x In s ==> f x In t)`,
  REWRITE_TAC[IN_FUNCSET; DOMAIN_EQ; CODOMAIN_SBSET; FUNCTIONAL;
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
  `f AP x = @y. x,,y In f`;;

let AP_UNIQUE = prove
 (`!f s x y. f FUNCTIONAL_ON s /\ x In s /\ x,,y In f ==> f AP x = y`,
  REWRITE_TAC[FUNCTIONAL_ON; AP] THEN MESON_TAC[]);;

let FUNC_AP = prove
 (`!x s. x In s ==> (FUNC) f s AP x = f x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AP_UNIQUE THEN
  ASM_MESON_TAC[FUNC_FUNCTIONAL_ON; IN_FUNC]);;

let FUNCSET_AP_UNIQUE = time prove
 (`!f s t x y. f In s => t /\ x In s /\ x,,y In f ==> f AP x = y`,
  REWRITE_TAC[FUNCSET_IFF_FUNCTIONAL_ON] THEN MESON_TAC[AP_UNIQUE]);;

(*
let FUNCTIONAL_EXTENSIONALITY = prove
 (`!f g. FUNCTIONAL f /\
         FUNCTIONAL g /\
         DOMAIN f = DOMAIN g /\
         (!x. x In DOMAIN f ==> f AP x = g AP x)
         ==> f = g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUNCTIONAL] THEN
  INTRO_TAC "(f1 f2) (g1 g2) eq1 eq2" THEN
  GEN_REWRITE_TAC I [SET_EQ] THEN FIX_TAC "[p]" THEN
  ASM_CASES_TAC `p In f`  THEN ASM_REWRITE_TAC[] THEN
   REMOVE_THEN "f1" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `p In f`))
   POP_ASSUM SUBST_VAR_TAC THEN
   CLAIM_TAC "x1" `x In DOMAIN f` THEN
   [REWRITE_TAC[IN_DOMAIN] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   CLAIM_TAC "fx" `f AP x = y` THENL
   [
     MATCH_MP_TAC AP_UNIQUE
   ]
  );;
*)

(* ------------------------------------------------------------------------- *)
(* Product set (i.e., dependent product).                                    *)
(* ------------------------------------------------------------------------- *)

let PRODSET_DEF = new_definition
  `Prodset s t =
   Separation (s => Unionset(Replacement t s))
              (\f. !x. x In s ==> f AP x In t x)`;;

let IN_PRODSET = prove
 (`!f. f In Prodset s t <=>
       f FUNCTIONAL_ON s /\
       (!x. x In s ==> f AP x In t x)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[PRODSET_DEF; IN_SEPARATION] THENL
  [REWRITE_TAC[IN_SEPARATION; FUNCSET_IFF_FUNCTIONAL_ON] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "f fx" THEN ASM_REWRITE_TAC[FUNCSET_IFF_FUNCTIONAL_ON] THEN
  REWRITE_TAC[SBSET; IN_CODOMAIN; IN_UNIONSET; IN_REPLACEMENT] THEN
  INTRO_TAC "![y]; @x. xy" THEN EXISTS_TAC `t (x:set):set` THEN
  CLAIM_TAC "x" `x In s` THENL [ASM_MESON_TAC[FUNCTIONAL_ON]; ALL_TAC] THEN
  USE_THEN "x" (HYP_TAC "fx" o C MATCH_MP) THEN
  SUBGOAL_THEN `f AP x = y` SUBST_ALL_TAC THENL
  [MATCH_MP_TAC AP_UNIQUE THEN ASM_MESON_TAC[FUNCTIONAL_ON];
   ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Grothendieck universes.                                                   *)
(* ------------------------------------------------------------------------- *)

let GROTHENDIECK_UNIVERSE = new_definition
  `GROTHENDIECK_UNIVERSE u <=>
   (!x s. x In s /\ s In u ==> x In u) /\
   (!x y. x In u /\ y In u ==> {x,y} In u) /\
   (!x. x In u ==> Powerset x In u) /\
   (!s t. s In u /\ (!x. x In s ==> t x In u)
          ==> Unionset (Replacement t s) In u)`;;

let GUNIV_IN_TRANS = prove
 (`!u x s. GROTHENDIECK_UNIVERSE u /\ x In s /\ s In u ==> x In u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

let GUNIV_2 = prove
 (`!u x y.
         GROTHENDIECK_UNIVERSE u /\ x In u /\ y In u
         ==> x INSERT y INSERT {} In u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

let GUNIV_POWERSET = prove
 (`!u x. GROTHENDIECK_UNIVERSE u /\ x In u ==> Powerset x In u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

let GUNIV_UNIONFAM = prove
 (`!u s t.
         GROTHENDIECK_UNIVERSE u /\ s In u /\ (!x. x In s ==> t x In u)
         ==> Unionset (Replacement t s) In u`,
  MESON_TAC[GROTHENDIECK_UNIVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Axiomatic sets associated to HOL sets (predicates).                       *)
(* ------------------------------------------------------------------------- *)

let IS_SETOF = new_definition
  `IS_SETOF (s:A->bool, t:set, enc:A->set, dec:set->A) <=>
   (!x. x IN s ==> enc x In t /\ dec (enc x) = x) /\
   (!y. y In t ==> dec y IN s /\ enc (dec y) = y)`;;

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
            ==> setencode p x In setof p /\
                setdecode p (setencode p x) = x) /\
   (!p:A setof y. y In setof p
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
     unit In nat => t /\
     bind In (nat => t) Crossset t => t /\
     (!f g x. f In nat => t /\ g In nat => t /\ x In t
              ==> bind AP (f,, bind AP (g,, x)) =
                  bind AP ((FUNC i. bind AP (f,, g AP i)) nat,, x)) /\
     (!f i. f In nat => t /\ i In nat
            ==> bind AP (f,,unit AP i) = f AP i) /\
     (!x. x In t ==> bind AP (unit,, x) = x)`;;

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
     ((!s t x. Inl x In s Amalg t <=> x In s) /\
      (!s t y. Inr y In s Amalg t <=> y In t)) /\
     (!x y. ~(Inl x = Inr y)) /\
     ((!x1 x2. Inl x1 = Inl x2 ==> x1 = x2) /\
      (!y1 y2. Inr y1 = Inr y2 ==> y1 = y2)) /\
     (!s t z. z In s Amalg t <=>
               (?x. x In s /\ z = Inl x) \/
               (?y. y In t /\ z = Inr y))`,
  EXISTS_TAC
    `\s t. Separation (boolset Crossset (s Un t))
            (\z. SNDSET z In (if FSTSET z = True then s else t))` THEN
  EXISTS_TAC `\x. (True,,x)` THEN
  EXISTS_TAC `\x. (False,,x)` THEN
  REWRITE_TAC[IN_SEPARATION; PAIRSET_IN_CROSSSET; PAIRSET_PROJ;
              PAIRSET_EQ; BOOLSET_RULES; BOOLSET_DISTINCTNESS] THEN
  CONJ_TAC THENL [ST_TAC[]; REPEAT GEN_TAC] THEN
  REWRITE_TAC[IN_CROSSSET_CASES; IN_BOOLSET] THEN EQ_TAC THENL
  [REWRITE_TAC[IMP_CONJ]; ALL_TAC] THEN
  STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  ASM_REWRITE_TAC[PAIRSET_PROJ; PAIRSET_EQ; BOOLSET_DISTINCTNESS] THEN
  ASM_ST_TAC[]);;

let [IN_MAYBE_RULES; MAYBE_DISTINCTNESS; MAYBE_INJECTIVITY], IN_MAYBE_CASES =
 (splitlist CONJ_PAIR o new_specification ["Maybe";"Just";"Nothing"] o prove)
 (`?(Maybe:set->set) Just Nothing.
    ((!A x. x In A ==> Just x In Maybe A) /\
      (!A. Nothing In Maybe A)) /\
    (!x. ~(Just x = Nothing)) /\
    (!x1 x2. Just x1 = Just x2 ==> x1 = x2) /\
    (!A y. y In Maybe A <=> y = Nothing \/ ?x. x In A /\ y = Just x)`,
  EXISTS_TAC `\A. A Amalg Singleton Zero` THEN
  EXISTS_TAC `Inl` THEN
  EXISTS_TAC `Inr Zero` THEN
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
     (!s:string. set_of_string s In stringset) /\
     (!s. string_of_set (set_of_string s) = s) /\
     (!s. s In stringset ==> set_of_string (string_of_set s) = s)`,
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
     (!s. s In DOMAIN o1 ==> o1>-s = o2>-s)`,
  );;

(* ------------------------------------------------------------------------- *)
(* Lambda calculus.                                                          *)
(* ------------------------------------------------------------------------- *)

(*
let [IN_LTERM_RULES; LTERM_DISTINCTNESS; LTERM_INJECTIVITY], IN_LTERM_CASES =
 (splitlist CONJ_PAIR o
  new_specification ["LTerm";"LVar";"LApp";"LAbs"] o prove)
 (`?(LTerm:set->set) LVar LApp LAbs.
     ((!A x. x In A ==> LVar x In LTerm A) /\
      (!A s t. s In LTerm A /\ t In LTerm A ==> LApp s t In LTerm A) /\
      (!A t. t In LTerm (Maybe A) ==> LAbs t In LTerm A)) /\
     ((!x s t. ~(LVar x = LApp s t)) /\
      (!x t. ~(LVar x = LAbs t)) /\
      (!s t u. ~(LApp s t = LAbs u))) /\
     ((!x1 x2. LVar x1 = LVar x2 ==> x1 = x2) /\
      (!s1 s2 t1 t2. LApp s1 t1 = LApp s2 t2 ==> s1 = s2 /\ t1 = t2) /\
      (!t1 t2. LAbs t1 = LAbs t2 ==> t1 = t2)) /\
     (!A u. u In LTerm A <=>
            (?x. x In A /\ u = LVar A) \/
            (?s t. s In LTerm A /\ t In LTerm A /\ u = LApp s t) \/
            (?t. t In LTerm (Maybe A) /\ u = LAbs t))`,
  CHEAT_TAC);;
*)

(* ------------------------------------------------------------------------- *)
(* Monads.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*
let IS_MONADSET = new_definition
  `IS_MONADSET (M:set->set,unit,bind) <=>
     (!A a. a In A ==> unit a In M A) /\
     (!A B f. (!a. a In))
     unit In nat => t /\
     bind In (nat => t) Crossset t => t /\
     (!f g x. f In nat => t /\ g In nat => t /\ x In t
              ==> bind AP (f,, bind AP (g,, x)) =
                  bind AP ((FUNC i. bind AP (f,, g AP i)) nat,, x)) /\
     (!f i. f In nat => t /\ i In nat
            ==> bind AP (f,,unit AP i) = f AP i) /\
     (!x. x In t ==> bind AP (unit,, x) = x)`;;
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
            src In arr => obj /\
            trg In arr => obj /\
            idt In obj => arr /\
            comp In

            `,)