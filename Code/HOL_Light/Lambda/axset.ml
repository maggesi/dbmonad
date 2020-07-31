(* ========================================================================= *)
(* Axiomatic Set Theory in HOL Light.                                        *)
(*                                                                           *)
(* Copyright (c) 2020 Marco Maggesi                                          *)
(* ========================================================================= *)

(*
time loadt "Lambda/axset.ml";;
*)

let LABEL_ABBREV_TAC tm : tactic =
  let s = name_of (lhand tm) in
  ABBREV_TAC tm THEN POP_ASSUM (LABEL_TAC (s^"_def"));;

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

(* ------------------------------------------------------------------------- *)
(* Sintax for the empty set, insertion and set enumeration.                  *)
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
  `Singleton s = Replacement (\x. s) (Powerset {})`;;

let UN_DEF = new_definition
  `s Un t = Unionset (Replacement (\x. if x = {} then s else t)
                                  (Powerset (Singleton {})))`;;

(* ------------------------------------------------------------------------- *)
(* Axioms.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SET_EQ = new_axiom
  `!s t. s = t <=> (!x. x In s <=> x In t)`;;

let IN_EMPTYSET = new_axiom
  `!x. ~(x In {})`;;

let IN_UNIONSET = new_axiom
  `!s x. x In Unionset s <=> ?t. x In t /\ t In s`;;

let IN_POWERSET = new_axiom
  `!s x. x In Powerset s <=> x Sbset s`;;

let IN_SEPARATION = new_axiom
  `!s p x. x In Separation s p <=> x In s /\ p x`;;

let IN_REPLACEMENT = new_axiom
  `!f s y. y In Replacement f s <=> ?x. x In s /\ y = f x`;;

let FOUNDATION_AX = new_axiom
  `!s. ~(s = {}) ==> ?x. x In s /\ x Int s = {}`;;

let INFINITY_AX = new_axiom
  `?s. {} In s /\ !x. x In s ==> x Un Singleton x In s`;;

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
   IN_EMPTYSET; IN_SEPARATION; IN_POWERSET; IN_UNIONSET;
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
  [UN_EMPTYSET; UN_IDEMP; FORALL_IN_UN; EXISTS_IN_UN;
   INT_EMPTYSET; INT_IDEMP];;

(* ------------------------------------------------------------------------- *)
(* Simple consequences of the axiom of foundations.                          *)
(* ------------------------------------------------------------------------- *)

search[`s Int Singleton s`];;

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
overload_interface("INSERT",`Insset`);;
prioritize_axset();;

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

let FORALL_IN_UNIONSET = ST_RULE
  `!P s. (!x. x In Unionset s ==> P x) <=>
         (!t. t In s ==> !x. x In t ==> P x)`;;

let EXISTS_IN_UNIONSET = ST_RULE
  `!P s. (?x. x In Unionset s /\ P x) <=>
         (?t. t In s /\ ?x. x In t /\ P x)`;;

extend_axset_rewrites
  [INSSET_ABSORPTION_IFF; INSSET_SYM; INSSET_IDEMP; INSSET_NOT_EMPTY;
   FORALL_IN_INSSET; EXISTS_IN_INSSET; UNIONSET_EMPTYSET; UNIONSET_SINGLETON;
   UNIONSET_UN; FORALL_IN_UNIONSET; EXISTS_IN_UNIONSET];;

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
