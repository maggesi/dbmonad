(* ========================================================================= *)
(* Axiomatic Set Theory in HOL Light.                                        *)
(*                                                                           *)
(* Incomplete code and leftovers.                                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Parser for set enumerations.                                              *)
(* Now replaced by the standard HOL Light overloading mechanism.             *)
(* ------------------------------------------------------------------------- *)

let parse_axset_enum =
  let (++<) p q = p ++ q >> fst
  and (++>) p q = p ++ q >> snd
  and pmk_axset_enum ptms =
    itlist (fun x t -> Combp(Combp(Varp("Setins",dpty),x),t)) ptms
           (Varp("Emptyset",dpty))
  and list_body =
    elistof parse_preterm (a (Resword ";"))
      "semicolon separated list of terms" in
  a (Ident "set") ++ a (Resword "{") ++>
  (list_body >> pmk_axset_enum) ++<  a (Resword "}");;

(* Tests. *)
(*
(parse_axset_enum o lex o explode) "set{}";;
(parse_axset_enum o lex o explode) "set{x}";;
(parse_axset_enum o lex o explode) "set{x;y}";;
*)

install_parser("setax",parse_axset_enum);;

(* ------------------------------------------------------------------------- *)
(* Collecting elements from HOL sets.                                        *)
(* ------------------------------------------------------------------------- *)

(* 
let COLLECT_DEF = new_definition
  `Collect s = @t. !x. x In t <=> x IN s`;;

let IN_COLLECT_SUPERSET = prove
 (`!s. (?t. !x. x IN s ==> x In t) ==> (!x. x In Collect s <=> x IN s)`,
  REWRITE_TAC[COLLECT_DEF] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?t. !x. x IN s <=> x In t` (fun th -> MESON_TAC[th]) THEN
  EXISTS_TAC `Separation t (\x. x IN s)` THEN
  REWRITE_TAC[IN_SEPARATION] THEN ASM_MESON_TAC[]);;

let IN_COLLECT_FINITE = prove
 (`!s. FINITE s ==> (!x. x In Collect s <=> x IN s)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IN_COLLECT_SUPERSET THEN
  EXISTS_TAC `ITSET (Setins) s Emptyset` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC (`s:set->bool`,`s:set->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FINITE_RECURSION; FINITE_EMPTY; SETINS_SYM] THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_EMPTYSET] THEN INTRO_TAC "!x s; ind _ _" THEN
  REWRITE_TAC[FORALL_IN_INSERT; IN_SETINS] THEN ASM_SIMP_TAC[]);;

let COLLECT_CLAUSES = prove
 (`Collect {} = Emptyset /\
   (!x s. FINITE s ==> Collect (x INSERT s) = x Setins Collect s)`,
  CONJ_TAC THENL
  [ONCE_REWRITE_TAC[SET_EQ] THEN SIMP_TAC[IN_COLLECT_FINITE; FINITE_EMPTY] THEN
   REWRITE_TAC[NOT_IN_EMPTY; IN_EMPTYSET];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!s. FINITE s ==> !x. Collect (x INSERT s) = x Setins Collect s`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [SET_EQ] THEN
  ASM_SIMP_TAC[IN_COLLECT_FINITE; FINITE_EMPTY; FINITE_INSERT;
               IN_INSERT; NOT_IN_EMPTY; IN_SETINS; IN_EMPTYSET]);;

let COLLECT_SING = prove
 (`!x. Collect {x} = Singleton x`,
  GEN_TAC THEN SIMP_TAC[COLLECT_CLAUSES; FINITE_EMPTY; FINITE_INSERT] THEN
  GEN_REWRITE_TAC I [SET_EQ] THEN
  REWRITE_TAC[IN_SETINS; IN_EMPTYSET; IN_SINGLETON]);;
*)

(* ------------------------------------------------------------------------- *)
(* Small collection of sets.                                                 *)
(* ------------------------------------------------------------------------- *)

(*
let SMALL = new_definition
  `SMALL s <=> (?t. !x. x In t <=> x IN s)`;;

let SMALL_SUPERSET = prove
 (`!s. SMALL s <=> (?t. !x. x IN s ==> x In t)`,
  GEN_TAC THEN REWRITE_TAC[SMALL] THEN EQ_TAC THENL
  [MESON_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `Separation t (\x. x IN s)` THEN ASM_ST_TAC[]);;

let IN_COLLECT_SMALL = prove
 (`!s. SMALL s ==> (!x. x In Collect s <=> x IN s)`,
  REWRITE_TAC[SMALL; COLLECT_DEF] THEN MESON_TAC[]);;

let COLLECT_BIG = prove
 (`!s. ~SMALL s ==> Collect s = Collect (:set)`,
  GEN_TAC THEN REWRITE_TAC[SMALL; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[COLLECT_DEF; IN_UNIV; MESON[NOT_UNIV] `~(!x. x In t)`]);;
*)


(* ------------------------------------------------------------------------- *)
(* Set of natural numbers.                                                   *)
(* ------------------------------------------------------------------------- *)

let NATURALS_EXIST = prove
 (`?nat f g z s.
     (!n:num. f n In nat) /\
     (!m n. f m = f n ==> m = n) /\
     (!n. ?m. n = f m)`,
  DESTRUCT_TAC "@u. u0 u1" INFINITY_AX THEN
  (DESTRUCT_TAC "@N. Nrules Nind Ncases" o prove_inductive_relations_exist)
    `N Emptyset /\
     (!n. N n ==> N (n Un Singleton n))` THEN
  USE_THEN "Nrules" (fun th1 -> USE_THEN "Nind"
    (fun th2 -> LABEL_TAC "Nind'" (derive_strong_induction(th1,th2)))) THEN
  HYP_TAC "Nrules:z s" I THEN
  CLAIM_TAC "N" `!n. N n ==> n In u` THENL
  [REMOVE_THEN "Nind" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (DESTRUCT_TAC "@f. f0 f1" o prove_recursive_functions_exist num_RECURSION)
    `f 0 = Emptyset /\ (!n. f (SUC n) = f n Un Singleton (f n))` THEN
  MAP_EVERY EXISTS_TAC [`Separation u N`; `f:num->set`] THEN
  CONJ_TAC THENL
  INDUCT_TAC THEN HYP REWRITE_TAC "f0 f1 u0 z" [IN_SEPARATION]


let SINGLETON_NO_FIXPOINT = prove
 (`!x. ~(Singleton x = x)`,
  ST_TAC[FOUNDATION_AX]);;

let VON_NEUMANN_SUCC = new_definition
  `VON_NEUMANN_SUCC n = n Un Singleton n`;;

let VON_NEUMANN_NUMERAL = new_recursive_definition num_RECURSION
  `VON_NEUMANN_NUMERAL 0 = Emptyset /\
   (!n. VON_NEUMANN_NUMERAL (SUC n) = VON_NEUMANN_SUCC (VON_NEUMANN_NUMERAL n))`;;

let UNIONSET_VON_NEUMANN_SUCC = prove
 (`!n. Unionset (VON_NEUMANN_SUCC (VON_NEUMANN_NUMERAL n)) = VON_NEUMANN_NUMERAL n`,
  INDUCT_TAC THEN REWRITE_TAC[VON_NEUMANN_NUMERAL] THENL
  [REWRITE_TAC[VON_NEUMANN_SUCC] THEN ST_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [VON_NEUMANN_SUCC] THEN
  ASM_REWRITE_TAC[UNIONSET_UN; UNIONSET_SINGLETON] THEN
  MATCH_MP_TAC (ST_RULE `!s t. s Sbset t ==> s Un t = t`) THEN
  REWRITE_TAC[VON_NEUMANN_SUCC] THEN ST_TAC[]);;
  
let VON_NEUMANN_NUMERAL_INJ = prove
 (`!m n. VON_NEUMANN_NUMERAL m = VON_NEUMANN_NUMERAL n ==> m = n`,
  INDUCT_TAC THEN REWRITE_TAC[VON_NEUMANN_NUMERAL] THENL
  [INDUCT_TAC THEN REWRITE_TAC[VON_NEUMANN_NUMERAL; VON_NEUMANN_SUCC] THEN ST_TAC[];
   ALL_TAC]
  INDUCT_TAC THEN REWRITE_TAC[VON_NEUMANN_NUMERAL]
   ST_TAC[]
   REWRITE_TAC[VON_NEUMANN_SUCC]
  DISCH_THEN (MP_TAC o AP_TERM `Unionset`)
  ASM_REWRITE_TAC[UNIONSET_VON_NEUMANN_SUCC; SUC_INJ]



 )
?nat. !n. n In Nat <=> 

let VON_NEUMANN_NAT = new_definition
  `VON_NEUMANN_NAT = `;;

(* let IN_REFL = prove
 (`!s. ~(s In s)`,
  GEN_TAC THEN ASM_CASES_TAC `s = Emptyset` THENL
   POP_ASSUM SUBST_VAR_TAC THEN REWRITE_TAC[IN_EMPTYSET]
   POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP FOUNDATION_AX) *)

let EXISTS_NATURAL_NUMBERS = prove
 (`?NN z s.
     z In NN /\
     (!n. n In NN ==> s n In NN) /\
     (!n. ~(s n = z)) /\
     (!m n. s m = s n ==> m = n) /\
     (!n. n In NN ==> n = z \/ (?m. m In NN /\ n = s m)) /\
     (!P. P z /\ (!n. n In NN /\ P n ==> P (s n)) ==> (!n. n In NN ==> P n))`,
  DESTRUCT_TAC "@u. u0 u1" INFINITY_AX THEN
  (DESTRUCT_TAC "@N. Nrules Nind Ncases" o prove_inductive_relations_exist)
    `N Emptyset /\
     (!n. N n ==> N (n Un Singleton n))` THEN
  USE_THEN "Nrules" (fun th1 -> USE_THEN "Nind"
    (fun th2 -> LABEL_TAC "Nind'" (derive_strong_induction(th1,th2)))) THEN
  HYP_TAC "Nrules:z s" I THEN
  CLAIM_TAC "N" `!n. N n ==> n In u` THENL
  [REMOVE_THEN "Nind" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
    [`Separation u N`; `Emptyset`; `\n. n Un Singleton n`] THEN
  SUBGOAL_THEN `!n. n In Separation u N <=> N n`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[IN_SEPARATION] THEN HYP MESON_TAC "N" [];
   HYP REWRITE_TAC "z s" []] THEN
  CONJ_TAC THENL [ST_TAC[]; ALL_TAC] THEN
  CLAIM_TAC "pred" `!n. N n ==> Unionset (n Un Singleton n) = n` THENL
  [
    REMOVE_THEN "Nind" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ST_TAC[]; INTRO_TAC "!n; nind"] THEN
    ONCE_REWRITE_TAC[UNIONSET_UN]
    ST_TAC[]
    

  ]
  CONJ_TAC THENL [
    REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o AP_TERM `\s. Unionset s Setdiff s`)
    SUBGOAL_THEN `!m n x. m Un Singleton m = n Un Singleton n /\ x In m ==> x In n` (fun th -> MESON_TAC[th; SET_EQ]) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_EQ]
    REWRITE_TAC[IN_UN; IN_SINGLETON]
    ST_TAC[]
    REWRITE_TAC[IN_UN] THEN INTRO_TAC "e; !x"
    POP_ASSUM (MP_TAC o SPEC `x:set`)
    ASM_CASES_TAC `x In m` THEN ASM_REWRITE_TAC[]
    REWRITE_TAC[ASM_CASEES]
    ; ALL_TAC] THEN
  CONJ_TAC THENL [ST_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN
   REMOVE_THEN "Ncases" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
   MESON_TAC[];
   INTRO_TAC "!P; P0 P1" THEN REMOVE_THEN "Nind'" MATCH_MP_TAC THEN
   HYP REWRITE_TAC "P0 P1" []]);;

let [ZERO_IN_NN; SUCC_IN_NN; NOT_SUCC_ZERO; SUCC_INJ; NN_CASES; NN_INDUCT] =
  CONJUNCTS (new_specification ["NN"; "Zero"; "Succ"] EXISTS_NATURAL_NUMBERS);;

let SUCC_INJ_EQ = prove
 (`!m n. Succ m = Succ n <=> m = n`,
  MESON_TAC[SUCC_INJ]);;

let NN_OF_NUM = new_recursive_definition num_RECURSION
  `NN_OF_NUM 0 = Zero /\
   (!n. NN_OF_NUM (SUC n) = Succ (NN_OF_NUM n))`;;

overload_interface("&",`NN_OF_NUM`);;


(* let NN_OF_NUM_INJ = prove
 (`!m n. NN_OF_NUM m = NN_OF_NUM n ==> m = n`,
  INDUCT_TAC THEN REWRITE_TAC[NN_OF_NUM]
   INDUCT_TAC THEN REWRITE_TAC[NN_OF_NUM; NOT_SUCC_ZERO]
   INDUCT_TAC THEN POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC[NN_OF_NUM; NOT_SUCC_ZERO; SUCC_INJ]
   MESON_TAC[NOT_SUCC_ZERO]
 );; *)