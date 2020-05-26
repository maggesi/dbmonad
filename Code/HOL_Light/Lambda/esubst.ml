(* ========================================================================= *)
(* Lambda calculus with explicit substitutions.                              *)
(* See Abadi et al.                                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Datatype for term and object substitutions.                               *)
(* ------------------------------------------------------------------------- *)

let eterm_INDUCT,eterm_RECUR = define_type
  "eterm  = EREF0
          | EAPP eterm eterm
          | EABS eterm
          | ESUBST eterm esubst;
   esubst = EID
          | ESHIFT1
          | EPUSH eterm esubst
          | ECOMP esubst esubst";;

(* ------------------------------------------------------------------------- *)
(* Reduction relation.                                                       *)
(* (Proof-irrelevant version)                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("~>",get_infix_status "HAS_SIZE");;
parse_as_infix(":>",get_infix_status "~>");;

let ETERMREL_RULES,ETERMREL_INDUCT,ETERMREL_CASES =
  (new_inductive_definition o
   vsubst [`ETERMREL:eterm->eterm->bool`,`(~>):eterm->eterm->bool`;
           `ESUBSTREL:esubst->esubst->bool`,`(:>):esubst->esubst->bool`])
  `ESUBST EREF0 EID ~> EREF0 /\
   (!x s. ESUBST EREF0 (EPUSH x s) ~> x) /\
   (!x y s.  ESUBST (EAPP x y) s ~> EAPP (ESUBST x s) (ESUBST y s)) /\
   (!x s. ESUBST (EABS x) s ~>
          EABS (ESUBST x (EPUSH EREF0 (ECOMP s ESHIFT1)))) /\
   (!x s t. ESUBST (ESUBST x s) t ~> ESUBST x (ECOMP s t)) /\

   (!x y. EAPP (EABS x) y ~> ESUBST x (EPUSH y EID)) /\

   (!s. ECOMP EID s :> s) /\
   ECOMP ESHIFT1 EID :> ESHIFT1 /\
   (!x s. ECOMP ESHIFT1 (EPUSH x s) :> s) /\
   (!x s t. ECOMP (EPUSH x s) t :> EPUSH (ESUBST x t) (ECOMP s t)) /\
   (!r s t. ECOMP (ECOMP r s) t :> ECOMP r (ECOMP s t))`;;

override_interface("~>",`ETERMREL`);;
override_interface(":>",`ESUBSTREL`);;
(* ETERMREL_RULES;; *)

(* ------------------------------------------------------------------------- *)
(* Alternative induction structure based on usual Ref constructor.           *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;

let ESHIFT = new_definition
  `ESHIFT i = ITER i (\x. ESUBST x ESHIFT1)`;;

let EREF = new_definition
  `EREF i = ESHIFT i EREF0`;;
