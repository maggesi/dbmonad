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

let ESUBSTFUN = new_recursive_definition eterm_RECUR

help "prove_recursive_functions_exist";;
  (map dest_var o frees)
prove_recursive_functions_exist eterm_RECUR
  `(!f. ESUBSTTM f EREF0 = f 0) /\
   (!f x y. ESUBSTTM f (EAPP x y) = EAPP (ESUBSTTM f x) (ESUBSTTM f x)) /\
   (!f x. ESUBSTTM f (EABS x) = EABS (ESUBSTTM f x)) /\
   (!f x s. ESUBSTTM f (ESUBST x s) = ESUBSTTM (ESUBSTTM f o ESUBSTFUN s) x) /\
   ESUBSTFUN EID = EREF /\
   ESUBSTFUN ESHIFT1 = EREF o SUC /\
   (!x s. ESUBSTFUN (EPUSH x s) = \i. match i with 0 -> x | SUC j -> ESUBSTFUN s j) /\
   (!s t. ESUBSTFUN (ECOMP s t) = ESUBSTTM (ESUBSTFUN t) o (ESUBSTFUN s))`;;

let MSUBST = new_recursive_definition eterm_RECUR
  `(!f. MSUBST f EREF0 = f 0) /\
   (!f x y. MSUBST f (EAPP x y) = EAPP (MSUBST f x) (MSUBST f y)) /\
   (!f x. MSUBST f (EABS x) = EABS (MSUBST (EPUSH EREF0 (ECOMP s ESHIFT1)) x)) /\
   (!f x s. MSUBST f (ESUBST x s) = ESUBST x (ECOMP f s)) /\

   `

let SHIFT = new_recursive_definition num_RECURSION
  `(!f. SHIFT f 0 = 0) /\
   (!f i. SHIFT f (SUC i) = SUC (f i))`;;

let ETERMREINDEX = new_recursive_definition eterm_RECUR
  `(!f. ETERMREINDEX f EREF0 = EREF (f 0)) /\
   (!f x y. ETERMREINDEX f (EAPP x y) = EAPP (ETERMREINDEX f x) (ETERMREINDEX f y)) /\
   (!f x. ETERMREINDEX f (EABS x) = EABS (ETERMREINDEX (SLIDE f) x)) /\
   (!f x s. ETERMREINDEX f (ESUBST x s) = ESUBST x (ESUBSTREINDEX f s)) /\
   (!f. ESUBSTREINDEX f EID = )`;;

let MSUBST = new_recursive_definition eterm_RECUR
  `(!f. MSUBST f EREF0 = f 0) /\
   (!f. MSUBST f (EAPP x y) = EAPP (MSUBST f `;;

   (!x y. EAPP (EABS x) y ~> ESUBST x (EPUSH y EID)) /\