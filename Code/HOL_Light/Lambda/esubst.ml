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

(* override_interface("~>",`ETERMREL`);; *)
(* override_interface(":>",`ESUBSTREL`);; *)

let ETERMCONG_RULES,ETERMCONG_INDUCT,ETERMCONG_CASES = new_inductive_definition
  `(!x x' y. R x x' ==> ETERMCONG R S (EAPP x y) (EAPP x' y)) /\
   (!x y y'. R y y' ==> ETERMCONG R S (EAPP x y) (EAPP x y')) /\
   (!x x'. R x x' ==> ETERMCONG R S (EABS x) (EABS x')) /\
   (!x x' s. R x x' ==> ETERMCONG R S (ESUBST x s) (ESUBST x' s)) /\
   (!x s s'. S s s' ==> ETERMCONG R S (ESUBST x s) (ESUBST x s')) /\
   (!x x' s. R x x' ==> ESUBSTCONG R S (EPUSH x s) (EPUSH x' s)) /\
   (!x s s'. S s s' ==> ESUBSTCONG R S (EPUSH x s) (EPUSH x s')) /\
   (!s s' t. S s s' ==> ESUBSTCONG R S (ECOMP s t) (ECOMP s' t)) /\
   (!s t t'. S t t' ==> ESUBSTCONG R S (ECOMP s t) (ECOMP s t'))`;;

needs "Library/rstc.ml";;
needs "Examples/reduct.ml";;
CR;;
WCR;;
search[`P ==> CR R`];;
search[`NORMAL`];;

let ESHIFT = new_recursive_definition num_RECURSION
  `ESHIFT 0 = EID /\
   (!i. ESHIFT (SUC i) = if i = 0
                         then ESHIFT1
                         else ECOMP ESHIFT1 (ESHIFT i))`;;

(RAND_CONV (TOP_DEPTH_CONV num_CONV) THENC
 REWRITE_CONV[ESHIFT; ARITH]) `ESHIFT 3`;;

let EREF = new_definition
  `EREF i = if i = 0
            then EREF0
            else ESUBST EREF0 (ESHIFT i)`;;

let EPUSHREF = new_recursive_definition num_RECURSION
  `(!s. EPUSHREF 0 s = s) /\
   (!k s. EPUSHREF (SUC k) s = EPUSHREF k (EPUSH (EREF k) s))`;;

(TOP_DEPTH_CONV num_CONV THENC
 REWRITE_CONV[EPUSHREF; EREF; SUC_INJ; NOT_SUC] THENC
 NUM_REDUCE_CONV)
`EPUSHREF 3 EID`;;

let ELIFT = new_recursive_definition eterm_RECUR
  `(!i k. ELIFT k i EREF0 = if k = 0 then EREF0 else EREF i) /\
   (!i k x y. ELIFT k i (EAPP x y) = EAPP (ELIFT k i x) (ELIFT k i y)) /\
   (!i k x. ELIFT k i (EABS x) = EABS (ELIFT (SUC k) i x)) /\
   (!i k x s. ELIFT k i (ESUBST x s) = ESUBST x (ELIFTSUBST k i s)) /\
   (!i k. ELIFTSUBST k i EID = EPUSHREF (PRE k) (ESHIFT i)) /\
   (!i k. ELIFTSUBST k i ESHIFT1 = EPUSHREF k (ESHIFT (SUC i))) /\
   (!i k x s. ELIFTSUBST k i (EPUSH x s) = EPUSH (ELIFT k i x) (ELIFTSUBST k i s)) /\
   (!i k s t. ELIFTSUBST k i (ECOMP s t) = ECOMP s (ELIFTSUBST k i t))`;;

let EBIND = new_recursive_definition eterm_RECUR

prove_recursive_functions_exist eterm_RECUR
  `(!x. EBIND EID x = x) /\
   (!x. EBIND ESHIFT1 x = ELIFT 0 1 x) /\
   (!s t x. EBIND (ECOMP s t) x = EBIND t (EBIND s x)) /\
   (!s x y. EBIND s (EAPP x y) = EAPP (EBIND s x) (EBIND s y)) /\
   (!s x. EBIND s (EABS x) = EABS (EBIND (ELIFTSUBST 0 1 s) x)) /\
   (!s x t. EBIND s (ESUBST x t) = ESUBST x (EBINDSUBST s t)) /\
   (!x s. EBIND (EPUSH x s) EREF0 = x)`;;

(* ------------------------------------------------------------------------- *)
(* Alternative induction structure based on usual Ref constructor.           *)
(* ------------------------------------------------------------------------- *)





needs "Library/iter.ml";;




let ESHIFT = new_definition
  `ESHIFT i = ITER i (\x. ESUBST x ESHIFT1)`;;

let EREF = new_definition
  `EREF i = ESHIFT i EREF0`;;

let ISUBSTFUN = new_recursive_definition eterm_RECUR

let SLIDE = new_recursive_definition num_RECURSION
  `(!f. SLIDE f 0 = 0) /\
   (!f i. SLIDE f (SUC i) = SUC (f i))`;;

let ESUBSTFUN = new_recursive_definition eterm_INDUCT

prove_recursive_functions_exist eterm_RECUR
  `ESUBSTFUN EID = EREF /\
   ESUBSTFUN ESHIFT1 = EREF o SUC /\
   (!x s. ESUBSTFUN (EPUSH x s) =
          \i. match i with 0 => x | SUC i -> EREF i) /\
   (!s t. ESUBSTFUN (ECOMP s t) = \i. ESUBSTTM (ESUBSTFUN s i) t) /\
   (ESUBSTTM EREF0 = \f. EREF (f 0)) /\
   (!x y. ESUBSTTM (EAPP x y) = \f. EAPP (ESUBSTTM x f) (ESUBSTTM y f)) /\
   (!x. ESUBSTTM (EABS x) = \f. EABS (ESUBSTTM x f)) /\
   (!x s. ESUBSTTM (ESUBST x s) = \f. )`;;

prove_recursive_functions_exist eterm_RECUR
  `(!f. EREINDEX f EREF0 = EREF (f 0)) /\
   (!f x y. EREINDEX f (EAPP x y) = EAPP (EREINDEX f x) (EREINDEX f x)) /\
   (!f x. EREINDEX f (EABS x) = EABS (EREINDEX (SLIDE f) x)) /\
   (!f x s. EREINDEX f (ESUBST x s) = ESUBST x (EREINDEXSUBST f s)) /\
   (!f. EREINDEXSUBST f EID = f)`;;
     /\
   (!f. EREINDEXSUBST f ESHIFT1 = f o SUC) /\
   (!x s. EREINDEXSUBST (EPUSH x s) =
      \i. match i with 0 -> x | SUC j -> EREINDEX SUC (f j)) /\
   (!s t. EREINDEXSUBST (ECOMP s t) = EREINDEXSUBST f t o EREINDEXSUBST I s)`;;



help "prove_recursive_functions_exist";;
  (map dest_var o frees)

   ISUBSTTM : (num => eterm) -> eterm -> eterm
  ISUBSTFUN : (num => eterm) -> esubst -> (num => eterm)

`IS_BD (f:nat->eterm) <=> (?n k. !i. n <= i ==> f i = EREF (i + k))`

prove_recursive_functions_exist eterm_RECUR
  `(!f. ISUBSTTM f EREF0 = f 0) /\
   (!f x y. ISUBSTTM f (EAPP x y) = EAPP (ISUBSTTM f x) (ISUBSTTM f x)) /\
   (!f x. ISUBSTTM f (EABS x) = EABS (ISUBSTTM f x)) /\
   (!f x s. ISUBSTTM f (ESUBST x s) = ISUBSTTM (ISUBSTTM f o ISUBSTFUN s) x) /\
   ISUBSTFUN EID = EREF /\
   ISUBSTFUN ESHIFT1 = EREF o SUC /\
   (!x s. ISUBSTFUN (EPUSH x s) =
      \i. match i with 0 -> x | SUC j -> ISUBSTFUN s j) /\
   (!s t. ISUBSTFUN (ECOMP s t) =
      ISUBSTTM (ISUBSTFUN t) o (ISUBSTFUN s))`;;

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
