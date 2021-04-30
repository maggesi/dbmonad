(* ========================================================================= *)
(* Named encoding of simple untyped lambda calculus.                         *)
(* Inspired by Harrison's "HOL in HOL"                                       *)
(* (folder Model in the HOL Light distribution).                             *)
(* ========================================================================= *)

let term_INDUCT,term_RECUR = define_type
  "term = Var num
        | Comb term term
        | Lam num term";;

let term_INJ = injectivity "term";;
let term_DISTINCT = distinctness "term";;
let term_CASES = cases "term";;

let FVARS_RULES,FVARS_INDUCT,FVARS_CASES = new_inductive_set
  `(!x. x IN FVARS (Var x)) /\
   (!x s t. x IN FVARS s ==> x IN FVARS (Comb s t)) /\
   (!x s t. x IN FVARS t ==> x IN FVARS (Comb s t)) /\
   (!x y t. ~(x = y) /\ x IN FVARS t ==> x IN FVARS (Lam y t))`;;

(* let ALPHA_RULES,ALPHA_INDUCT,ALPHA_CASES = new_inductive_definition
  `(x,y) IN R ==> ALPHA R (Var x) (Var y)`;; *)

(* ------------------------------------------------------------------------- *)
(* Alpha-conversion.                                                         *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS = define
  `(ALPHAVARS [] tmp <=> (FST tmp = SND tmp)) /\
   (ALPHAVARS (CONS tp oenv) tmp <=>
        (tmp = tp) \/
        ~(FST tp = FST tmp) /\ ~(SND tp = SND tmp) /\ ALPHAVARS oenv tmp)`;;

let RACONV_RULES,RACONV_INDUCT,RACONV_CASES = new_inductive_definition
 `(!env x y.
     ALPHAVARS env (x,y)
     ==> RACONV env (Var x,Var y)) /\
  (!env s1 t1 s2 t2.
     RACONV env (s1,s2) /\ RACONV env (t1,t2)
     ==> RACONV env (Comb s1 t1,Comb s2 t2)) /\
  (!env x s y t.
     RACONV (CONS (x,y) env) (s,t) ==> RACONV env (Lam x s,Lam y t))`;;

let RACONV = prove
 (`(RACONV env (Var x1,Var x2) <=> ALPHAVARS env (x1,x2)) /\
   (RACONV env (Var x1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1,Lam x2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Lam x2 t2) <=> F) /\
   (RACONV env (Lam x1 t1,Var x2) <=> F) /\
   (RACONV env (Lam x1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Lam x1 t1,Lam x2 t2) <=>
        RACONV (CONS (x1,x2) env) (t1,t2))`,
  REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RACONV_CASES] THEN
  REWRITE_TAC[term_INJ; term_DISTINCT; PAIR_EQ] THEN MESON_TAC[]);;

let ACONV = new_definition
 `ACONV t1 t2 <=> RACONV [] (t1,t2)`;;
