(* ========================================================================= *)
(* Named encoding of simple untyped lambda calculus.                         *)
(* Partially inspired by Harrison's "HOL in HOL"                             *)
(* (folder Model in the HOL Light distribution).                             *)
(* ========================================================================= *)

type_invention_warning := false;;
needs "Library/rstc.ml";;
type_invention_warning := true;;

needs "De_Bruijn/misc.ml";;
needs "De_Bruijn/lib.ml";;

let term_INDUCT,term_RECUR = define_type
  "term = Var num
        | Comb term term
        | Lam num term";;

let term_INJ = injectivity "term";;
let term_DISTINCT = distinctness "term";;
let term_CASES = cases "term";;

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
 (`RACONV env (Var x1,Var x2) = ALPHAVARS env (x1,x2) /\
   RACONV env (Var x1,Comb l2 r2) = F /\
   RACONV env (Var x1,Lam x2 t2) = F /\
   RACONV env (Comb l1 r1,Var x2) = F /\
   RACONV env (Comb l1 r1,Comb l2 r2) =
     (RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   RACONV env (Comb l1 r1,Lam x2 t2) = F /\
   RACONV env (Lam x1 t1,Var x2) = F /\
   RACONV env (Lam x1 t1,Comb l2 r2) = F /\
   RACONV env (Lam x1 t1,Lam x2 t2) = RACONV (CONS (x1,x2) env) (t1,t2)`,
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [RACONV_CASES] THEN
  REWRITE_TAC[term_INJ; term_DISTINCT; PAIR_EQ] THEN MESON_TAC[]);;

let ACONV = new_definition
 `ACONV t1 t2 <=> RACONV [] (t1,t2)`;;

(* ------------------------------------------------------------------------- *)
(* Reflexivity of alpha-conversion.                                          *)
(* ------------------------------------------------------------------------- *)

let ALPHAVARS_REFL = prove
 (`!env t. ALL (\(s,t). s = t) env ==> ALPHAVARS env (t,t)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL; ALPHAVARS] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[PAIR_EQ]);;

let RACONV_REFL = prove
 (`!t env. ALL (\(s,t). s = t) env ==> RACONV env (t,t)`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[RACONV] THEN REPEAT STRIP_TAC THENL
  [ASM_SIMP_TAC[ALPHAVARS_REFL];
   ASM_MESON_TAC[];
   ASM_MESON_TAC[];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL]]);;

let ACONV_REFL = prove
 (`!t. ACONV t t`,
  REWRITE_TAC[ACONV] THEN SIMP_TAC[RACONV_REFL; ALL]);;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let FVARS_RULES,FVARS_INDUCT,FVARS_CASES = new_inductive_set
  `(!x. x IN FVARS (Var x)) /\
   (!x s t. x IN FVARS s ==> x IN FVARS (Comb s t)) /\
   (!x s t. x IN FVARS t ==> x IN FVARS (Comb s t)) /\
   (!x y t. ~(x = y) /\ x IN FVARS t ==> x IN FVARS (Lam y t))`;;

let FVARS_INVERSION = prove
 (`(!x y. x IN FVARS (Var y) <=> x = y) /\
   (!x s t. x IN FVARS (Comb s t) <=> x IN FVARS s \/ x IN FVARS t) /\
   (!x y t. x IN FVARS (Lam y t) <=> ~(x = y) /\ x IN FVARS t)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [FVARS_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ] THEN MESON_TAC[]);;

let FVARS_CLAUSES = prove
 (`FVARS (Var x) = {x} /\
   FVARS (Comb s t) = FVARS s UNION FVARS t /\
   FVARS (Lam x t) = FVARS t DELETE x`,
  REWRITE_TAC[EXTENSION; FVARS_INVERSION] THEN SET_TAC[]);;

let ALPHAVARS_EQ = prove
 (`!env x x' y y':A. ALPHAVARS env (x,y) /\ ALPHAVARS env (x',y')
                     ==> (x = x' <=> y = y')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALPHAVARS] THENL [MESON_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `h:A#A` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

let FVARS_RACONV = prove
 (`!env p. RACONV env p
           ==> (!x. x IN FVARS (FST p) /\ ~(?y. MEM (x,y) env) <=>
                    x IN FVARS (SND p) /\ ~(?y. MEM (y,x) env))`,
  MATCH_MP_TAC RACONV_INDUCT THEN
  REWRITE_TAC[FVARS_INVERSION; MEM; PAIR_EQ] THEN CONJ_TAC THENL
  [LIST_INDUCT_TAC THEN REWRITE_TAC[ALPHAVARS; MEM] THENL
   [MESON_TAC[];
    STRUCT_CASES_TAC (ISPEC `h:num#num` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]];
   MESON_TAC[]]);;

let VFARS_ACONV = prove
 (`!s t x. ACONV s t ==> (x IN FVARS s <=> x IN FVARS t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ACONV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FVARS_RACONV) THEN
  SIMP_TAC[MEM; FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* Variant function. Deliberately underspecified at the moment. In a bid to  *)
(* expunge use of sets, just pick it distinct from what's free in a term.    *)
(* ------------------------------------------------------------------------- *)

let FINITE_FVARS = prove
 (`!t. FINITE (FVARS t)`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[FVARS_CLAUSES; FINITE_SING; FINITE_UNION; FINITE_DELETE]);;

let AVOID_FINITE_EXISTS = prove
 (`!s:A->bool. INFINITE (:A) /\ FINITE s ==> ?x. ~(x IN s)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((:A) DIFF s= {})` (fun th -> SET_TAC[th]) THEN
  MATCH_MP_TAC INFINITE_NONEMPTY THEN ASM_SIMP_TAC[INFINITE_DIFF_FINITE]);;

let FRESH = (specify o prove)
 (`!s:num->bool. FINITE s ==> ?FRESH. ~(FRESH IN s)`,
  MESON_TAC[AVOID_FINITE_EXISTS; num_INFINITE]);;

(* ------------------------------------------------------------------------- *)
(* Term substitution.                                                        *)
(* ------------------------------------------------------------------------- *)

let VSUBST = define
  `(!f x. VSUBST f (Var x) = f x) /\
   (!f s t. VSUBST f (Comb s t) = Comb (VSUBST f s) (VSUBST f t)) /\
   (!f x t. VSUBST f (Lam x t) =
            let x' = FRESH (UNIONS {FVARS (f y) | y IN FVARS t}) in
            Lam x' (VSUBST (\v. if v = x then Var x' else f v) t))`;;

let IN_FVARS_VSUBST = prove
 (`!t u f. u IN FVARS (VSUBST f t) <=>
           ?y. y IN FVARS t /\ u IN FVARS (f y)`,
  MATCH_MP_TAC term_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VSUBST; FVARS_INVERSION] THENL
  [REWRITE_TAC[UNWIND_THM2]; MESON_TAC[]; ALL_TAC] THEN
  LET_TAC THEN ASM_REWRITE_TAC[FVARS_INVERSION] THEN EQ_TAC THENL
  [STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THENL
   [POP_ASSUM (SUBST_VAR_TAC o GSYM); ASM_REWRITE_TAC[]] THEN
   ASM_REWRITE_TAC[FVARS_INVERSION] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[FVARS_INVERSION]] THEN
  SUBGOAL_THEN `u IN UNIONS {FVARS (f y) | y IN FVARS a1} /\
                ~(x' IN UNIONS {FVARS (f y) | y IN FVARS a1})`
               (fun th -> MESON_TAC[th]) THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN CONJ_TAC THENL
  [ASM SET_TAC []; MATCH_MP_TAC FRESH] THEN
  REWRITE_TAC[FINITE_UNIONS; FORALL_IN_GSPEC; FINITE_FVARS] THEN
  SUBGOAL_THEN
    `!f t. {FVARS (f y) | y IN FVARS t} = IMAGE (FVARS o f) (FVARS t)`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[IMAGE_o] THEN SET_TAC[];
   MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_FVARS]]);;

let FVARS_VSUBST = prove
 (`!t f. FVARS (VSUBST f t) = UNIONS (IMAGE (FVARS o f) (FVARS t))`,
  REWRITE_TAC[IMAGE_o; IN_FVARS_VSUBST; EXTENSION] THEN SET_TAC[]);;

let ALPHAVARS_IMP_EQ = prove
 (`!env x y:A. ALPHAVARS env (x,y) /\
               (~(?y. MEM (x,y) env) \/ ~(?x. MEM (x,y) env))
               ==> x = y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALPHAVARS; MEM] THEN
  STRUCT_CASES_TAC (ISPEC `h:A#A` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

let RACONV_ENV_INDEPENDENT = prove
 (`!env1 env2 s t.
     (!x y. x IN FVARS s /\ y IN FVARS t
            ==> (ALPHAVARS env1 (x,y) <=> ALPHAVARS env2 (x,y)))
     ==> (RACONV env1 (s,t) <=> RACONV env2 (s,t))`,
  SUBGOAL_THEN
    `!env p. RACONV env p
             ==> !env'. (!x y. x IN FVARS (FST p) /\ y IN FVARS (SND p)
                               ==> (ALPHAVARS env (x,y) <=>
                                    ALPHAVARS env' (x,y)))
                        ==> RACONV env' p`
      (fun th -> MESON_TAC[REWRITE_RULE[FORALL_PAIR_THM] th]) THEN
  MATCH_MP_TAC RACONV_INDUCT THEN REWRITE_TAC[FVARS_INVERSION; RACONV] THEN
  REPEAT CONJ_TAC THENL [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ALPHAVARS; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ALPHAVARS; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let SWAP = new_definition
  `SWAP (x:A,y:B) = (y,x)`;;

let REV_ASSOCD = define
  `(REV_ASSOCD a [] d = d) /\
   (REV_ASSOCD a (CONS (x,y) t) d =
        if y = a then x else REV_ASSOCD a t d)`;;

let ASSOCD = define
  `(ASSOCD a [] d = d) /\
   (ASSOCD a (CONS (x,y) t) d =
        if x = a then y else ASSOCD a t d)`;;

let ACONV_COMB = prove
 (`!s1 s2 t1 t2. ACONV (Comb s1 t1) (Comb s2 t2) <=>
                 ACONV s1 s2 /\ ACONV t1 t2`,
  REWRITE_TAC[ACONV; RACONV]);;

(*
let RACONV_VSUBST = prove
 (`!env s t f g.
     RACONV env (s,t) /\
     (!x y. ALPHAVARS env (x,y) /\ (~MEM (x,y) env ==> x IN FVARS s)
            ==> RACONV env (f x,g y))
     ==> RACONV env (VSUBST f s,VSUBST g t)`,

  SUBGOAL_THEN
    `!env p. RACONV env p
             ==> !f g. (!x y. ALPHAVARS env (x,y) /\
                             (~MEM (x,y) env ==> x IN FVARS (FST p))
                             ==> RACONV env (f x,g y))
                       ==> RACONV env (VSUBST f (FST p),VSUBST g (SND p))`
    (fun th -> MESON_TAC[REWRITE_RULE[FORALL_PAIR_THM] th]) THEN
*)

(* 
let ACONV_VSUBST = prove
 (`!s t f g. ACONV s t /\ (!x. x IN FVARS s ==> ACONV (f x) (g x))
             ==> ACONV (VSUBST f s) (VSUBST g t)`,

REWRITE_TAC[ACONV]

 );;
*)
