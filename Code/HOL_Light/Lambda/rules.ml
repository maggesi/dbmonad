(* ========================================================================= *)
(*  Initial semantics based on De Brujin encoding                            *)
(*  with substoids and their modules.                                        *)
(*                                                                           *)
(*  (c) Copyright, Marco Maggesi 2005 2006 2017, 2020                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Inductive datatype of the reduction rules of lambda calculus.             *)
(* ------------------------------------------------------------------------- *)

let lcrel_INDUCT,lcrel_RECUR = define_type
  "lcrel = LCREL_REFL dblambda
         | LCREL_TRANS lcrel lcrel
         | LCREL_APP lcrel lcrel
         | LCREL_ABS lcrel
         | LCREL_BETA dblambda dblambda
         | LCREL_ETA dblambda";;

let RED_RULES,RED_INDUCT,RED_CASES = new_inductive_definition
  `(!x. RED (x,x,LCREL_REFL x)) /\
   (!x y z r s. RED (x,y,r) /\ RED (y,z,s) ==> RED (x,z,LCREL_TRANS r s)) /\
   (!x1 x2 y1 y2 r1 r2. RED (x1,y1,r1) /\ RED (x2,y2,r2)
      ==> RED (APP x1 x2, APP y1 y2, LCREL_APP r1 r2)) /\
   (!x y r. RED (x,y,r) ==> RED (ABS x, ABS y, LCREL_ABS r)) /\
   (!x y. RED (APP (ABS x) y, SUBST1 y x, LCREL_BETA x y)) /\
   (!x. RED (ABS (APP (REINDEX SUC x) (REF 0)), x, LCREL_ETA x))`;;

let [RED_REFL;RED_TRANS;RED_APP;RED_ABS;RED_BETA;RED_ETA] =
  CONJUNCTS RED_RULES;;

let RED_INDUCT_ALT = prove
 (`!P. (!x. P x x (LCREL_REFL x)) /\
       (!x y z r s.
            P x y r /\ P y z s ==> P x z (LCREL_TRANS r s)) /\
       (!x1 x2 y1 y2 r1 r2.
            P x1 y1 r1 /\ P x2 y2 r2
            ==> P (APP x1 x2) (APP y1 y2) (LCREL_APP r1 r2)) /\
       (!x y r. P x y r ==> P (ABS x) (ABS y) (LCREL_ABS r)) /\
       (!x y.
            P (APP (ABS x) y) (SUBST1 y x) (LCREL_BETA x y)) /\
       (!x. P (ABS (APP (REINDEX SUC x) (REF 0))) x (LCREL_ETA x))
       ==> (!x y r. RED (x,y,r) ==> P x y r)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. RED t ==> let x,y,r = t in P x y r` MP_TAC THENL
  [MATCH_MP_TAC RED_INDUCT THEN REPEAT STRIP_TAC THEN CONV_TAC let_CONV THEN
   REPEAT (FIRST_X_ASSUM (MP_TAC o CONV_RULE let_CONV)) THEN ASM_MESON_TAC[];
   REWRITE_TAC[FORALL_PAIR_THM]] THEN
  CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN MESON_TAC[]);;

let RED_IMP_LC_REL = prove
 (`!x y r. RED (x,y,r) ==> BETAETARED x y`,
  MATCH_MP_TAC RED_INDUCT_ALT THEN REWRITE_TAC[BETAETARED_RULES] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
  [MATCH_MP_TAC BETAETARED_BETA; MATCH_MP_TAC BETAETARED_ETA] THEN
  REWRITE_TAC[DBLAMBDA_BETA_RULES; DBLAMBDA_ETA_RULES]);;

let BETAETARED_EQ_RED = prove
 (`!x y. BETAETARED x y <=> ?r. RED (x,y,r)`,
  SUBGOAL_THEN `!x y. BETAETARED x y ==> ?r. RED (x,y,r)`
   (fun th -> MESON_TAC[th; RED_IMP_LC_REL]) THEN
  MATCH_MP_TAC BETAETARED_INDUCT THEN CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_BETA_INDUCT THEN GEN_TAC THEN GEN_TAC THEN
   EXISTS_TAC `LCREL_BETA x y` THEN REWRITE_TAC[RED_RULES];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC DBLAMBDA_ETA_INDUCT THEN GEN_TAC THEN
   EXISTS_TAC `LCREL_ETA x` THEN REWRITE_TAC[RED_RULES];
   ALL_TAC] THEN
  MESON_TAC[RED_RULES]);;

let RED1 = new_recursive_definition lcrel_RECUR
  `(!x. RED1 (LCREL_REFL x) = x) /\
   (!r s. RED1 (LCREL_TRANS r s) = RED1 r) /\
   (!r s. RED1 (LCREL_APP r s) = APP (RED1 r) (RED1 s)) /\
   (!r. RED1 (LCREL_ABS r) = ABS (RED1 r)) /\
   (!x y. RED1 (LCREL_BETA x y) = APP (ABS x) y) /\
   (!x. RED1 (LCREL_ETA x) = ABS (APP (REINDEX SUC x) (REF 0)))`;;

let RED2 = new_recursive_definition lcrel_RECUR
  `(!x. RED2 (LCREL_REFL x) = x) /\
   (!r s. RED2 (LCREL_TRANS r s) = RED2 s) /\
   (!r s. RED2 (LCREL_APP r s) = APP (RED2 r) (RED2 s)) /\
   (!r. RED2 (LCREL_ABS r) = ABS (RED2 r)) /\
   (!x y. RED2 (LCREL_BETA x y) = SUBST1 y x) /\
   (!x. RED2 (LCREL_ETA x) = x)`;;

let RED_PROJECTIONS = prove
 (`!x y r. RED (x,y,r) ==> RED1 r = x /\ RED2 r = y`,
  MATCH_MP_TAC RED_INDUCT_ALT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[RED1; RED2]);;

(* ------------------------------------------------------------------------- *)
(* Reduction relation.                                                       *)
(* ------------------------------------------------------------------------- *)

let RFREES_RULES,RFREES_INDUCT,RFREES_CASES = new_inductive_set
  `(!i x. i IN FREES x ==> i IN RFREES (LCREL_REFL x)) /\
   (!i r s. i IN RFREES r ==> i IN RFREES (LCREL_TRANS r s)) /\
   (!i r s. i IN RFREES s ==> i IN RFREES (LCREL_TRANS r s)) /\
   (!i r s. i IN RFREES r ==> i IN RFREES (LCREL_APP r s)) /\
   (!i r s. i IN RFREES s ==> i IN RFREES (LCREL_APP r s)) /\
   (!i r. SUC i IN RFREES r ==> i IN RFREES (LCREL_ABS r)) /\
   (!i x y. SUC i IN FREES x ==> i IN RFREES (LCREL_BETA x y)) /\
   (!i x y. i IN FREES y ==> i IN RFREES (LCREL_BETA x y)) /\
   (!i x. i IN FREES x ==> i IN RFREES (LCREL_ETA x))`;;

let RFREES_INVERSION = prove
 (`(!i x. i IN RFREES (LCREL_REFL x) <=> i IN FREES x) /\
   (!i r s. i IN RFREES (LCREL_TRANS r s) <=>
            i IN RFREES r \/ i IN RFREES s) /\
   (!i r s. i IN RFREES (LCREL_APP r s) <=> i IN RFREES r \/ i IN RFREES s) /\
   (!i r. i IN RFREES (LCREL_ABS r) <=> SUC i IN RFREES r) /\
   (!i r s x. i IN RFREES (LCREL_BETA x y) <=>
              SUC i IN FREES x \/ i IN FREES y) /\
   (!i r s x. i IN RFREES (LCREL_ETA x) <=> i IN FREES x)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RFREES_CASES] THEN
  REWRITE_TAC[distinctness "lcrel"; injectivity "lcrel"; UNWIND_THM1] THEN
  MESON_TAC[]);;

let RFREES_CLAUSES = prove
 (`(!x. RFREES (LCREL_REFL x) = FREES x) /\
   (!r s. RFREES (LCREL_TRANS r s) = RFREES r UNION RFREES s) /\
   (!r s. RFREES (LCREL_APP r s) = RFREES r UNION RFREES s) /\
   (!r. RFREES (LCREL_ABS r) = {i | SUC i IN RFREES r}) /\
   (!r s x. RFREES (LCREL_BETA x y) = {i | SUC i IN FREES x} UNION FREES y) /\
   (!r s x. RFREES (LCREL_ETA x) = FREES x)`,
  REWRITE_TAC[EXTENSION; RFREES_INVERSION] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* SBMODULE structure of the reduction relations. *)
(* ------------------------------------------------------------------------- *)

let RSUBST = new_recursive_definition lcrel_RECUR
  `(!f x. RSUBST f (LCREL_REFL x) = LCREL_REFL (SUBST f x)) /\
   (!f r s. RSUBST f (LCREL_TRANS r s) =
            LCREL_TRANS (RSUBST f r) (RSUBST f s)) /\
   (!f r s. RSUBST f (LCREL_APP r s) = LCREL_APP (RSUBST f r) (RSUBST f s)) /\
   (!f r. RSUBST f (LCREL_ABS r) = LCREL_ABS (RSUBST (DERIV f) r)) /\
   (!f x y. RSUBST f (LCREL_BETA x y) =
            LCREL_BETA (SUBST (DERIV f) x) (SUBST f y)) /\
   (!f x. RSUBST f (LCREL_ETA x) = LCREL_ETA (SUBST f x))`;;

let RSUBST_EXTENS = prove
 (`!r f g. RSUBST f r = RSUBST g r <=> (!i. i IN RFREES r ==> f i = g i)`,
  MATCH_MP_TAC lcrel_INDUCT THEN
  REWRITE_TAC[RSUBST; RFREES_INVERSION; injectivity "lcrel"; SUBST_EXTENS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DERIV_EXTENS] THEN
  METIS_TAC[PRE; NOT_SUC; cases "num"]);;

let RSUBST_SUBST = prove
 (`!r f g. RSUBST f (RSUBST g r) = RSUBST (SUBST f o g) r`,
  MATCH_MP_TAC lcrel_INDUCT THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[RSUBST; SUBST_SUBST; injectivity "lcrel";
                  RSUBST_EXTENS; SUBST_EXTENS; o_THM; SUBST_DERIV]);;

let RSUBST_REF = prove
 (`!r. RSUBST REF r = r`,
  MATCH_MP_TAC lcrel_INDUCT THEN
  REWRITE_TAC[RSUBST; SUBST_REF; DERIV_REF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBST_RED1 = prove
 (`!r f. SUBST f (RED1 r) = RED1 (RSUBST f r)`,
  MATCH_MP_TAC lcrel_INDUCT THEN REWRITE_TAC[RED1; RSUBST; SUBST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "dblambda"; DERIV] THEN
  REWRITE_TAC[SUBST_REINDEX; REINDEX_SUBST; SUBST_EXTENS; o_THM; DERIV]);;

let SUBST_RED2 = prove
 (`!r f. SUBST f (RED2 r) = RED2 (RSUBST f r)`,
  MATCH_MP_TAC lcrel_INDUCT THEN
  REWRITE_TAC[RED2; RSUBST; SUBST; SUBST1_EQ_SUBST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[injectivity "dblambda"] THEN
  REWRITE_TAC[SUBST_SUBST; SUBST_EXTENS; o_THM; SUBST_DERIV] THEN
  GEN_TAC THEN DISCH_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[DERIV; PUSHENV; SUBST; SUBST_REINDEX] THEN
  MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC[SUBST_REF_EQ; o_THM; PUSHENV]);;

let SBMODULE_RSUBST = prove
 (`SBMODULE SUBST RSUBST`,
  REWRITE_TAC[SBMODULE_DEF; DBLAMBDA_SUBSTOID; DBLAMBDA_SBUNIT;
              RSUBST_REF; RSUBST_SUBST]);;

let SBMODULE_SUBST = prove
 (`SBMODULE SUBST SUBST`,
  REWRITE_TAC[SBMODULE_DEF; DBLAMBDA_SUBSTOID; DBLAMBDA_SBUNIT;
              SUBST_REF; SUBST_SUBST]);;

let SBMODULE_MOR_RED1 = prove
 (`SBMODULE_MOR SUBST RSUBST SUBST RED1`,
  REWRITE_TAC[SBMODULE_MOR; SBMODULE_RSUBST; SBMODULE_SUBST; SUBST_RED1]);;

let SBMODULE_MOR_RED2 = prove
 (`SBMODULE_MOR SUBST RSUBST SUBST RED2`,
  REWRITE_TAC[SBMODULE_MOR; SBMODULE_RSUBST; SBMODULE_SUBST; SUBST_RED2]);;

(* ------------------------------------------------------------------------- *)
(* Reduction module.                                                         *)
(* ------------------------------------------------------------------------- *)

let red_tybij =
  let eth = prove
   (`?t. RED t`,
    EXISTS_TAC `REF 0, REF 0, LCREL_REFL (REF 0)` THEN
    REWRITE_TAC[RED_REFL]) in
  new_type_definition "red" ("MK_RED","DEST_RED") eth;;

let MK_DEST_RED = prove
 (`!t. MK_RED (DEST_RED t) = t`,
  REWRITE_TAC[red_tybij]);;

let DEST_MK_RED_EQ = prove
 (`!t. DEST_RED (MK_RED t) = t <=> RED t`,
  REWRITE_TAC[red_tybij]);;

let DEST_MK_RED = prove
 (`!t. RED t ==> DEST_RED (MK_RED t) = t`,
  REWRITE_TAC[DEST_MK_RED_EQ]);;

let red_CASES = prove
 (`!t. ?u. t = MK_RED u /\ RED u`,
  MESON_TAC[red_tybij]);;

let  FORALL_RED_THM = prove
 (`!P. (!t. P t) <=> (!u. RED u ==> P (MK_RED u))`,
  MESON_TAC[red_tybij]);;

let  FORALL_RED_THM_IMP = prove
 (`!P. (!u. RED u ==> P (MK_RED u)) ==> (!t. P t)`,
  REWRITE_TAC[FORALL_RED_THM]);;

let MK_RED_INJ_EQ = prove
 (`!u u'. RED u /\ RED u' ==> (MK_RED u = MK_RED u' <=> u = u')`,
  MESON_TAC[red_tybij]);;

let MK_RED_INJ = prove
 (`!u u'. RED u /\ RED u' /\ MK_RED u = MK_RED u' ==> u = u'`,
  MESON_TAC[MK_RED_INJ_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Substitution for the SBMODULE of reductions.                              *)
(* ------------------------------------------------------------------------- *)

let TSUBST = new_definition
  `TSUBST f t =
   let x,y,r = DEST_RED t in
   MK_RED (SUBST f x,SUBST f y,RSUBST f r)`;;

let TSUBST_MK_RED = prove
 (`!x y r f.
     RED (x,y,r)
     ==> TSUBST f (MK_RED (x,y,r)) = MK_RED (SUBST f x,SUBST f y,RSUBST f r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TSUBST] THEN LET_TAC THEN
  ASM_METIS_TAC[PAIR_EQ; DEST_MK_RED]);;

let RED_INVERSION = prove
 (`(!x y. RED (x,y,LCREL_REFL x) <=> x = y) /\
   (!x y r1 r2. RED (x,y,LCREL_TRANS r1 r2) <=>
                (?z. RED (x,z,r1) /\ RED (z,y,r2))) /\
   (!x y r1 r2.
        RED (x,y,LCREL_APP r1 r2) <=>
        (?x1 x2 y1 y2.
           x = APP x1 x2 /\ y = APP y1 y2 /\
           RED (x1,y1,r1) /\ RED (x2,y2,r2))) /\
   (!x y r. RED (x,y,LCREL_ABS r) <=>
            (?z w. x = ABS z /\ y = ABS w /\ RED (z,w,r))) /\
   (!x y u v. RED (x,y,LCREL_BETA u v) <=>
          x = APP (ABS u) v /\ y = SUBST1 v u) /\
   (!x y. RED (x,y,LCREL_ETA u) <=>
          x = ABS (APP (REINDEX SUC u) (REF 0)) /\ y = u)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [RED_CASES] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "lcrel"; distinctness "lcrel"] THEN
  MESON_TAC[]);;

let RED_SUBST = prove
 (`!x y r f. RED (x,y,r) ==> RED (SUBST f x,SUBST f y,RSUBST f r)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC RED_INDUCT_ALT THEN
  REWRITE_TAC[SUBST; RSUBST; DERIV; SUBST_REINDEX; DERIV_O_SUC; RED_RULES] THEN
  REWRITE_TAC[RED_INVERSION; injectivity "dblambda"; SUBST1_EQ_SUBST;
    SUBST_SUBST; SUBST_REINDEX; REINDEX_SUBST; GSYM CONJ_ASSOC; UNWIND_THM1;
    RIGHT_EXISTS_AND_THM; SUBST_EXTENS; o_THM; SUBST_PUSHENV_LEMMA] THEN
  MESON_TAC[]);;

let TSUBST_TSUBST = prove
 (`!f g t. TSUBST f (TSUBST g t) = TSUBST (SUBST f o g) t`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FORALL_RED_THM_IMP THEN
  SIMP_TAC[FORALL_PAIR_THM; TSUBST_MK_RED; RED_SUBST;
           SUBST_SUBST; RSUBST_SUBST]);;

let TSUBST_REF = prove
 (`!t. TSUBST REF t = t`,
  MATCH_MP_TAC FORALL_RED_THM_IMP THEN
  SIMP_TAC[FORALL_PAIR_THM; TSUBST_MK_RED; RED_SUBST; SUBST_REF; RSUBST_REF]);;

let SBMODULE_TSUBST = prove
 (`SBMODULE SUBST TSUBST`,
  REWRITE_TAC[SBMODULE_DEF; DBLAMBDA_SUBSTOID; DBLAMBDA_SBUNIT;
              TSUBST_REF; TSUBST_TSUBST]);;

let TRED1 = new_definition
  `TRED1 t = let x,y,r = DEST_RED t in x`;;

let TRED2 = new_definition
  `TRED2 t = let x,y,r = DEST_RED t in y`;;

let TRED1_MK_RED = prove
 (`!x y r. RED (x,y,r) ==> TRED1 (MK_RED (x,y,r)) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TRED1] THEN LET_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[DEST_MK_RED; PAIR_EQ]);;

let TRED2_MK_RED = prove
 (`!x y r. RED (x,y,r) ==> TRED2 (MK_RED (x,y,r)) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TRED2] THEN LET_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[DEST_MK_RED; PAIR_EQ]);;

let TRED1_TSUBST = prove
 (`!f t. TRED1 (TSUBST f t) = SUBST f (TRED1 t)`,
  GEN_TAC THEN MATCH_MP_TAC FORALL_RED_THM_IMP THEN
  SIMP_TAC[FORALL_PAIR_THM; TSUBST_MK_RED; TRED1_MK_RED; RED_SUBST]);;

let TRED2_TSUBST = prove
 (`!f t. TRED2 (TSUBST f t) = SUBST f (TRED2 t)`,
  GEN_TAC THEN MATCH_MP_TAC FORALL_RED_THM_IMP THEN
  SIMP_TAC[FORALL_PAIR_THM; TSUBST_MK_RED; TRED2_MK_RED; RED_SUBST]);;

let SBMODULE_MOR_TRED1 = prove
 (`SBMODULE_MOR SUBST TSUBST SUBST TRED1`,
  REWRITE_TAC[SBMODULE_MOR; SBMODULE_TSUBST; SBMODULE_SUBST; TRED1_TSUBST]);;

let SBMODULE_MOR_TRED2 = prove
 (`SBMODULE_MOR SUBST TSUBST SUBST TRED2`,
  REWRITE_TAC[SBMODULE_MOR; SBMODULE_TSUBST; SBMODULE_SUBST; TRED2_TSUBST]);;

(* ------------------------------------------------------------------------- *)
(* Reduction monads.                                                         *)
(* ------------------------------------------------------------------------- *)

let REDMONAD = new_definition
  `REDMONAD (op,mop,p1,p2) <=>
   SBMODULE_MOR op mop op p1 /\
   SBMODULE_MOR op mop op p2`;;

let REDMONAD_CLAUESES = prove
 (`!op mop p1 p2:A->B.
     REDMONAD (op,mop,p1,p2)
     ==> SUBSTOID op /\
         SBMODULE op mop /\
         SBMODULE_MOR op mop op p1 /\
         SBMODULE_MOR op mop op p2`,
  SIMP_TAC[REDMONAD; SBMODULE_MOR; SBMODULE_DEF]);;

let REDMONAD_MOR = new_definition
  `REDMONAD_MOR (op,mop,p1,(p2:M->A))
                (op',mop',p1',(p2':N->B))
                (f:A->B,g:M->N) <=>
   REDMONAD (op,mop,p1,p2) /\
   REDMONAD (op',mop',p1',p2') /\
   SUBSTOID_MOR op op' f /\
   SBMODULE_MOR op mop (PBMOP op op' f mop') g /\
   p1' o g = f o p1 /\
   p2' o g = f o p2`;;

(* ------------------------------------------------------------------------- *)
(* Lambda calculus as reduction monad.                                       *)
(* ------------------------------------------------------------------------- *)

let REDMONAD_SUBSTOID = prove
 (`REDMONAD (SUBST,TSUBST,TRED1,TRED2)`,
  REWRITE_TAC[REDMONAD; SBMODULE_MOR; SBMODULE_SUBST; SBMODULE_TSUBST;
              TRED1_TSUBST; TRED2_TSUBST]);;
