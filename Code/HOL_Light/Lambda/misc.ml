(* ========================================================================= *)
(* Miscellanea.                                                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Handy wrapper function around new_specification.                          *)
(* ------------------------------------------------------------------------- *)

let specify th =
  let vars = fst (strip_forall (concl th)) in
  let th = GEN_REWRITE_RULE TRY_CONV [RIGHT_IMP_EXISTS_THM] (SPEC_ALL th) in
  let names = map name_of (fst(strip_exists (concl th))) in
  let th = GEN_REWRITE_RULE DEPTH_CONV [SKOLEM_THM] (GENL vars th) in
  new_specification names th;;

(* ------------------------------------------------------------------------- *)
(* List of all variables occurring in a goal                                 *)
(* (in the hypothesis or in the conclusion).                                 *)
(* ------------------------------------------------------------------------- *)

let goal_variables () =
  let (asl,w) = top_goal () in
  let vlist = itlist ((@) o variables) asl (variables w) in
  setify vlist;;

(* ------------------------------------------------------------------------- *)
(* As before, but split each variable in name and type, so that the types    *)
(* are shown to the user.                                                    *)
(* ------------------------------------------------------------------------- *)

let show_goal_variables () =
  map dest_var (goal_variables ());;

(* ------------------------------------------------------------------------- *)
(* Variant of tactics that use label.                                        *)
(* ------------------------------------------------------------------------- *)

let LABEL_ABBREV_TAC tm : tactic =
  let s = name_of (lhand tm) in
  ABBREV_TAC tm THEN POP_ASSUM (LABEL_TAC (s^"_def"));;

let LABEL_INDUCT_TAC : tactic =
  fun (_,w) as gl ->
    try let s = name_of (fst (dest_forall w)) in
        (INDUCT_TAC THENL [ALL_TAC; POP_ASSUM (LABEL_TAC (s^"_ind"))]) gl
    with Failure _ -> failwith "LABEL_INDUCT_TAC";;

(* ------------------------------------------------------------------------- *)
(* Some general theorems.                                                    *)
(* ------------------------------------------------------------------------- *)

let IMP_ANTISYM_EQ = prove
 (`!p q. (p ==> q) /\ (q ==> p) <=> (p <=> q)`,
  CONV_TAC TAUT);;

let IMP_ANTISYM = prove
 (`!p q. (p ==> q) /\ (q ==> p) ==> (p <=> q)`,
  REWRITE_TAC[IMP_ANTISYM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* General theorems about HOL sets.                                          *)
(* ------------------------------------------------------------------------- *)

let EXTENSION_ALT = prove
 (`!s t. s = t <=> (!x. x IN s ==> x IN t) /\ (!x. x IN t ==> x IN s)`,
  SET_TAC[]);;

let CHOICE_UNIQUE = prove
 (`!s x. s = {x} ==> CHOICE s = x`,
  REWRITE_TAC[EXTENSION; CHOICE; IN_SING] THEN MESON_TAC[]);;

let IMAGE_EQ = prove
 (`!f g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  SET_TAC[]);;
