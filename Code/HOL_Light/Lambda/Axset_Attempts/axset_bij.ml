(* ------------------------------------------------------------------------- *)
(* Correspondences.                                                          *)
(* ------------------------------------------------------------------------- *)

let CORRESPONDENCE = new_definition
  `CORRESPONDENCE (P,Q) (f:A->B,g) <=>
   (!x. P x ==> Q (f x)) /\
   (!y. Q y ==> P (g y)) /\
   (!x. P x ==> g (f x) = x) /\
   (!y. Q y ==> f (g y) = y)`;;

let COORESPONDENCE_INV = prove
 (`!P Q f:A->B g. CORRESPONDENCE (P,Q) (f,g) ==> CORRESPONDENCE (Q,P) (g,f)`,
  REWRITE_TAC[CORRESPONDENCE] THEN MESON_TAC[]);;

let COORESPONDENCE_INV_EQ = prove
 (`!P Q f:A->B g. CORRESPONDENCE (Q,P) (g,f) <=> CORRESPONDENCE (P,Q) (f,g)`,
  MESON_TAC[COORESPONDENCE_INV]);;

let CORRESPONDENCE_NUM_NAT = prove
 (`CORRESPONDENCE ((\x. T),(\x. x In nat)) (nat_of_num,num_of_nat)`,
  REWRITE_TAC[CORRESPONDENCE; NAT_OF_NUM_IN_NAT;
              NAT_OF_NUM_OF_NAT; NUM_OF_NAT_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Encoding in sets.                                                         *)
(* ------------------------------------------------------------------------- *)

let SETENCODING_BIJ = new_definition
  `SETENCODING f s t <=> BIJ f s {x | x In t}`;;

let SETENCODING_EXPLICIT = prove
 (`SETENCODING f s t <=>
   (!x:A. x IN s ==> f x In t) /\
   (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
   (!y. y In t ==> ?x. x IN s /\ y = f x)`,
  REWRITE_TAC[SETENCODING_BIJ; BIJ; INJ; SURJ; IN_ELIM_THM] THEN MESON_TAC[]);;

let SETENCODING_INJ = prove
 (`!f s t x y:A. SETENCODING f s t /\ x IN s /\ y IN s /\ f x = f y ==> x = y`,
  MESON_TAC[SETENCODING_EXPLICIT]);;

let SETENCODING_INJ_EQ = prove
 (`!f s t. SETENCODING f s t
           ==> !x y:A. x IN s /\ y IN s ==> (x = y <=> f x = f y)`,
  MESON_TAC[SETENCODING_INJ]);;

let SETENCODING_SURJ = prove
 (`!f s t y. SETENCODING f s t /\ y In t ==> ?x:A. x IN s /\ y = f x`,
  MESON_TAC[SETENCODING_EXPLICIT]);;

let SETENCODING_SEPARATION = prove
 (`!f:A->set s t P.
     SETENCODING f s t
     ==> ?s'. s' SUBSET s /\ SETENCODING f s' (Separation t P)`,
  REPEAT GEN_TAC THEN INTRO_TAC "enc" THEN
  EXISTS_TAC `{x:A | x IN s /\ P (f x:set)}` THEN
  CONJ_TAC THENL [SET_TAC[]; POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[SETENCODING_EXPLICIT; FORALL_IN_GSPEC;
              IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_SEPARATION; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let RESTRICT_SETENCODING = prove
 (`!f s t s':A->bool. SETENCODING f s t /\ s' SUBSET s
                      ==> ?t'. t' Sbset t /\ SETENCODING f s' t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SETENCODING_EXPLICIT; SUBSET] THEN
  STRIP_TAC THEN
  EXISTS_TAC `Separation t (\y. y IN IMAGE (f:A->set) s')` THEN
  REWRITE_TAC[SBSET; IN_SEPARATION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let SETENCODING_NAT_OF_NUM = prove
 (`SETENCODING nat_of_num (:num) nat`,
  REWRITE_TAC[SETENCODING_EXPLICIT; IN_UNIV;
    NAT_OF_NUM_IN_NAT; NAT_OF_NUM_EQ; NAT_OF_NUM_SURJ]);;

let COUNTABLE_IMP_EXISTS_SET = prove
 (`!s:A->bool. COUNTABLE s
               ==> ?t f g.
                     (!x. x IN s ==> f x In t) /\
                     (!y. y In t ==> g y IN s) /\
                     (!x. x IN s ==> g (f x) = x) /\
                     (!y. y In t ==> f (g y) = y) /\
                     (!x x'. x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\
                     (!y. y In t ==> )
                     (!y y'. y IN t /\ y' IN t /\ g y = g y' ==> y = y') /\
                      `)

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

let setencoding_TYBIJ =
 (new_type_definition "setencoding" ("MK_SETENCODING","DEST_SETENCODING") o
  prove)
 (`?p f:A->set s t. p = (f,s,t) /\ BIJ f s {x | x In t}`,
  MAP_EVERY EXISTS_TAC
   [`(\x:A.{}:set),{}:A->bool,{}:set`;
    `\x:A.{}:set`;`{}:A->bool`;`{}:set`] THEN
  REWRITE_TAC[BIJ; INJ; SURJ; IN_EMPTYSET] THEN SET_TAC[]);;

let SETENCODE = new_definition
  `SETENCODE p = FST (DEST_SETENCODING p)`;;

let ENCODING_DOMAIN = new_definition
  `ENCODING_DOMAIN p = FST (SND (DEST_SETENCODING p))`;;

let ENCODING_SET = new_definition
  `ENCODING_SET p = SND (SND (DEST_SETENCODING p))`;;

let SETENCODING_THM = prove
 (`!p:A setencoding.
     BIJ (SETENCODE p) (ENCODING_DOMAIN p) {x | x In ENCODING_SET p}`,
  GEN_TAC THEN STRIP_ASSUME_TAC
    (REWRITE_RULE [CONJUNCT1 setencoding_TYBIJ]
       (ISPEC `DEST_SETENCODING (p:A setencoding)`
              (CONJUNCT2 setencoding_TYBIJ))) THEN
  ASM_REWRITE_TAC[SETENCODE; ENCODING_DOMAIN; ENCODING_SET]);;

let MK_SETENCODING = prove
 (`!f:A->num s t.
     BIJ f s {x | x In t}
     ==> `,)
let NUMENCODING = new_definition
  `NUMENCODING = MK_SETENCODING (nat_of_num,(:num),nat)`;;


(* ------------------------------------------------------------------------- *)
(* Functions.                                                                *)
(* ------------------------------------------------------------------------- *)

prioritize_axset();;
prioritize_hol_set();;





(* 

FINITE_IMP_COUNTABLE;;
COUNTABLE_CASES;;
NUM_COUNTABLE;;

search[`COUNTABLE`; `FINITE`];;
search[`COUNTABLE`; `INFINITE`];;
search[`COUNTABLE`; omit `FINITE`];;
COUNTABLE_AS_INJECTIVE_IMAGE;;

s <=_c t /\ ?u enc.  *)

(* search[`COUNTABLE`];;
search[`(>=_c)`];;
search[`(<=_c)`];;

   ("le_c",
    |- !t s.
           s <=_c t <=>
           (?f. (!x. x IN s ==> f x IN t) /\
                (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)));

  [("COUNTABLE", |- !t. COUNTABLE t <=> (:num) >=_c t);
   ("GE_C",
    |- !s t. s >=_c t <=> (?f. !y. y IN t ==> (?x. x IN s /\ y = f x)));
   ("ge_c", |- !t s. s >=_c t <=> t <=_c s)]

let FINITE_EXISTS_SET = prove
 (`!s:A->bool. FINITE s ==> ?t:set enc. BIJ enc s {y | y In t}`,


let COUNTABLE_EXISTS_SET = prove
 (`!s:A->bool. COUNTABLE s
               ==> ?t:set enc dec.
                     (!x. x IN s ==> enc x In t) /\
                     (!x. x In t ==> dec x IN s) /\
                     (!x. x IN s ==> dec (enc x) = x) /\
                     (!x. x In t ==> enc (dec x) = x)`,
  GEN_TAC THEN REWRITE_TAC[COUNTABLE; ge_c; le_c]
  INTRO_TAC "@enc. _ enc_inj"

 );; *)