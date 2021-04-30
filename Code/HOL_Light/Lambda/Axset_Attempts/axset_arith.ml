
(* ------------------------------------------------------------------------- *)
(* We use `nat` as undefined return value.                                   *)
(* The following operator `nat_cast` can help to enforce this convention.    *)
(* ------------------------------------------------------------------------- *)

let nat_cast = new_definition
  `nat_cast n = if n In nat then n else nat`;;

let NAT_CAST_OF_NUM = prove
 (`!n. nat_cast(nat_of_num n) = nat_of_num n`,
  REWRITE_TAC[nat_cast; NAT_OF_NUM_IN_NAT]);;

let FORALL_NAT_CAST = prove
 (`!P. (!n:num. P n) <=> (!n. P (num_of_nat n))`,
  MESON_TAC[NUM_OF_NAT_SURJ]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operators.                                                     *)
(* ------------------------------------------------------------------------- *)

let define_nat_op =
  let eth = prove
   (`!nop. ?op. !n. op n = if n In nat then &(nop (num_of_nat n)) else nat`,
    GEN_TAC THEN
    EXISTS_TAC `\n. if n In nat then &(nop (num_of_nat n)) else nat` THEN
    REWRITE_TAC[NAT_OF_NUM_IN_NAT]) in
  let pth = prove
   (`!nop op.
       (!n. op n = if n In nat then &(nop (num_of_nat n)) else nat)
       ==> !n. op (&n) : set = &(nop n)`,
    REPEAT GEN_TAC THEN DISCH_THEN
      (fun th -> REWRITE_TAC[th; NAT_OF_NUM_IN_NAT; NUM_OF_NAT_OF_NUM])) in
  fun (s,tm) ->
    let th = new_specification [s] (SPEC tm eth) in
    th, MATCH_MP pth th;;

let nat_fact,NAT_FACT = define_nat_op("nat_fact",`FACT`);;

let define_nat_binop =
  let eth = prove
   (`!nop. ?op. !m n.
       op m n = if m In nat /\ n In nat
                then &(nop (num_of_nat m) (num_of_nat n))
                else nat`,
    GEN_TAC THEN
    EXISTS_TAC `\m n. if m In nat /\ n In nat
                      then &(nop (num_of_nat m) (num_of_nat n))
                      else nat` THEN
    REWRITE_TAC[NAT_OF_NUM_IN_NAT]) in
  let pth = prove
   (`!nop op.
       (!m n. op m n = if m In nat /\ n In nat
                       then &(nop (num_of_nat m) (num_of_nat n))
                       else nat)
       ==> !m n. op (&m) (&n) : set = &(nop m n)`,
    REPEAT GEN_TAC THEN DISCH_THEN
      (fun th -> REWRITE_TAC[th; NAT_OF_NUM_IN_NAT; NUM_OF_NAT_OF_NUM])) in
  fun (s,tm) ->
    let th = new_specification [s] (SPEC tm eth) in
    th, MATCH_MP pth th;;

let nat_add,NAT_ADD = define_nat_binop("nat_add",`(+):num->num->num`);;
let nat_sub,NAT_SUB = define_nat_binop("nat_sub",`(-):num->num->num`);;
let nat_mul,NAT_MUL = define_nat_binop("nat_mul",`( * ):num->num->num`);;
let nat_div,NAT_DIV = define_nat_binop("nat_div",`(DIV):num->num->num`);;
let nat_mod,NAT_MOD = define_nat_binop("nat_mod",`(MOD):num->num->num`);;

let define_nat_rel =
  let eth = prove
   (`!nrel. ?rel. !m n.
       rel m n <=> m In nat /\ n In nat /\ nrel (num_of_nat m) (num_of_nat n)`,
    GEN_TAC THEN EXISTS_TAC
      `\m n. m In nat /\ n In nat /\ nrel (num_of_nat m) (num_of_nat n)` THEN
    REWRITE_TAC[]) in
  let pth = prove
   (`!nrel rel.
       (!m n. rel m n <=>
              m In nat /\ n In nat /\ nrel (num_of_nat m) (num_of_nat n))
       ==> !m n. rel (&m) (&n) <=> nrel m n`,
    REPEAT GEN_TAC THEN DISCH_THEN
      (fun th -> REWRITE_TAC[th; NAT_OF_NUM_IN_NAT; NUM_OF_NAT_OF_NUM])) in
  fun (s,tm) ->
    let th = new_specification [s] (SPEC tm eth) in
    th, MATCH_MP pth th;;

let nat_lt,NAT_LT = define_nat_rel("nat_lt",`(<):num->num->bool`);;
let nat_gt,NAT_GT = define_nat_rel("nat_gt",`(>):num->num->bool`);;
let nat_le,NAT_LE = define_nat_rel("nat_le",`(<=):num->num->bool`);;
let nat_ge,NAT_GE = define_nat_rel("nat_ge",`(>=):num->num->bool`);;

let NUM_OF_NAT_ADD = prove
 (`!m n. num_of_nat (nat_add (&m) (&n)) = m + n`,
  REWRITE_TAC[FORALL_NUM_OF_NAT; NAT_ADD; NUM_OF_NAT_OF_NUM]);;

let NAT_ADD_IN_NAT = prove
 (`!m n. &(num_of_nat(nat_add m n)) = nat_add m n`,
    GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[nat_add] THEN
    COND_CASES_TAC THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM])
     ASM_SIMP_TAC[GSYM NAT_ADD; NUM_OF_NAT_ADD]
    );;

REWRITE_RULE[GSYM NAT_OF_NUM_EQ; FORALL_NAT_CAST; GSYM NUM_OF_NAT_ADD] ADD_ASSOC;;
REWRITE_RULE[GSYM NUM_OF_NAT_ADD] ADD_ASSOC;;



let NAT_OF_NUM_THM =
  let op_thl = map GSYM [NAT_OF_NUM_EQ;
    NAT_ADD; NAT_SUB; NAT_MUL; NAT_DIV; NAT_MOD]
  and pthl = [RIGHT_IMP_FORALL_THM; IMP_IMP; FORALL_NUM_OF_NAT] in
  SIMP_RULE[NAT_OF_NUM_OF_NAT] o
  PURE_REWRITE_RULE (pthl @ op_thl);;

NAT_OF_NUM_THM ADD_SYM;;

let NAT_ADD_SYM = NAT_OF_NUM_THM ADD_SYM;;
let NAT_ADD_ASSOC = NAT_OF_NUM_THM ADD_ASSOC;;


  let op_thl = map GSYM [nat_add; nat_sub; nat_mul; nat_div; nat_mod]
  and pthl = [GSYM NAT_OF_NUM_EQ;
     GSYM FORALL_NAT; IMP_IMP; RIGHT_IMP_FORALL_THM] in
  let thl = op_thl @ pthl in
  (GEN_REWRITE_RULE DEPTH_CONV thl o GEN_ALL)
  ADD_SYM;;

search[`(+):num->num->num`; name "ADD"];;


let add_thms = search[`(+):num->num->num`; name "ADD"];;

let [NAT_ADD;
     NAT_ADD1;
     NAT_ADD_AC;
     NAT_ADD_ASSOC;
     NAT_ADD_SYM;
     NAT_ADD_CLAUSES;
     NAT_ADD_EQ_0;
     NAT_ADD_SUB;
     NAT_ADD_SUB2;
     NAT_ADD_SUBR;
     NAT_ADD_SUBR2;
     NAT_ADD_SUC] =
  map NAT_OF_NUM_THM
    [ADD;
     ADD1;
     ADD_AC;
     ADD_ASSOC;
     ADD_SYM;
     ADD_CLAUSES;
     ADD_EQ_0;
     ADD_SUB;
     ADD_SUB2;
     ADD_SUBR;
     ADD_SUBR2;
     ADD_SUC];;


(* 

# 
val it : (string * thm) list =
  [("ADD", |- (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n)));
   ("ADD1", |- !m. SUC m = m + 1); ("ADD_0", |- !m. m + 0 = m);
   ("ADD_AC",
    |- m + n = n + m /\ (m + n) + p = m + n + p /\ m + n + p = n + m + p);
   ("ADD_ASSOC", |- !m n p. m + n + p = (m + n) + p);
   ("ADD_CLAUSES",
    |- (!n. 0 + n = n) /\
       (!m. m + 0 = m) /\
       (!m n. SUC m + n = SUC (m + n)) /\
       (!m n. m + SUC n = SUC (m + n)));
   ("ADD_EQ_0", |- !m n. m + n = 0 <=> m = 0 /\ n = 0);
   ("ADD_SUB", |- !m n. (m + n) - n = m);
   ("ADD_SUB2", |- !m n. (m + n) - m = n);
   ("ADD_SUBR", |- !m n. n - (m + n) = 0);
   ("ADD_SUBR2", |- !m n. m - (m + n) = 0);
   ("ADD_SUC", |- !m n. m + SUC n = SUC (m + n));
   ("ADD_SYM", |- !m n. m + n = n + m);

   ("DIST_ADD2", |- !m n p q. dist (m + n,p + q) <= dist (m,p) + dist (n,q));
   ("DIST_ADD2_REV",
    |- !m n p q. dist (m,p) <= dist (m + n,p + q) + dist (n,q));
   ("DIST_ADDBOUND", |- !m n. dist (m,n) <= m + n);
   ("DIST_LADD", |- !m p n. dist (m + n,m + p) = dist (n,p));
   ("DIST_LADD_0", |- !m n. dist (m + n,m) = n);
   ("DIST_RADD", |- !m p n. dist (m + p,n + p) = dist (m,n));
   ("DIST_RADD_0", |- !m n. dist (m,m + n) = n);
   ("DIV_ADD",
    |- !d a b.
           d divides a \/ d divides b ==> (a + b) DIV d = a DIV d + b DIV d);
   ("DIV_ADD_MOD",
    |- !a b n.
           ~(n = 0)
           ==> ((a + b) MOD n = a MOD n + b MOD n <=>
                (a + b) DIV n = a DIV n + b DIV n));
   ("DIV_MULT_ADD",
    |- (!a b n. ~(n = 0) ==> (a * n + b) DIV n = a + b DIV n) /\
       (!a b n. ~(n = 0) ==> (n * a + b) DIV n = a + b DIV n) /\
       (!a b n. ~(n = 0) ==> (b + a * n) DIV n = b DIV n + a) /\
       (!a b n. ~(n = 0) ==> (b + n * a) DIV n = b DIV n + a));
   ("EQ_ADD_LCANCEL", |- !m n p. m + n = m + p <=> n = p);
   ("EQ_ADD_LCANCEL_0", |- !m n. m + n = m <=> n = 0);
   ("EQ_ADD_RCANCEL", |- !m n p. m + p = n + p <=> m = n);
   ("EQ_ADD_RCANCEL_0", |- !m n. m + n = n <=> m = 0);
   ("EVEN_ADD", |- !m n. EVEN (m + n) <=> EVEN m <=> EVEN n);
   ("EXP_ADD", |- !m n p. m EXP (n + p) = m EXP n * m EXP p);
   ("HREAL_OF_NUM_ADD", |- !m n. hreal_add (&m) (&n) = &(m + n));
   ("INT_OF_NUM_ADD", |- !m n. &m + &n = &(m + n));
   ("INT_POW_ADD", |- !x m n. x pow (m + n) = x pow m * x pow n);
   ("LEFT_ADD_DISTRIB", |- !m n p. m * (n + p) = m * n + m * p);
   ("LET_ADD2", |- !m n p q. m <= p /\ n < q ==> m + n < p + q);
   ("LE_ADD", |- !m n. m <= m + n);
   ("LE_ADD2", |- !m n p q. m <= p /\ n <= q ==> m + n <= p + q);
   ("LE_ADDR", |- !m n. n <= m + n);
   ("LE_ADD_LCANCEL", |- !m n p. m + n <= m + p <=> n <= p);
   ("LE_ADD_RCANCEL", |- !m n p. m + p <= n + p <=> m <= n);
   ("LTE_ADD2", |- !m n p q. m < p /\ n <= q ==> m + n < p + q);
   ("LT_ADD", |- !m n. m < m + n <=> 0 < n);
   ("LT_ADD2", |- !m n p q. m < p /\ n < q ==> m + n < p + q);
   ("LT_ADDR", |- !m n. n < m + n <=> 0 < m);
   ("LT_ADD_LCANCEL", |- !m n p. m + n < m + p <=> n < p);
   ("LT_ADD_RCANCEL", |- !m n p. m + p < n + p <=> m < n);
   ("MOD_ADD_CASES",
    |- !m n p.
           m < p /\ n < p
           ==> (m + n) MOD p = (if m + n < p then m + n else (m + n) - p));
   ("MOD_ADD_MOD", |- !a b n. (a MOD n + b MOD n) MOD n = (a + b) MOD n);
   ("MOD_MULT_ADD",
    |- (!m n p. (m * n + p) MOD n = p MOD n) /\
       (!m n p. (n * m + p) MOD n = p MOD n) /\
       (!m n p. (p + m * n) MOD n = p MOD n) /\
       (!m n p. (p + n * m) MOD n = p MOD n));
   ("MONOIDAL_ADD", |- monoidal (+));
   ("NADD_ADD",
    |- !x y. dest_nadd (nadd_add x y) = (\n. dest_nadd x n + dest_nadd y n));
   ("NADD_ADDITIVE",
    |- !x. ?B. !m n.
                   dist (dest_nadd x (m + n),dest_nadd x m + dest_nadd x n) <=
                   B);
   ("NADD_ALTMUL",
    |- !x y.
           ?A B.
               !n. dist
                   (n * dest_nadd x (dest_nadd y n),
                    dest_nadd x n * dest_nadd y n) <=
                   A * n + B);
   ("NADD_BOUND", |- !x. ?A B. !n. dest_nadd x n <= A * n + B);
   ("NADD_CAUCHY",
    |- !x. ?B. !m n.
                   dist (m * dest_nadd x n,n * dest_nadd x m) <= B * (m + n));
   ("NADD_DIST_LEMMA",
    |- !x. ?B. !m n. dist (dest_nadd x (m + n),dest_nadd x m) <= B * n);
   ("NADD_LE_TOTAL_LEMMA",
    |- !x y.
           ~nadd_le x y
           ==> (!B. ?n. ~(n = 0) /\ dest_nadd y n + B < dest_nadd x n));
   ("NADD_MULTIPLICATIVE",
    |- !x. ?B. !m n.
                   dist (dest_nadd x (m * n),m * dest_nadd x n) <= B * m + B);
   ("NADD_MUL_LINV_LEMMA0",
    |- !x. ~nadd_eq x (nadd_of_num 0)
           ==> (?A B. !n. nadd_rinv x n <= A * n + B));
   ("NADD_MUL_LINV_LEMMA4",
    |- !x. ~nadd_eq x (nadd_of_num 0)
           ==> (?N. !m n.
                        N <= m /\ N <= n
                        ==> (dest_nadd x m * dest_nadd x n) *
                            dist (m * nadd_rinv x n,n * nadd_rinv x m) <=
                            (m * n) *
                            dist (m * dest_nadd x n,n * dest_nadd x m) +
                            (dest_nadd x m * dest_nadd x n) * (m + n)));
   ("NADD_MUL_LINV_LEMMA5",
    |- !x. ~nadd_eq x (nadd_of_num 0)
           ==> (?B N.
                    !m n.
                        N <= m /\ N <= n
                        ==> (dest_nadd x m * dest_nadd x n) *
                            dist (m * nadd_rinv x n,n * nadd_rinv x m) <=
                            B * (m * n) * (m + n)));
   ("NADD_MUL_LINV_LEMMA6",
    |- !x. ~nadd_eq x (nadd_of_num 0)
           ==> (?B N.
                    !m n.
                        N <= m /\ N <= n
                        ==> (m * n) *
                            dist (m * nadd_rinv x n,n * nadd_rinv x m) <=
                            B * (m * n) * (m + n)));
   ("NADD_MUL_LINV_LEMMA7",
    |- !x. ~nadd_eq x (nadd_of_num 0)
           ==> (?B N.
                    !m n.
                        N <= m /\ N <= n
                        ==> dist (m * nadd_rinv x n,n * nadd_rinv x m) <=
                            B * (m + n)));
   ("NADD_MUL_LINV_LEMMA7a",
    |- !x. ~nadd_eq x (nadd_of_num 0)
           ==> (!N. ?A B.
                        !m n.
                            m <= N
                            ==> dist (m * nadd_rinv x n,n * nadd_rinv x m) <=
                                A * n + B));
   ("NADD_MUL_LINV_LEMMA8",
    |- !x. ~nadd_eq x (nadd_of_num 0)
           ==> (?B. !m n.
                        dist (m * nadd_rinv x n,n * nadd_rinv x m) <=
                        B * (m + n)));
   ("NADD_OF_NUM_ADD",
    |- !m n.
           nadd_eq (nadd_add (nadd_of_num m) (nadd_of_num n))
           (nadd_of_num (m + n)));
   ("NAT_ADD_ASSOC", |- !m n p. &(m + n + p) = &((m + n) + p));
   ("NAT_ADD_NUM",
    |- !m n.
           m In nat /\ n In nat
           ==> num_of_nat m + num_of_nat n = num_of_nat (nat_add m n));
   ("NAT_ADD_SYM", |- !m n. &(m + n) = &(n + m));
   ("NEUTRAL_ADD", |- neutral (+) = 0);
   ("NSUM_ADD",
    |- !f g s. FINITE s ==> nsum s (\x. f x + g x) = nsum s f + nsum s g);
   ("NSUM_ADD_GEN",
    |- !f g s.
           FINITE {x | x IN s /\ ~(f x = 0)} /\
           FINITE {x | x IN s /\ ~(g x = 0)}
           ==> nsum s (\x. f x + g x) = nsum s f + nsum s g);
   ("NSUM_ADD_NUMSEG",
    |- !f g m n. nsum (m..n) (\i. f i + g i) = nsum (m..n) f + nsum (m..n) g);
   ("NSUM_ADD_SPLIT",
    |- !f m n p.
           m <= n + 1
           ==> nsum (m..n + p) f = nsum (m..n) f + nsum (n + 1..n + p) f);
   ("NUMSEG_ADD_SPLIT",
    |- !m n p. m <= n + 1 ==> m..n + p = (m..n) UNION (n + 1..n + p));
   ("NUM_OF_INT_ADD",
    |- !x y.
           &0 <= x /\ &0 <= y
           ==> num_of_int (x + y) = num_of_int x + num_of_int y);
   ("ODD_ADD", |- !m n. ODD (m + n) <=> ~(ODD m <=> ODD n));
   ("REAL_OF_NUM_ADD", |- !m n. &m + &n = &(m + n));
   ("REAL_POW_ADD", |- !x m n. x pow (m + n) = x pow m * x pow n);
   ("RIGHT_ADD_DISTRIB", |- !m n p. (m + n) * p = m * p + n * p);
   ("SUB_ADD", |- !m n. n <= m ==> m - n + n = m);
   ("SUB_ADD_LCANCEL", |- !m n p. (m + n) - (m + p) = n - p);
   ("SUB_ADD_RCANCEL", |- !m n p. (m + p) - (n + p) = m - n);
   ("SUM_ADD_SPLIT",
    |- !f m n p.
           m <= n + 1
           ==> sum (m..n + p) f = sum (m..n) f + sum (n + 1..n + p) f);
   ("TREAL_OF_NUM_ADD",
    |- !m n.
           treal_of_num m treal_add treal_of_num n treal_eq
           treal_of_num (m + n))]
*)