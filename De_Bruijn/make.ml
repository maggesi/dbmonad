(* ========================================================================= *)
(*  Initial semantics based on De Bruijn encoding                            *)
(*  with dbmonads and their modules.                                         *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi 2005 2006 2017, 2020                *)
(* ========================================================================= *)

prioritize_num();;

type_invention_warning := false;;
needs "Library/rstc.ml";;               (* Refl, symm, trans closure.       *)
needs "Library/iter.ml";;               (* Iteration.                       *)
type_invention_warning := true;;

loadt "De_Bruijn/lib.ml";;              (* Misc tactics and theorems        *)
loadt "De_Bruijn/dblambda.ml";;         (* Syntax of the Lambda calculus    *)
loadt "De_Bruijn/lambda.ml";;           (* Lambda calculus modulo beta-eta  *)
loadt "De_Bruijn/substoid.ml";;         (* De Bruijn monads and             *)
loadt "De_Bruijn/univ.ml";;             (* Universal property of lc         *)
