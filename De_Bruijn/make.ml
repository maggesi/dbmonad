(* ========================================================================= *)
(*  Initial semantics based on De Brujin encoding                            *)
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
loadt "De_Bruijn/dblambda.ml";;         (* Lambda calculus                  *)
loadt "De_Bruijn/dbmonad.ml";;          (* dB-monads                        *)
loadt "De_Bruijn/dbmodule.ml";;         (* dB-modules                       *)
loadt "De_Bruijn/dblambda_initial.ml";; (* Lambda calculus is initial       *)

loadt "De_Bruijn/lambda.ml";;           (* Lambda calculus modulo beta-eta  *)
loadt "De_Bruijn/substoid.ml";;         (* Substoids and modules            *)
loadt "De_Bruijn/univ.ml";;             (* Universal property of lc         *)
loadt "De_Bruijn/rules.ml";;            (* Reduction module                 *)
