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

type_invention_warning := false;;
needs "Library/rstc.ml";;               (* Refl, symm, trans closure.       *)
needs "Library/iter.ml";;               (* Iteration.                       *)
type_invention_warning := true;;

loadt "Lambda/lib.ml";;                 (* Misc tactics and theorems        *)
loadt "Lambda/dblambda.ml";;            (* Lambda calculus                  *)
loadt "Lambda/dbmonad.ml";;             (* dB-monads                        *)
loadt "Lambda/dbmodule.ml";;            (* dB-modules                       *)
loadt "Lambda/dblambda_initial.ml";;    (* Lambda calculus is initial       *)

loadt "Lambda/lambda.ml";;              (* Lambda calculus modulo beta-eta. *)
loadt "Lambda/substoid.ml";;            (* Substoids and modules.           *)
loadt "Lambda/univ.ml";;                (* Universal property of lc.        *)
loadt "Lambda/rules.ml";;               (* Reduction module.                *)