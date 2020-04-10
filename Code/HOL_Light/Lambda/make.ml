(* ========================================================================= *)
(*  Lambda Calculus, Operad and the proof of an universal property.          *)
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

loadt "Lambda/lib.ml";;                 (* Misc tactics and theorems.       *)
loadt "Lambda/dblambda.ml";;            (* Lambda (de Bruijn) calculus.     *)
loadt "Lambda/betaeta.ml";;             (* Beta and eta rules.              *)
loadt "Lambda/lambda.ml";;              (* Lambda calculus modulo beta-eta. *)
loadt "Lambda/dbmonad.ml";;             (* Operads and modules.             *)
loadt "Lambda/univ.ml";;                (* Universal property of lc.        *)
