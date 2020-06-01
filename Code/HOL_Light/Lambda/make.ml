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
loadt "Lambda/new_dbmonad.ml";;         (* dB-monads                        *)
loadt "Lambda/new_dbmodule.ml";;        (* dB-modules                       *)
loadt "Lambda/dblambda.ml";;            (* Lambda calculus                  *)
(* loadt "Lambda/transition.ml";; *)    (* Transition monad for cbv         *)

(* OLD STUFF *)
(*
loadt "Lambda/dblambda.ml";;            (* Lambda (de Bruijn) calculus.     *)
loadt "Lambda/betaeta.ml";;             (* Beta and eta rules.              *)
loadt "Lambda/lambda.ml";;              (* Lambda calculus modulo beta-eta. *)
loadt "Lambda/dbmonad.ml";;             (* Operads and modules.             *)
loadt "Lambda/univ.ml";;                (* Universal property of lc.        *)
loadt "Lambda/rules.ml";;               (* Reduction module.                *)
*)