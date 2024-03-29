(* ========================================================================= *)
(* Initial semantics based on the De Bruijn encoding                         *)
(* using De Bruijn monads and their modules.                                 *)
(* ========================================================================= *)

prioritize_num();;

type_invention_warning := false;;
needs "Library/rstc.ml";;               (* Refl, symm, trans closure.       *)
needs "Library/iter.ml";;               (* Iteration.                       *)
type_invention_warning := true;;

loadt "De_Bruijn/lib.ml";;              (* Misc tactics and theorems        *)
loadt "De_Bruijn/dblambda.ml";;         (* Syntax of the Lambda calculus    *)
loadt "De_Bruijn/lambda.ml";;           (* Lambda calculus modulo beta-eta  *)
loadt "De_Bruijn/dbmonad.ml";;          (* De Bruijn monads and modules     *)
loadt "De_Bruijn/univ.ml";;             (* Universal property of lc         *)
loadt "De_Bruijn/binding.ml";;          (* Binding signatures               *)
