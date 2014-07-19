Require Export Container.

(* This type captures algebras over a given signature and a given
carrier type [R]. *)

Definition Alg C (R : Type) : Type := Ext C R -> R.
