(* This module defines trees over functors represented by containers
(i.e. fixpoints of functors). *)

Require Export Vector.
Require Export Container.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Export Coq.Program.Equality.
Require Export Algebra.

Set Implicit Arguments.

Section Tree.

Set Implicit Arguments.


Variable C : Cont.

Inductive Tree : Type := 
| In : Ext C Tree -> Tree.


(* Custom induction principle. *)

Fixpoint Tree_ind' (P : Tree -> Prop)
         (step : forall  (args : Ext C Tree),
                   cforall P args -> P (In args))
         g : P g :=
  match g with 
    | In args => step args (fun p => Tree_ind' step (elems args p))
  end.

End Tree.



(* This defines the fold corresponding to the given algebra. *)

Fixpoint fold {C R} (alg : Alg C R) (g : Tree C) : R :=
  match g with
    | In args => alg (cmap (fold alg) args)
  end.

Ltac tree_ind g := induction g using Tree_ind';simpl; auto.

(* Fold fusion theorem. *)

Theorem fold_fusion
        {C R1 R2}
        (alg1 : Alg C R1)
        (alg2 : Alg C R2)
        (g : Tree C) (f : R1 -> R2) :
  (forall x, f (alg1 x) = alg2 (cmap f x)) -> 
  f (fold alg1 g) = fold alg2 g.
Proof.
  
  intros Hom. tree_ind g.
  
  rewrite Hom. rewrite cmap_cmap. f_equal. 
  apply cforall_rewrite. unfold compose. unfold cforall in *. auto.
Qed.