(* This module defines containers. *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.



Set Implicit Arguments.

Record Cont : Type := cont {shapes: Type; pos: shapes -> Type}.


Record Ext (C:Cont )(X:Type):Type := ext {shape: shapes C; elems : pos C shape -> X }.

Definition cforall {X} (P : X -> Prop) {C} (E : Ext C X) : Prop :=
  forall (p : pos C (shape E)), P (elems E p).
                                              
Definition cmap {C} {X Y} (f : X -> Y) (E : Ext C X) : Ext C Y :=
  {| shape := shape E; elems := (fun p => f (elems E p)) |}.

Lemma cmap_cmap  {X Y Z} (f : X -> Y) (g : Y -> Z) {C} (E : Ext C X) :
  cmap g (cmap f E) = cmap (compose g f) E.
Proof. auto. Qed.
             

Lemma cmap_id {X} {C} (E : Ext C X) :
  cmap (fun x => x) E = E.
Proof. destruct E. reflexivity. Qed.


    

Ltac cmap_eq := intros; unfold cmap; f_equal; simpl; apply functional_extensionality; intros; 
  unfold cforall in *; auto.


Lemma cforall_rewrite {X Y} (f g : X -> Y) {C} (E : Ext C X):
  cforall (fun x => f x = g x) E -> cmap f E = cmap g E.
Proof.
  cmap_eq.
Qed.