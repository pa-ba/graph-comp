(* Proof of Theorem 2 from the paper *)

Require Import Graph.
Require Import Tree.
Require Import Coq.Program.Basics.

Set Implicit Arguments.

(* Definition of unravelling. *)

Definition unravelM {A C} (e : Env (Tree C) A) : GraphM C A -> Tree C :=
  ufoldM e (fun x => In x).

Definition unravel {C} : Graph C -> Tree C :=
  unravelM (Empty (zero _)).

(* Lemma detailing how unravelling affects let bindings. *)

Lemma unravelM_let {C A} {b : GraphM C A} {s e} : 
  unravelM e (Let b s) = unravelM (Extend (unravelM e b) e) s.
Proof.
  reflexivity.
Qed.

(* Monadic version of Theorem 2. *)

Theorem ufoldM_fold {R C A} (alg : Alg C R) (g : GraphM C A)
(e : Env (Tree C) A) : 
  ufoldM (emap (fold alg) e) alg g = fold alg (unravelM e g).
Proof.
  unfold ufoldM.
  intros. generalize dependent A. induction g using Graph_ind'; intros; simpl.
  simpl. rewrite cmap_cmap. unfold compose. simpl. f_equal.
  cmap_eq. apply H.

  apply emap_lookup. 

  rewrite IHg1 by assumption. rewrite unravelM_let. simpl. rewrite <- IHg2.
  reflexivity.
Qed.

(* Theorem 2. *)

Theorem ufold_fold {R C} (alg : Alg C R) (g : Graph C):
  ufold alg  g = fold alg (unravel g).
Proof.
  unfold ufold, unravel. rewrite <- ufoldM_fold. simpl. repeat f_equal. symmetry.
  apply zero_unique.
Qed.

(* Some convenience lemmas that detail how unravelling works on [letx]
and [var]. *)

Lemma unravelM_letx {C A} {b : GraphM C A} {s e} : 
  unravelM e (letx b s) = unravelM (Extend (unravelM e b) e) (s _ tt).
Proof.
  reflexivity.
Qed.

Lemma unravelM_var {C A e v} (x : unit) : 
  unravelM (Extend v e) (var (C := C) (A := A :> unit) x) = v.
Proof.
  unfold var. unfold compose. simpl. unfold unravelM. unfold ufoldM. simpl. destruct x. reflexivity.
Qed.