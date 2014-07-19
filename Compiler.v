(* Implementation of the compiler (both tree-based and graph-based
variant) and proof of Lemma 1 from the paper (compT e = unravel (compG
e).  *)


Require Import Graph.
Require Import Tree.
Require Import GraphUnravel.
Require Import Coq.Program.Basics.
Require Import CalculationTactics.

Require Import Coq.Logic.FunctionalExtensionality.

(* Source language. *)

Inductive Expr : Set :=
  | Val : nat -> Expr
  | Add : Expr -> Expr -> Expr
  | Throw  : Expr
  | Catch : Expr -> Expr -> Expr.

(* For the definition of the source language we have to use containers
in order to instantiate the definition of trees and graphs (which use
containers to represent strictly positive functors). *)

(* The shape type. *)

Inductive CodeSh : Set := 
| PUSH : nat -> CodeSh
| ADD : CodeSh
| THROW : CodeSh
| MARK : CodeSh
| UNMARK : CodeSh
| HALT : CodeSh.

(* Definition of the container to represent the functor [Code] from
the paper. *)

Definition Code : Cont := 
  {| shapes := CodeSh;
    pos := fun s => match s with
                      | PUSH _ => unit
                      | ADD => unit
                      | THROW => Zero
                      | MARK => sum unit unit
                      | UNMARK => unit
                      | HALT => Zero
                    end
   |}.

(* Functions to define unary and binary constructors (of the functor). *)
Definition one {A} (a : A) (x : unit) : A := a.
Definition two {A} (a b : A) (x : sum unit unit) : A := 
  match x with
            | inl _  => a
            | inr _ => b
  end.


(* Definition of the constructors for the [Code] functor. *)
Definition mkPUSH {A} i (c : A) : Ext Code A := (ext Code (PUSH i) (one c)).
Definition mkADD {A} (c : A) : Ext Code A := (ext Code ADD (one c)).
Definition mkTHROW {A} : Ext Code A := (ext Code THROW (zero _)).
Definition mkMARK {A} (c c' : A) : Ext Code A := (ext Code MARK (two c c')).
Definition mkUNMARK {A} (c : A) : Ext Code A := (ext Code UNMARK (one c)).
Definition mkHALT {A}  : Ext Code A := (ext Code HALT (zero _)).

(* Graph variants of the constructors. *)
Import Graph.
Definition gPUSH {A} i c : GraphM Code A := In (mkPUSH i c).
Definition gADD {A} c : GraphM Code A := In (mkADD c).
Definition gTHROW {A} : GraphM Code A := In mkTHROW.
Definition gMARK {A} c c' : GraphM Code A := In (mkMARK c c').
Definition gUNMARK {A} c : GraphM Code A := In (mkUNMARK c).
Definition gHALT {A} : GraphM Code A := In mkHALT.

(* Tree variants of the constructors. *)
Import Tree.
Definition tPUSH i c : Tree Code := In (mkPUSH i c).
Definition tADD c : Tree Code := In (mkADD c).
Definition tTHROW : Tree Code := In mkTHROW.
Definition tMARK c c' : Tree Code := In (mkMARK c c').
Definition tUNMARK c : Tree Code := In (mkUNMARK c).
Definition tHALT : Tree Code := In mkHALT.


Infix "|>" := (apply) (at level 60, right associativity).

(* Definition of the graph-based compiler. *)
Fixpoint compG' {A} (e : Expr) (c : GraphM Code A) : GraphM Code A :=
  match e with
      | Val n =>  gPUSH n |> c
      | Add x y =>  compG' x |> compG' y |> gADD |> c
      | Throw =>  gTHROW
      | Catch x h => letx c (fun _ c' =>
                               gMARK (compG' h |> var c') (compG' x |> gUNMARK |> var c'))
  end.

Definition compG (e : Expr) : Graph Code := compG' e |> gHALT.

(* Definition of the tree-based compiler. *)
Fixpoint compT' (e : Expr) (c : Tree Code) : Tree Code :=
  match e with
      | Val n =>  tPUSH n |> c
      | Add x y =>  compT' x |> compT' y |> tADD |> c
      | Throw =>  tTHROW
      | Catch x h => tMARK (compT' h |> c) (compT' x |> tUNMARK |> c)
  end.

Definition compT (e : Expr) : Tree Code := compT' e |> tHALT.

(* Convenience lemmas that state how unravelling works on the
constructors. *)

Lemma unravelM_mark {A env} {c1 c2 : GraphM Code A} : 
  unravelM env (gMARK c1 c2) = tMARK (unravelM env c1) (unravelM env c2).
Proof.
  unfold unravelM, ufoldM, tMARK, gMARK, mkMARK. simpl. unfold cmap, two. simpl. repeat f_equal.
  apply functional_extensionality. intros. destruct x; reflexivity. 
Qed.

Lemma unravelM_throw {A} {env : Env _ A} :  unravelM env gTHROW = tTHROW.
Proof. 
  unfold gTHROW, tTHROW, mkTHROW, unravelM, ufoldM.  simpl. unfold cmap. simpl. repeat f_equal.
  apply zero_unique.
Qed.

Lemma unravelM_halt {A} {env : Env _ A} :  unravelM env gHALT = tHALT.
Proof. 
  unfold gHALT, tHALT, mkHALT, unravelM, ufoldM.  simpl. unfold cmap. simpl. repeat f_equal.
  apply zero_unique.
Qed.

(* Proof of Lemma 1 from the paper. The following is the main lemma
for the proof, which corresponds to the induction proof from the
paper. *)

Lemma comp_unravelM {A} {e : Expr} {env} {c : GraphM Code A} : compT' e (unravelM env c)
                                                              = unravelM env (compG' e c).
Proof.   Begin.
  unfold compT, unravel, compG, apply. 

  generalize dependent A.  induction e; intros; simpl; unfold apply. 

  reflexivity. 

  rewrite <- IHe1.  rewrite <- IHe2. reflexivity.

  rewrite unravelM_throw. reflexivity.


  RHS
  = { rewrite unravelM_letx }
  (unravelM (Extend (unravelM env c) env)
            (gMARK (compG' e2 (var tt)) (compG' e1 (gUNMARK (var tt))))).
  = { rewrite unravelM_mark }
  (tMARK ( unravelM (Extend (unravelM env c) env) (compG' e2 (var tt)))
         ( unravelM (Extend (unravelM env c) env) (compG' e1 (gUNMARK (var tt))))).
  = { rewrite IHe1 }
      (tMARK ( unravelM (Extend (unravelM env c) env) (compG' e2 (var tt)))
             ( compT' e1 (unravelM (Extend (unravelM env c) env) (gUNMARK (var tt))))).
  = { rewrite IHe2 }
      (tMARK ( compT' e2 (unravelM (Extend (unravelM env c) env)(var tt)))
             ( compT' e1 (unravelM (Extend (unravelM env c) env) (gUNMARK (var tt))))).
  = { reflexivity }
      (tMARK ( compT' e2 (unravelM env c))
             ( compT' e1 (tUNMARK (unravelM env c)))).
  [].
Qed.

(* From the above lemma we can then derive Lemma 1. *)

Lemma comp_unravel {e : Expr} : compT e = unravel (compG e).
Proof.
  unfold compT, compG, apply, unravel. erewrite <- unravelM_halt. eapply comp_unravelM.
Qed.
  

  