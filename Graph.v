(* This module defines acylic graphs over functors represented by
containers using Bernardy & Pouillard's 'Names For Free' approach. *)

Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Basics.
Require Export Container.
Require Export Algebra.


Infix "∘" := compose (at level 40, left associativity).

Inductive Vars A V : Type :=
| Old : A -> Vars A V
| New : V -> Vars A V.

Implicit Arguments Old [[A][V]].
Implicit Arguments New [[A][V]].


Infix ":>" := (@Vars) (at level 60, right associativity).

Definition Succ (a : Type) : Type := a :> unit.

Inductive Zero : Type := .

Definition zero (A : Type) (z : Zero) : A :=
  match z with
  end.

Lemma zero_unique {A} (f : Zero -> A) : f = zero A.
Proof.
  apply functional_extensionality. destruct x.
Qed.

Definition Scope (m : Type -> Type)  (A : Type) : Type := m (Succ A).

Section Graph.

Set Implicit Arguments.


Variable C : Cont.

Inductive GraphM : Type -> Type := 
| In : forall A, Ext C (GraphM A) -> GraphM A
| Var : forall A, A -> GraphM A
| Let : forall A, GraphM A -> Scope GraphM A -> GraphM A.


Definition Graph : Type := GraphM Zero.

Implicit Arguments Var [[A]].
Implicit Arguments Let [[A]].
Implicit Arguments In [[A]].


Fixpoint Graph_ind' (P : forall a, GraphM a -> Prop)
         (step : forall a (args : Ext C (GraphM a)),
                   cforall (P a) args -> P a (In args))
         (var : forall a v, P a (Var v))
         (let_ : forall a (g : GraphM a) s, P a g -> P (Succ a) s -> P a (Let g s))
         n t : P n t :=
  match t with 
    | In n args => step n args (fun p => Graph_ind' P step var let_ (elems args p))
    | Var n m => var n m
    | Let n g s => let_ n g s (Graph_ind' P step var let_ g) 
                        (Graph_ind' P step var let_ s)
  end.

Inductive Env A : Type -> Type :=
  | Empty : forall I, (I -> A) -> Env A I
  | Extend : forall I, A -> Env A I -> Env A (Succ I).

Fixpoint emap {I A B} (f : A -> B) (e : Env A I) : Env B I :=
  match e with
    | Empty _ f' => Empty (fun x => f (f' x))
    | Extend _ b r  => Extend (f b) (emap f r)
  end.

Fixpoint lookupEnv {A I} (e : Env A I) : I -> A :=
  match e with
      | Empty _ f => f
      | Extend _ b r => fun v => match v with
                     | Old v' => lookupEnv r v'
                     | New tt => b
                   end
  end.

Lemma emap_lookup {I A B} {e : Env A I} {i : I} {f : A -> B} : lookupEnv (emap f e) i = f (lookupEnv e i).
Proof.
  induction e.
  reflexivity.
  simpl. destruct i. auto. destruct u. reflexivity.
Qed.
    
Fixpoint gfoldM {A R V} (var : V -> R) (le : R -> (V -> R) -> R) (alg : Alg C R) (g : GraphM A) : Env R A -> R :=
  match g with
      | Var _ x => fun e => lookupEnv e x
      | In _ args => fun e => alg (cmap (fun g => gfoldM var le alg g e) args)
      | Let _ b s => fun e => le (gfoldM var le alg b e) 
                                   (fun r => gfoldM var le alg s (Extend (var r) e))
  end.
    

Definition gfold {R V} (var : V -> R) (le : R -> (V -> R) -> R) (alg : Alg C R) (g :Graph) : R 
  := gfoldM var le alg g (Empty (zero _)).

Definition ufoldM {R A} (env : Env R A) (alg : Alg C R) (g : GraphM A) : R 
  :=  gfoldM (fun x => x) (fun b s => s b) alg g env.


Definition ufold {R} : Alg C R -> Graph -> R 
  :=  ufoldM (Empty (zero _)).

Theorem gfoldM_fusion
        {R1 R2 R' A}
        (var1 : R' -> R1) (le1 : R1 -> (R' -> R1) -> R1) (alg1 : Alg C R1) 
        (var2 : R' -> R2) (le2 : R2 -> (R' -> R2) -> R2) (alg2 : Alg C R2) 
        (env1 : Env R1 A) (env2 : Env R2 A)
        (g : GraphM A) (f : R1 -> R2) (f' : R2 -> R1) :
  (forall x, f (alg1 x) = alg2 (cmap f x)) -> 
  (forall b s, f (le1 b s) = le2 (f b) (f ∘ s)) ->
  (forall x, f (var1 x) = var2 x) ->
  (forall x, f (lookupEnv env1 x) = lookupEnv env2 x) ->

  f (gfoldM var1 le1 alg1 g env1) = gfoldM var2 le2 alg2 g env2.
Proof.
  intros Hom Le Var En. induction g using Graph_ind'; simpl.

   rewrite Hom. rewrite cmap_cmap. f_equal. apply
  cforall_rewrite. unfold compose.  unfold cforall in *. auto.

   auto.
  
   rewrite Le. unfold compose. f_equal. 
   apply IHg1. apply En.
   apply functional_extensionality. intros. apply IHg2. induction x0. 
   simpl. auto. simpl. destruct v. auto.
Qed.

End Graph.

Implicit Arguments Var [[C][A]].
Implicit Arguments Let [[C][A]].
Implicit Arguments In [[C][A]].



Definition letx {A C} (b : GraphM C A) (s : forall V , V -> GraphM C (A :> V)) : GraphM C A
:= Let b (s _ tt).

Class Elem (V A : Type) := {
  inj : V -> A
}.

Infix "∈" := (@Elem) (at level 60, right associativity).

Instance Elem_New {V A} : V ∈ (A :> V) := {
  inj := New 
}.

Instance Elem_Old {V V' A} `{V ∈ A} : V ∈ (A :> V') := {
  inj := Old ∘ inj
}.

Definition var {C V A} `{V ∈ A} : V -> GraphM C A := Var ∘ inj.