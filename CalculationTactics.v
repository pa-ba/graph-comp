(* $Id: calculationalFormProof.v,v 1.4 2009-05-19 17:23:26 julien Exp $ *)

(** * Definition of tactics for the step by step refinement of
   specification The purpose here is to have an interactive refinement
   which remains readable and for which the proof of equivalence
   beetween each step is certified by coq.  This proof should be as
   automatic as possible so that the user can focus on the derivation
   itself.  *)
Require Import String.
Require Export Setoid.


(* Module Type AbstractEquivalence. *)
(* Parameter A : Type. *)
(* Parameter R : A->A->Prop. *)
(* Instance  equiv_R : Equivalence  R. *)

(* End AbstractEquivalence. *)


(* Module CalcProof ( S : AbstractEquivalence). *)

(* Export S. *)

(* Add Parametric Relation  : (A) (R) *)
(*  reflexivity proved by (bisim_refl) *)
(*  symmetry proved by (bisim_sym) *)
(*  transitivity proved by (bisim_trans) *)
(*  as bisim_rel. *)

(* Parameter A : Type.  *)
(* Parameter R : A -> A-> Prop.  *)

Inductive state : Prop :=
  RHS : state
| LHS : state
| BOTH_SIDE : state
| ADHOC : forall s:string, state.  
Require Import List.


Inductive memo (s: state) : Prop :=
  mem  :  memo s
.

Tactic Notation "memorize" constr(s) := 
  pose ( mem _ : memo s)
.
Tactic Notation "setRHS" := 
  first [(match goal with 
    | [ H  : memo RHS |- _]=> idtac "already RHS"
    | [ H  : memo LHS |- _]=> clear H; memorize RHS
    | [ H  : memo BOTH_SIDE |- _]=> clear H; memorize RHS
    | [ H  : memo (ADHOC ?s) |- _]=> memorize RHS
  end
  ) | (memorize RHS)]
.


Tactic Notation "setLHS" := 
  first [(match goal with 
    | [ H  : memo RHS |- _]=> clear H ; memorize LHS
    | [ H  : memo LHS |- _]=> idtac "already LHS"
    | [ H  : memo BOTH_SIDE |- _]=> clear H ; memorize LHS
    | [ H  : memo (ADHOC ?s) |- _]=> memorize LHS
  end
  ) | (memorize LHS)]
.

Tactic Notation "setBOTH_SIDE" := 
  first [(match goal with 
    | [ H  : memo RHS |- _]=> clear H ; memorize BOTH_SIDE
    | [ H  : memo LHS |- _]=> clear H ; memorize BOTH_SIDE
    | [ H  : memo BOTH_SIDE |- _]=> idtac "already BOTH_SIDE"
    | [ H  : memo (ADHOC ?s) |- _]=> memorize BOTH_SIDE
  end
  ) | (memorize BOTH_SIDE)]
.


Tactic Notation (at level 0) "if_RHS_LHS_BOTH_NOTH"  tactic(trhs) tactic(tlhs) tactic(tboth) tactic(tnoth) :=
  (lazymatch goal with
    | [ H : memo RHS |- _]=> trhs
    | [ H : memo LHS |- _]=>  tlhs
    | [ H : memo BOTH_SIDE |- _]=> tboth
    | _ => tnoth
  end
)
  .

Tactic Notation  (at level 0)  "if_RHS_LHS_BOTH"  tactic(trhs) tactic(tlhs) tactic(tboth)  :=
  if_RHS_LHS_BOTH_NOTH  (trhs) (tlhs) (tboth) (fail "no side indication").
  Require Export Setoid.

Require Export Relation_Definitions.


Tactic Notation "is_equivalence" constr(R) :=
  let H:= fresh in assert (Equivalence R) by (typeclasses eauto); clear H.

(** Selection of the side to rewrite in the equation *)
(** Right Side  *)
Tactic Notation  (at level 1)  "RHS" tactic(t) :=
  (if_RHS_LHS_BOTH_NOTH
    (idtac) 
    (idtac;
      match goal with 
        | [|- (?R ?lhs  ?rhs)] =>  subst rhs
      end
    ) 
    (idtac)
    (idtac)
  ) ;
  setRHS;
  match goal with 
    | [|-?R ?lhs ?rhs] =>  is_equivalence R;let LHS := fresh "LHS" in set (LHS:=lhs);
      assert(R LHS   rhs);[|assumption]
  end
  ;
  t.

(** Left Side  *)
Tactic Notation (at level 1) "LHS" tactic(t) :=
  (if_RHS_LHS_BOTH_NOTH
  (idtac;
    match goal with 
      | [|-?R ?lhs ?rhs] =>  subst lhs
    end
  ) 
  (idtac
  ) 
  (idtac)
  (idtac)
  );
  setLHS;
  match goal with 
    | [|-?R ?lhs ?rhs] =>  is_equivalence R; let RHS := fresh "RHS" in set (RHS:=rhs);
      assert(R lhs   RHS);[|assumption]
  end;
  t
  .

(** Both Side  *)
Tactic Notation  (at level 1)  "BOTH_SIDE" tactic(t) :=
  (if_RHS_LHS_BOTH_NOTH
  (idtac;
    match goal with 
      | [|-?R ?lhs ?rhs] =>  subst lhs
    end
  ) 
  (idtac;
    match goal with 
      | [|-?R ?lhs ?rhs] =>  subst rhs
    end
  ) 
  (idtac)
  (idtac)
  );
  setBOTH_SIDE;
  t
  .
  

(* debbuging tactics *)
Ltac print_goal :=
  match goal with
    [|-?G]=> idtac G
end.


(** *Derivation tactics  *)

(**Elimination of existentially quantified variable *)
Tactic Notation "elim_ex" constr(e):=
  repeat (
    match (type of e) with 
      | exists x,_ => econstructor 
      | sig _ => econstructor 
      | _ => fail
    end
    )
.
Tactic Notation "econstructors" := 
  repeat( match goal with 
            | [|- exists A :?T,_] => 
              econstructor
            | [|-sig _] => econstructor 
          end
 ).


(** Start an interactive derivation session*)
Ltac Begin := 
  intros;
  match goal with 
    | [|-?R ?lhs ?rhs] => is_equivalence R; idtac
    | [|- exists A ,_] =>
      econstructors;Begin
    | [|- sig _] =>
      econstructors;Begin
    | _ => idtac "no existential, no equivalence"
  end.

(** Start an interactive derivation session*)
Ltac BeginDebug := 
  intros;
  match goal with 
    | [|-?R ?LHS ?rhs] =>  is_equivalence R;idtac "Goal";print_goal
    | [|- exists A :?T,?B] =>  
      idtac "Existential goal ";print_goal; econstructors; BeginDebug
  end.


(** End of an interactive derivation session *)
Tactic Notation "[]" := 
  BOTH_SIDE reflexivity.

(** this tactic adds e=e2 in hypothesis if it can be proved by 1 rewritting step (using e1)
   then e is rewritted in e2 in the goal  *)
Tactic Notation "proved" constr(e) "=" "{" constr(e1) "}" constr(e2) :=
  let h := fresh in assert (h : e = e2) by (rewrite e1;reflexivity) ;rewrite h.

Tactic Notation "proved" constr(e) "=" "{" tactic(t1) "}" constr(e2) :=
  let h := fresh in assert (h : e = e2) by (t1;reflexivity) ;rewrite h.

Tactic Notation "proved" constr(e) "=" "{" constr(e1) "}" "using" constr(R) constr(e2) :=
  let h := fresh in assert (h : R e e2) by (rewrite e1;reflexivity) ;rewrite h.
Tactic Notation "proved" constr(e) "=" "{" tactic(t1) "}" "using" constr(R) constr(e2) :=
  let h := fresh in assert (h : R e e2) by (t1;reflexivity) ;rewrite h.

Tactic Notation  (at level 2)    "=" "{"tactic(t1) "}" constr(e2) :=
  if_RHS_LHS_BOTH
  (idtac;
    match goal with
      | [|-?R ?lhs ?rhs] =>
        is_equivalence R;
      first [let h := fresh "rewriting" in 
             assert(h : R rhs e2) by (t1;reflexivity) ;rewrite h| fail 2]
      | _ => fail 1 "goal is not an equivalence"
    end)
  (idtac;
    match goal with
     [|-?R ?lhs ?rhs] =>
     is_equivalence R;
     first [let h := fresh "rewriting" in 
       assert(h : R lhs e2) by (t1;reflexivity) ;rewrite h | fail 2]
      | _ => fail 1 "goal is not an equivalence"
   end
  )
  (idtac;
    match goal with
     [|-?R ?lhs ?rhs] =>
     is_equivalence R;
     match e2 with
       | ?R ?lhs_e2  ?rhs_e2 =>
         is_equivalence R;
       first [
         let h := fresh "rewriting" in 
           assert(h : R lhs lhs_e2) by (t1;reflexivity) ;
           rewrite h;
             let h2 := fresh "rewriting" in 
               assert(h : R rhs rhs_e2) by (t1;reflexivity) ;
               rewrite h2 | fail 3]
       | _ => fail 2 e2 " is not an equivalence"
     end
     | _ => fail 1 "goal is not an equivalence"
   end
  )
  .

Tactic Notation (at level 2 )   "=" "{" tactic(t1) "}d" constr(e2) :=
 info(  = { t1 } e2).



(** Starting form a goal with a LHS=RHS form, this tactic adds LHS=e2 in hypothesis if it can be proved by 1 rewritting step at place given by the function f using the equality e2
   then LHS is rewritted in e2 in the goal 
example with a goal x+x+x+x+x we want rewrite it as 2x+x+2x using ax: forall x, x+x=2x : 
    LHS 
    ={ pat (fun l=> l+x+l) (ax x)}
    2*x+x+2*x

*)
Tactic Notation "pat" constr(f) constr(e1)  :=
  refine (eq_ind_r f _ e1) || fail "refining failed"
.



(** derivations true by definition of a given term*)
Tactic Notation "by" "def" reference(e1) :=
  first [progress unfold e1 | idtac "cannot unfold " e1 ; fail ].



(** derivation by tactics t   *)
Tactic Notation "!<"tactic(t) ">" (* ident(e2) *) :=
  t.

Tactic Notation "!<" "apply" constr(thm) ">":=
    apply thm;intros.


 
(** check that e1 is the LHS*)
Tactic Notation "check" constr(e1) "is" "LHS" (* ident(e2) *) :=
match goal with 
  [|- ?R e1?RHS] =>  is_equivalence R;idtac "OK"
  | _ => idtac "failed";fail
end.

(** check that e1 is the GOAL*)
Tactic Notation "check" constr(e1) "is" "GOAL" :=
match goal with 
  [|-e1] =>  idtac "OK"
  | _ => idtac "failed";fail
end.

(* (** check that e1 is the LHS*) *)
(* Tactic Notation "case" constr(e1) := *)
(*   if_RHS_LHS_BOTH *)
(*   (idtac; *)
(*     match goal with *)
(*       | [|-?lhs=?rhs] => let h:=fresh in *)
(*           (assert(h :rhs=-= e1) by (reflexivity)||fail);clear h *)
(*     end) *)
(*   (idtac; *)
(*     match goal with *)
(*      [|-?lhs=?rhs] =>let h:=fresh in *)
(*           (assert(h :lhs=-= e1) by (reflexivity)||fail);clear h *)
(*    end *)
(*   ) *)
(*   (idtac; *)
(*     match goal with *)
(*      [|-?lhs=?rhs] => *)
(*      match e1 with *)
(*        | ?lhs_e2 = ?rhs_e2 => *)
(*          let h := fresh "rewriting" in  *)
(*            (assert(h : R lhs lhs_e2) by (reflexivity)||fail) ; *)
(*            clear h; *)
(*            let h2 := fresh "rewriting" in  *)
(*              (assert(h : R rhs rhs_e2) by (reflexivity)||fail) ; *)
(*                clear h2 *)
(*      end *)
(*    end *)
(*   ) *)
(*   . *)


(** check that e1 is the GOAL*)
Tactic Notation "check" constr(e1) "is" "GOAL" :=
match goal with 
  [|-e1] =>  idtac "OK"
  | _ => idtac "failed";fail
end.

(* End CalcProof. *)
