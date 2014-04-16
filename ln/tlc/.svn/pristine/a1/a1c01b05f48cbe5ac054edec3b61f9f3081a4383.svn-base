(**************************************************************************
* TLC: A library for Coq                                                  *
* Functions                                                               *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic.
Generalizable Variables A.


(* ********************************************************************** *)
(** * Function combinators *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of the combinators *)

(** Indentity function *)

Definition id {A} (x : A) := 
  x.

(** Constant function *)

Definition const {A B} (v : B) : A -> B := 
  fun _ => v.

(** Constant function of higher arities *)

Definition const1 := 
  @const.
Definition const2 {A1 A2 B} (v:B) : A1->A2->B :=
  fun _ _ => v.
Definition const3 {A1 A2 A3 B} (v:B) : A1->A2->A3->B :=
  fun _ _ _ => v.
Definition const4 {A1 A2 A3 A4 B} (v:B) : A1->A2->A3->A4->B :=
  fun _ _ _ _ => v.
Definition const5 {A1 A2 A3 A4 A5 B} (v:B) : A1->A2->A3->A4->A5->B :=
  fun _ _ _ _ _ => v.

(** Function application *)

Definition apply {A B} (f : A -> B) (x : A) :=
  f x.

Definition apply_to (A : Type) (x : A) (B : Type) (f : A -> B) :=
  f x.

(** Function composition *)

Definition compose {A B C} (g : B -> C) (f : A -> B) := 
  fun x => g (f x).

Notation "f1 \o f2" := (compose f1 f2) 
  (at level 49, right associativity) : fun_scope.

Open Scope fun_scope.

(* ---------------------------------------------------------------------- *)
(** ** Properties of combinators *)

Section Combinators.
Variables (A B C D : Type).

Lemma compose_id_l : forall (f:A->B),
  id \o f = f. 
Proof. intros. apply~ func_ext_1. Qed.

Lemma compose_id_r : forall (f:A->B),
  f \o id = f. 
Proof. intros. apply~ func_ext_1. Qed.

Lemma compose_assoc : forall (f:C->D) (g:B->C) (h:A->B), 
  (f \o g) \o h = f \o (g \o h).
Proof. intros. apply~ func_ext_1. Qed.

Lemma compose_eq_l : forall (f:B->C) (g1 g2:A->B),
  g1 = g2 -> f \o g1 = f \o g2.
Proof. intros. subst~. Qed.

Lemma compose_eq_r : forall (f:A->B) (g1 g2:B->C),
  g1 = g2 -> g1 \o f = g2 \o f.
Proof. intros. subst~. Qed.

End Combinators.

(* ---------------------------------------------------------------------- *)
(** ** Tactic for simplifying function compositions *)

Hint Rewrite compose_id_l compose_id_r compose_assoc : rew_compose.
Tactic Notation "rew_compose" := 
  autorewrite with rew_compose.
Tactic Notation "rew_compose" "in" "*" := 
  autorewrite with rew_compose in *.
Tactic Notation "rew_compose" "in" hyp(H) := 
  autorewrite with rew_compose in H.
