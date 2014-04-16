(**************************************************************************
* TLC: A library for Coq                                                  *
* Epsilon operator                                                        *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic.
Generalizable Variables A B.


(* ********************************************************************** *)
(** * Definition and specificaiton of Hilbert's epsilon operator *)

(* ---------------------------------------------------------------------- *)
(** ** Construction of epsilon *)

(* TODO: inline the lemma? *)
Lemma Inhab_witness : forall `{Inhab A}, { x : A | True }.
Proof. intros. destruct H as [H]. apply~ indefinite_description. Qed.

Lemma epsilon_def : forall `{Inhab A} (P : A->Prop), 
  { x : A | (exists y, P y) -> P x }.
Proof.
  intros A I P. destruct (classicT (exists y, P y)) as [H|H].
    apply indefinite_description. destruct H. exists~ x.
    destruct (@Inhab_witness _ I) as [x _].
     exists x. auto_false~.
Qed.

Definition epsilon `{Inhab A} (P : A -> Prop) : A
  := proj1_sig (epsilon_def P).

(* ---------------------------------------------------------------------- *)
(** ** Specification of epsilon *)

Lemma epsilon_spec_exists : forall `{Inhab A} (P : A->Prop),
  (exists x, P x) -> P (epsilon P).
Proof. intros. apply~ (proj2_sig (epsilon_def P)). Qed.

Lemma epsilon_elim_exists : forall `{Inhab A} (P Q : A->Prop),
  (exists x, P x) -> (forall x, P x -> Q x) -> Q (epsilon P).
Proof. introv E M. apply M. apply~ epsilon_spec_exists. Qed.

Lemma epsilon_spec : forall `{Inhab A} (P : A->Prop) x,
  P x -> P (epsilon P).
Proof. intros. apply* (epsilon_spec_exists). Qed.

Lemma epsilon_elim : forall `{Inhab A} (P Q : A->Prop) x,
  P x -> (forall x, P x -> Q x) -> Q (epsilon P).
Proof. introv Px W. apply W. apply* epsilon_spec_exists. Qed.

Lemma epsilon_eq : forall A {I:Inhab A} (P P':A->Prop),
  (forall x, P x <-> P' x) -> 
  epsilon P = epsilon P'.
Proof. introv H. fequals. apply~ prop_ext_1. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Tactics to work with [epsilon] *)

(* TODO: comment and demos *)

Lemma epsilon_spec' : forall A (P:A->Prop) (x:A),
  forall (H:P x) {IA:Inhab A}, P (epsilon P).
Proof. intros. applys* epsilon_spec. Qed.

Lemma epsilon_spec_exists' : forall A (P : A->Prop) {IA:Inhab A},
  (exists x, P x) -> P (epsilon P).
Proof. intros. applys* epsilon_spec_exists. Qed.

Ltac find_epsilon cont :=
  match goal with 
  | |- context [epsilon ?E] => cont E
  | H: context [epsilon ?E] |- _ => cont E
  end.

Ltac find_epsilon_in H cont :=
  match type of H with context [epsilon ?E] => cont E end.

Ltac spec_epsilon_post E X W I := 
   first [ lets I: (>> (@epsilon_spec' _ E W) __ __) 
         | lets I: (>> (@epsilon_spec' _ E _ W) __)  ]; 
   [ | sets X: (epsilon E) ].

Ltac spec_epsilon_exists_post E X I := 
   lets I: (>> (@epsilon_spec_exists' _ E) __ __); [ | sets X: (epsilon E) ].

Tactic Notation "sets_epsilon" "as" ident(X) :=
  find_epsilon ltac:(fun E => sets X: (epsilon E)).

Tactic Notation "sets_epsilon" "in" hyp(H) "as" ident(X) :=
  find_epsilon_in H ltac:(fun E => sets X: (epsilon E)).

Tactic Notation "spec_epsilon" constr(W) "as" ident(X) simple_intropattern(I) :=
  find_epsilon ltac:(fun E => spec_epsilon_post E X W I).

Tactic Notation "spec_epsilon" constr(W) "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  find_epsilon_in H ltac:(fun E => spec_epsilon_post E X W I).

Tactic Notation "spec_epsilon" "as" ident(X) simple_intropattern(I) :=
  find_epsilon ltac:(fun E => spec_epsilon_exists_post E X I).
Tactic Notation "spec_epsilon" "as" ident(X) :=
  let H := fresh "H" X in spec_epsilon as X H.

Tactic Notation "spec_epsilon" "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  find_epsilon_in H ltac:(fun E => spec_epsilon_exists_post E X I).
Tactic Notation "spec_epsilon" "in" hyp(H) "as" ident(X) :=
  let H := fresh "H" X in spec_epsilon in H as X H. 

Tactic Notation "spec_epsilon" "~" constr(W) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" constr(W) "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W in H as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" "as" ident(X) simple_intropattern(I) :=
  spec_epsilon as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" "as" ident(X) :=
  spec_epsilon as X; auto_tilde.
Tactic Notation "spec_epsilon" "~" "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon in H as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" "in" hyp(H) "as" ident(X) :=
  spec_epsilon in H as X; auto_tilde.

Tactic Notation "spec_epsilon" "*" constr(W) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W as X I; auto_star.
Tactic Notation "spec_epsilon" "*" constr(W) "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W in H as X I; auto_star.
Tactic Notation "spec_epsilon" "*" "as" ident(X) simple_intropattern(I) :=
  spec_epsilon as X I; auto_star.
Tactic Notation "spec_epsilon" "*" "as" ident(X) :=
  spec_epsilon as X; auto_star.
Tactic Notation "spec_epsilon" "*" "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon in H as X I; auto_star.
Tactic Notation "spec_epsilon" "*" "in" hyp(H) "as" ident(X) :=
  spec_epsilon in H as X; auto_star.

