(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Full Beta Reduction      *
* Brian Aydemir & Arthur Charguéraud, July 2007                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.

Require Import 
  STLC_Core_Definitions 
  STLC_Core_Infrastructure
  STLC_Core_Soundness.

(* ********************************************************************** *)
(** * Definitions *)

(** Full beta reduction *)

Inductive fullred : trm -> trm -> Prop :=
  | fullred_red : forall t1 t2,
      body t1 -> 
      term t2 ->
      fullred (trm_app (trm_abs t1) t2) (t1 ^^ t2) 
  | fullred_app1 : forall t1 t1' t2, 
      term t2 ->
      fullred t1 t1' -> 
      fullred (trm_app t1 t2) (trm_app t1' t2) 
  | fullred_app2 : forall t1 t2 t2',
      term t1 ->
      fullred t2 t2' ->
      fullred (trm_app t1 t2) (trm_app t1 t2') 
  | fullred_abs : forall L t1 t1', 
     (forall x, x \notin L -> fullred (t1 ^ x) (t1' ^ x)) ->
     fullred (trm_abs t1) (trm_abs t1').

Notation "t -->> t'" := (fullred t t') (at level 68).

(* ********************************************************************** *)
(** * Infrastructure *)

Lemma fullred_regular : forall e e',
  fullred e e' -> term e /\ term e'.
Proof.
  lets: value_regular. induction 1; jauto.
  split; apply_fresh term_abs as x; forwards*: (H1 x).
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: fullred t _ |- _ => apply (proj1 (fullred_regular H))
  | H: fullred _ t |- _ => apply (proj2 (fullred_regular H))
  end.

Hint Constructors fullred.

(* ********************************************************************** *)
(** * Proofs *)

Lemma preservation_for_full_reduction : forall E t t' T,
  E |= t ~: T ->
  t -->> t' ->
  E |= t' ~: T.
Proof.
  introv Typ. gen t'.
  induction Typ; intros t' Red; inversions Red.
  apply_fresh* typing_abs as x.
  inversions Typ1. pick_fresh x.
    rewrite* (@subst_intro x). apply_empty* typing_subst.
  apply* typing_app.
  apply* typing_app.
Qed.