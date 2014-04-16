(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Adequacy                 *
* Brian Aydemir & Arthur Charguéraud, July 2007                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.

Require Import 
  STLC_Core_Definitions 
  STLC_Core_Infrastructure
  STLC_Core_Soundness.

(***************************************************************************)
(** * Definitions with the exists-fresh quantification *)

(** Terms are locally-closed pre-terms *)

Inductive eterm : trm -> Prop :=
  | eterm_var : forall x,
      eterm (trm_fvar x)
  | eterm_abs : forall x t1,
      x \notin fv t1 ->
      eterm (t1 ^ x) ->
      eterm (trm_abs t1)
  | eterm_app : forall t1 t2,
      eterm t1 -> 
      eterm t2 -> 
      eterm (trm_app t1 t2).

(** Typing relation *)

Reserved Notation "E |== t ~: T" (at level 69).

Inductive etyping : env -> trm -> typ -> Prop :=
  | etyping_var : forall E x T,
      ok E ->
      binds x T E ->
      E |== (trm_fvar x) ~: T
  | etyping_abs : forall x E U T t1,
      x \notin dom E \u fv t1 ->
      (E & x ~ U) |== (t1 ^ x) ~: T ->
      E |== (trm_abs t1) ~: (typ_arrow U T)
  | etyping_app : forall S T E t1 t2,
      E |== t1 ~: (typ_arrow S T) -> 
      E |== t2 ~: S ->
      E |== (trm_app t1 t2) ~: T

where "E |== t ~: T" := (etyping E t T).

(** Definition of values (only abstractions are values) *)

Inductive evalue : trm -> Prop :=
  | evalue_abs : forall t1, 
      eterm (trm_abs t1) -> evalue (trm_abs t1).

(** Reduction relation - one step in call-by-value *)

Inductive ered : trm -> trm -> Prop :=
  | ered_beta : forall t1 t2,
      eterm (trm_abs t1) ->
      evalue t2 ->
      ered (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | ered_app_1 : forall t1 t1' t2,
      eterm t2 ->
      ered t1 t1' ->
      ered (trm_app t1 t2) (trm_app t1' t2)
  | ered_app_2 : forall t1 t2 t2',
      evalue t1 ->
      ered t2 t2' ->
      ered (trm_app t1 t2) (trm_app t1 t2').

Notation "t -->> t'" := (ered t t') (at level 68).

(** Goal is to prove preservation and progress *)

Definition epreservation := forall E t t' T,
  E |== t ~: T ->
  t -->> t' ->
  E |== t' ~: T.

Definition eprogress := forall t T, 
  empty |== t ~: T ->
     evalue t 
  \/ exists t', t -->> t'.



(***************************************************************************)
(** * Detailed Proofs of Renaming Lemmas (without high automation)  *)


(* ********************************************************************** *)
(** ** Proving the renaming lemma for [term]. *)

Lemma term_rename : forall x y t,
  x \notin fv t -> term (t ^ x) ->
  y \notin fv t -> term (t ^ y).
Proof.
  introv Frx Wx Fry.
  (* introduce a renaming *)
  rewrite (@subst_intro x). 
  (* apply substitution result *)
  apply* subst_term.
  (* use the fact that x is fresh *)
  assumption.
  (* prove term (trm_fvar y) *)
  apply* term_var.
Qed.

(* ********************************************************************** *)
(** ** Proving the renaming lemma for [typing]. *)

Lemma typing_rename : forall x y E t U T,
  x \notin dom E \u fv t -> (E & x ~ U) |= (t ^ x) ~: T ->
  y \notin dom E \u fv t -> (E & y ~ U) |= (t ^ y) ~: T.
Proof.
  introv Frx Typx Fry.
  (* ensure x <> y, so as to be able to build (E & y ~ U & x ~ U) *)
  tests: (x = y). subst*.
  (* assert that E is ok *)
  lets K: (proj1 (typing_regular Typx)). destruct (ok_concat_inv K).
  (* introduce substitution *)
  rewrite~ (@subst_intro x).
  (* apply substitution lemma *)
  apply_empty* typing_subst.
  (* apply weakening lemma *)
  lets P: (@typing_weaken (x ~ U) E (y ~ U)). 
   simpls. apply* P.
  (* prove (E & y ~ U |= trm_fvar y ~: U) *)
  apply* typing_var.
Qed.


(***************************************************************************)
(** * Proofs of equivalence.  *)


(* ********************************************************************** *)
(** ** Proving the equivalence of [term] and [eterm] *)

Hint Constructors term eterm.

Lemma term_to_eterm : forall t,
  term t -> eterm t.
Proof.
  induction 1; eauto.
  pick_fresh x. apply* (@eterm_abs x).
Qed.

Lemma eterm_to_term : forall t,
  eterm t -> term t.
Proof.
  induction 1; eauto.
  apply_fresh* term_abs as y. apply* term_rename.
Qed.   

(* ********************************************************************** *)
(** ** Proving the equivalence of [value] and [evalue] *)

Hint Constructors value evalue.

Lemma value_to_evalue : forall t,
  value t -> evalue t.
Proof.
  lets: term_to_eterm. induction 1; jauto.
Qed.

Lemma evalue_to_value : forall t,
  evalue t -> value t.
Proof.
  lets: eterm_to_term. induction 1; jauto.
Qed.

(* ********************************************************************** *)
(** ** Proving the equivalence of [red] and [ered] *)

Hint Constructors red ered.

Lemma red_to_ered : forall t t',
  red t t' -> ered t t'.
Proof.
  lets: term_to_eterm. lets: value_to_evalue. induction 1; jauto.
Qed.

Lemma ered_to_red : forall t t',
  ered t t' -> red t t'.
Proof.
  lets: eterm_to_term. lets: evalue_to_value. induction 1; jauto.
Qed.

(* ********************************************************************** *)
(** ** Proving the equivalence of [typing] and [etyping] *)

Hint Constructors typing etyping.

Lemma typing_to_etyping : forall E t T,
  E |= t ~: T  ->  E |== t ~: T.
Proof.
  induction 1; eauto.
  pick_fresh x. apply* (@etyping_abs x).
Qed.

Lemma etyping_to_typing : forall E t T,
  E |== t ~: T  ->  E |= t ~: T.
Proof.
  induction 1; eauto.
  apply_fresh* typing_abs as y. apply* typing_rename.   
Qed.

(* ********************************************************************** *)


