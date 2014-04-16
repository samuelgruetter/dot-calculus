(***************************************************************************
* Equivalence of big-step and small-step in call-by-value - Equivalence    *
* Arthur Charguéraud, March 2009                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN
  BigStep_Definitions BigStep_Infrastructure.


(* ********************************************************************** *)
(** * Basic lemmas used in the proofs *)

(** A simplified rule for reasoning on big-step reduction
    of a value applied to a value *)

Lemma reds_red_val : forall t1 v2 r,
  body t1 -> value v2 ->
  reds (t1 ^^ v2) r ->
  reds (trm_app (trm_abs t1) v2) r.
Proof. intros. applys~ reds_red. Qed.

(** Beta-star is a transitive relationship *)

Lemma beta_star_trans : forall t2 t1 t3,
  beta_star t1 t2 -> 
  beta_star t2 t3 -> 
  beta_star t1 t3.
Proof.
  introv R1. gen t3. induction R1; intros.
  auto.
  apply* beta_star_step.
Qed.

(** A term that reduces in big-step reaches a value *)
    
Lemma reds_to_value : forall t v,
  reds t v -> value v.
Proof. introv Rt. induction~ Rt. Qed.
Hint Extern 1 (value ?v) =>
  match goal with H: reds _ v |- _ =>
    apply (@reds_to_value _ _ H) end.


(* ********************************************************************** *)
(** From big-step to small-step *)

Lemma beta_star_app1 : forall t1 t1' t2, 
  term t2 ->
  beta_star t1 t1' -> 
  beta_star (trm_app t1 t2) (trm_app t1' t2).
Proof.
  introv T H. induction H.
  apply* beta_star_refl.
  apply* beta_star_step.
Qed.

Lemma beta_star_app2 : forall t1 t2 t2', 
  value t1 ->
  beta_star t2 t2' ->
  beta_star (trm_app t1 t2) (trm_app t1 t2').
Proof.
  introv T H. induction H.
  apply* beta_star_refl.
  apply* beta_star_step.
Qed.

Lemma reds_to_beta_star : forall t v,
  reds t v -> beta_star t v /\ value v.
Proof.
  introv H. induction H.
  split~. apply* beta_star_refl.
  destruct IHreds1. destruct IHreds2. destruct IHreds3. split~.
   apply (@beta_star_trans (trm_app (trm_abs t3) t2)).
     apply~ beta_star_app1.
   apply (@beta_star_trans (trm_app (trm_abs t3) v2)).
     apply~ beta_star_app2.
   apply~ (@beta_star_step (t3 ^^ v2)).
Qed.


(* ********************************************************************** *)
(** * From small-step to big-step (the simpler proof) *)

Lemma beta_reds_to_reds : forall t t' v,
  beta t t' -> reds t' v -> value v -> reds t v.
Proof.
  introv Rt Rt' Vv. gen v.
  induction Rt; intros.
  apply~ reds_red_val.
  inversions Rt'. false_invert. apply* reds_red.
  inversions Rt'. false_invert. apply* reds_red. apply* IHRt.
Qed.

Lemma beta_star_to_reds : forall t v,
  beta_star t v -> value v -> reds t v.
Proof.
  introv Rt Vv. induction Rt.
  auto. 
  apply* beta_reds_to_reds.
Qed.


(* ********************************************************************** *)
(** * Proof of equivalence *)

Lemma equivalence_result : equivalence.
Proof. 
  split; intros.
  apply* reds_to_beta_star.
  apply* beta_star_to_reds.
Qed.


(* ********************************************************************** *)
(** * Another proof of small-step implies big-step *)

Require Import LibNat LibInt.
Import LibTacticsCompatibility.
Open Scope nat_scope.
(* TODO: should include LibNat LibOmega *)

(** [beta_starn n t1 t2] describes the fact that [t1] reduces
    to [t2] in exactly [n] steps. *)

Inductive beta_starn : nat -> trm -> trm -> Prop :=
  | beta_starn_refl : forall t,
     term t ->
     beta_starn 0 t t
  | beta_starn_step : forall t2 n t1 t3,
     beta t1 t2 -> 
     beta_starn n t2 t3 -> 
     beta_starn (S n) t1 t3.

(** [beta_starn] is regular. *)

Lemma beta_starn_regular : forall n e e',
  beta_starn n e e' -> term e /\ term e'.
Proof.
  induction 1. 
  auto*.
  destruct* (beta_regular H).
Qed.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: beta_starn _ t _ |- _ => apply (proj1 (beta_starn_regular H))
  | H: beta_starn _ _ t |- _ => apply (proj2 (beta_starn_regular H))
  end.

Hint Constructors beta_star beta_starn.

(** Equivalence between [beta_star] and [beta_starn]. *)

Lemma beta_starn_to_beta_star : forall n t1 t2,
  beta_starn n t1 t2 -> beta_star t1 t2.
Proof.
  introv H. induction* H.
Qed.

Lemma beta_star_to_beta_starn : forall t1 t2,
  beta_star t1 t2 -> exists n, beta_starn n t1 t2.
Proof.
  introv H. induction H.
  auto*.
  destruct* IHbeta_star.
Qed.

(** Some inversion results for [beta_starn]. *)

Lemma beta_starn_inv : forall n t v,
  beta_starn n t v -> value v -> ~ (value t) ->
  exists t', beta t t' /\ beta_starn (n-1) t' v.
Proof.
  introv Rn Vv Vt. inversions Rn.
    false~.
    exists t2. math_rewrite~ (S n0 - 1 = n0). 
Qed.

Lemma beta_starn_inv_val : forall n t v,
  beta_starn n t v -> value t -> t = v.
Proof.
  introv Rn Vt. inversions Rn.
    auto.
    inversions Vt. false_invert. 
Qed.

(** Main induction. *)

Ltac auto_star ::= intuition eauto with maths.

Lemma beta_starn_inv_app : forall n t1 t2 v,
  beta_starn n (trm_app t1 t2) v -> value v ->
  exists n1 v1 n2 v2 n3, 
     beta_starn n1 t1 v1 /\ value v1
  /\ beta_starn n2 t2 v2 /\ value v2
  /\ beta_starn n3 (trm_app v1 v2) v
  /\ n1 < n /\ n2 < n /\ n3 <= n. 
Proof.
  introv H. inductions H; introv Vv.
  inversions Vv. inversions H.
  exists* 0 (trm_abs t0) 0 t2 (S n).
  destruct~ (IHbeta_starn t1' t2) 
   as (n1&v1&n2&v2&n3&S1&V1&S2&V2&S3&L1&L2&L3).
   exists* (S n1) v1 n2 v2 n3. 
  destruct~ (IHbeta_starn t1 t2') 
   as (n1&v1&n2&v2&n3&S1&V1&S2&V2&S3&L1&L2&L3).
   exists* n1 v1 (S n2) v2 n3.
Qed.

Lemma beta_starn_to_red : forall n t v,
  beta_starn n t v -> value v -> reds t v.
Proof.
  induction n using peano_induction.
  introv Rn Vv. destruct t.
  destruct (beta_starn_inv Rn Vv) as [t' [Rt Rp]].
   intros K; inversions K. inversion Rt.
  destruct (beta_starn_inv Rn Vv) as [t' [Rt Rp]].
   intros K; inversions K. inversion Rt.
  rewrite~ (beta_starn_inv_val Rn).
  destruct~ (beta_starn_inv_app Rn) 
   as (n1&v1&n2&v2&n3&S1&V1&S2&V2&S3&L1&L2&L3).
   inversions V1. inversions S3; [ inversions Vv | ].
   inversions H1; [ | inversions H7 | inversions V2; inversions H7 ].
   eapply reds_red.
     apply* (H n1). 
     apply* (H n2).
     apply* (H n0).
Qed.

Lemma beta_star_to_red : forall t v,
  beta_star t v -> value v -> reds t v.
Proof.
  introv Rt Vv. destruct (beta_star_to_beta_starn Rt). 
  apply* beta_starn_to_red.
Qed.


