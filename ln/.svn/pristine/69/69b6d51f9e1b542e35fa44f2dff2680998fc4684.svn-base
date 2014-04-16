(***************************************************************************
* Calculus of Constructions - Properties of Beta Star                      *
* Arthur Charguéraud, April 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoC_Definitions CoC_Infrastructure.


(* ********************************************************************** *)
(** ** Generalities on relations *)

Lemma red_all_to_out : forall (R : relation), 
  red_all R -> red_refl R -> red_out R.
Proof.
  intros_all. auto*.
Qed.

Lemma red_out_to_rename : forall (R : relation),
  red_out R -> red_rename R.
Proof.
  intros_all. 
  rewrite* (@subst_intro x t). 
  rewrite* (@subst_intro x t').
Qed.

Lemma red_all_to_through : forall (R : relation),
  red_regular R -> red_all R -> red_through R.
Proof.
  intros_all. lets: (H _ _ H4).
  rewrite* (@subst_intro x t1). 
  rewrite* (@subst_intro x u1).
Qed.  


(* ********************************************************************** *)
(** ** Properties of beta relation *)

Lemma beta_red_out : red_out beta.
Proof.
  intros_all. induction H0; simpl.
  rewrite* subst_open.
  apply* beta_app1. 
  apply* beta_app2.
  apply* beta_abs1.
  apply_fresh* beta_abs2 as y. cross*. 
  apply* beta_prod1.
  apply_fresh* beta_prod2 as y. cross*. 
Qed.

Lemma beta_red_rename : red_rename beta.
Proof.
  apply* (red_out_to_rename beta_red_out).
Qed.

(* ********************************************************************** *)
(** ** Properties of beta star relation *)

Lemma beta_star_app1 : forall t1 t1' t2,
  (beta star) t1 t1' -> term t2 ->
  (beta star) (trm_app t1 t2) (trm_app t1' t2).
Proof.
  intros. induction H. 
  apply* star_refl.
  apply* (@star_trans beta (trm_app t0 t2)).
  apply* star_step.
Qed.

Lemma beta_star_app2 : forall t1 t2 t2',
  (beta star) t2 t2' -> term t1 ->
  (beta star) (trm_app t1 t2) (trm_app t1 t2').
Proof.
  intros. induction H. 
  apply* star_refl. 
  apply* (@star_trans beta (trm_app t1 t2)).
  apply* star_step.
Qed.

Lemma beta_star_abs1 : forall t1 t1' t2,
  (beta star) t1 t1' -> body t2 ->
  (beta star) (trm_abs t1 t2) (trm_abs t1' t2).
Proof.
  intros. induction H. 
  apply* star_refl. 
  apply* (@star_trans beta (trm_abs t0 t2)). 
  apply* star_step.
Qed.

Lemma beta_star_prod1 : forall t1 t1' t2,
  (beta star) t1 t1' -> body t2 ->
  (beta star) (trm_prod t1 t2) (trm_prod t1' t2).
Proof.
  intros. induction H. 
  apply* star_refl. 
  apply* (@star_trans beta (trm_prod t0 t2)). 
  apply* star_step.
Qed.

Lemma beta_star_abs2 : forall L t1 t2 t2',  
  term t1 ->
  (forall x, x \notin L -> (beta star) (t2 ^ x) (t2' ^ x)) ->
  (beta star) (trm_abs t1 t2) (trm_abs t1 t2').
Proof.
  introv R1 R2. pick_fresh x. forwards~ Red: (R2 x).
  assert (body t2).
    exists L. intros y Fry. forwards*: (R2 y).
  assert (body t2').
    exists L. intros y Fry. forwards*: (R2 y).
  gen_eq u: (t2 ^ x). gen_eq u': (t2' ^ x).
  clear R2. gen t2 t2'.
  induction Red; intros; subst. 
  rewrite* (@open_var_inj x t2 t2').
  destruct~ (@close_var_spec t2 x) as [u [P [Q R]]].
   apply* (@star_trans beta (trm_abs t1 u)).
  apply star_step.
   apply_fresh* beta_abs2 as y. 
   apply* (@beta_red_rename x).
Qed. 

Lemma beta_star_prod2 : forall L t1 t2 t2',  
  term t1 ->
  (forall x, x \notin L -> (beta star) (t2 ^ x) (t2' ^ x)) ->
  (beta star) (trm_prod t1 t2) (trm_prod t1 t2').
Proof.
  introv R1 R2. pick_fresh x. forwards~ Red: (R2 x).
  assert (body t2).
    exists L. intros y Fry. forwards*: (R2 y).
  assert (body t2').
    exists L. intros y Fry. forwards*: (R2 y).
  gen_eq u: (t2 ^ x). gen_eq u': (t2' ^ x).
  clear R2. gen t2 t2'.
  induction Red; intros; subst. 
  rewrite* (@open_var_inj x t2 t2').
  destruct~ (@close_var_spec t2 x) as [u [P [Q R]]].
   apply* (@star_trans beta (trm_prod t1 u)).
  apply star_step.
   apply_fresh* beta_prod2 as y. 
   apply* (@beta_red_rename x).
Qed. 

Lemma beta_star_red_in : red_in (beta star).
Proof.
  introv Wf Red. lets: term. induction Wf; simpl.
  case_var*.
  apply~ (@star_trans beta (trm_app ([x ~> u']t1) ([x ~> u]t2))).
    apply* beta_star_app1.
    apply* beta_star_app2.
  auto*.
  apply~ (@star_trans beta (trm_abs ([x ~> u']t1) ([x ~> u]t2))).
    apply* beta_star_abs1.
    apply* (@beta_star_abs2 (L \u \{x})). intros y Fr. cross*.
  apply~ (@star_trans beta (trm_prod ([x ~> u']t1) ([x ~> u]t2))).
    apply* beta_star_prod1.
    apply* (@beta_star_prod2 (L \u \{x})). intros y Fr. cross*.
Qed.

Lemma beta_star_red_all : red_all (beta star).
Proof.
  introv Redt. induction Redt; simpl; intros u u' Redu. 
  apply* beta_star_red_in.
  apply* (@star_trans beta ([x ~> u]t2)).
  apply* (@star_trans beta ([x ~> u]t')).
   apply* star_step. apply* beta_red_out.
   apply* beta_star_red_in.
Qed.

Lemma beta_star_red_through : red_through (beta star).
Proof.
  apply* (red_all_to_through red_regular_beta_star beta_star_red_all).
Qed.

