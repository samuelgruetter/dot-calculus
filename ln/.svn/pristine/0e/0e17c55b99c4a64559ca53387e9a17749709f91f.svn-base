(***************************************************************************
* Calculus of Constructions - Church-Rosser Property                       *
* Arthur Charguéraud, April 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoC_Definitions CoC_Infrastructure CoC_BetaStar.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Additional Definitions Used in this Proof *)

(* ********************************************************************** *)
(** Definition of parallel reduction *)

Inductive para : relation :=
  | para_red : forall L t1 t2 t2' u u',
      term t1 ->
      (forall x, x \notin L -> para (t2 ^ x) (t2' ^ x) ) ->
      para u u' ->
      para (trm_app (trm_abs t1 t2) u) (t2' ^^ u') 
  | para_var : forall x, 
      para (trm_fvar x) (trm_fvar x)
  | para_srt : forall n, 
      para (trm_type n) (trm_type n)
  | para_app : forall t1 t1' t2 t2',
      para t1 t1' -> 
      para t2 t2' ->
      para (trm_app t1 t2) (trm_app t1' t2')
  | para_abs : forall L t1 t1' t2 t2',
     para t1 t1' -> 
     (forall x, x \notin L -> para (t2 ^ x) (t2' ^ x) ) ->
     para (trm_abs t1 t2) (trm_abs t1' t2')
  | para_prod : forall L t1 t1' t2 t2',
     para t1 t1' -> 
     (forall x, x \notin L -> para (t2 ^ x) (t2' ^ x) ) ->
     para (trm_prod t1 t2) (trm_prod t1' t2').


(* ********************************************************************** *)
(** Definition of the transitive closure of a relation *)

Inductive iter_ (R : relation) : relation :=
  | iter_trans : forall t2 t1 t3,
      iter_ R t1 t2 -> iter_ R t2 t3 -> iter_ R t1 t3
  | iter_step : forall t t',
      R t t' -> iter_ R t t'.

Notation "R 'iter'" := (iter_ R) (at level 69).

(* ********************************************************************** *)
(** ** Lemmas Associated to Additional Definitions *)

Hint Constructors para iter_.

(* ********************************************************************** *)
(** Regularity *)

Lemma red_regular_para : red_regular para.
Proof.
  intros_all. induction* H.
Qed.

Lemma red_regular_para_iter : red_regular (para iter).
Proof.
  intros_all. induction* H. apply* red_regular_para.
Qed.

Hint Extern 1 (term ?t) => match goal with
  | H: para t _ |- _ => apply (proj1 (red_regular_para H))
  | H: para _ t |- _ => apply (proj2 (red_regular_para H))
  | H: (para iter) t _ |- _ => apply (proj1 (red_regular_para_iter))
  | H: (para iter) _ t |- _ => apply (proj2 (red_regular_para_iter))
  end.

(* ********************************************************************** *)
(** Automation *)

Hint Resolve para_var para_srt para_app.

Hint Extern 1 (para (trm_abs _ _) (trm_abs _ _)) =>
  let y := fresh "y" in apply_fresh para_abs as y.
Hint Extern 1 (para (trm_prod _ _) (trm_prod _ _)) =>
  let y := fresh "y" in apply_fresh para_prod as y.
Hint Extern 1 (para (trm_app (trm_abs _ _) _) (_ ^^ _)) =>
  let y := fresh "y" in apply_fresh para_red as y.


(* ********************************************************************** *)
(** Properties of parallel reduction and its iterated version *)

Section ParaProperties.

Hint Extern 1 (para (if _ == _ then _ else _) _) => case_var.

Lemma para_red_all : red_all para.
Proof.
  intros x t t' H. induction H; intros; simple*.
  rewrite* subst_open. apply_fresh* para_red as y. cross*.
  case_var*.
  apply_fresh* para_abs as y. cross*.
  apply_fresh* para_prod as y. cross*.
Qed.

Lemma para_red_refl : red_refl para.
Proof.
  intros_all. induction* H. 
Qed.

Lemma para_red_out : red_out para.
Proof.
  apply* (red_all_to_out para_red_all para_red_refl). 
Qed.

Lemma para_red_rename : red_rename para.
Proof.
  apply* (red_out_to_rename para_red_out).
Qed.

Lemma para_red_through : red_through para.
Proof.
  apply* (red_all_to_through red_regular_para para_red_all).
Qed.

Lemma para_iter_red_refl : red_refl (para iter).
Proof.
  intros_all. auto* para_red_refl.
Qed.

End ParaProperties.

(* ********************************************************************** *)
(** Equality of beta star and iterated parallel reductions *)

Lemma beta_star_to_para_iter : 
  (beta star) simulated_by (para iter).
Proof.
  intros_all. induction* H. 
  apply* para_iter_red_refl.
  apply iter_step. induction H; auto* para_red_refl.
Qed.

Lemma para_iter_to_beta_star : 
  (para iter) simulated_by (beta star).
Proof.
  intros_all. induction H; eauto.
  induction H.
  applys~ (@star_trans beta (t2 ^^ u)).
   pick_fresh x. apply* (@beta_star_red_through x).
  apply* star_refl.
  apply* star_refl.
  apply~ (@star_trans beta (trm_app t1' t2)).
   apply* beta_star_app1. apply* beta_star_app2.
  apply~ (@star_trans beta (trm_abs t1' t2)).
    apply* beta_star_abs1. apply* beta_star_abs2.
  apply~ (@star_trans beta (trm_prod t1' t2)).
    apply* beta_star_prod1. apply* beta_star_prod2.
Qed.


(* ********************************************************************** *)
(** ** Proof of Church-Rosser Property for Beta Reduction *)

(* ********************************************************************** *)
(** Confluence of parallel reduction *)

Lemma para_abs_inv : forall t1 t2 u,
  para (trm_abs t1 t2) u -> exists L t1' t2', 
  u = (trm_abs t1' t2') /\ para t1 t1' /\
  forall x : var, x \notin L -> para (t2 ^ x) (t2' ^ x).
intros. inversion H. exists* L.
Qed.

Lemma para_prod_inv : forall t1 t2 u,
  para (trm_prod t1 t2) u -> exists L t1' t2', 
  u = (trm_prod t1' t2') /\ para t1 t1' /\
  forall x : var, x \notin L -> para (t2 ^ x) (t2' ^ x).
Proof.
  intros. inversion H. exists* L.
Qed.

Lemma para_confluence : confluence para.
Proof.
  introv HS. gen T. induction HS; intros T HT; inversions HT.
    (* case: red / red *)
  lets~ [u2 [U2a U2b]]: IHHS u'0 __. clear IHHS.
  pick_fresh x. lets~ [u1x [U1a U1b]]: H1 (t2'0 ^ x) __. auto. clear H1. 
  destruct~ (@close_var_spec u1x x) as [u1 [EQu1 termu1]].
  rewrite EQu1 in U1a, U1b. 
  exists (u1 ^^ u2). split; apply* (@para_red_through x).
    (* case: red / trm_app *)
  lets~ [u2 [U2a U2b]]: IHHS t2'0 __. clear IHHS.
  lets [L2 [t1'0x [t2'0x [EQ [Ht1'0 Ht2'0]]]]]: (para_abs_inv H4).
  rewrite EQ in H4 |- *.
  pick_fresh x. lets~ [u1x [U1a U1b]]: H1 (t2'0x ^ x) __. auto.
  lets~ [u1 [EQu1 termu1]]: (@close_var_spec u1x x) __.
  rewrite EQu1 in U1a, U1b.
  exists (u1 ^^ u2). split. 
    apply* (@para_red_through x). 
    apply_fresh para_red as y; auto. 
    apply* (@para_red_rename x).
    (* case: var / var *)
  auto*.
    (* case: srt / srt *)
  auto*.
    (* case: trm_app / red *)
  lets~ [u2 [U2a U2b]]: IHHS2 u' __. clear IHHS2.
  lets [L2 [t1'x [t2'x [EQ [Ht1'x Ht2'x]]]]]: (para_abs_inv HS1).
  lets~ [u1x [U1a U1b]]: (IHHS1 (trm_abs t1'x t2'0)) __. clear IHHS1.
  rewrite EQ in HS1, U1a |- *.
  lets~ [L1 [v1 [v2 [EQ' [Hv1 Hv2]]]]]: (para_abs_inv U1b). 
  rewrite EQ' in U1a, U1b.
  exists (v2 ^^ u2). split.
    inversions U1a. 
    apply* (@para_red L0).
    pick_fresh x. apply* (@para_red_through x).
    (* case: trm_app / trm_app *)
  lets~ [P1 [HP11 HP12]]: (IHHS1 t1'0) __. 
  lets~ [P2 [HP21 HP22]]: (IHHS2 t2'0) __. 
  exists* (trm_app P1 P2). 
    (* case: trm_abs / trm_abs *)
  pick_fresh x. lets~ [px [P0 P1]]: H0 (t2'0 ^ x) __. auto.
  lets~ [u1 [HP1 HP2]]: (IHHS t1'0) __. clear H0 IHHS.
  lets~ [p [EQP termp]]: (@close_var_spec px x) __.
  rewrite EQP in P0, P1.
  exists (trm_abs u1 p). split; 
   apply_fresh* para_abs as y; apply* (@para_red_rename x). 
    (* case: trm_prod / trm_prod *)
  pick_fresh x. lets~ [px [P0 P1]]: H0 (t2'0 ^ x) __. auto. 
  lets~ [u1 [HP1 HP2]]: IHHS t1'0 __. clear H0 IHHS.
  lets~ [p [EQP termp]]: (@close_var_spec px x) __.
  rewrite EQP in P0, P1.
  exists (trm_prod u1 p). split; 
   apply_fresh* para_prod as y; apply* (@para_red_rename x). 
Qed.

(* ********************************************************************** *)
(** Confluence of iterated parallel reduction *)

Lemma para_iter_parallelogram : 
  forall M S, (para iter) M S -> forall T, para M T ->
  exists P, para S P /\ (para iter) T P. 
Proof.
  introv H. induction H; intros T MtoT.
  destruct~ (IHiter_1 T) as [P [HP1 HP2]]. 
   destruct~ (IHiter_2 P) as [Q [HQ1 HQ2]].
   exists Q. auto* (@iter_trans para P).
  destruct* (para_confluence H MtoT).
Qed.

Lemma para_iter_confluence : confluence (para iter).
Proof.
  introv MtoS MtoT. gen T.
  induction MtoS; intros T MtoT.
  destruct~ (IHMtoS1 T) as [P [HP1 HP2]]. 
   destruct~ (IHMtoS2 P) as [Q [HQ1 HQ2]]. exists* Q. 
  destruct* (para_iter_parallelogram MtoT H).
Qed.

(* ********************************************************************** *)
(** Church-Rosser property of beta reduction *)

Lemma confluence_beta_star : confluence (beta star).
Proof.
  intros_all. destruct (@para_iter_confluence M S T).
  auto* beta_star_to_para_iter.
  auto* beta_star_to_para_iter.
  auto* para_iter_to_beta_star.
Qed.

Lemma church_rosser_beta : church_rosser beta.
Proof.
  introv H. induction H.
  exists* t.
  destruct* IHequiv_.
  destruct IHequiv_1 as [u [Pu Qu]].
   destruct IHequiv_2 as [v [Pv Qv]].
   destruct (confluence_beta_star Qu Pv) as [w [Pw Qw]].
   exists w. split.
     apply* (@star_trans beta u).
     apply* (@star_trans beta v).
  exists* t'.
Qed.

