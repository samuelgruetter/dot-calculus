(***************************************************************************
* Calculus of Constructions - Properties of Conversion                     *
* Arthur Charguéraud, April 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoC_Definitions CoC_Infrastructure 
 CoC_BetaStar CoC_ChurchRosser.


(* ********************************************************************** *)
(** ** Some Properties of Conversion *)

Lemma conv_red_out : red_out conv.
Proof.
  intros_all. lets: beta_red_out. induction* H0.
Qed.

Lemma conv_from_beta_star : 
  (beta star) simulated_by (conv).
Proof.
  intros_all. induction* H.
Qed.

Lemma conv_from_beta_star_trans : forall T U1 U2,
  (beta star) U1 T -> (beta star) U2 T -> conv U1 U2.
Proof.
 introv R1 R2. apply (@equiv_trans beta T).
   apply* conv_from_beta_star.
   apply equiv_sym. apply* conv_from_beta_star.
Qed.

Lemma conv_from_open_beta : forall u u' t,
  body t -> beta u u' -> conv (t ^^ u') (t ^^ u).
Proof.
  introv B R. destruct B as [L Fr].
  pick_fresh x.
  rewrite* (@subst_intro x t u).
  rewrite* (@subst_intro x t u').
  unfold conv. apply equiv_sym.
  apply conv_from_beta_star.
  apply* beta_star_red_in.
Qed.


(* ********************************************************************** *)
(** ** Inversion Lemmas for Conversion *)

Section ProdInv.

Tactic Notation "helper" :=
 match goal with |- ex (fun _ => ex (fun _ => 
  trm_prod ?A ?B = trm_prod _ _ /\ _)) =>
  exists A B; splits 3; [auto | | exists_fresh ] end.

Tactic Notation "helper" "*" := helper; eauto.

Lemma beta_star_prod_any_inv : forall P U1 T1,
  (beta star) (trm_prod U1 T1) P ->
  exists U2, exists T2, P = trm_prod U2 T2 /\
  (beta star) U1 U2 /\
  exists L, forall x, x \notin L ->
   (beta star) (T1 ^ x) (T2 ^ x).
Proof.
  introv H. gen_eq Q: (trm_prod U1 T1). gen U1 T1.
  induction H; intros; subst.
  inversions H. helper*.
  destruct~ (IHstar_1 U1 T1) as [U3 [T3 [EQ3 [H3 [L3 R3]]]]]. subst.
   destruct~ (IHstar_2 U3 T3) as [U2 [T2 [EQ2 [H2 [L2 R2]]]]]. subst.
   helper*.
   inversions H; helper*.
Qed.

End ProdInv.

Lemma beta_star_type_any_inv : forall P i,
  (beta star) (trm_type i) P -> P = trm_type i.
Proof.
  introv R.
  gen_eq T: (trm_type i). 
  induction R; intros EQ; subst.
  auto.
  forwards*: IHR1. subst. auto.
  inversion H.
Qed.

Lemma conv_prod_prod_inv : forall U1 T1 U2 T2,
  conv (trm_prod U1 T1) (trm_prod U2 T2) -> 
     conv U1 U2
  /\ exists L, forall x, x \notin L -> conv (T1 ^ x) (T2 ^ x).
Proof.
  unfold conv. introv C.
  destruct (church_rosser_beta C) as [P3 [Red1 Red2]].
  destruct (beta_star_prod_any_inv Red1) 
   as [P3_11 [P3_12 [EQ1 [R1 [L1 S1]]]]].
  destruct (beta_star_prod_any_inv Red2) 
   as [P3_21 [P3_22 [EQ2 [R2 [L2 S2]]]]].
  subst. inversions EQ2.
  split. applys conv_from_beta_star_trans R1 R2.
  exists_fresh. intros x Fr.
   forwards~ K1: (S1 x). forwards~ K2: (S2 x). 
   apply* conv_from_beta_star_trans.
Qed.

Lemma conv_type_type_inv : forall i j,
  conv (trm_type i) (trm_type j) -> i = j.
Proof.
  unfold conv. introv C.
  destruct (church_rosser_beta C) as [T [Red1 Red2]].
  rewrite (beta_star_type_any_inv Red1) in Red2.
  lets K: (beta_star_type_any_inv Red2). inversions* K.
Qed.

Lemma conv_type_prod_inv : forall U1 U2 i,
  conv (trm_type i) (trm_prod U1 U2) -> False.
Proof.
  unfold conv. introv C.
  destruct (church_rosser_beta C) as [P3 [Red1 Red2]].
  destruct (beta_star_prod_any_inv Red2) 
     as [P3_11 [P3_12 [EQ1 [R1 [L1 S1]]]]].
  rewrite (beta_star_type_any_inv Red1) in *.
  false.
Qed.
