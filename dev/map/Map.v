Require Import Fsub.
Require Import Dsub.

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.
Implicit Types X : var.

(* to adjust the bound identifier when shifting from a plain arrow to an all type *)
Fixpoint inc_bound_rec (k: nat) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_sel t       => typ_sel (inc_bound_e_rec k t)
  | typ_mem b T     => typ_mem b (inc_bound_rec k T)
  | typ_all T1 T2   => typ_all (inc_bound_rec k T1) (inc_bound_rec (S k) T2)
  end
with inc_bound_e_rec (k: nat) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar (If (k <= i) then (S i) else i)
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs (inc_bound_rec k V) (inc_bound_e_rec (S k) e1)
  | trm_mem T     => trm_mem (inc_bound_rec k T)
  | trm_app e1 e2 => trm_app (inc_bound_e_rec k e1) (inc_bound_e_rec k e2)
  end.

Definition inc_bound T := inc_bound_rec 0 T.

Fixpoint emb_t (T: Fsub.typ): Dsub.typ :=
  match T with
    | Fsub.typ_top => typ_top
    | Fsub.typ_bvar i => typ_sel (trm_bvar i)
    | Fsub.typ_fvar x => typ_sel (trm_fvar x)
    | Fsub.typ_arrow T U => typ_all (emb_t T) (inc_bound (emb_t U))
    | Fsub.typ_all T U => typ_all (typ_mem false (emb_t T)) (emb_t U)
  end.

Fixpoint emb_e (e: Fsub.trm): Dsub.trm :=
  match e with
    | Fsub.trm_bvar i => trm_bvar i
    | Fsub.trm_fvar x => trm_fvar x
    | Fsub.trm_abs T e => trm_abs (emb_t T) (emb_e e)
    | Fsub.trm_tabs T e => trm_abs (typ_mem false (emb_t T)) (emb_e e)
    | Fsub.trm_app e1 e2 => trm_app (emb_e e1) (emb_e e2)
    | Fsub.trm_tapp e1 U => trm_app (emb_e e1) (trm_mem (emb_t U))
  end.

Definition emb_tb (b: bind): Dsub.typ :=
  match b with
    | bind_sub T => typ_mem false (emb_t T)
    | bind_typ T => emb_t T
  end.

Definition emb_env (E: Fsub.env): Dsub.env := map emb_tb E.

Lemma binds_preserved: forall X b E,
  binds X b E ->
  binds X (emb_tb b) (emb_env E).
Proof.
  intros. apply* binds_map.
Qed.

Lemma binds_sub_preserved: forall X U E,
  binds X (bind_sub U) E ->
  binds X (typ_mem false (emb_t U)) (emb_env E).
Proof.
  intros. apply binds_preserved in H. simpl in H. apply H.
Qed.

Lemma binds_typ_preserved: forall X U E,
  binds X (bind_typ U) E ->
  binds X (emb_t U) (emb_env E).
Proof.
  intros. apply binds_preserved in H. simpl in H. apply H.
Qed.

Lemma inc_bound_open_commute_rec:
  (forall T y n k, k <= n ->
     inc_bound_rec k (open_t_rec n (trm_fvar y) T) =
     open_t_rec (S n) (trm_fvar y) (inc_bound_rec k T))
  /\
  (forall e y n k, k <= n ->
     inc_bound_e_rec k (open_e_rec n (trm_fvar y) e) =
     open_e_rec (S n) (trm_fvar y) (inc_bound_e_rec k e)).
Proof.
  apply typ_trm_mutind; intros; simpl; eauto;
  try solve [rewrite H; auto; omega];
  try solve [f_equal; [rewrite H; auto; omega | rewrite H0; auto; omega]].
  - case_if; case_if; simpl; auto.
    rewrite If_l in H0; congruence.
    case_if; simpl; auto. omega.
Qed.

Lemma inc_bound_open_commute: forall T y n,
  inc_bound (open_t_rec n (trm_fvar y) T) =
  open_t_rec (S n) (trm_fvar y) (inc_bound T).
Proof.
  intros. unfold inc_bound. apply inc_bound_open_commute_rec.
  omega.
Qed.

Lemma open_var_emb_commute: forall T y,
  (emb_t (T open_tt_var y))=(emb_t T open_t_var y).
Proof.
  intros. unfold Fsub.open_tt. unfold Dsub.open_t.
  remember 0 as n. clear Heqn. generalize dependent n.
  induction T; intros; eauto.
  - simpl. case_if; eauto.
  - simpl. f_equal. rewrite IHT1. reflexivity.
    rewrite IHT2. rewrite inc_bound_open_commute. reflexivity.
  - simpl. rewrite IHT1. rewrite IHT2. reflexivity.
Qed.

Lemma type_inc_bound_noop: forall T,
  type T ->
  inc_bound T = T.
Proof.
  admit.
Qed.

Lemma wft_preserved: forall E T,
  ok (emb_env E) ->
  Fsub.wft E T ->
  Dsub.wft (emb_env E) (emb_t T).
Proof.
  introv Ok H. induction H; eauto.
  - simpl. apply wft_sel. right. eexists. reflexivity.
    eapply wfe_var. eapply binds_sub_preserved; eauto.
  - simpl. apply wft_all with (L:=dom (emb_env E)); eauto; intros.
    rewrite open_t_var_type. apply wft_weaken_right.
    rewrite type_inc_bound_noop. eapply IHwft2; eauto.
    apply* wft_type. apply ok_push; eauto.
    rewrite type_inc_bound_noop. apply* wft_type. apply* wft_type.
  - simpl. apply wft_all with (L:=L \u dom (emb_env E)); eauto. intros y Fry.
    assert (y \notin L) as Fr by auto. specialize (H1 y Fr).
    assert (ok (emb_env (E & y ~ bind_sub T1))) as A. {
      unfold emb_env in *. rewrite map_concat. rewrite map_single.
      apply ok_push. apply Ok. auto*.
    }
    specialize (H1 A). unfold emb_env in *.
    rewrite map_concat in H1. rewrite map_single in H1. simpl in H1.
    rewrite open_var_emb_commute in H1. apply H1.
Qed.

Lemma okt_preserved: forall E,
  Fsub.okt E ->
  Dsub.okt (emb_env E).
Proof.
  intros. induction E using env_ind.
  - unfold emb_env. rewrite map_empty. auto.
  - unfold emb_env. rewrite map_concat. rewrite map_single.
    destruct (Fsub.okt_push_inv H) as [T [? | ?]]; subst.
    + destruct (Fsub.okt_push_sub_inv H) as [Ok [Hwf Fr]].
      apply okt_push; auto.
      specialize (IHE Ok).
      assert (ok (emb_env E)) as Ok' by solve [apply* ok_from_okt].
      lets Hwf': (wft_preserved Ok' Hwf).
      unfold emb_env in Hwf'. simpl.
      apply wft_mem. apply Hwf'.
    + destruct (Fsub.okt_push_typ_inv H) as [Ok [Hwf Fr]].
      apply okt_push; auto.
      specialize (IHE Ok).
      assert (ok (emb_env E)) as Ok' by solve [apply* ok_from_okt].
      lets Hwf': (wft_preserved Ok' Hwf).
      unfold emb_env in Hwf'. simpl.
      apply Hwf'.
Qed.

Theorem preservation_of_subtyping: forall E S T,
  Fsub.sub E S T ->
  Dsub.sub (emb_env E) (emb_t S) (emb_t T).
Proof.
  admit.
Qed.