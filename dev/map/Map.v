Require Import Fsub.
Require Import Dsub.

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.
Implicit Types X : var.

Fixpoint emb_t (T: Fsub.typ): Dsub.typ :=
  match T with
    | Fsub.typ_top => typ_top
    | Fsub.typ_bvar i => typ_sel (trm_bvar i)
    | Fsub.typ_fvar x => typ_sel (trm_fvar x)
    | Fsub.typ_arrow T U => typ_all (emb_t T) (emb_t U)
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

Lemma open_var_emb_commute: forall T y,
  (emb_t (T open_tt_var y))=(emb_t T open_t_var y).
Proof.
  intros. unfold Fsub.open_tt. unfold Dsub.open_t.
  remember 0 as n. clear Heqn. generalize dependent n.
  induction T; intros; simpl;
  try rewrite IHT1; try rewrite IHT2;
  eauto.
  - simpl. case_if; eauto.
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
    eapply IHwft2; eauto. apply ok_push; eauto. apply* wft_type.
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
  intros. induction H.
  - apply* sub_top. apply* okt_preserved. apply* wft_preserved.
    apply* ok_from_okt. apply* okt_preserved.
  - simpl. apply* sub_refl_sel. apply* okt_preserved.
    apply wft_preserved in H0. simpl in H0. apply H0.
    apply ok_from_okt. apply* okt_preserved.
  - simpl. apply* sub_sel1. eapply has_sub. apply has_var.
    apply* okt_preserved. eapply binds_sub_preserved; eauto.
    apply* sub_mem_false.
  - simpl. apply sub_all with (L:=dom (emb_env E)). auto. intros y Fr.
    rewrite open_t_var_type. rewrite open_t_var_type.
    rewrite <- (@concat_empty_r typ (y ~ emb_t T1)). rewrite concat_assoc.
    eapply sub_weakening1. assumption. rewrite concat_empty_r.
    apply okt_push. apply* okt_preserved.
    apply sub_regular in IHsub1. auto*. auto.
    apply* wft_type. apply* wft_type.
  - simpl. apply sub_all with (L:=L \u dom (emb_env E)); eauto.
    apply* sub_mem_false. intros y Fry. assert (y \notin L) as Fr by auto.
    specialize (H1 y Fr). unfold emb_env in H1. simpl in H1.
    rewrite map_concat in H1. rewrite map_single in H1. simpl in H1.
    repeat rewrite open_var_emb_commute in H1. apply H1.
Qed.

Fixpoint subst_tt (z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_sel (trm_fvar x) => If x = z then U else typ_sel (trm_fvar x)
  | typ_sel e            => typ_sel (subst_te z U e)
  | typ_top         => typ_top
  | typ_mem b T1    => typ_mem b (subst_tt z U T1)
  | typ_all T1 T2   => typ_all (subst_tt z U T1) (subst_tt z U T2)
  end
with subst_te (z : var) (U : typ) (e : trm) {struct e } : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs (subst_tt z U V) (subst_te z U e1)
  | trm_mem T1    => trm_mem (subst_tt z U T1)
  | trm_app e1 e2 => trm_app (subst_te z U e1) (subst_te z U e2)
  end.

Lemma subst_tt_emb_commute: forall X U T,
  type (emb_t U) ->
  emb_t (Fsub.subst_tt X U T) = subst_tt X (emb_t U) (emb_t T).
Proof.
  intros.
  induction T; intros; subst; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2;
  eauto.
  - case_if; eauto.
Qed.