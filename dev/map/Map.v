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

Lemma subst_tt_open_t_var_rec :
  (forall T X Y U, Y <> X -> type U -> forall k,
   open_t_rec k (trm_fvar Y) (subst_tt X U T) = subst_tt X U (open_t_rec k (trm_fvar Y) T))
  /\
  (forall e X Y U, Y <> X -> type U -> forall k,
   open_e_rec k (trm_fvar Y) (subst_te X U e) = subst_te X U (open_e_rec k (trm_fvar Y) e)).
Proof.
  apply typ_trm_mutind; intros; simpl; eauto;
  try rewrite* H; try rewrite* H0.
  - simpl. specialize (H X Y U H0 H1 k).
    destruct t; simpl in *; eauto; try solve [f_equal; auto].
    case_if; eauto. case_if; eauto. case_if; eauto.
    rewrite <- (proj1 open_rec_lc). reflexivity. auto.
  - case_if; eauto.
Qed.

Lemma subst_tt_open_t_var : forall X Y U T, Y <> X -> type U ->
  (subst_tt X U T) open_t_var Y = subst_tt X U (T open_t_var Y).
Proof.
  intros. unfold open_t. apply* (proj1 subst_tt_open_t_var_rec).
Qed.

Lemma subst_te_open_t_var : forall X Y U e, Y <> X -> type U ->
  (subst_te X U e) open_e_var Y = subst_te X U (e open_e_var Y).
Proof.
  intros. unfold open_e. apply* (proj2 subst_tt_open_t_var_rec).
Qed.

Lemma wf_subst_tt:
  (forall E T, wft E T -> ok E -> forall x U, wft E U -> wft E (subst_tt x U T))
  /\
  (forall E e, wfe E e -> ok E -> forall x U, wft E U -> wfe E (subst_te x U e)).
Proof.
  apply wf_mutind; intros; subst; eauto.
  - specialize (H H0 x U H1). destruct o as [Hv | Hx].
    + inversion Hv; subst.
      * simpl. simpl in H. apply wft_sel.
        left. apply value_abs. apply* wfe_term. auto.
      * simpl. simpl in H. apply wft_sel.
        left. apply value_mem. apply* wfe_term. auto.
    + destruct Hx as [z ?]. subst. simpl. case_if; auto*.
  - apply* wft_mem.
  - simpl. apply_fresh* wft_all as y.
    assert (y \notin L) as FrL by auto.
    assert (ok (E & y ~ T1)) as Ok'. {
      auto*.
    }
    specialize (H0 y FrL Ok' x U).
    assert (wft (E & y ~ T1) U) as HU'. {
      rewrite <- (@concat_empty_r typ (y ~ T1)). rewrite concat_assoc.
      apply wft_weaken.
      rewrite concat_empty_r. auto.
      rewrite concat_empty_r. auto.
    }
    specialize (H0 HU'). rewrite <- subst_tt_open_t_var in H0.
    rewrite <- (@concat_empty_r typ (y ~ subst_tt x U T1)).
    rewrite concat_assoc.
    eapply wft_narrow. rewrite concat_empty_r. eauto.
    rewrite concat_empty_r. auto*. auto. apply* wft_type.
  - simpl. auto*.
  - simpl. apply_fresh* wfe_abs as y.
    assert (y \notin L) as FrL by auto.
    assert (ok (E & y ~ V)) as Ok'. {
      auto*.
    }
    specialize (H0 y FrL Ok' x U).
    assert (wft (E & y ~ V) U) as HU'. {
      rewrite <- (@concat_empty_r typ (y ~ V)). rewrite concat_assoc.
      apply wft_weaken.
      rewrite concat_empty_r. auto.
      rewrite concat_empty_r. auto.
    }
    specialize (H0 HU'). rewrite <- subst_te_open_t_var in H0.
    rewrite <- (@concat_empty_r typ (y ~ subst_tt x U V)).
    rewrite concat_assoc.
    eapply (proj2 wf_narrow). eapply H0. rewrite concat_empty_r. eauto.
    rewrite concat_empty_r. auto*. auto. apply* wft_type.
  - simpl. auto*.
  - simpl. auto*.
Qed.

Lemma sub_subst_tt_admissible_rec:
  (forall E T,
     wft E T ->
     (forall x U,
        has E (trm_fvar x) (typ_mem true U) ->
        sub E (subst_tt x U T) T /\ sub E T (subst_tt x U T)))
  /\
  (forall E e,
     wfe E e -> value e ->
     (forall x U,
        has E (trm_fvar x) (typ_mem true U) ->
        sub E (typ_sel (subst_te x U e)) (typ_sel e) /\
        sub E (typ_sel e) (typ_sel (subst_te x U e)))).
Proof.
  apply wf_mutind; intros; subst; eauto.
  - destruct o as [Hv | Hx].
    + inversion Hv; subst; simpl; specialize (H Hv x U H0); apply H.
    + destruct Hx as [z ?]. subst. simpl. case_if.
      * split. apply* sub_sel2. apply* sub_sel1.
        apply* has_sub. apply* sub_mem_false. apply* sub_reflexivity.
        apply (proj2 sub_has_regular) in H0. inversion H0 as [? [? A]].
        inversion A; subst. assumption.
      * split; apply* sub_refl_sel.
  - simpl. specialize (H x U H0). destruct H as [IH1 IH2].
    destruct b.
    * split; apply* sub_mem_true.
    * split; apply* sub_mem_false.
  - simpl.
    assert (type U) as HU. {
      apply (proj2 sub_has_regular) in H1. inversion H1 as [? [? A]].
      inversion A; subst. apply* wft_type.
    }
    split.
    + apply_fresh* sub_all as y.
      apply* H.
      assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      assert (has (E & y ~ T1) (trm_fvar x) (typ_mem true U)) as Has'. {
        rewrite <- (@concat_empty_r typ (y ~ T1)). rewrite concat_assoc.
        apply* has_weakening1. rewrite concat_empty_r. auto*.
      }
      specialize (H0 x U Has').
      destruct H0 as [IH1 IH2].
      rewrite subst_tt_open_t_var. apply IH1. auto*. auto*.
    + apply_fresh* sub_all as y.
      apply* H.
      assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      assert (has (E & y ~ T1) (trm_fvar x) (typ_mem true U)) as Has'. {
        rewrite <- (@concat_empty_r typ (y ~ T1)). rewrite concat_assoc.
        apply* has_weakening1. rewrite concat_empty_r. auto*.
      }
      specialize (H0 x U Has').
      destruct H0 as [IH1 IH2].
      rewrite subst_tt_open_t_var.
      rewrite <- (@concat_empty_r typ (y ~ subst_tt x U T1)).
      rewrite concat_assoc.
      apply* sub_narrowing. eapply H; eauto. rewrite concat_empty_r. apply IH2.
      auto*. auto*.
  - inversion H.
  - specialize (H x U H2). destruct H as [IH1 IH2].
    simpl.
    assert (ok E) as Ok by auto*.
    assert (wft E U) as HwfU. {
      apply (proj2 sub_has_regular) in H2. destruct H2 as [? [? A]].
      inversion A; subst. assumption.
    }
    assert (wfe E (trm_abs V e)) as Hwfe by auto*.
    lets Hwfe': ((proj2 wf_subst_tt) E (trm_abs V e) Hwfe Ok x U HwfU).
    split; apply* sub_sel_abs.
  - specialize (H x U H1). destruct H as [IH1 IH2].
    simpl. split.
    + eapply sub_trans.
      eapply sub_sel1. eapply has_mem. auto*. auto*.
      eapply sub_trans. eapply IH1.
      apply* sub_sel2. apply* has_mem.
    + eapply sub_trans.
      eapply sub_sel1. eapply has_mem. auto*. auto*.
      eapply sub_trans. eapply IH2.
      apply* sub_sel2. apply* has_mem.
  - inversion H1.
Qed.