
Require Import LibLN.
Set Implicit Arguments.

Inductive avar: Set :=
| avar_b: nat -> avar
| avar_f: var -> avar.

Inductive typ: Set :=
| typ_top: typ
| typ_bot: typ
| typ_var: avar -> typ
| typ_fun: typ -> typ -> typ
| typ_pair: typ -> typ -> typ
(*  \mu alpha . T1 -> T2 *)
| typ_mu : typ -> typ -> typ.

Definition ctx := env typ.

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_var a      => typ_var (open_rec_avar k u a)
  | typ_fun T1 T2  => typ_fun  (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_pair T1 T2 => typ_pair (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_mu T1 T2   => typ_mu (open_rec_typ (S k) u T1) (open_rec_typ (S k) u T2)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.

(* G A |- T wf
   G: env
   A: wf-ness assumptions
   T: type to be checked *)
Inductive wf_typ: ctx -> fset typ -> typ -> Prop :=
| wf_top: forall G A, wf_typ G A typ_top
| wf_bot: forall G A, wf_typ G A typ_bot
| wf_var: forall G A a T,
    binds a T G ->
    wf_typ G A T -> (* <-- makes finite proofs of recursive types impossible
                           (unless we have an assumption mechanism) *)
    wf_typ G A (typ_var (avar_f a))
| wf_hyp: forall G A T,
    T \in A ->
    wf_typ G A T
| wf_fun : forall G A T1 T2, wf_typ G A T1 -> wf_typ G A T2 -> wf_typ G A (typ_fun  T1 T2)
| wf_pair: forall G A T1 T2, wf_typ G A T1 -> wf_typ G A T2 -> wf_typ G A (typ_pair T1 T2)
| wf_mu: forall L G A T1 T2,
    (forall a, a \notin L ->
       wf_typ (G & a ~ (typ_mu T1 T2)) (A \u \{ typ_mu T1 T2 }) (open_typ a T1)) ->
    (forall a, a \notin L ->
       wf_typ (G & a ~ (typ_mu T1 T2)) (A \u \{ typ_mu T1 T2 }) (open_typ a T2)) ->
    wf_typ G A (typ_mu T1 T2).

Ltac do_open :=
  repeat match goal with
  | _: _ |- context[open_avar _ _] => unfold open_avar; simpl
  | _: _ |- context[open_typ  _ _] => unfold open_typ ; simpl
  | _: _ |- context[(If _ = _ then _ else _)] => case_if; simpl
  end.

Ltac prove_binds := solve [
  unfold binds; rewrite EnvOps.get_def; unfold get_impl;
  repeat (rewrite <- cons_to_push || case_if); auto].

Module ex1.

(* stream = top -> top * stream *)
Example stream := typ_mu typ_top (typ_pair typ_top (typ_var (avar_b 0))).

Example stream_wf: wf_typ empty \{} stream.
  unfold stream.
  apply wf_mu with \{}; intros a _; do_open.
  - apply wf_top.
  - apply wf_pair.
    + apply wf_top.
    + eapply wf_var.
      * prove_binds.
      * apply wf_hyp. rewrite in_union. right. rewrite in_singleton. reflexivity.
Qed.

End ex1.

Hint Constructors wf_typ.


(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_var a      => (fv_avar a)
  | typ_fun T U    => (fv_typ T) \u (fv_typ U)
  | typ_pair T U   => (fv_typ T) \u (fv_typ U)
  | typ_mu T U     => (fv_typ T) \u (fv_typ U)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let I := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u E \u I).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* Locate "_ \- _". called remove (set difference) *)

Lemma add_hyps: forall A1 A2 G T,
  wf_typ G A1 T ->
  wf_typ G (A1 \u A2) T.
Proof.
  introv Wf. induction Wf; eauto.
  + (* case wf_hyp *)
    apply wf_hyp. rewrite in_union. auto.
  + (* case wf_mu *)
    rename H0 into IH1, H2 into IH2, H into Wf1, H1 into Wf2.
    rewrite <- union_assoc in *.
    rewrite (union_comm \{ typ_mu T1 T2 } A2) in *.
    rewrite union_assoc in *.
    eauto.
Qed.

Lemma weaken_wf: forall G A T, wf_typ G A T -> forall G1 G2 G3,
  G = G1 & G3 ->
  ok (G1 & G2 & G3) ->
  wf_typ (G1 & G2 & G3) A T.
Proof.
  introv Wf. induction Wf; intros; subst G; eauto.
  + (* case wf_var *)
    eapply wf_var.
    - apply* binds_weaken.
    - apply* IHWf.
  + (* case wf_mu *)
    rename H0 into IH1, H2 into IH2, H into Wf1, H1 into Wf2.
    apply_fresh wf_mu as a; rewrite <- concat_assoc.
    - refine (IH1 a _ G1 G2 (G3 & a ~ typ_mu T1 T2) _ _);
      try rewrite concat_assoc; auto.
    - refine (IH2 a _ G1 G2 (G3 & a ~ typ_mu T1 T2) _ _);
      try rewrite concat_assoc; auto.
Qed.

Lemma weaken_wf_end: forall G1 G2 A T,
  wf_typ G1 A T ->
  ok (G1 & G2) ->
  wf_typ (G1 & G2) A T.
Proof.
  introv Wf Ok.
  lets Wf': (@weaken_wf _ _ _ Wf G1 G2 empty).
  repeat rewrite concat_empty_r in Wf'.
  auto.
Qed.

Lemma remove_from_hyps: forall G A T U,
  wf_typ G A T ->
  wf_typ G \{} U ->
  ok G ->
  wf_typ G (A \- \{ U }) T.
Proof.
  introv Wf WfU Ok. induction Wf; eauto.
  + (* case wf_hyp *)
    destruct (classicT (T = U)) as [Eq | Ne].
    - subst T. rewrite <- (union_empty_l (A \- \{ U })). apply add_hyps. exact WfU.
    - apply wf_hyp. rewrite in_remove. apply (conj H). rewrite notin_singleton. exact Ne.
  + (* case wf_mu *)
    rename H0 into IH1, H2 into IH2, H into Wf1, H1 into Wf2.
    destruct (classicT ((typ_mu T1 T2) = U)) as [Eq | Ne].
    - rewrite <- (union_empty_l (A \- \{ U })). subst U. apply add_hyps. exact WfU.
    - assert (Eq: (A \u \{ typ_mu T1 T2}) \- \{ U} = (A \- \{ U } \u \{ typ_mu T1 T2})). {
        apply fset_extens; unfold subset; intros X H;
        repeat (rewrite in_remove in * || rewrite in_union in *).
        + auto_star.
        + destruct H as [[H1 H2] | H].
          - auto.
          - rewrite in_singleton in H. subst X. split.
            * right. rewrite in_singleton. reflexivity.
            * rewrite notin_singleton. exact Ne.
      }
      rewrite Eq in *.
      apply_fresh wf_mu as a;
      assert (Ok': ok (G & a ~ typ_mu T1 T2)) by auto;
      lets WfU': (weaken_wf_end WfU Ok').
      * apply* IH1.
      * apply* IH2.
Qed.

Lemma singleton_remove: forall (T: Type) (v: T),
  \{ v } \- \{ v } = \{}.
Proof.
  intros. apply fset_extens; unfold subset; intros.
  - rewrite in_remove in H. destruct H as [H1 H2]. rewrite in_singleton in H1. subst.
    exfalso. rewrite notin_singleton in H2. apply H2. reflexivity.
  - exfalso. apply (notin_empty H).
Qed.

Lemma invert_wf_mu: forall G T1 T2,
  wf_typ G \{} (typ_mu T1 T2) ->
  ok G ->                        (*   empty (that's the whole point) *)
  exists L,                      (*     |                            *)
    (forall a, a \notin L ->     (*     V                            *)
       wf_typ (G & a ~ (typ_mu T1 T2)) \{} (open_typ a T1)) /\
    (forall a, a \notin L ->
       wf_typ (G & a ~ (typ_mu T1 T2)) \{} (open_typ a T2)).
Proof.
  introv Wf. inversion Wf; subst.
  - exfalso. rewrite in_empty in H. exact H.
  - intro Ok. exists (L \u (dom G)).
    split;
    [(rename H3 into IH; clear H4) | (rename H4 into IH; clear H3)];
    intros a aFr; 
    assert (aL: a \notin L) by auto;
    specialize (IH a aL);
    rewrite union_empty_l in IH;
    assert (Ok': ok (G & a ~ typ_mu T1 T2)) by auto;
    lets Wf': (weaken_wf_end Wf Ok');
    lets P: (remove_from_hyps IH Wf' Ok');
    rewrite singleton_remove in P;
    exact P.
Qed.

Print Assumptions invert_wf_mu.

