Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_mem  : typ -> typ -> typ (* {L: S..U} *)
  | typ_sel  : avar -> typ (* x.L *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *).

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_val  : val -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
with val : Set :=
  | val_def  : typ -> val
  | val_lambda : typ -> trm -> val.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env val.

(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k)
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_mem T U    => typ_mem (open_rec_typ k u T) (open_rec_typ k u U)
  | typ_sel x    => typ_sel (open_rec_avar k u x)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_def T => val_def (open_rec_typ k u T)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.

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
  | typ_mem T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x      => (fv_avar x)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a       => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_def T       => (fv_typ T)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).

(* ###################################################################### *)
(** ** Operational Semantics *)

Inductive red : trm -> sto -> trm -> sto -> Prop :=
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    red (trm_app (avar_f f) (avar_f a)) s (open_trm a t) s
| red_let : forall v t s x,
    x # s ->
    red (trm_let (trm_val v) t) s (open_trm x t) (s & x ~ v)
| red_let_var : forall t s x,
    red (trm_let (trm_var (avar_f x)) t) s (open_trm x t) s
| red_let_tgt : forall t0 t s t0' s',
    red t0 s t0' s' ->
    red (trm_let t0 t) s (trm_let t0' t) s'.

(* ###################################################################### *)
(** ** Typing *)

Inductive tymode: Set := ty_precise | ty_general.
Inductive submode: Set := sub_tight | sub_general.

Inductive ty_trm : tymode -> submode -> ctx -> trm -> typ -> Prop :=
| ty_var : forall m1 m2 G x T,
    binds x T G ->
    ty_trm m1 m2 G (trm_var (avar_f x)) T
| ty_all_intro : forall L m1 m2 G T t U,
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) (open_trm x t) (open_typ x U)) ->
    ty_trm m1 m2 G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall m2 G x z S T,
    ty_trm ty_general m2 G (trm_var (avar_f x)) (typ_all S T) ->
    ty_trm ty_general m2 G (trm_var (avar_f z)) S ->
    ty_trm ty_general m2 G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_def_intro : forall m1 m2 G T,
    ty_trm m1 m2 G (trm_val (val_def T)) (typ_mem T T)
| ty_let : forall L m2 G t u T U,
    ty_trm ty_general m2 G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) (open_trm x u) U) ->
    ty_trm ty_general m2 G (trm_let t u) U
| ty_sub : forall m1 m2 G t T U,
    (m1 = ty_precise -> exists x, t = trm_var (avar_f x)) ->
    ty_trm m1 m2 G t T ->
    subtyp m1 m2 G T U ->
    ty_trm m1 m2 G t U

with subtyp : tymode -> submode -> ctx -> typ -> typ -> Prop :=
| subtyp_top: forall m2 G T,
    subtyp ty_general m2 G T typ_top
| subtyp_bot: forall m2 G T,
    subtyp ty_general m2 G typ_bot T
| subtyp_refl: forall m2 G T,
    subtyp ty_general m2 G T T
(* NOTE(dsub): we don't really need trans in ty_precise typing,
   since it's not useful without intersections,
   but we leave it anyways... *)
| subtyp_trans: forall m1 m2 G S T U,
    subtyp m1 m2 G S T ->
    subtyp m1 m2 G T U ->
    subtyp m1 m2 G S U
| subtyp_typ: forall m2 G S1 T1 S2 T2,
    subtyp ty_general m2 G S2 S1 ->
    subtyp ty_general m2 G T1 T2 ->
    subtyp ty_general m2 G (typ_mem S1 T1) (typ_mem S2 T2)
| subtyp_sel2: forall G x S T,
    ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_mem S T) ->
    subtyp ty_general sub_general G S (typ_sel (avar_f x))
| subtyp_sel1: forall G x S T,
    ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_mem S T) ->
    subtyp ty_general sub_general G (typ_sel (avar_f x)) T
| subtyp_sel2_tight: forall G x T,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_mem T T) ->
    subtyp ty_general sub_tight G T (typ_sel (avar_f x))
| subtyp_sel1_tight: forall G x T,
    ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_mem T T) ->
    subtyp ty_general sub_tight G (typ_sel (avar_f x)) T
| subtyp_all: forall L m2 G S1 T1 S2 T2,
    subtyp ty_general m2 G S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general sub_general (G & x ~ S2) (open_typ x T1) (open_typ x T2)) ->
    subtyp ty_general m2 G (typ_all S1 T1) (typ_all S2 T2).

Inductive wf_sto: ctx -> sto -> Prop :=
| wf_sto_empty: wf_sto empty empty
| wf_sto_push: forall G s x T v,
    wf_sto G s ->
    x # G ->
    x # s ->
    ty_trm ty_precise sub_general G (trm_val v) T ->
    wf_sto (G & x ~ T) (s & x ~ v).

(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme trm_mut  := Induction for trm  Sort Prop
with   val_mut  := Induction for val Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut.

Scheme ts_ty_trm_mut := Induction for ty_trm    Sort Prop
with   ts_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_subtyp.

(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sto       => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : val       => fv_val   x) in
  let H := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac in_empty_contradiction :=
  solve [match goal with
  | H: _ \in \{} |- _ => rewrite in_empty in H; exfalso; exact H
  end].

Ltac eq_specialize :=
  repeat match goal with
  | H:                 _ = _ -> _ |- _ => specialize (H         eq_refl)
  | H: forall _      , _ = _ -> _ |- _ => specialize (H _       eq_refl)
  | H: forall _ _    , _ = _ -> _ |- _ => specialize (H _ _     eq_refl)
  | H: forall _ _ _  , _ = _ -> _ |- _ => specialize (H _ _ _   eq_refl)
  | H: forall _ _ _ _, _ = _ -> _ |- _ => specialize (H _ _ _ _ eq_refl)
  end.

Ltac crush := eq_specialize; eauto.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors
  ty_trm
  subtyp.

Hint Constructors wf_sto.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Proofs *)

(* ###################################################################### *)
(** ** Weakening *)

Lemma weaken_rules:
  (forall m1 m2 G t T, ty_trm m1 m2 G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm m1 m2 (G1 & G2 & G3) t T) /\
  (forall m1 m2 G T U, subtyp m1 m2 G T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m1 m2 (G1 & G2 & G3) T U).
Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; eauto.
  + intros. subst.
    apply_fresh ty_all_intro as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst.
    apply_fresh subtyp_all as z.
    eauto.
    eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma weaken_ty_trm:  forall m1 m2 G1 G2 t T,
    ty_trm m1 m2 G1 t T ->
    ok (G1 & G2) ->
    ty_trm m1 m2 (G1 & G2) t T.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

Lemma weaken_subtyp: forall m1 m2 G1 G2 S U,
  subtyp m1 m2 G1 S U ->
  ok (G1 & G2) ->
  subtyp m1 m2 (G1 & G2) S U.
Proof.
  intros.
    assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r. reflexivity.
  }
  rewrite EqG. apply* weaken_rules.
  rewrite concat_empty_r. reflexivity.
  rewrite <- EqG. assumption.
Qed.

(* ###################################################################### *)
(** ** Well-formed store *)

Lemma wf_sto_to_ok_s: forall s G,
  wf_sto G s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto G s -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto G s ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise sub_general G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) v.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
Qed.

Lemma sto_binds_to_ctx_binds_raw: forall s G x v,
  wf_sto G s ->
  binds x v s ->
  exists G1 G2 T, G = G1 & (x ~ T) & G2 /\ ty_trm ty_precise sub_general G1 (trm_val v) T.
Proof.
  introv Wf Bi. gen x v Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists G (@empty typ) T.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [T0' [Eq Ty]]]].
      subst. exists G1 (G2 & x ~ T) T0'. rewrite concat_assoc. auto.
Qed.

Lemma invert_wf_sto_concat: forall s G1 G2,
  wf_sto (G1 & G2) s ->
  exists s1 s2, s = s1 & s2 /\ wf_sto G1 s1.
Proof.
  introv Wf. gen_eq G: (G1 & G2). gen G1 G2. induction Wf; introv Eq; subst.
  - do 2 exists (@empty val). rewrite concat_empty_r.
    apply empty_concat_inv in Eq. destruct Eq. subst. auto.
  - destruct (env_case G2) as [Eq1 | [x' [T' [G2' Eq1]]]].
    * subst G2. rewrite concat_empty_r in Eq. subst G1.
      exists (s & x ~ v) (@empty val). rewrite concat_empty_r. auto.
    * subst G2. rewrite concat_assoc in Eq. apply eq_push_inv in Eq.
      destruct Eq as [? [? ?]]. subst x' T' G. specialize (IHWf G1 G2' eq_refl).
      destruct IHWf as [s1 [s2 [Eq Wf']]]. subst.
      exists s1 (s2 & x ~ v). rewrite concat_assoc. auto.
Qed.

Lemma sto_unbound_to_ctx_unbound: forall s G x,
  wf_sto G s ->
  x # s ->
  x # G.
Proof.
  introv Wf Ub_s.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub_s).
    - auto.
Qed.

Lemma ctx_unbound_to_sto_unbound: forall s G x,
  wf_sto G s ->
  x # G ->
  x # s.
Proof.
  introv Wf Ub.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub).
    - auto.
Qed.

Lemma typing_implies_bound: forall m1 m2 G x T,
  ty_trm m1 m2 G (trm_var (avar_f x)) T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_var (avar_f x)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

Lemma typing_bvar_implies_false: forall m1 m2 G a T,
  ty_trm m1 m2 G (trm_var (avar_b a)) T ->
  False.
Proof.
  intros. remember (trm_var (avar_b a)) as t. induction H; try solve [inversion Heqt].
  eapply IHty_trm. auto.
Qed.

(* ###################################################################### *)
(** ** Substitution *)

Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => (avar_f (If x = z then u else x))
  end.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_mem T U    => typ_mem (subst_typ z u T) (subst_typ z u U)
  | typ_sel x      => typ_sel (subst_avar z u x)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_val v        => trm_val (subst_val z u v)
  | trm_app x1 x2    => trm_app (subst_avar z u x1) (subst_avar z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: var) (v: val) : val :=
  match v with
  | val_def T        => val_def (subst_typ z u T)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  end.

Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx := map (subst_typ z u) G.

(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_typ: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ).
Proof.
  intros x y. intros T; induction T; intros; simpls; f_equal*. apply* subst_fresh_avar.
Qed.

Lemma subst_fresh_trm_val: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ).
Qed.

Definition subst_fresh_trm (x y: var) := proj1 (subst_fresh_trm_val x y).
Definition subst_fresh_val (x y: var) := proj2 (subst_fresh_trm_val x y).

Lemma invert_fv_ctx_types_push: forall x z T G,
  x \notin fv_ctx_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_ctx_types G).
Proof.
  introv N.
  unfold fv_ctx_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

Lemma subst_fresh_ctx: forall x y G,
  x \notin fv_ctx_types G -> subst_ctx x y G = G.
Proof.
  intros x y.
  apply (env_ind (fun G => x \notin fv_ctx_types G -> subst_ctx x y G = G)).
  + intro N. unfold subst_ctx. apply map_empty.
  + intros G z T IH N.
    apply invert_fv_ctx_types_push in N. destruct N as [N1 N2].
    unfold subst_ctx in *. rewrite map_push.
    rewrite (IH N2).
    rewrite (subst_fresh_typ _ T N1).
    reflexivity.
Qed.

Definition subst_fvar(x y z: var): var := If z = x then y else z.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a)
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_rec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)).
Proof.
  intros x y u t. induction t; intros; simpl; f_equal*.
  apply subst_open_commute_avar.
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_rec.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_trm_val: forall x y u,
  (forall t : trm, forall n: Datatypes.nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: Datatypes.nat,
     subst_val x y (open_rec_val n u v)
     = open_rec_val n (subst_fvar x y u) (subst_val x y v)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ_rec).
Qed.

Lemma subst_open_commute_trm: forall x y u t,
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commute_trm_val.
Qed.

Lemma subst_open_commute_val: forall x y u v,
  subst_val x y (open_val u v) = open_val (subst_fvar x y u) (subst_val x y v).
Proof.
  intros. apply* subst_open_commute_trm_val.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh_trm_val x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_val: forall x u v, x \notin (fv_val v) ->
  open_val u v = subst_val x u (open_val x v).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_val.
  destruct (@subst_fresh_trm_val x u) as [_ Q]. rewrite* (Q v).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commute_typ.
  rewrite* (@subst_fresh_typ x u).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_undo_avar: forall x y,
  (forall a, y \notin fv_avar a -> (subst_avar y x (subst_avar x y a)) = a).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + unfold fv_avar in H. assert (y <> v) by auto. repeat case_if; reflexivity.
Qed.

Lemma subst_undo_typ: forall x y T,
   y \notin fv_typ  T  -> (subst_typ  y x (subst_typ  x y T )) = T.
Proof.
  intros x y T.
  induction T; intros; simpl; unfold fv_typ in *; f_equal*.
  apply* subst_undo_avar.
Qed.

Lemma subst_undo_trm_val: forall x y,
   (forall t , y \notin fv_trm  t  -> (subst_trm  y x (subst_trm  x y t )) = t )
/\ (forall v , y \notin fv_val  v  -> (subst_val  y x (subst_val  x y v )) = v ).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_val in *; f_equal*;
    (apply* subst_undo_avar || apply* subst_undo_typ).
Qed.

Lemma subst_undo_trm: forall x y t,
  y \notin fv_trm t -> (subst_trm y x (subst_trm x y t)) = t.
Proof.
  apply* subst_undo_trm_val.
Qed.

Lemma subst_idempotent_avar: forall x y,
  (forall a, (subst_avar x y (subst_avar x y a)) = (subst_avar x y a)).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + repeat case_if; reflexivity.
Qed.

Lemma subst_idempotent_typ: forall x y T,
   subst_typ x y (subst_typ x y T) = subst_typ x y T.
Proof.
  intros x y T.
  induction T; intros; simpl; unfold fv_typ in *; f_equal*.
  apply* subst_idempotent_avar.
Qed.

Lemma subst_idempotent_trm_val: forall x y,
   (forall t , subst_trm  x y (subst_trm  x y t ) = (subst_trm  x y t ))
/\ (forall v , subst_val  x y (subst_val  x y v ) = (subst_val  x y v )).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_val in *; f_equal*;
    (apply* subst_idempotent_avar || apply* subst_idempotent_typ).
Qed.

Lemma subst_idempotent_trm: forall x y t,
  subst_trm x y (subst_trm x y t) = subst_trm x y t.
Proof.
  apply* subst_idempotent_trm_val.
Qed.

(* ###################################################################### *)
(** ** The substitution principle *)

Lemma subst_rules: forall y S,
  (forall m1 m2 G t T, ty_trm m1 m2 G t T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general sub_general (G1 & (subst_ctx x y G2)) (trm_var (avar_f y)) (subst_typ x y S) ->
    m1 = ty_general ->
    m2 = sub_general ->
    ty_trm m1 m2 (G1 & (subst_ctx x y G2)) (subst_trm x y t) (subst_typ x y T)) /\
  (forall m1 m2 G T U, subtyp m1 m2 G T U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_ctx_types G1 ->
    ty_trm ty_general sub_general (G1 & (subst_ctx x y G2)) (trm_var (avar_f y)) (subst_typ x y S) ->
    m1 = ty_general ->
    m2 = sub_general ->
    subtyp m1 m2 (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U)).
Proof.
  intros y S. apply rules_mutind; intros; subst.
  - (* ty_var *)
    simpl. case_if.
    + apply binds_middle_eq_inv in b. subst. assumption. assumption.
    + apply subst_fresh_ctx with (y:=y) in H1.
      apply binds_subst in b.
      apply ty_var. rewrite <- H1.
      unfold subst_ctx. rewrite <- map_concat.
      apply binds_map. assumption. assumption.
  - (* ty_all_intro *)
    simpl.
    apply_fresh ty_all_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    rewrite <- A at 3. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_all_elim *)
    simpl. rewrite subst_open_commute_typ.
    eapply ty_all_elim.
    simpl in H.
    apply H; eauto.
    apply H0; eauto.
  - (* ty_def_intro *)
    simpl. eauto.
  - (* ty_let *)
    simpl.
    apply_fresh ty_let as z; eauto.
    assert (subst_ctx x y G2 & z ~ subst_typ x y T = subst_ctx x y (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- subst_open_commute_trm.
    apply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
  - (* ty_sub *)
    eapply ty_sub; eauto.
    intro Contra. inversion Contra.
  - (* subtyp_top *)
    apply subtyp_top.
  - (* subtyp_bot *)
    apply subtyp_bot.
  - (* subtyp_refl *)
    apply subtyp_refl.
  - (* subtyp_trans *)
    eapply subtyp_trans; eauto.
  - (* subtyp_typ *)
    eapply subtyp_typ; eauto.
  - (* subtyp_sel2 *)
    eapply subtyp_sel2; eauto.
  - (* subtyp_sel1 *)
    eapply subtyp_sel1; eauto.
  - (* subtyp_sel2_tight *) inversion H5.
  - (* subtyp_sel1_tight *) inversion H5.
  - (* subtyp_all *)
    simpl. apply_fresh subtyp_all as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x y z = z) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A at 2. rewrite <- A at 3.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x y G2 & z ~ subst_typ x y S2 = subst_ctx x y (G2 & z ~ S2)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite <- concat_assoc. rewrite B.
    apply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
    rewrite <- B. rewrite concat_assoc. apply weaken_ty_trm. assumption.
    apply ok_push. apply ok_concat_map. eauto. unfold subst_ctx. eauto.
Qed.

Lemma subst_ty_trm: forall y S G x t T,
    ty_trm ty_general sub_general (G & x ~ S) t T -> 
    ok (G & x ~ S) ->
    x \notin fv_ctx_types G ->
    ty_trm ty_general sub_general G (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_trm ty_general sub_general G (subst_trm x y t) (subst_typ x y T).
Proof.
  intros.
  apply (proj51 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H.
  unfold subst_ctx in H. rewrite map_empty in H. rewrite concat_empty_r in H.
  apply H.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. assumption.
  assumption.
  unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r. assumption.
  reflexivity.
  reflexivity.
Qed.

(* ###################################################################### *)
(** ** Some Lemmas *)

Lemma corresponding_types: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  ((exists S U t, binds x (val_lambda S t) s /\
                  ty_trm ty_precise sub_general G (trm_val (val_lambda S t)) (typ_all S U) /\
                  T = typ_all S U) \/
   (exists S, binds x (val_def S) s /\
                 ty_trm ty_precise sub_general G (trm_val (val_def S)) (typ_mem S S) /\
                 T = typ_mem S S)).
Proof.
  introv H Bi. induction H.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists T0. exists U. exists t.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * right. exists T0.
        split. auto. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * assert (exists x, trm_val v = trm_var (avar_f x)) as A. {
          apply H3. reflexivity.
        }
        destruct A as [? A]. inversion A.
    + specialize (IHwf_sto Bi).
      inversion IHwf_sto as [IH | IH].
      * destruct IH as [S [U [t [IH1 [IH2 IH3]]]]].
        left. exists S. exists U. exists t.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
      * destruct IH as [S [IH1 [IH2 IH3]]].
        right. exists S.
        split. assumption. split.
        apply weaken_ty_trm. assumption. apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
Qed.

Lemma unique_rec_subtyping: forall G S T,
  subtyp ty_precise sub_general G (typ_mem S S) T ->
  T = typ_mem S S.
Proof.
  introv Hsub.
  remember (typ_mem S S) as T'.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1 Heqm2). subst.
    apply IHHsub2; eauto.
Qed.

Lemma unique_all_subtyping: forall G S U T,
  subtyp ty_precise sub_general G (typ_all S U) T ->
  T = typ_all S U.
Proof.
  introv Hsub.
  remember (typ_all S U) as T'.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hsub; try solve [inversion Heqm1].
  - specialize (IHHsub1 HeqT' Heqm1 Heqm2). subst.
    apply IHHsub2; reflexivity.
Qed.

Lemma unique_lambda_typing: forall G x S U T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) T ->
  T = typ_all S U.
Proof.
  introv Bi Hty.
  remember (trm_var (avar_f x)) as t.
  remember ty_precise as m1.
  remember sub_general as m2.
  induction Hty; try solve [inversion Heqt; inversion Heqm1].
  - inversions Heqt.
    unfold binds in Bi. unfold binds in H.
    rewrite H in Bi. inversion Bi.
    reflexivity.
  - specialize (IHHty Bi Heqt Heqm1 Heqm2).
    rewrite IHHty in H0. rewrite Heqm1 in H0. rewrite Heqm2 in H0.
    apply unique_all_subtyping in H0.
    apply H0.
Qed.

Lemma lambda_not_rcd: forall G x S U T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_mem T T) ->
  False.
Proof.
  introv Bi Hty.
  assert (typ_mem T T = typ_all S U) as Contra. {
    eapply unique_lambda_typing; eassumption.
  }
  inversion Contra.
Qed.

Lemma precise_def_typing: forall G d S U,
  ty_trm ty_precise sub_general G (trm_val (val_def d)) (typ_mem S U) ->
  S = U.
Proof.
  intros.
  inversion H; subst; eauto.
  + assert (exists x, trm_val (val_def d) = trm_var (avar_f x)) as Contra. {
      apply H0; eauto.
    }
    destruct Contra as [? Contra]. inversion Contra.
Qed.

(* NOTE(dsub): in fact, precise subtyping is just reflexivity...
   since we don't have intersections... *)
Lemma precise_subtyping: forall G T T',
  subtyp ty_precise sub_general G T T' ->
  T = T'.
Proof.
  introv Hsub. dependent induction Hsub.
  - subst. reflexivity.
Qed.

Lemma shape_new_typing: forall G x S T,
  binds x (typ_mem S S) G ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) T ->
  T = typ_mem S S.
Proof.
  introv Bi Hx. dependent induction Hx.
  - unfold binds in H. unfold binds in Bi. rewrite H in Bi. inversion Bi.
    reflexivity.
  - assert (T = typ_mem S S) as A. {
      eapply IHHx; eauto.
    }
    subst. symmetry. eapply precise_subtyping. eassumption.
Qed.

Lemma unique_tight_bounds: forall G s x T1 T2,
  wf_sto G s ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_mem T1 T1) ->
  ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_mem T2 T2) ->
  T1 = T2.
Proof.
  introv Hwf Hty1 Hty2.
  assert (exists T, binds x T G) as Bi. {
    eapply typing_implies_bound. eassumption.
  }
  destruct Bi as [T Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis [Ht EqT]]]]].
    false.
    eapply lambda_not_rcd.
    subst. eassumption. eassumption.
  - destruct H as [S [Bis [Ht EqT]]]. subst.
    lets A1: (shape_new_typing Bi Hty1).
    lets A2: (shape_new_typing Bi Hty2).
    inversions A1. inversions A2. reflexivity.
Qed.

Lemma precise_to_general:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_precise ->
     m2 = sub_general ->
     ty_trm ty_general sub_general G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_precise ->
     m2 = sub_general ->
     subtyp ty_general sub_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
Qed.

Lemma precise_to_general_typing: forall G t T,
  ty_trm ty_precise sub_general G t T ->
  ty_trm ty_general sub_general G t T.
Proof.
  intros. apply* precise_to_general.
Qed.

Lemma tight_to_general:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_general ->
     m2 = sub_tight ->
     ty_trm ty_general sub_general G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_general ->
     m2 = sub_tight ->
     subtyp ty_general sub_general G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
  - apply precise_to_general in t; eauto.
  - apply precise_to_general in t; eauto.
Qed.

Lemma tight_to_general_typing: forall G t T,
  ty_trm ty_general sub_tight G t T ->
  ty_trm ty_general sub_general G t T.
Proof.
  intros. apply* tight_to_general.
Qed.

Lemma tight_to_general_subtyping: forall G S U,
  subtyp ty_general sub_tight G S U ->
  subtyp ty_general sub_general G S U.
Proof.
  intros. apply* tight_to_general.
Qed.

Lemma precise_to_tight:
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     m1 = ty_precise ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     m1 = ty_precise ->
     m2 = sub_general ->
     subtyp ty_general sub_tight G S U).
Proof.
  apply ts_mutind; intros; subst; eauto; inversion H0.
Qed.

Lemma precise_to_tight_typing: forall G t T,
  ty_trm ty_precise sub_general G t T ->
  ty_trm ty_general sub_tight G t T.
Proof.
  intros. apply* precise_to_tight.
Qed.

Lemma sto_binds_to_ctx_binds: forall G s x v,
  wf_sto G s -> binds x v s -> exists S, binds x S G.
Proof.
  introv Hwf Bis.
  remember Hwf as Hwf'. clear HeqHwf'.
  apply sto_binds_to_ctx_binds_raw with (x:=x) (v:=v) in Hwf.
  destruct Hwf as [G1 [G2 [T [EqG Hty]]]].
  subst.
  exists T.
  eapply binds_middle_eq. apply wf_sto_to_ok_G in Hwf'.
  apply ok_middle_inv in Hwf'. destruct Hwf'. assumption.
  assumption.
Qed.

Lemma ctx_binds_to_sto_binds: forall G s x T,
  wf_sto G s -> binds x T G -> exists v, binds x v s.
Proof.
  introv Hwf Bi.
  remember Hwf as Hwf'. clear HeqHwf'.
  apply ctx_binds_to_sto_binds_raw with (x:=x) (T:=T) in Hwf.
  destruct Hwf as [G1 [G2 [v [EqG [Bis Hty]]]]].
  subst.
  exists v.
  assumption.
  assumption.
Qed.

Lemma record_type_new: forall G s x T d,
  wf_sto G s ->
  binds x (val_def d) s ->
  binds x T G ->
  exists S, T = typ_mem S S.
Proof.
  introv Hwf Bis.
  destruct (sto_binds_to_ctx_binds Hwf Bis) as [S Bi].
  destruct (corresponding_types Hwf Bi) as [Hlambda | Hnew].
  destruct Hlambda as [? [? [? [Bis' ?]]]].
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  destruct Hnew as [? [Bis' [? ?]]]. subst.
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  intro Bi'.
  unfold binds in Bi'. unfold binds in Bi. rewrite Bi' in Bi. inversions Bi.
  eexists. reflexivity.
Qed.

(* ###################################################################### *)
(** ** Narrowing *)

Definition subenv(G1 G2: ctx) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ subtyp ty_general sub_general G1 T1 T2.

Lemma subenv_push: forall G G' x T,
  subenv G' G ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T).
Proof.
  intros.
  unfold subenv. intros xb Tb Bi. apply binds_push_inv in Bi.
  destruct Bi as [Bi | Bi].
  + destruct Bi as [Bi1 Bi2]. subst.
    left. eauto.
  + destruct Bi as [Bi1 Bi2].
    unfold subenv in H. specialize (H xb Tb Bi2). destruct H as [Bi' | Bi'].
    * left. eauto.
    * right. destruct Bi' as [T' [Bi1' Bi2']].
      exists T'. split. eauto. apply weaken_subtyp. assumption. eauto.
Qed.

Lemma subenv_last: forall G x S U,
  subtyp ty_general sub_general G S U ->
  ok (G & x ~ S) ->
  subenv (G & x ~ S) (G & x ~ U).
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists S. split; eauto.
    apply weaken_subtyp; eauto.
  - destruct Bi. left. eauto.
Qed.

Lemma narrow_rules:
  (forall m1 m2 G t T, ty_trm m1 m2 G t T -> forall G',
    m1 = ty_general ->
    m2 = sub_general ->
    ok G' ->
    subenv G' G ->
    ty_trm m1 m2 G' t T)
/\ (forall m1 m2 G S U, subtyp m1 m2 G S U -> forall G',
    m1 = ty_general ->
    m2 = sub_general ->
    ok G' ->
    subenv G' G ->
    subtyp m1 m2 G' S U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. unfold subenv in H2. specialize (H2 x T b).
    destruct H2.
    + eauto.
    + destruct H as [T' [Bi Hsub]].
      eapply ty_sub; eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    eapply H; eauto. apply subenv_push; eauto.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    apply H0 with (x:=y); eauto. apply subenv_push; eauto.
  - inversion H1 (* sub_tight *).
  - inversion H1 (* sub_tight *).
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    apply H0; eauto. apply subenv_push; eauto.
Qed.

Lemma narrow_typing: forall G G' t T,
  ty_trm ty_general sub_general G t T ->
  subenv G' G -> ok G' ->
  ty_trm ty_general sub_general G' t T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall G G' S U,
  subtyp ty_general sub_general G S U ->
  subenv G' G -> ok G' ->
  subtyp ty_general sub_general G' S U.
Proof.
  intros. apply* narrow_rules.
Qed.

(* ###################################################################### *)
(** * Has member *)

Inductive has_member: ctx -> var -> typ -> typ -> typ -> Prop :=
| has_any : forall G x T S U,
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T ->
  has_member_rules G x T S U ->
  has_member G x T S U
with has_member_rules: ctx -> var -> typ -> typ -> typ -> Prop :=
| has_refl : forall G x S U,
  has_member_rules G x (typ_mem S U) S U
| has_sel : forall G x y T' S U,
  ty_trm ty_precise sub_general G (trm_var (avar_f y)) (typ_mem T' T') ->
  has_member G x T' S U ->
  has_member_rules G x (typ_sel (avar_f y)) S U
| has_bot  : forall G x S U,
  has_member_rules G x typ_bot S U
.

Scheme has_mut := Induction for has_member Sort Prop
with hasr_mut := Induction for has_member_rules Sort Prop.
Combined Scheme has_mutind from has_mut, hasr_mut.

Lemma has_member_rules_inv: forall G x T S U, has_member_rules G x T S U ->
  (T = typ_mem S U) \/
  (exists y T', T = typ_sel (avar_f y) /\
    ty_trm ty_precise sub_general G (trm_var (avar_f y)) (typ_mem T' T') /\
    has_member G x T' S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst.
  - left. eauto.
  - right. left. exists y T'. eauto.
  - right. right. reflexivity.
Qed.

Lemma has_member_inv: forall G x T S U, has_member G x T S U ->
  (T = typ_mem S U) \/
  (exists y T', T = typ_sel (avar_f y) /\
    ty_trm ty_precise sub_general G (trm_var (avar_f y)) (typ_mem T' T') /\
    has_member G x T' S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst. apply has_member_rules_inv in H1. apply H1.
Qed.

Lemma val_new_typing: forall G s x M,
  wf_sto G s ->
  binds x (val_def M) s ->
  ty_trm ty_precise sub_general G (trm_val (val_def M)) (typ_mem M M).
Proof.
  introv Hwf Bis.
  assert (exists T, binds x T G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis' [Ht EqT]]]]].
    false.
  - destruct H as [T' [Bis' [Ht EqT]]]. subst.
    unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis.
    inversion Bis. subst.
    assumption.
Qed.

Lemma has_member_tightness: forall G s x T S U,
  wf_sto G s ->
  binds x (val_def T) s ->
  has_member G x (typ_mem T T) S U ->
  S = U.
Proof.
  introv Hwf Bis Hmem.
  inversion Hmem; subst. inversion H0; subst.
  reflexivity.
Qed.

Lemma has_member_covariance: forall G s T1 T2 x S2 U2,
  wf_sto G s ->
  subtyp ty_general sub_tight G T1 T2 ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T1 ->
  has_member G x T2 S2 U2 ->
  exists S1 U1, has_member G x T1 S1 U1 /\
                subtyp ty_general sub_tight G S2 S1 /\
                subtyp ty_general sub_tight G U1 U2.
Proof.
  introv Hwf Hsub Hty Hmem.
  generalize dependent U2.
  generalize dependent S2.
  dependent induction Hsub; subst; intros.
  - (* top *)
    inversion Hmem; subst. inversion H0.
  - (* bot *)
    exists S2 U2. split.
    apply has_any. assumption. apply has_bot.
    split; apply subtyp_refl.
  - (* refl *)
    exists S2 U2. eauto.
  - (* trans *)
    assert (ty_trm ty_general sub_tight G (trm_var (avar_f x)) T) as HS. {
      eapply ty_sub. intros Hp. subst. eexists; eauto.
      eapply Hty.
      eassumption.
    }
    specialize (IHHsub2 Hwf HS S2 U2 Hmem).
    destruct IHHsub2 as [S3 [U3 [Hmem3 [Hsub31 Hsub32]]]].
    specialize (IHHsub1 Hwf Hty S3 U3 Hmem3).
    destruct IHHsub1 as [S1 [U1 [Hmem1 [Hsub11 Hsub12]]]].
    exists S1 U1. split. apply Hmem1. split; eauto.
  - (* typ *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversions Hmem.
      exists S1 T1. split.
      apply has_any. assumption. apply has_refl.
      split; assumption.
    + destruct Hmem as [y [T' [Heq _]]]. inversion Heq.
    + inversion Hmem.
  - (* sel2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [y [T' [Heq [Htyb Hmem]]]]. inversions Heq.
      assert (T' = T) as HeqT. {
        eapply unique_tight_bounds; eassumption.
      }
      subst. eauto.
    + inversion Hmem.
  - (* sel1 *)
    exists S2 U2. split.
    eapply has_any. assumption. eapply has_sel. eassumption. eassumption.
    eauto.
  - (* all *)
    inversion Hmem; subst. inversion H2; subst.
Qed.

Lemma has_member_monotonicity: forall G s x T0 T S U,
  wf_sto G s ->
  binds x (val_def T0) s ->
  has_member G x T S U ->
  exists T1, has_member G x (typ_mem T0 T0) T1 T1 /\
             subtyp ty_general sub_tight G S T1 /\
             subtyp ty_general sub_tight G T1 U.
Proof.
  introv Hwf Bis Hmem. inversion Hmem; subst.
  generalize dependent U. generalize dependent S.
  dependent induction H; intros.
  - (* var *)
    destruct (corresponding_types Hwf H).
    destruct H1 as [S0 [U0 [t [Bis' _]]]]. unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversion Bis.
    destruct H1 as [S0 [Bis' [Hty Heq]]]. unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversions Bis'.
    assert (S = U). {
      eapply has_member_tightness. eassumption. eassumption.
      eapply has_any.
      eapply ty_var. eassumption.
      eassumption.
    }
    subst.
    exists U. eauto.
  - (* sub *)
    destruct (has_member_covariance Hwf H1 H0 Hmem) as [S' [U' [Hmem' [Hsub1' Hsub2']]]].
    inversion Hmem'; subst.
    specialize (IHty_trm Hwf Bis S' U' Hmem' H4).
    destruct IHty_trm as [T1 [Hmem1 [Hsub1 Hsub2]]].
    exists T1. eauto.
Qed.

(* ###################################################################### *)
(** * Tight bound completeness *)

Lemma wf_sto_val_new_in_G: forall G s x T,
  wf_sto G s ->
  binds x (val_def T) s ->
  binds x (typ_mem T T) G.
Proof.
  introv Hwf Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [S Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [? [? [? [Bis' _]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversion Bis'.
  - destruct H as [T' [Bis' [Hty Heq]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
    assumption.
Qed.

(* If G ~ s, s |- x = new(x: T)d, and G |-# x: {A: S..U} then G |-# x.A <: U and G |-# S <: x.A. *)
Lemma tight_bound_completeness: forall G s x T S U,
  wf_sto G s ->
  binds x (val_def T) s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_mem S U) ->
  subtyp ty_general sub_tight G (typ_sel (avar_f x)) U /\
  subtyp ty_general sub_tight G S (typ_sel (avar_f x)).
Proof.
  introv Hwf Bis Hty.
  assert (has_member G x (typ_mem S U) S U) as Hmem. {
    apply has_any. assumption. apply has_refl.
  }
  apply has_member_monotonicity with (s:=s) (T0:=T) in Hmem.
  destruct Hmem as [T1 [Hmem [Hsub1 Hsub2]]]. inversion Hmem; subst. inversion H0; subst.
  assert (ty_trm ty_precise sub_general G (trm_var (avar_f x)) (typ_mem T1 T1)) as Htyp. {
    eapply ty_var. eapply wf_sto_val_new_in_G. eassumption. eassumption.
  }
  split.
  eapply subtyp_trans. eapply subtyp_sel1_tight. eapply Htyp. eapply Hsub2.
  eapply subtyp_trans. eapply Hsub1. eapply subtyp_sel2_tight. eapply Htyp.
  eapply Hwf. eapply Bis.
Qed.

(* ###################################################################### *)
(** * Misc Inversions *)

Lemma all_intro_inversion: forall G S t U,
  ty_trm ty_precise sub_general G (trm_val (val_lambda S t)) U ->
  exists T, U = typ_all S T.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
Qed.

Lemma new_intro_inversion: forall G T U,
  ty_trm ty_precise sub_general G (trm_val (val_def T)) U ->
  U = typ_mem T T.
Proof.
  intros. inversion H; subst.
  - reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H0 Heqm1). destruct H0. inversion H0.
Qed.

(* ###################################################################### *)
(** ** Possible types *)

(*
Definition (Possible types)
*)

(* NOTE(dsub): the pt_new seems to also be removable from the full DOT proof. *)
Inductive possible_types: ctx -> var -> val -> typ -> Prop :=
| pt_top : forall G x v,
  possible_types G x v typ_top
| pt_mem : forall G x T S U,
  subtyp ty_general sub_general G S T ->
  subtyp ty_general sub_general G T U ->
  possible_types G x (val_def T) (typ_mem S U)
| pt_lambda : forall L G x S t T S' T',
  (forall y, y \notin L ->
   ty_trm ty_general sub_general (G & y ~ S) (open_trm y t) (open_typ y T)) ->
  subtyp ty_general sub_general G S' S ->
  (forall y, y \notin L ->
   subtyp ty_general sub_general (G & y ~ S') (open_typ y T) (open_typ y T')) ->
  possible_types G x (val_lambda S t) (typ_all S' T')
| pt_sel : forall G x v y S,
  possible_types G x v S ->
  ty_trm ty_precise sub_general G (trm_var y) (typ_mem S S) ->
  possible_types G x v (typ_sel y)
.

Lemma var_new_typing: forall G s x T,
  wf_sto G s ->
  binds x (val_def T) s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_mem T T).
Proof.
  intros.
  apply ty_var. eapply wf_sto_val_new_in_G; eauto.
Qed.

(*
Lemma (Possible types closure)

If G ~ s and G |- x: T and s |- x = v then Ts(G, x, v) is closed wrt G |- _ <: _.

Let SS = Ts(G, x, v). We first show SS is closed wrt G |-# _ <: _.

Assume T0 in SS and G |- T0 <: U0.s We show U0 in SS by an induction on subtyping derivations of G |-# T0 <: U0.
*)

Lemma possible_types_closure_tight: forall G s x v T0 U0,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v T0 ->
  subtyp ty_general sub_tight G T0 U0 ->
  possible_types G x v U0.
Proof.
  introv Hwf Bis HT0 Hsub. dependent induction Hsub.
  - (* Top *) apply pt_top.
  - (* Bot *) inversion HT0; subst.
  - (* Refl-<: *) assumption.
  - (* Trans-<: *)
    apply IHHsub2; try assumption.
    apply IHHsub1; assumption.
  - (* Typ-<:-Typ *)
    inversion HT0; subst.
    eapply pt_mem.
    eapply subtyp_trans. eapply tight_to_general_subtyping. eassumption. eassumption.
    eapply subtyp_trans. eassumption. eapply tight_to_general_subtyping. eassumption.
  - (* <:-Sel-tight *)
    eapply pt_sel. eassumption. assumption.
  - (* Sel-<:-tight *)
    inversion HT0; subst.
    assert (T = S) as B. {
      eapply unique_tight_bounds; eauto.
    }
    subst. assumption.
  - (* All-<:-All *)
    inversion HT0; subst.
    apply_fresh pt_lambda as y.
    eapply H3; eauto.
    eapply subtyp_trans. eapply tight_to_general_subtyping. eassumption. eassumption.
    eapply subtyp_trans.
    eapply narrow_subtyping. eapply H8; eauto.
    eapply subenv_last. eapply tight_to_general_subtyping. eapply Hsub.
    eapply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
    eapply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
    eapply H; eauto.
Qed.

(*
Lemma (Possible types completeness for values)

If `G ~ s` and `x = v in s` and  `G |-! v: T` then `T in Ts(G, x, v)`.
 *)

Lemma possible_types_completeness_for_values: forall G s x v T,
  wf_sto G s ->
  binds x v s ->
  ty_trm ty_precise sub_general G (trm_val v) T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty. destruct v as [S ds | S t].
  - inversion Hty; subst. eapply pt_mem. apply subtyp_refl. apply subtyp_refl.
    assert (ty_precise = ty_precise) as Heqm1 by auto. specialize (H Heqm1).
    destruct H as [? Contra]. inversion Contra.
  - remember Hty as Hty'. clear HeqHty'. inversion Hty'; subst.
    + apply all_intro_inversion in Hty. destruct Hty as [T' Heq]. subst.
      apply_fresh pt_lambda as y.
      eapply H5; eauto.
      apply subtyp_refl.
      apply subtyp_refl.
    + assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
      specialize (H Heqm1). destruct H. inversion H.
Qed.

(*
Lemma (Possible types completeness)

If `G ~ s` and `x = v in s` and  `G |-# x: T` then `T in Ts(G, x, v)`.

Lemma (Possible types)

If `G ~ s` and `G |- x: T` then, for some value `v`,
`s(x) = v` and `T in Ts(G, x, v)`.
*)

Lemma possible_types_completeness_tight: forall G s x T,
  wf_sto G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T) as A. {
      destruct (ctx_binds_to_sto_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
      eapply wf_sto_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure_tight; eauto.
Qed.

Lemma tight_ty_rcd_typ__new: forall G s x S U,
  wf_sto G s ->
  ty_trm ty_general sub_tight G (trm_var (avar_f x)) (typ_mem S U) ->
  exists T, binds x (val_def T) s.
Proof.
  introv Hwf Hty.
  destruct (possible_types_completeness_tight Hwf Hty) as [v [Bis Hpt]].
  inversion Hpt; subst; repeat eexists; eauto.
Qed.


Lemma general_to_tight: forall G0 s0,
  wf_sto G0 s0 ->
  (forall m1 m2 G t T,
     ty_trm m1 m2 G t T ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     ty_trm ty_general sub_tight G t T) /\
  (forall m1 m2 G S U,
     subtyp m1 m2 G S U ->
     G = G0 ->
     m1 = ty_general ->
     m2 = sub_general ->
     subtyp ty_general sub_tight G S U).
Proof.
  intros G0 s0 Hwf.
  apply ts_mutind; intros; subst; eauto.
  - assert (exists S, binds x (val_def S) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? Bis].
    eapply proj2. eapply tight_bound_completeness; eauto.
  - assert (exists S, binds x (val_def S) s0) as Bis. {
      eapply tight_ty_rcd_typ__new; eauto.
    }
    destruct Bis as [? Bis].
    eapply proj1. eapply tight_bound_completeness; eauto.
Qed.

Lemma general_to_tight_subtyping: forall G s S U,
   wf_sto G s ->
  subtyp ty_general sub_general G S U ->
  subtyp ty_general sub_tight G S U.
Proof.
  intros. apply* general_to_tight.
Qed.

Lemma possible_types_closure: forall G s x v S T,
  wf_sto G s ->
  binds x v s ->
  possible_types G x v S ->
  subtyp ty_general sub_general G S T ->
  possible_types G x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
  eapply general_to_tight_subtyping; eauto.
Qed.

Lemma possible_types_completeness: forall G s x T,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) T ->
  exists v, binds x v s /\ possible_types G x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T) as A. {
      destruct (ctx_binds_to_sto_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_ty_trm. assumption. rewrite concat_assoc.
      eapply wf_sto_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [v [Bis Hp]].
    exists v. split. apply Bis. eapply possible_types_closure; eauto.
Qed.

Lemma possible_types_lemma: forall G s x v T,
  wf_sto G s ->
  binds x v s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) T ->
  possible_types G x v T.
Proof.
  introv Hwf Bis Hty.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.

Lemma ctx_binds_to_sto_binds_typing: forall G s x T,
  wf_sto G s ->
  binds x T G ->
  exists v, binds x v s /\ ty_trm ty_precise sub_general G (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_sto_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  apply weaken_ty_trm; eauto.
  rewrite concat_assoc.
  eapply wf_sto_to_ok_G; eauto.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall G s x T U,
  wf_sto G s ->
  ty_trm ty_general sub_general G (trm_var (avar_f x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general sub_general G T T' /\
  (forall y, y \notin L -> ty_trm ty_general sub_general (G & y ~ T) (open_trm y t) (open_typ y U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  inversion Hp; subst.
  - pick_fresh y. exists (dom G \u L). exists S0. exists t.
    split. apply Bis. split. assumption.
    intros y0 Fr0.
    eapply ty_sub.
    intros Contra. inversion Contra.
    eapply narrow_typing.
    eapply H1; eauto.
    apply subenv_last. apply H5.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    apply ok_push. eapply wf_sto_to_ok_G; eauto. eauto.
    eapply H6; eauto.
Qed.

(* ###################################################################### *)
(** * Misc *)

Lemma var_typing_implies_avar_f: forall G a T,
  ty_trm ty_general sub_general G (trm_var a) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm.
Qed.

Lemma val_typing: forall G v T,
  ty_trm ty_general sub_general G (trm_val v) T ->
  exists T', ty_trm ty_precise sub_general G (trm_val v) T' /\
             subtyp ty_general sub_general G T' T.
Proof.
  intros. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_mem T T). split.
    apply ty_def_intro; eauto. apply subtyp_refl.
  - destruct IHty_trm as [T' [Hty Hsub]].
    exists T'. split; eauto.
Qed.

(* ###################################################################### *)
(** * Safety *)

Inductive normal_form: trm -> Prop :=
| nf_var: forall x, normal_form (trm_var x)
| nf_val: forall v, normal_form (trm_val v).

Hint Constructors normal_form.

(*
Let G |- t: T and G ~ s. Then either

- t is a normal form, or
- there exists a store s', term t' such that s | t -> s' | t', and for any such s', t' there exists an environment G'' such that, letting G' = G, G'' one has G' |- t': T and G' ~ s'.
The proof is by a induction on typing derivations of G |- t: T.
*)

Lemma safety: forall G s t T,
  wf_sto G s ->
  ty_trm ty_general sub_general G t T ->
  (normal_form t \/ (exists s' t' G' G'', red t s t' s' /\ G' = G & G'' /\ ty_trm ty_general sub_general G' t' T /\ wf_sto G' s')).
Proof.
  introv Hwf H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets C: (canonical_forms_1 Hwf H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (open_trm z t) G (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm. eapply Hty.
    apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=S).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto. eauto.
  - (* Let *) right.
    destruct t.
    + (* var *)
      assert (exists x, a = avar_f x) as A. {
        eapply var_typing_implies_avar_f. eassumption.
      }
      destruct A as [x A]. subst a.
      exists s (open_trm x u) G (@empty typ).
      split.
      apply red_let_var.
      split.
      rewrite concat_empty_r. reflexivity.
      split.
      pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      rewrite subst_intro_trm with (x:=y).
      rewrite <- subst_fresh_typ with (x:=y) (y:=x).
      eapply subst_ty_trm. eapply H0.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
      rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. eauto.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (s & x ~ v) (open_trm x u) (G & (x ~ T')) (x ~ T').
      split.
      apply red_let. eauto.
      split. reflexivity. split.
      apply narrow_typing with (G:=G & x ~ T).
      assumption.
      apply subenv_last. assumption.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply wf_sto_push. assumption. eauto. eauto. assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply (proj51 weaken_rules). apply H0. auto. reflexivity.
      rewrite <- IH2. apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      rewrite IH2.
      rewrite <- IH2. eauto.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH].
    + left. assumption.
    + right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' t' G' G''.
      split; try split; try split; try assumption.
      apply ty_sub with (T:=T).
      intro Contra. inversion Contra.
      assumption.
      rewrite IH2. apply weaken_subtyp. assumption.
      rewrite <- IH2. eapply wf_sto_to_ok_G. eassumption.
Qed.