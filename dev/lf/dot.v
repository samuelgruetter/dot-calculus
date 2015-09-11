Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter trm_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive typ : Set :=
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ (* x.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> typ -> dec (* a: T *).

Inductive trm : Set :=
  | trm_val  : val -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
  | val_var  : avar -> val
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env val.

(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ => label_typ L
| def_trm m _ => label_trm m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_trm m _ => label_trm m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.
Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

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
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m T => dec_trm m (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_sel v m    => trm_sel (open_rec_avar k u v) m
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: var) (v: val): val :=
  match v with
  | val_new T ds => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  | val_var a => val_var (open_rec_avar k u a)
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_val  u v := open_rec_val   0 u v.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.

(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv_avar x)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m T   => (fv_typ T)
  end.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
  | val_var a       => (fv_avar a)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv_typ T)
  | def_trm _ t     => (fv_trm t)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).

(* ###################################################################### *)
(** ** Operational Semantics *)

Inductive sto_get_val : sto -> var -> val -> Prop :=
| sto_get_val_var : forall s x v,
    binds x v s ->
    sto_get_val s x v
| sto_get_val_trans : forall s x v y,
    sto_get_val s x (val_var (avar_f y)) ->
    sto_get_val s y v ->
    sto_get_val s x v.

Inductive sto_get_def : sto -> var -> def -> Prop :=
| sto_get_def_any : forall s x T ds d,
    sto_get_val s x (val_new T ds) ->
    defs_has ds d ->
    sto_get_def s x (open_def x d).

Inductive red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x m s t,
    sto_get_def s x (def_trm m t) ->
    red (trm_sel (avar_f x) m) s t s
| red_app : forall f a s T t,
    sto_get_val s f (val_lambda T t) ->
    red (trm_app (avar_f f) (avar_f a)) s (open_trm a t) s
| red_let : forall v t s x,
    x # s ->
    red (trm_let (trm_val v) t) s (open_trm x t) (s & x ~ v)
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
    ty_trm m1 m2 G (trm_val (val_var (avar_f x))) T
| ty_all_intro : forall L m1 m2 G T t U,
    wf_typ G T ->
    (forall x, x \notin L ->
      ty_trm m1 sub_general (G & x ~ T) t (open_typ x U)) ->
    ty_trm m1 m2 G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall m2 G x z S T,
    ty_trm ty_general m2 G (trm_val (val_var (avar_f x))) (typ_all S T) ->
    ty_trm ty_general m2 G (trm_val (val_var (avar_f z))) S ->
    ty_trm ty_general m2 G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro : forall L m1 m2 G T ds,
    (forall x, x \notin L ->
      wf_typ (G & (x ~ open_typ x T)) (open_typ x T)) ->
    (forall x, x \notin L ->
      ty_defs (G & (x ~ open_typ x T)) (open_defs x ds) (open_typ x T)) ->
    ty_trm m1 m2 G (trm_val (val_new T ds)) (typ_bnd T)
| ty_new_elim : forall m2 G x m T,
    ty_trm ty_general m2 G (trm_val (val_var (avar_f x))) (typ_rcd (dec_trm m T)) ->
    ty_trm ty_general m2 G (trm_sel (avar_f x) m) T
| ty_rec_intro : forall m2 G x T T',
    ty_trm ty_general m2 G (trm_val (val_var (avar_f x))) T ->
    T = open_typ x T' ->
    ty_trm ty_general m2 G (trm_val (val_var (avar_f x))) (typ_bnd T')
| ty_rec_elim : forall m1 m2 G x T,
    ty_trm m1 m2 G (trm_val (val_var (avar_f x))) (typ_bnd T) ->
    ty_trm m1 m2 G (trm_val (val_var (avar_f x))) (open_typ x T)
| ty_let : forall L m2 G t u T U,
    ty_trm ty_general m2 G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general sub_general (G & x ~ T) u U) ->
    wf_typ G U ->
    ty_trm ty_general m2 G (trm_let t u) U
| ty_sub : forall m1 m2 G t T U,
    ty_trm m1 m2 G t T ->
    subtyp m1 m2 G T U ->
    ty_trm m1 m2 G t U
with ty_def : ctx -> def -> dec -> Prop :=
| ty_def_typ : forall G A T,
    wf_typ G T ->
    ty_def G (def_typ A T) (dec_typ A T T)
| ty_def_trm : forall G a t T,
    ty_trm ty_general sub_general G t T ->
    ty_def G (def_trm a t) (dec_trm a T)
with ty_defs : ctx -> defs -> typ -> Prop :=
| ty_defs_one : forall G d D,
    ty_def G d D ->
    ty_defs G (defs_cons defs_nil d) (typ_rcd D)
| ty_defs_cons : forall G ds d T D,
    ty_defs G ds T ->
    ty_def G d D ->
    defs_hasnt ds (label_of_def d) ->
    ty_defs G (defs_cons ds d) (typ_and T (typ_rcd D))

with subtyp : tymode -> submode -> ctx -> typ -> typ -> Prop :=
| subtyp_refl: forall m2 G T,
    subtyp ty_general m2 G T T
| subtyp_trans: forall m1 m2 G S T U,
    subtyp m1 m2 G S T ->
    subtyp m1 m2 G T U ->
    subtyp m1 m2 G S U
| subtyp_and11: forall m1 m2 G T U,
    subtyp m1 m2 G (typ_and T U) T
| subtyp_and12: forall m1 m2 G T U,
    subtyp m1 m2 G (typ_and T U) U
| subtyp_and2: forall m2 G S T U,
    subtyp ty_general m2 G S T ->
    subtyp ty_general m2 G S U ->
    subtyp ty_general m2 G S (typ_and T U)
| subtyp_fld: forall m2 G a T U,
    subtyp ty_general m2 G T U ->
    subtyp ty_general m2 G (typ_rcd (dec_trm a T)) (typ_rcd (dec_trm a U))
| subtyp_typ: forall m2 G A S1 T1 S2 T2,
    subtyp ty_general m2 G S2 S1 ->
    subtyp ty_general m2 G T1 T2 ->
    subtyp ty_general m2 G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2: forall G x A S T,
    ty_trm ty_general sub_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A S T)) ->
    subtyp ty_general sub_general G S (typ_sel (avar_f x) A)
| subtyp_sel1: forall G x A S T,
    ty_trm ty_general sub_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A S T)) ->
    subtyp ty_general sub_general G (typ_sel (avar_f x) A) T
| subtyp_sel2_tight: forall G x A T,
    ty_trm ty_general sub_tight G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general sub_tight G T (typ_sel (avar_f x) A)
| subtyp_sel1_tight: forall G x A T,
    ty_trm ty_general sub_tight G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general sub_tight G (typ_sel (avar_f x) A) T
| subtyp_bnd: forall L m2 G T U,
    (forall x, x \notin L ->
       subtyp ty_general sub_general (G & x ~ (open_typ x T)) (open_typ x T) (open_typ x U)) ->
    subtyp ty_general m2 G (typ_bnd T) (typ_bnd U)
| subtyp_all: forall L m2 G S1 T1 S2 T2,
    subtyp ty_general m2 G S2 S1 ->
    wf_typ G S2 ->
    (forall x, x \notin L ->
       subtyp ty_general sub_general (G & x ~ S2) T1 T2) ->
    subtyp ty_general m2 G (typ_all S1 T1) (typ_all S2 T2)

with wf_typ : ctx -> typ -> Prop :=
| wft_fld: forall G a T,
     wf_typ G T ->
     wf_typ G (typ_rcd (dec_trm a T))
| wft_typ: forall G A T U,
     wf_typ G T ->
     wf_typ G U ->
     wf_typ G (typ_rcd (dec_typ A T U))
| wft_and: forall G T U,
     wf_typ G T ->
     wf_typ G U ->
     wf_typ G (typ_and T U)
| wft_sel: forall G x A T U,
     ty_trm ty_general sub_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A T U)) ->
     wf_typ G (typ_sel (avar_f x) A)
| wft_bnd: forall L G T,
     (forall x, x \notin L ->
        wf_typ (G & x ~ open_typ x T) (open_typ x T)) ->
     wf_typ G (typ_bnd T)
| wft_all: forall L G T U,
     wf_typ G T ->
     (forall x, x \notin L ->
        wf_typ (G & x ~ T) U) ->
     wf_typ G (typ_all T U).

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

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, def_mut, defs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_def_mut    := Induction for ty_def    Sort Prop
with   rules_defs_mut   := Induction for ty_defs   Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop
with   rules_wf_typ     := Induction for wf_typ    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp, rules_wf_typ.

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
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  let I := gather_vars_with (fun x : defs      => fv_defs  x) in
  let J := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J).

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
  ty_trm ty_def ty_defs
  subtyp
  wf_typ.

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
  (forall G d D, ty_def G d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_def (G1 & G2 & G3) d D) /\
  (forall G ds T, ty_defs G ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_defs (G1 & G2 & G3) ds T) /\
  (forall m1 m2 G T U, subtyp m1 m2 G T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m1 m2 (G1 & G2 & G3) T U) /\
  (forall G T, wf_typ G T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    wf_typ (G1 & G2 & G3) T).
Proof.
  apply rules_mutind; try solve [eauto].
  + intros. subst.
    eapply ty_var. eapply binds_weaken; eauto.
  + intros. subst.
    apply_fresh ty_all_intro as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    - specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
      repeat rewrite concat_assoc in H.
      apply* H.
    - specialize (H0 z zL G1 G2 (G3 & z ~ open_typ z T)).
      repeat rewrite concat_assoc in H0.
      apply* H0.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
    eauto.
  + intros. subst.
    apply_fresh subtyp_bnd as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh subtyp_all as z.
    eauto.
    eauto.
    assert (zL: z \notin L) by auto.
    specialize (H1 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H1.
    apply* H1.
  + intros. subst.
    apply_fresh wft_bnd as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ open_typ z T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh wft_all as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma weaken_sto_get_val: forall s x v,
  sto_get_val s x v -> forall s',
  ok (s & s') ->
  sto_get_val (s & s') x v.
Proof.
  introv H. induction H; introv Ok.
  - apply sto_get_val_var.
    rewrite <- concat_empty_r. apply binds_weaken.
    rewrite -> concat_empty_r. assumption.
    rewrite -> concat_empty_r. assumption.
  - eapply sto_get_val_trans.
    eapply IHsto_get_val1. assumption.
    eapply IHsto_get_val2. assumption.
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
  ty_trm m1 m2 G (trm_val (val_var (avar_f x))) T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_val (val_var (avar_f x))) as t. induction H; try solve [inversion Heqt].
  - inversion Heqt. subst. exists T. assumption.
  - inversion Heqt. subst. eapply IHty_trm. reflexivity.
  - inversion Heqt. subst. eapply IHty_trm. reflexivity.
  - subst. eapply IHty_trm. reflexivity.
Qed.

Lemma typing_bvar_implies_false: forall m1 m2 G a T,
  ty_trm m1 m2 G (trm_val (val_var (avar_b a))) T ->
  False.
Proof.
  intros. remember (trm_val (val_var (avar_b a))) as t. induction H; try solve [inversion Heqt].
  eapply IHty_trm. auto.
Qed.

Lemma ctx_binds_to_sto_get_val: forall n, forall s G x T,
  LibList.length G <= n ->
  wf_sto G s ->
  binds x T G ->
  (exists U ds, sto_get_val s x (val_new U ds)) \/
  (exists U t, sto_get_val s x (val_lambda U t)).
Proof.
  intros n. induction n.
  - introv LE Hwf Bi.
    assert (G = empty) as A. {
      destruct G. symmetry. apply empty_def.
      rewrite LibList.length_cons in LE. omega.
    }
    subst. false* binds_empty_inv.
  - introv LE Hwf Bi.
    assert (exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise sub_general G1 (trm_val v) T) as H. {
      apply ctx_binds_to_sto_binds_raw; assumption.
    }
    destruct H as [G1 [G2 [v [HeqG [Bis Hty]]]]].
    destruct v.
    + left. eexists. eexists. eapply sto_get_val_var. eassumption.
    + right. eexists. eexists. eapply sto_get_val_var. eassumption.
    + destruct a.
      * false* typing_bvar_implies_false.
      * eapply typing_implies_bound in Hty. destruct Hty as [T1 Bi1].
        subst.
        remember Hwf as Hwf'. clear HeqHwf'.
        rewrite <- concat_assoc in Hwf.
        apply invert_wf_sto_concat in Hwf. destruct Hwf as [s1 [s2 [Eqs Hwf]]].
        assert ((exists U ds, sto_get_val s1 v (val_new U ds)) \/
                (exists U t,  sto_get_val s1 v (val_lambda U t))) as A. {
          apply IHn with (G:=G1) (T:=T1).
          rewrite concat_def in LE.
          rewrite LibList.length_app in LE.
          rewrite LibList.length_app in LE.
          rewrite single_def in LE.
          simpl in LE.
          omega.
          assumption.
          assumption.
        }
        destruct A as [[U [ds A]] | [U [t A]]].
        left. exists U. exists ds.
        eapply sto_get_val_trans. eapply sto_get_val_var. eapply Bis.
        rewrite Eqs. eapply weaken_sto_get_val. eapply A.
        eapply wf_sto_to_ok_s. rewrite <- Eqs. eassumption.
        right. exists U. exists t.
        eapply sto_get_val_trans. eapply sto_get_val_var. eapply Bis.
        rewrite Eqs. eapply weaken_sto_get_val. eapply A.
        eapply wf_sto_to_ok_s. rewrite <- Eqs. eassumption.
Qed.

(*
Lemma tight_bound_inversion: forall G s x A T,
  wf_sto G s ->
  ty_trm ty_precise sub_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A T T)) ->
  exists S ds, sto_get_val s x (val_new S ds) /\ defs_has ds (def_typ A T).
Proof.
  introv Hwf Hty.
  remember (trm_val (val_var (avar_f x))) as t.
  remember (typ_rcd (dec_typ A T T)) as T0.
  induction Hty; try solve [inversion Heqt].
  - inversion Heqt.
    apply ctx_binds_to_sto_binds_raw with (x:=x) (T:=T0) in Hwf.
    subst. destruct Hwf as [G1 [G2 [v [HeqG [Bis Ht]]]]].
    inversion Ht; subst.
Qed.
*)