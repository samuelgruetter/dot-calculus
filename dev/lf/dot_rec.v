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

Inductive fvar : Set :=
| in_sto : var -> fvar
| in_ctx : var -> fvar.

Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : fvar -> avar.

Definition avar_s x := avar_f (in_sto x).
Definition avar_c x := avar_f (in_ctx x).

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ (* x.L *)
  | typ_bnd  : typ -> typ (* rec(x: T) *)
  | typ_all  : typ -> typ -> typ (* all(x: S)T *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* A: S..U *)
  | dec_trm  : trm_label -> typ -> dec (* a: T *).

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_val  : val -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm (* let x = t in u *)
with val : Set :=
  | val_new  : typ -> defs -> val
  | val_lambda : typ -> trm -> val
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

Definition open_rec_avar (k: nat) (u: fvar) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f v => avar_f v
  end.

Fixpoint open_rec_typ (k: nat) (u: fvar) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2)
  end
with open_rec_dec (k: nat) (u: fvar) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_trm m T => dec_trm m (open_rec_typ k u T)
  end.

Fixpoint open_rec_trm (k: nat) (u: fvar) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_val v      => trm_val (open_rec_val k u v)
  | trm_sel v m    => trm_sel (open_rec_avar k u v) m
  | trm_app f a    => trm_app (open_rec_avar k u f) (open_rec_avar k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  end
with open_rec_val (k: nat) (u: fvar) (v: val): val :=
  match v with
  | val_new T ds => val_new (open_rec_typ (S k) u T) (open_rec_defs (S k) u ds)
  | val_lambda T e => val_lambda (open_rec_typ k u T) (open_rec_trm (S k) u e)
  end
with open_rec_def (k: nat) (u: fvar) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end
with open_rec_defs (k: nat) (u: fvar) (ds: defs): defs :=
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

Definition var_of (v: fvar): var :=
  match v with
  | in_sto x => x
  | in_ctx x => x
  end.

Definition fv_fvar (v: fvar) : vars := \{var_of v}.

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f v => fv_fvar v
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
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
  | trm_var a       => (fv_avar a)
  | trm_val v        => (fv_val v)
  | trm_sel x m      => (fv_avar x)
  | trm_app f a      => (fv_avar f) \u (fv_avar a)
  | trm_let t1 t2    => (fv_trm t1) \u (fv_trm t2)
  end
with fv_val (v: val) : vars :=
  match v with
  | val_new T ds    => (fv_typ T) \u (fv_defs ds)
  | val_lambda T e  => (fv_typ T) \u (fv_trm e)
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
Definition fv_sto_vals(s: sto): vars := (fv_in_values (fun T => fv_val T) s).

(* ###################################################################### *)
(** ** Operational Semantics *)

Inductive red : trm -> sto -> trm -> sto -> Prop :=
| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs (in_sto x) ds) (def_trm m t) ->
    red (trm_sel (avar_s x) m) s t s
| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    red (trm_app (avar_s f) (avar_s a)) s (open_trm (in_sto a) t) s
| red_let : forall v t s x,
    x # s ->
    red (trm_let (trm_val v) t) s (open_trm (in_sto x) t) (s & x ~ v)
| red_let_var : forall t s x,
    red (trm_let (trm_var (avar_s x)) t) s (open_trm (in_sto x) t) s
| red_let_tgt : forall t0 t s t0' s',
    red t0 s t0' s' ->
    red (trm_let t0 t) s (trm_let t0' t) s'.

(* ###################################################################### *)
(** ** Typing *)

Inductive tymode: Set := ty_precise | ty_general.

Inductive restricted_by : var -> ctx -> ctx -> Prop :=
| lim_ctx : forall x T G G1 G2,
              G = G1 & (x ~ T) & G2 ->
              restricted_by x G (G1 & (x ~ T)).

Inductive ty_trm : tymode -> ctx -> ctx -> trm -> typ -> Prop :=
| ty_var_s : forall m Gs G x T,
    binds x T Gs ->
    ty_trm m Gs G (trm_var (avar_s x)) T
| ty_var_c : forall m Gs G x T,
    binds x T G ->
    ty_trm m Gs G (trm_var (avar_c x)) T
| ty_all_intro : forall L m Gs G T t U,
    (forall x, x \notin L ->
      ty_trm ty_general Gs (G & x ~ T) (open_trm (in_ctx x) t) (open_typ (in_ctx x) U)) ->
    ty_trm m Gs G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall Gs G x z S T,
    ty_trm ty_general Gs G (trm_var (avar_f x)) (typ_all S T) ->
    ty_trm ty_general Gs G (trm_var (avar_f z)) S ->
    ty_trm ty_general Gs G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro : forall L m Gs G T ds,
    (forall x, x \notin L ->
      ty_defs Gs (G & (x ~ open_typ (in_ctx x) T)) (open_defs (in_ctx x) ds) (open_typ (in_ctx x) T)) ->
    ty_trm m Gs G (trm_val (val_new T ds)) (typ_bnd T)
| ty_new_elim : forall Gs G x m T,
    ty_trm ty_general Gs G (trm_var (avar_f x)) (typ_rcd (dec_trm m T)) ->
    ty_trm ty_general Gs G (trm_sel (avar_f x) m) T
| ty_let : forall L Gs G t u T U,
    ty_trm ty_general Gs G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general Gs (G & x ~ T) (open_trm (in_ctx x) u) U) ->
    ty_trm ty_general Gs G (trm_let t u) U
| ty_rec_intro : forall Gs G x T,
    ty_trm ty_general Gs G (trm_var (avar_f x)) (open_typ x T) ->
    ty_trm ty_general Gs G (trm_var (avar_f x)) (typ_bnd T)
| ty_rec_elim : forall m Gs G x T,
    ty_trm m Gs G (trm_var (avar_f x)) (typ_bnd T) ->
    ty_trm m Gs G (trm_var (avar_f x)) (open_typ x T)
| ty_and_intro : forall Gs G x T U,
    ty_trm ty_general Gs G (trm_var (avar_f x)) T ->
    ty_trm ty_general Gs G (trm_var (avar_f x)) U ->
    ty_trm ty_general Gs G (trm_var (avar_f x)) (typ_and T U)
| ty_sub : forall m Gs G t T U,
    (m = ty_precise -> exists x, t = trm_var (avar_f x)) ->
    ty_trm m Gs G t T ->
    subtyp m Gs G T U ->
    ty_trm m Gs G t U
with ty_def : ctx -> ctx -> def -> dec -> Prop :=
| ty_def_typ : forall Gs G A T,
    ty_def Gs G (def_typ A T) (dec_typ A T T)
| ty_def_trm : forall Gs G a t T,
    ty_trm ty_general Gs G t T ->
    ty_def Gs G (def_trm a t) (dec_trm a T)
with ty_defs : ctx -> ctx -> defs -> typ -> Prop :=
| ty_defs_one : forall Gs G d D,
    ty_def Gs G d D ->
    ty_defs Gs G (defs_cons defs_nil d) (typ_rcd D)
| ty_defs_cons : forall Gs G ds d T D,
    ty_defs Gs G ds T ->
    ty_def Gs G d D ->
    defs_hasnt ds (label_of_def d) ->
    ty_defs Gs G (defs_cons ds d) (typ_and T (typ_rcd D))

with subtyp : tymode -> ctx -> ctx -> typ -> typ -> Prop :=
| subtyp_top: forall Gs G T,
    subtyp ty_general Gs G T typ_top
| subtyp_bot: forall Gs G T,
    subtyp ty_general Gs G typ_bot T
| subtyp_refl: forall Gs G T,
    subtyp ty_general Gs G T T
| subtyp_trans: forall m Gs G S T U,
    subtyp m Gs G S T ->
    subtyp m Gs G T U ->
    subtyp m Gs G S U
| subtyp_and11: forall m Gs G T U,
    subtyp m Gs G (typ_and T U) T
| subtyp_and12: forall m Gs G T U,
    subtyp m Gs G (typ_and T U) U
| subtyp_and2: forall Gs G S T U,
    subtyp ty_general Gs G S T ->
    subtyp ty_general Gs G S U ->
    subtyp ty_general Gs G S (typ_and T U)
| subtyp_fld: forall Gs G a T U,
    subtyp ty_general Gs G T U ->
    subtyp ty_general Gs G (typ_rcd (dec_trm a T)) (typ_rcd (dec_trm a U))
| subtyp_typ: forall Gs G A S1 T1 S2 T2,
    subtyp ty_general Gs G S2 S1 ->
    subtyp ty_general Gs G T1 T2 ->
    subtyp ty_general Gs G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2: forall Gs G G' x A S T,
    restricted_by x G G' ->
    ty_trm ty_general Gs G' (trm_var (avar_c x)) (typ_rcd (dec_typ A S T)) ->
    subtyp ty_general Gs G S (typ_sel (avar_c x) A)
| subtyp_sel1: forall Gs G G' x A S T,
    restricted_by x G G' ->
    ty_trm ty_general Gs G' (trm_var (avar_c x)) (typ_rcd (dec_typ A S T)) ->
    subtyp ty_general Gs G (typ_sel (avar_c x) A) T
| subtyp_sel2_tight: forall Gs G x A T,
    ty_trm ty_precise Gs empty (trm_var (avar_s x)) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general Gs G T (typ_sel (avar_s x) A)
| subtyp_sel1_tight: forall Gs G x A T,
    ty_trm ty_precise Gs empty (trm_var (avar_s x)) (typ_rcd (dec_typ A T T)) ->
    subtyp ty_general Gs G (typ_sel (avar_s x) A) T
| subtyp_all: forall L Gs G S1 T1 S2 T2,
    subtyp ty_general Gs G S2 S1 ->
    (forall x, x \notin L ->
       subtyp ty_general Gs (G & x ~ S2) (open_typ (in_ctx x) T1) (open_typ (in_ctx x) T2)) ->
    subtyp ty_general Gs G (typ_all S1 T1) (typ_all S2 T2)
| subtyp_bnd: forall L Gs G T1 T2,
    (forall x, x \notin L ->
       subtyp ty_general Gs (G & x ~ (typ_bnd T1)) (open_typ (in_ctx x) T1) (open_typ (in_ctx x) T2)) ->
    subtyp ty_general Gs G (typ_bnd T1) (typ_bnd T2).

Inductive wf_sto: ctx -> sto -> Prop :=
| wf_sto_empty: wf_sto empty empty
| wf_sto_push: forall G s x T v,
    wf_sto G s ->
    x # G ->
    x # s ->
    ty_trm ty_precise G empty (trm_val v) T ->
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
with   val_mut  := Induction for val Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, val_mut, def_mut, defs_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut.

Scheme ts_ty_trm_mut := Induction for ty_trm    Sort Prop
with   ts_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm    Sort Prop
with   rules_def_mut    := Induction for ty_def    Sort Prop
with   rules_defs_mut   := Induction for ty_defs   Sort Prop
with   rules_subtyp     := Induction for subtyp    Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_def_mut, rules_defs_mut, rules_subtyp.

(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sto       => dom x   \u (fv_sto_vals x)) in
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
(** ** Well-formed store *)
Lemma wf_sto_to_ok_s: forall s G,
  wf_sto G s -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto G s -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

(* ###################################################################### *)
(** ** Weakening *)

Lemma ok_restricted_by: forall x G G',
  ok G ->
  restricted_by x G G' ->
  ok G'.
Proof.
  introv Hok r. destruct r. subst.
  eauto.
Qed.

Lemma binds_exists: forall {V} x (T:V) G,
  binds x T G ->
  ok G ->
  exists G1 G2, G = G1 & (x ~ T) & G2.
Proof.
  introv Bi Hok. induction Hok.
  - false. eapply binds_empty_inv. eassumption.
  - apply binds_push_inv in Bi.
    destruct Bi as [[Heqx Heqv] | [Neqx Bi]].
    + subst. exists E. exists (@empty V). rewrite concat_empty_r. reflexivity.
    + specialize (IHHok Bi). destruct IHHok as [G1 [G2 EqE]].
      subst. exists G1. exists (G2 & x0 ~ v).
      rewrite concat_assoc. reflexivity.
Qed.

Lemma concat_ok_eq: forall {V} G1 G2 G1' G2' x (T:V) (T':V),
  G1 & x ~ T & G2 = G1' & x ~ T' & G2' ->
  ok (G1 & x ~ T & G2) ->
  G1 = G1' /\ G2 = G2' /\ T = T'.
Proof.
  introv Eq Hok.
  assert (ok G1) as Hok1. {
    apply ok_remove in Hok. eauto.
  }
  assert (ok G1') as Hok1'. {
    rewrite Eq in Hok. apply ok_remove in Hok. eauto.
  }
  assert (ok G2) as Hok2. {
    apply ok_remove in Hok. eauto.
  }
  assert (ok G2') as Hok2'. {
    rewrite Eq in Hok. apply ok_remove in Hok. eauto.
  }
  assert (ok (G1' & x ~ T' & G2')) as Hok'. {
    rewrite Eq in Hok. eauto.
  }
  generalize dependent G2'.
  generalize dependent G1'.
  induction Hok2; intros; inversion Hok2'; subst.
  - rewrite concat_empty_r in Eq. rewrite concat_empty_r in Eq.
    eapply eq_push_inv  in Eq. destruct Eq as [? [? Eq]]. eauto.
  - rewrite concat_empty_r in Eq. rewrite concat_assoc in Eq.
    eapply eq_push_inv in Eq. destruct Eq as [? [? Eq]]. subst.
    eapply ok_middle_inv in Hok'. destruct Hok' as [? Contra].
    eapply fresh_push_eq_inv in Contra. inversion Contra.
  - rewrite concat_empty_r in Eq. rewrite concat_assoc in Eq.
    eapply eq_push_inv in Eq. destruct Eq as [? [? Eq]]. subst.
    rewrite concat_empty_r in Hok'. eapply ok_remove in Hok'.
    assert (G1 & x ~ T & x ~ T' = G1 & x ~ T & (empty & x ~ T')) as A. {
      rewrite concat_empty_l. reflexivity.
    }
    rewrite A in Hok'. eapply ok_middle_inv in Hok'. destruct Hok' as [_ Contra].
    eapply fresh_push_eq_inv in Contra. inversion Contra.
  - rewrite concat_assoc in Eq. rewrite concat_assoc in Eq.
    eapply eq_push_inv in Eq. destruct Eq as [? [? Eq]]. subst.
    assert (G1 = G1' /\ E = E0 /\ T = T') as A. {
      eapply IHHok2; eauto.
      rewrite concat_assoc in Hok. eauto.
      rewrite concat_assoc in Hok'. eauto.
    }
    destruct A as [? [? ?]]. subst. split; eauto.
Qed.

Lemma weaken_restricted_by: forall x G' G1 G2 G3,
  restricted_by x (G1 & G3) G' ->
  ok (G1 & G2 & G3) ->                                 
  restricted_by x (G1 & G2 & G3) G' \/
  exists G3', G' = G1 & G3' /\ restricted_by x (G1 & G2 & G3) (G1 & G2 & G3').
Proof.
  introv r Hok. inversion r; subst.
  assert (ok (G1 & G3)) as Hok13 by eauto.
  destruct binds_concat_inv with (E1:=G1) (E2:=G3) (x:=x) (v:=T); eauto.
  rewrite H. apply binds_middle_eq.
  rewrite H in Hok13.
  apply ok_middle_inv in Hok13. destruct Hok13. assumption.
  right.
  assert (exists G3a G3b, G3 = G3a & (x ~ T) & G3b) as E3. {
    apply binds_exists; eauto.
  }
  destruct E3 as [G3a [G3b Eq3]]. subst.
  assert (G1 & G3a = G0 /\ G3b = G4 /\ T = T) as A. {
    eapply concat_ok_eq.
    repeat rewrite concat_assoc in H. eapply H.
    repeat rewrite concat_assoc in Hok13. eapply Hok13.
  }
  destruct A as [A1 [A2 ?]]. subst.
  exists (G3a & x ~ T). split. rewrite concat_assoc. reflexivity.
  repeat rewrite concat_assoc. apply lim_ctx with (G2:=G4). reflexivity.
  left. destruct H0 as [NoBi3 Bi1].
  assert (exists G1a G1b, G1 = G1a & (x ~ T) & G1b) as E1. {
    apply binds_exists; eauto.
  }
  destruct E1 as [G1a [G1b Eq1]]. subst.
  assert (G1a = G0 /\ G1b & G3 = G4 /\ T = T) as A. {
    eapply concat_ok_eq.
    repeat rewrite concat_assoc. eapply H.
    repeat rewrite concat_assoc. eapply Hok13.
  }
  destruct A as [A1 [A2 ?]]. subst.
  apply lim_ctx with (G2:=G1b & G2 & G3).
  repeat rewrite concat_assoc. reflexivity.
Qed.

Lemma weaken_rules:
  (forall m Gs G t T, ty_trm m Gs G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm m Gs (G1 & G2 & G3) t T) /\
  (forall Gs G d D, ty_def Gs G d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_def Gs (G1 & G2 & G3) d D) /\
  (forall Gs G ds T, ty_defs Gs G ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_defs Gs (G1 & G2 & G3) ds T) /\
  (forall m Gs G T U, subtyp m Gs G T U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp m Gs (G1 & G2 & G3) T U).
Proof.
  apply rules_mutind; try solve [eauto 4].
  + intros. subst.
    eapply ty_var_c. eapply binds_weaken; eauto.
  + intros. subst.
    apply_fresh ty_all_intro as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H.
    apply* H.
  + intros. subst.
    apply_fresh ty_new_intro as z; assert (zL: z \notin L) by auto.
    - specialize (H z zL G1 G2 (G3 & z ~ open_typ (in_ctx z) T)).
      repeat rewrite concat_assoc in H.
      apply* H.
  + intros. subst.
    apply_fresh ty_let as z. eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ T)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst.
    inversion r; subst.
    apply weaken_restricted_by with (G2:=G2) in r.
    destruct r.
    eapply subtyp_sel2. eassumption. eassumption.
    destruct H2 as [G3' [Heq r]].
    eapply subtyp_sel2. eapply r. eapply H. eapply Heq.
    rewrite Heq in H0. eapply ok_restricted_by; eauto.
    eauto.
  + intros. subst.
    inversion r; subst.
    apply weaken_restricted_by with (G2:=G2) in r.
    destruct r.
    eapply subtyp_sel1. eassumption. eassumption.
    destruct H2 as [G3' [Heq r]].
    eapply subtyp_sel1. eapply r. eapply H. eapply Heq.
    rewrite Heq in H0. eapply ok_restricted_by; eauto.
    eauto.
  + intros. subst.
    apply_fresh subtyp_all as z.
    eauto.
    eauto.
    assert (zL: z \notin L) by auto.
    specialize (H0 z zL G1 G2 (G3 & z ~ S2)).
    repeat rewrite concat_assoc in H0.
    apply* H0.
  + intros. subst.
    apply_fresh subtyp_bnd as z.
    assert (zL: z \notin L) by auto.
    specialize (H z zL G1 G2 (G3 & z ~ typ_bnd T1)).
    repeat rewrite concat_assoc in H.
    apply* H.
Qed.

Lemma weaken_ty_trm:  forall m Gs G1 G2 t T,
    ty_trm m Gs G1 t T ->
    ok (G1 & G2) ->
    ty_trm m Gs (G1 & G2) t T.
Proof.
  intros.
  assert (G1 & G2 = G1 & G2 & empty) as EqG. {
    rewrite concat_empty_r.
    reflexivity.
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

Lemma weaken_sto_rules:
  (forall m Gs G t T, ty_trm m Gs G t T -> forall Gs',
    ok (Gs & Gs') ->
    ty_trm m (Gs & Gs') G t T) /\
  (forall Gs G d D, ty_def Gs G d D -> forall Gs',
    ok (Gs & Gs') ->
    ty_def (Gs & Gs') G d D) /\
  (forall Gs G ds T, ty_defs Gs G ds T -> forall Gs',
    ok (Gs & Gs') ->
    ty_defs (Gs & Gs') G ds T) /\
  (forall m Gs G T U, subtyp m Gs G T U -> forall Gs',
    ok (Gs & Gs') ->
    subtyp m (Gs & Gs') G T U).
Proof.
  apply rules_mutind; eauto 4 using binds_concat_left_ok.
Qed.

Lemma weaken_sto_ty_trm:  forall m Gs Gs' G t T,
    ty_trm m Gs G t T ->
    ok (Gs & Gs') ->
    ty_trm m (Gs & Gs') G t T.
Proof.
  intros.
  apply* weaken_sto_rules.
Qed.

Lemma weaken_sto_subtyp:  forall m Gs Gs' G S U,
    subtyp m Gs G S U ->
    ok (Gs & Gs') ->
    subtyp m (Gs & Gs') G S U.
Proof.
  intros.
  apply* weaken_sto_rules.
Qed.

(* ###################################################################### *)

Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto G s ->
  binds x T G ->
  exists G1 G2 v, G = G1 & (x ~ T) & G2 /\ binds x v s /\ ty_trm ty_precise G1 empty (trm_val v) T.
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
  exists G1 G2 T, G = G1 & (x ~ T) & G2 /\ ty_trm ty_precise G1 empty (trm_val v) T.
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


Lemma typing_implies_ctx_bound: forall m Gs G x T,
  ty_trm m Gs G (trm_var (avar_c x)) T ->
  exists S, binds x S G.
Proof.
  intros. remember (trm_var (avar_c x)) as t.
  induction H;
    try solve [inversion Heqt];
    try solve [inversion Heqt; eapply IHty_trm; eauto];
    try solve [inversion Heqt; eapply IHty_trm1; eauto].
  - inversion Heqt. subst. exists T. assumption.
Qed.

Lemma typing_implies_sto_bound: forall m Gs G x T,
  ty_trm m Gs G (trm_var (avar_s x)) T ->
  exists T, binds x T Gs.
Proof.
  intros. remember (trm_var (avar_s x)) as t.
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
(** ** Extra Rec *)

(*
Lemma extra_bnd_rules:
  (forall m1 m2 G t T, ty_trm m1 m2 G t T -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    ty_trm m1 m2 G' t T)
/\ (forall G d D, ty_def G d D -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    ty_def G' d D)
/\ (forall G ds T, ty_defs G ds T -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    ty_defs G' ds T)
/\ (forall m1 m2 G J T U, subtyp m1 m2 G J T U -> forall G1 G2 x S G',
    G = G1 & (x ~ open_typ x S) & G2 ->
    G' = G1 & (x ~ typ_bnd S) & G2 ->
    subtyp m1 m2 G' J T U).
Proof.
  apply rules_mutind; intros; eauto.
  - (* ty_var *)
    subst. apply binds_middle_inv in b. destruct b as [Bi | [Bi | Bi]].
    + apply ty_var. eauto.
    + destruct Bi as [Bin [Eqx EqT ]]. subst.
      apply ty_rec_elim. apply ty_var. eauto.
    + destruct Bi as [Bin [Neqx Bi]]. apply ty_var. eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H y FrL).
    specialize (H G1 (G2 & y ~ T) x S).
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as y; eauto;
    assert (y \notin L) as FrL by eauto.
    specialize (H y FrL).
    specialize (H G1 (G2 & y ~ open_typ y T) x S).
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H0 y FrL).
    specialize (H0 G1 (G2 & y ~ T) x S).
    eapply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    assert (y \notin L) as FrL by eauto.
    specialize (H0 y FrL).
    specialize (H0 G1 (G2 & y ~ S2) x S).
    eapply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. reflexivity.
Qed.
 *)

(* ###################################################################### *)
(** ** Substitution *)

Definition subst_fvar (z: var) (u: fvar) (v: fvar) : fvar :=
  match v with
  | in_sto x => in_sto x
  | in_ctx x => (If x = z then u else in_ctx x)
  end.

Definition subst_avar (z: var) (u: fvar) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f v => avar_f (subst_fvar z u v)
  end.

Fixpoint subst_typ (z: var) (u: fvar) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_sel x L    => typ_sel (subst_avar z u x) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: fvar) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L U => dec_trm L (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: fvar) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_val v        => trm_val (subst_val z u v)
  | trm_sel x1 L     => trm_sel (subst_avar z u x1) L
  | trm_app x1 x2    => trm_app (subst_avar z u x1) (subst_avar z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  end
with subst_val (z: var) (u: fvar) (v: val) : val :=
  match v with
  | val_new T ds     => val_new (subst_typ z u T) (subst_defs z u ds)
  | val_lambda T t   => val_lambda (subst_typ z u T) (subst_trm z u t)
  end
with subst_def (z: var) (u: fvar) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
  | def_trm L t => def_trm L (subst_trm z u t)
  end
with subst_defs (z: var) (u: fvar) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

Definition subst_ctx (z: var) (u: fvar) (G: ctx) : ctx := map (subst_typ z u) G.
Definition subst_sto (z: var) (u: fvar) (s: sto) : sto := map (subst_val z u) s.

(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_fvar: forall x y,
  (forall v: fvar, x \notin fv_fvar v -> subst_fvar x y v = v).
Proof.
  intros. unfold fv_fvar in *. destruct* v. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. f_equal. apply* subst_fresh_fvar.
Qed.

Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_avar.
Qed.

Definition subst_fresh_typ x y := proj1 (subst_fresh_typ_dec x y).
Definition subst_fresh_dec x y := proj2 (subst_fresh_typ_dec x y).

Lemma subst_fresh_trm_val_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall v : val , x \notin fv_val  v  -> subst_val  x y v  = v ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec).
Qed.

Definition subst_fresh_trm  x y := proj41 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_val  x y := proj42 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_def  x y := proj43 (subst_fresh_trm_val_def_defs x y).
Definition subst_fresh_defs x y := proj44 (subst_fresh_trm_val_def_defs x y).

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
    rewrite ((proj1 (subst_fresh_typ_dec _ _)) _ N1).
    reflexivity.
Qed.

Lemma fv_ctx_types_binds: forall x z T G,
  x \notin fv_ctx_types G -> binds z T G ->
  x \notin fv_typ T.
Proof.
  intros.
  unfold fv_ctx_types in *.
  eapply fv_in_values_binds; eassumption.
Qed.

Lemma invert_fv_sto_vals_push: forall x z v s,
  x \notin fv_sto_vals (s & z ~ v) -> x \notin fv_val v /\ x \notin (fv_sto_vals s).
Proof.
  introv N.
  unfold fv_sto_vals in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

Lemma subst_fresh_sto: forall x y s,
  x \notin fv_sto_vals s -> subst_sto x y s = s.
Proof.
  intros x y.
  apply (env_ind (fun s => x \notin fv_sto_vals s -> subst_sto x y s = s)).
  + intro N. unfold subst_sto. apply map_empty.
  + intros G z T IH N.
    apply invert_fv_sto_vals_push in N. destruct N as [N1 N2].
    unfold subst_sto in *. rewrite map_push.
    rewrite (IH N2).
    rewrite subst_fresh_val.
    reflexivity.
    apply N1.
Qed.

Lemma fv_sto_vals_binds: forall x z v s,
  x \notin fv_sto_vals s -> binds z v s ->
  x \notin fv_val v.
Proof.
  intros.
  unfold fv_sto_vals in *.
  eapply fv_in_values_binds; eassumption.
Qed.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a)
    = open_rec_avar n (subst_fvar x y u) (subst_avar x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + reflexivity.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_avar.
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec.
Qed.

Lemma subst_open_commute_dec: forall x y u D,
  subst_dec x y (open_dec u D) = open_dec (subst_fvar x y u) (subst_dec x y D).
Proof.
  intros. apply* subst_open_commute_typ_dec.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_trm_val_def_defs: forall x y u,
  (forall t : trm, forall n: Datatypes.nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall v : val, forall n: Datatypes.nat,
     subst_val x y (open_rec_val n u v)
     = open_rec_val n (subst_fvar x y u) (subst_val x y v)) /\
  (forall d : def , forall n: Datatypes.nat,
     subst_def x y (open_rec_def n u d)
     = open_rec_def n (subst_fvar x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: Datatypes.nat,
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ_dec).
Qed.

Lemma subst_open_commute_trm: forall x y u t,
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

Lemma subst_open_commute_val: forall x y u v,
  subst_val x y (open_val u v) = open_val (subst_fvar x y u) (subst_val x y v).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

Lemma subst_open_commute_defs: forall x y u ds,
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commute_trm_val_def_defs.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm (in_ctx x) t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh_trm_val_def_defs x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_val: forall x u v, x \notin (fv_val v) ->
  open_val u v = subst_val x u (open_val (in_ctx x) v).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_val.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [Q _]]. rewrite* (Q v).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs (in_ctx x) ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_defs.
  destruct (@subst_fresh_trm_val_def_defs x u) as [_ [_ [_ Q]]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ (in_ctx x) T).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commute_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_dec: forall x u D, x \notin (fv_dec D) ->
  open_dec u D = subst_dec x u (open_dec (in_ctx x) D).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_dec.
  destruct (@subst_fresh_typ_dec x u) as [_ Q]. rewrite* (Q D).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_undo_fvar: forall x y,
  (forall v, y \notin fv_fvar v -> (subst_fvar y (in_ctx x) (subst_fvar x (in_ctx y) v)) = v).
Proof.
  intros. unfold subst_fvar, subst_fvar; destruct v.
  + reflexivity.
  + unfold fv_fvar in H. assert (y <> v) by auto. repeat case_if; reflexivity.
Qed.

Lemma subst_undo_avar: forall x y,
  (forall a, y \notin fv_avar a -> (subst_avar y (in_ctx x) (subst_avar x (in_ctx y) a)) = a).
Proof.
  intros. unfold subst_avar; destruct a.
  + reflexivity.
  + f_equal. apply* subst_undo_fvar.
Qed.

Lemma subst_undo_typ_dec: forall x y,
   (forall T , y \notin fv_typ  T  -> (subst_typ y (in_ctx x) (subst_typ  x (in_ctx y) T )) = T )
/\ (forall D , y \notin fv_dec  D  -> (subst_dec y (in_ctx x) (subst_dec  x (in_ctx y) D )) = D ).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*.
  apply* subst_undo_avar.
Qed.

Lemma subst_undo_trm_val_def_defs: forall x y,
   (forall t , y \notin fv_trm  t  -> (subst_trm  y (in_ctx x) (subst_trm  x (in_ctx y) t )) = t )
/\ (forall v , y \notin fv_val  v  -> (subst_val  y (in_ctx x) (subst_val  x (in_ctx y) v )) = v )
/\ (forall d , y \notin fv_def  d  -> (subst_def  y (in_ctx x) (subst_def  x (in_ctx y) d )) = d )
/\ (forall ds, y \notin fv_defs ds -> (subst_defs y (in_ctx x) (subst_defs x (in_ctx y) ds)) = ds).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_val, fv_def, fv_defs in *; f_equal*;
    (apply* subst_undo_avar || apply* subst_undo_typ_dec).
Qed.

Lemma subst_typ_undo: forall x y T,
  y \notin fv_typ T -> (subst_typ y (in_ctx x) (subst_typ x (in_ctx y) T)) = T.
Proof.
  apply* subst_undo_typ_dec.
Qed.

Lemma subst_trm_undo: forall x y t,
  y \notin fv_trm t -> (subst_trm y (in_ctx x) (subst_trm x (in_ctx y) t)) = t.
Proof.
  apply* subst_undo_trm_val_def_defs.
Qed.

Lemma subst_idempotent_fvar: forall x y,
  (forall v, (subst_fvar x y (subst_fvar x y v)) = (subst_fvar x y v)).
Proof.
  intros. unfold subst_fvar; destruct v.
  + reflexivity.
  + case_if; eauto; destruct y; eauto; case_if; eauto.
Qed.

Lemma subst_idempotent_avar: forall x y,
  (forall a, (subst_avar x y (subst_avar x y a)) = (subst_avar x y a)).
Proof.
  intros. unfold subst_avar; destruct a.
  + reflexivity.
  + f_equal. apply* subst_idempotent_fvar.
Qed.

Lemma subst_idempotent_typ_dec: forall x y,
   (forall T, subst_typ x y (subst_typ x y T) = subst_typ x y T)
/\ (forall D, subst_dec x y (subst_dec x y D) = subst_dec x y D).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*.
  apply* subst_idempotent_avar.
Qed.

Lemma subst_idempotent_trm_val_def_defs: forall x y,
   (forall t , subst_trm  x y (subst_trm  x y t ) = (subst_trm  x y t ))
/\ (forall v , subst_val  x y (subst_val  x y v ) = (subst_val  x y v ))
/\ (forall d , subst_def  x y (subst_def  x y d ) = (subst_def  x y d ))
/\ (forall ds, subst_defs x y (subst_defs x y ds) = (subst_defs x y ds)).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_val, fv_def, fv_defs in *; f_equal*;
    (apply* subst_idempotent_avar || apply* subst_idempotent_typ_dec).
Qed.

Lemma subst_typ_idempotent: forall x y T,
  subst_typ x y (subst_typ x y T) = subst_typ x y T.
Proof.
  apply* subst_idempotent_typ_dec.
Qed.

Lemma subst_trm_idempotent: forall x y t,
  subst_trm x y (subst_trm x y t) = subst_trm x y t.
Proof.
  apply* subst_idempotent_trm_val_def_defs.
Qed.

Lemma subst_label_of_dec: forall x y D,
  label_of_dec D = label_of_dec (subst_dec x y D).
Proof.
  intros. destruct D; simpl; reflexivity.
Qed.

Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct d; simpl; reflexivity.
Qed.

Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - simpl. reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if. apply (IHds Eq).
Qed.

(* ###################################################################### *)
(** ** Some Lemmas *)

Lemma corresponding_types: forall Gs s x T,
  wf_sto Gs s ->
  binds x T Gs ->
  ((exists S U t, binds x (val_lambda S t) s /\
                  ty_trm ty_precise Gs empty (trm_val (val_lambda S t)) (typ_all S U) /\
                  T = typ_all S U) \/
   (exists S ds, binds x (val_new S ds) s /\
                 ty_trm ty_precise Gs empty (trm_val (val_new S ds)) (typ_bnd S) /\
                 T = typ_bnd S)).
Proof.
  introv H Bi. induction H.
  - false* binds_empty_inv.
  - unfolds binds. rewrite get_push in *. case_if.
    + inversions Bi. inversion H2; subst.
      * left. exists T0. exists U. exists t.
        split. auto. split.
        eapply weaken_sto_ty_trm. assumption.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        reflexivity.
      * right. exists T0. exists ds.
        split. auto. split.
        eapply weaken_sto_ty_trm. assumption.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
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
        eapply weaken_sto_ty_trm. assumption.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
      * destruct IH as [S [ds [IH1 [IH2 IH3]]]].
        right. exists S. exists ds.
        split. assumption. split.
        eapply weaken_sto_ty_trm. assumption.
        apply ok_push. eapply wf_sto_to_ok_G. eassumption. assumption.
        assumption.
Qed.

Lemma unique_rec_subtyping: forall Gs G S T,
  subtyp ty_precise Gs G (typ_bnd S) T ->
  T = typ_bnd S.
Proof.
  introv Hsub.
  remember (typ_bnd S) as T'.
  remember ty_precise as m.
  induction Hsub; try solve [inversion Heqm].
  - specialize (IHHsub1 HeqT' Heqm). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_all_subtyping: forall G Gs S U T,
  subtyp ty_precise G Gs (typ_all S U) T ->
  T = typ_all S U.
Proof.
  introv Hsub.
  remember (typ_all S U) as T'.
  remember ty_precise as m.
  induction Hsub; try solve [inversion Heqm].
  - specialize (IHHsub1 HeqT' Heqm). subst.
    apply IHHsub2; reflexivity.
  - inversion HeqT'.
  - inversion HeqT'.
Qed.

Lemma unique_lambda_typing: forall G Gs x S U T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise G Gs (trm_var (avar_s x)) T ->
  T = typ_all S U.
Proof.
  introv Bi Hty.
  remember (trm_var (avar_s x)) as t.
  remember ty_precise as m.
  induction Hty; try solve [inversion Heqt; inversion Heqm].
  - inversions Heqt.
    unfold binds in Bi. unfold binds in H.
    rewrite H in Bi. inversion Bi.
    reflexivity.
  - specialize (IHHty Bi Heqt Heqm).
    inversion IHHty.
  - specialize (IHHty Bi Heqt Heqm).
    rewrite IHHty in H0. rewrite Heqm in H0.
    apply unique_all_subtyping in H0.
    apply H0.
Qed.

Lemma lambda_not_rcd: forall G Gs x S U A T,
  binds x (typ_all S U) G ->
  ty_trm ty_precise G Gs (trm_var (avar_s x)) (typ_rcd (dec_typ A T T)) ->
  False.
Proof.
  introv Bi Hty.
  assert (typ_rcd (dec_typ A T T) = typ_all S U) as Contra. {
    eapply unique_lambda_typing; eassumption.
  }
  inversion Contra.
Qed.

Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T)
.

Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of_dec D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of_dec D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l})
.

Definition record_type T := exists ls, record_typ T ls.

Lemma open_dec_preserves_label: forall D x i,
  label_of_dec D = label_of_dec (open_rec_dec i x D).
Proof.
  intros. induction D; simpl; reflexivity.
Qed.

Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open_dec x D).
Proof.
  intros. inversion H; unfold open_dec; simpl; constructor.
Qed.

Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open_typ x T) ls.
Proof.
  intros. induction H.
  - unfold open_typ. simpl.
    apply rt_one.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
  - unfold open_typ. simpl.
    apply rt_cons; try assumption.
    apply open_record_dec. assumption.
    rewrite <- open_dec_preserves_label. assumption.
Qed.

Lemma open_eq_avar: forall v x i a1 a2,
  x = var_of v ->
  x \notin fv_avar a1 -> x \notin fv_avar a2 ->
  open_rec_avar i v a1 = open_rec_avar i v a2 ->
  a1 = a2.
Proof.
  introv Eq Fr1 Fr2 H. induction a1; induction a2; simpl in H; inversion H.
  - case_if; case_if.
    + reflexivity.
    + inversion H. subst. reflexivity.
  - case_if.
    inversion H. subst. false.
    apply notin_same in Fr2. assumption.
  - case_if.
    inversion H. subst. false.
    apply notin_same in Fr1. assumption.
  - subst. reflexivity.
Qed.

Lemma open_eq_typ_dec: forall v x,
  x = var_of v ->
  (forall T1, x \notin fv_typ T1 ->
   forall T2, x \notin fv_typ T2 ->
   forall i, open_rec_typ i v T1 = open_rec_typ i v T2 ->
   T1 = T2) /\
  (forall D1, x \notin fv_dec D1 ->
   forall D2, x \notin fv_dec D2 ->
   forall i, open_rec_dec i v D1 = open_rec_dec i v D2 ->
   D1 = D2).
Proof.
  introv Eq. apply typ_mutind; intros.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H1. induction T2; simpl in H1; inversion H1.
    reflexivity.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal. eapply H; eauto.
  - simpl in H3; induction T2; simpl in H3; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H1; induction T2; simpl in H1; inversion H1.
    f_equal. eapply open_eq_avar; eauto.
  - simpl in H2. induction T2; simpl in H2; inversion H2.
    f_equal.
    eapply H; eauto.
  - simpl in H3. induction T2; simpl in H3; inversion H3.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H3. induction D2; simpl in H3; inversion H3.
    subst.
    f_equal.
    eapply H; eauto using notin_union_r1.
    eapply H0; eauto using notin_union_r2.
  - simpl in H2. induction D2; simpl in H2; inversion H2.
    subst.
    f_equal.
    eapply H; eauto.
Qed.

Lemma open_eq_typ: forall v x i T1 T2,
  x = var_of v ->
  x \notin fv_typ T1 -> x \notin fv_typ T2 ->
  open_rec_typ i v T1 = open_rec_typ i v T2 ->
  T1 = T2.
Proof.
  introv Eq Fr1 Fr2 Heq.
  destruct (open_eq_typ_dec v Eq) as [HT HD].
  eapply HT; eauto.
Qed.

Lemma open_record_dec_rev: forall v D,
  (var_of v) \notin fv_dec D ->
  record_dec (open_dec v D) -> record_dec D.
Proof.
  introv Fr H. remember (open_dec v D) as DX.
  generalize dependent D.
  inversion H; intros.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    assert (t0 = t1) as Heq. {
      eapply open_eq_typ; eauto using notin_union_r1, notin_union_r2.
    }
    subst. constructor.
  - destruct D; unfold open_dec in HeqDX; simpl in HeqDX; inversion HeqDX.
    subst. constructor.
Qed.

Lemma open_record_typ_rev: forall v T ls,
   (var_of v) \notin fv_typ T ->
  record_typ (open_typ v T) ls -> record_typ T ls.
Proof.
  introv Fr H. remember (open_typ v T) as TX.
  generalize dependent T.
  induction H; intros.
  - destruct T; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_one; eauto.
    eapply open_record_dec_rev; eauto.
  - destruct T0; unfold open_typ in HeqTX; simpl in HeqTX; inversion HeqTX.
    subst.
    destruct T0_2; unfold open_typ in H5; simpl in H5; inversion H5.
    subst.
    rewrite <- open_dec_preserves_label.
    apply rt_cons; try assumption.
    eapply IHrecord_typ; eauto using notin_union_r1.
    eapply open_record_dec_rev; eauto using notin_union_r2.
    eauto.
    rewrite <- open_dec_preserves_label in H2. apply H2.
Qed.

Lemma open_record_type: forall v T,
  record_type T -> record_type (open_typ v T).
Proof.
  intros. destruct H as [ls H]. exists ls. eapply open_record_typ.
  eassumption.
Qed.

Lemma open_record_type_rev: forall v T,
  (var_of v) \notin fv_typ T ->
  record_type (open_typ v T) -> record_type T.
Proof.
  introv Fr H. destruct H as [ls H]. exists ls. eapply open_record_typ_rev; eauto.
Qed.

Lemma label_same_typing: forall s G d D,
  ty_def s G d D -> label_of_def d = label_of_dec D.
Proof.
  intros. inversion H; subst; simpl; reflexivity.
Qed.

Lemma record_defs_typing_rec: forall s G ds S,
  ty_defs s G ds S ->
  exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l.
Proof.
  intros. induction H.
  - eexists. split.
    apply rt_one.
    inversion H; subst; constructor.
    reflexivity.
    apply label_same_typing in H. rewrite <- H.
    intros. split; intro A.
    + unfold defs_hasnt. simpl.
      apply notin_singleton in A.
      rewrite If_r. reflexivity. eauto.
    + unfold defs_hasnt in A. unfold get_def in A.
      case_if. apply notin_singleton. eauto.
  - destruct IHty_defs as [ls [IH1 IH2]].
    eexists. split.
    apply rt_cons; try eassumption.
    inversion H0; subst; constructor.
    reflexivity.
    apply label_same_typing in H0. rewrite <- H0.
    specialize (IH2 (label_of_def d)).
    destruct IH2 as [IH2A IH2B].
    apply IH2B. assumption.
    intros. split; intro A.
    + specialize (IH2 l).
      destruct IH2 as [IH2A IH2B].
      unfold defs_hasnt. simpl.
      rewrite If_r. unfold defs_hasnt in IH2A. apply IH2A.
      apply notin_union in A. destruct A as [A1 A2]. assumption.
      apply notin_union in A. destruct A as [A1 A2]. apply notin_singleton in A2.
      apply label_same_typing in H0. rewrite <- H0 in A2. eauto.
    + apply notin_union. split.
      * specialize (IH2 l).
        destruct IH2 as [IH2A IH2B].
        apply IH2B. inversion A.
        case_if. unfold defs_hasnt. assumption.
      * apply label_same_typing in H0. rewrite <- H0.
        unfold defs_hasnt in A. unfold get_def in A.
        case_if in A.
        apply notin_singleton. eauto.
Qed.

Lemma record_defs_typing: forall s G ds S,
  ty_defs s G ds S ->
  record_type S.
Proof.
  intros.
  assert (exists ls, record_typ S ls /\ forall l, l \notin ls <-> defs_hasnt ds l) as A.
  eapply record_defs_typing_rec; eauto.
  destruct A as [ls [A1 A2]].
  exists ls. apply A1.
Qed.

Lemma record_new_typing: forall s G S ds,
  ty_trm ty_precise s G (trm_val (val_new S ds)) (typ_bnd S) ->
  record_type S.
Proof.
  intros.
  inversion H; subst.
  + pick_fresh x.
    apply open_record_type_rev with (v:= in_ctx x).
    unfold var_of. eauto.
    eapply record_defs_typing. eapply H4. eauto.
  + assert (exists x, trm_val (val_new S ds) = trm_var (avar_f x)) as Contra. {
      apply H0; eauto.
    }
    destruct Contra as [? Contra]. inversion Contra.
Qed.

Inductive record_sub : typ -> typ -> Prop :=
| rs_refl: forall T,
  record_sub T T
| rs_dropl: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_rcd D)
| rs_drop: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) T'
| rs_pick: forall T T' D,
  record_sub T T' ->
  record_sub (typ_and T (typ_rcd D)) (typ_and T' (typ_rcd D))
.

Lemma record_typ_sub_closed : forall T T' ls,
  record_sub T T' ->
  record_typ T ls ->
  exists ls', record_typ T' ls' /\ subset ls' ls.
Proof.
  introv Hsub Htyp. generalize dependent ls.
  induction Hsub; intros.
  - exists ls. split. assumption. apply subset_refl.
  - inversion Htyp; subst.
    eexists. split.
    eapply rt_one. assumption. reflexivity.
    rewrite <- union_empty_l with (E:=\{ label_of_dec D}) at 1.
    apply subset_union_2. apply subset_empty_l. apply subset_refl.
  - inversion Htyp; subst.
    specialize (IHHsub ls0 H1). destruct IHHsub as [ls' [IH1 IH2]].
    exists ls'. split. assumption.
    rewrite <- union_empty_r with (E:=ls').
    apply subset_union_2. assumption. apply subset_empty_l.
  - inversion Htyp; subst.
    specialize (IHHsub ls0 H1). destruct IHHsub as [ls0' [IH1 IH2]].
    exists (ls0' \u \{ label_of_dec D }). split.
    apply rt_cons; eauto.
    unfold "\c" in IH2. unfold "\notin". intro I.
    specialize (IH2 (label_of_dec D) I). eauto.
    apply subset_union_2. assumption. apply subset_refl.
Qed.

Lemma record_type_sub_closed : forall T T',
  record_sub T T' ->
  record_type T ->
  record_type T'.
Proof.
  introv Hsub Htype. destruct Htype as [ls Htyp].
  apply record_typ_sub_closed with (ls:=ls) in Hsub; try assumption.
  destruct Hsub as [ls' [Htyp' ?]].
  exists ls'. apply Htyp'.
Qed.

Lemma record_sub_trans: forall T1 T2 T3,
  record_sub T1 T2 ->
  record_sub T2 T3 ->
  record_sub T1 T3.
Proof.
  introv H12 H23. generalize dependent T3.
  induction H12; intros.
  - assumption.
  - inversion H23; subst. eapply rs_dropl. eassumption.
  - apply rs_drop. apply IHrecord_sub. assumption.
  - inversion H23; subst.
    + apply rs_pick. assumption.
    + eapply rs_dropl. eassumption.
    + apply rs_drop. apply IHrecord_sub. assumption.
    + apply rs_pick. apply IHrecord_sub. assumption.
Qed.

Lemma record_subtyping: forall s G T T',
  subtyp ty_precise s G T T' ->
  record_type T ->
  record_sub T T'.
Proof.
  introv Hsub Hr. generalize dependent Hr. dependent induction Hsub.
  - intros HS.
    apply record_sub_trans with (T2:=T).
    apply IHHsub1. apply HS.
    apply IHHsub2.
    eapply record_type_sub_closed. apply IHHsub1. apply HS. apply HS.
  - intros Htype. destruct Htype as [ls Htyp].
    inversion Htyp; subst.
    apply rs_drop. apply rs_refl.
  - intros Htype. destruct Htype as [ls Htyp].
    inversion Htyp; subst.
    eapply rs_dropl. apply rs_refl.
Qed.

Lemma record_typ_sub_label_in: forall T D ls,
  record_typ T ls ->
  record_sub T (typ_rcd D) ->
  label_of_dec D \in ls.
Proof.
  introv Htyp Hsub. generalize dependent D. induction Htyp; intros.
  - inversion Hsub. subst. apply in_singleton_self.
  - inversion Hsub; subst.
    + rewrite in_union. right. apply in_singleton_self.
    + rewrite in_union. left. apply IHHtyp. assumption.
Qed.

Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_sub T (typ_rcd (dec_typ A T1 T1)) ->
  record_sub T (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Htype Hsub1 Hsub2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Hsub1; inversion Hsub2; subst.
  - inversion H5. subst. reflexivity.
  - inversion H9. subst. reflexivity.
  - apply record_typ_sub_label_in with (D:=dec_typ A T2 T2) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - apply record_typ_sub_label_in with (D:=dec_typ A T1 T1) in Htyp.
    simpl in Htyp. simpl in H1. unfold "\notin" in H1. unfold not in H1.
    specialize (H1 Htyp). inversion H1.
    assumption.
  - eapply IHHtyp; eassumption.
Qed.

Lemma record_type_sub_not_rec: forall S T v,
  record_sub (open_typ v S) (typ_bnd T) ->
  record_type S ->
  False.
Proof.
  introv Hsub Htype. remember (open_typ v S) as Sx.
  apply open_record_type with (v:=v) in Htype.
  rewrite <- HeqSx in Htype. clear HeqSx.
  destruct Htype as [ls Htyp]. induction Htyp.
  - inversion Hsub.
  - inversion Hsub; subst. apply IHHtyp. assumption.
Qed.

Lemma shape_new_typing: forall Gs G x S T,
  binds x (typ_bnd S) Gs ->
  record_type S ->
  ty_trm ty_precise Gs G (trm_var (avar_s x)) T ->
  T = typ_bnd S \/ record_sub (open_typ (in_sto x) S) T.
Proof.
  introv Bi HS Hx. dependent induction Hx.
  - unfold binds in H. unfold binds in Bi. rewrite H in Bi. inversion Bi.
    left. reflexivity.
  - assert (typ_bnd T = typ_bnd S \/ record_sub (open_typ (in_sto x) S) (typ_bnd T)) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + inversion A. right. apply rs_refl.
    + apply record_type_sub_not_rec in A. inversion A. assumption.
  - assert (T = typ_bnd S \/ record_sub (open_typ (in_sto x) S) T) as A. {
      eapply IHHx; eauto.
    }
    destruct A as [A | A].
    + subst. apply unique_rec_subtyping in H0. left. assumption.
    + right. eapply record_sub_trans. eassumption.
      eapply record_subtyping. eassumption.
      eapply record_type_sub_closed. eassumption.
      eapply open_record_type. assumption.
Qed.

Lemma unique_tight_bounds: forall Gs s x T1 T2 A,
  wf_sto Gs s ->
  ty_trm ty_precise Gs empty (trm_var (avar_s x)) (typ_rcd (dec_typ A T1 T1)) ->
  ty_trm ty_precise Gs empty (trm_var (avar_s x)) (typ_rcd (dec_typ A T2 T2)) ->
  T1 = T2.
Proof.
  introv Hwf Hty1 Hty2.
  assert (exists T, binds x T Gs) as Bi. {
    eapply typing_implies_sto_bound. eassumption.
  }
  destruct Bi as [T Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis [Ht EqT]]]]].
    false.
    eapply lambda_not_rcd.
    subst. eassumption. eassumption.
  - destruct H as [S [ds [Bis [Ht EqT]]]]. subst.
    assert (record_type S) as Htype. {
      eapply record_new_typing. eassumption.
    }
    destruct (shape_new_typing Bi Htype Hty1) as [Contra1 | A1].
    inversion Contra1.
    destruct (shape_new_typing Bi Htype Hty2) as [Contra2 | A2].
    inversion Contra2.
    assert (record_type (open_typ (in_sto x) S)) as HXtype. {
      apply open_record_type. assumption.
    }
    eapply unique_rcd_typ.
    apply HXtype.
    eassumption.
    eassumption.
Qed.

Lemma precise_to_general:
  (forall m Gs G t T,
     ty_trm m Gs G t T ->
     m = ty_precise ->
     ty_trm ty_general Gs G t T) /\
  (forall m Gs G S U,
     subtyp m Gs G S U ->
     m = ty_precise ->
     subtyp ty_general Gs G S U).
Proof.
  apply ts_mutind; intros; subst; eauto.
Qed.

Lemma precise_to_general_typing: forall Gs G t T,
  ty_trm ty_precise Gs G t T ->
  ty_trm ty_general Gs G t T.
Proof.
  intros. apply* precise_to_general.
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

Lemma record_type_new: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  record_type (open_typ (in_sto x) T).
Proof.
  introv Hwf Bis.
  destruct (sto_binds_to_ctx_binds Hwf Bis) as [S Bi].
  destruct (corresponding_types Hwf Bi) as [Hlambda | Hnew].
  destruct Hlambda as [? [? [? [Bis' ?]]]].
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  destruct Hnew as [? [? [Bis' [? ?]]]]. subst.
  unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
  apply record_new_typing in H.
  apply open_record_type. assumption.
Qed.

(* ###################################################################### *)
(** ** Narrowing *)

Inductive subenv(Gs: ctx): ctx -> ctx -> Prop :=
| se_refl: forall G, subenv Gs G G
| se_push: forall G1 G2 T1 T2 x,
  subenv Gs G1 G2 ->
  subtyp ty_general Gs (G1 & (x ~ T1)) T1 T2 ->
  subenv Gs (G1 & (x ~ T1)) (G2 & (x ~ T2)).

Lemma subenv_last: forall Gs G x S U,
  subtyp ty_general Gs G S U ->
  ok (G & x ~ S) ->
  subenv Gs (G & x ~ S) (G & x ~ U).
Proof.
  intros.
  eapply se_push.
  eapply se_refl.
  apply weaken_subtyp; eauto.
Qed.

Lemma subenv_last_only: forall Gs x S U,
  subtyp ty_general Gs empty S U ->
  subenv Gs (x ~ S) (x ~ U).
Proof.
  intros.
  assert ((@empty typ) & (x ~ S) = (x ~ S)) as A. {
    rewrite concat_empty_l. reflexivity.
  }
  assert ((@empty typ) & (x ~ U) = (x ~ U)) as B. {
    rewrite concat_empty_l. reflexivity.
  }
  rewrite <- A. rewrite <- B.
  eapply subenv_last; eauto.
Qed.

Lemma restricted_by_skip: forall x y T G G',
  ok (G & y ~ T) ->
  x <> y ->
  restricted_by x (G & y ~ T) G' ->
  restricted_by x G G'.
Proof.
  admit.
Qed.

Lemma narrow_restricted_by: forall Gs G0 G,
  ok G ->
  subenv Gs G0 G -> forall x G',
  restricted_by x G G' ->
  exists G0', subenv Gs G0' G' /\ restricted_by x G G'.
Proof.
  introv Hok SE.
  dependent induction SE; intros.
  - exists G'. split. apply se_refl. assumption.
  - destruct (classicT (x0 = x)) as [Eq | Ne].
    + subst. inversion H0; subst.
      assert (G2 = G0 /\ empty = G3 /\ T2 = T) as A. {
        eapply concat_ok_eq.
        rewrite concat_empty_r. eapply H1.
        rewrite concat_empty_r.
        eauto.
      }
      destruct A as [? [? ?]]. subst.
      exists (G1 & x ~ T1). split; eauto.
      eapply se_push; eauto.
    + assert (exists G0', subenv Gs G0' G' /\ restricted_by x0 G2 G') as A. {
        eapply IHSE; eauto.
        eapply restricted_by_skip; eauto.
      }
      destruct A as [G0' [A1 A2]].
      exists G0'. split; eauto.
Qed.

Lemma narrow_rules:
  (forall m Gs G t T, ty_trm m Gs G t T -> forall G',
    m = ty_general ->
    ok G' ->
    subenv Gs G' G ->
    ty_trm m Gs G' t T)
/\ (forall Gs G d D, ty_def Gs G d D -> forall G',
    ok G' ->
    subenv Gs G' G ->
    ty_def Gs G' d D)
/\ (forall Gs G ds T, ty_defs Gs G ds T -> forall G',
    ok G' ->
    subenv Gs G' G ->
    ty_defs Gs G' ds T)
/\ (forall m Gs G S U, subtyp m Gs G S U -> forall G',
    m = ty_general ->
    ok G' ->
    subenv Gs G' G ->
    subtyp m Gs G' S U).
Proof.
  apply rules_mutind; intros; eauto 4.
  - (* ty_var *)
    subst.
    generalize dependent T. dependent induction H1.
    + eauto.
    + introv Bi.
      destruct (classicT (x = x0)) as [Eq | Ne].
      * subst. eapply binds_push_eq_inv in Bi. subst.
        eapply ty_sub; eauto 4.
        intros Contra. inversion Contra.
      * assert (ty_trm ty_general Gs G1 (trm_var (avar_c x)) T) as A. {
          eapply IHsubenv; eauto.
          eapply binds_push_neq_inv. eassumption. assumption.
        }
        eapply weaken_ty_trm. apply A. assumption.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto.
    eapply H; eauto.
    eapply se_push; eauto.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as y; eauto.
    apply H; eauto.
    eapply se_push; eauto.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto.
    apply H0 with (x:=y); eauto.
    eapply se_push; eauto.
  - admit.
  - admit.
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto 4.
    apply H0; eauto. eapply se_push; eauto.
  - (* subtyp_bnd *)
    subst.
    apply_fresh subtyp_bnd as y; eauto 4.
    apply H; eauto. eapply se_push; eauto.
Qed.

Lemma narrow_typing: forall Gs G G' t T,
  ty_trm ty_general Gs G t T ->
  subenv Gs G' G -> ok G' ->
  ty_trm ty_general Gs G' t T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall Gs G G' S U,
  subtyp ty_general Gs G S U ->
  subenv Gs G' G -> ok G' ->
  subtyp ty_general Gs G' S U.
Proof.
  intros. apply* narrow_rules.
Qed.

(* ###################################################################### *)
(** * Has member *)

Inductive has_member: ctx -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_any : forall G x T A S U,
  ty_trm ty_general G empty (trm_var (avar_s x)) T ->
  has_member_rules G x T A S U ->
  has_member G x T A S U
with has_member_rules: ctx -> var -> typ -> typ_label -> typ -> typ -> Prop :=
| has_refl : forall G x A S U,
  has_member_rules G x (typ_rcd (dec_typ A S U)) A S U
| has_and1 : forall G x T1 T2 A S U,
  has_member G x T1 A S U ->
  has_member_rules G x (typ_and T1 T2) A S U
| has_and2 : forall G x T1 T2 A S U,
  has_member G x T2 A S U ->
  has_member_rules G x (typ_and T1 T2) A S U
| has_bnd : forall G x T A S U,
  has_member G x (open_typ (in_sto x) T) A S U ->
  has_member_rules G x (typ_bnd T) A S U
| has_sel : forall G x y B T' A S U,
  ty_trm ty_precise G empty (trm_var (avar_s y)) (typ_rcd (dec_typ B T' T')) ->
  has_member G x T' A S U ->
  has_member_rules G x (typ_sel (avar_s y) B) A S U
| has_bot  : forall G x A S U,
  has_member_rules G x typ_bot A S U
.

Scheme has_mut := Induction for has_member Sort Prop
with hasr_mut := Induction for has_member_rules Sort Prop.
Combined Scheme has_mutind from has_mut, hasr_mut.

Lemma has_member_rules_inv: forall G x T A S U, has_member_rules G x T A S U ->
  (T = typ_rcd (dec_typ A S U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G x T1 A S U \/
     has_member G x T2 A S U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G x (open_typ (in_sto x) T') A S U) \/
  (exists y B T', T = typ_sel (avar_s y) B /\
    ty_trm ty_precise G empty (trm_var (avar_s y)) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst.
  - left. eauto.
  - right. left. exists T1 T2. eauto.
  - right. left. exists T1 T2. eauto.
  - right. right. left. exists T0. eauto.
  - right. right. right. left. exists y B T'. eauto.
  - right. right. right. right. reflexivity.
Qed.

Lemma has_member_inv: forall G x T A S U, has_member G x T A S U ->
  (T = typ_rcd (dec_typ A S U)) \/
  (exists T1 T2, T = typ_and T1 T2 /\
    (has_member G x T1 A S U \/
     has_member G x T2 A S U)) \/
  (exists T', T = typ_bnd T' /\
    has_member G x (open_typ (in_sto x) T') A S U) \/
  (exists y B T', T = typ_sel (avar_s y) B /\
    ty_trm ty_precise G empty (trm_var (avar_s y)) (typ_rcd (dec_typ B T' T')) /\
    has_member G x T' A S U) \/
  (T = typ_bot).
Proof.
  intros. inversion H; subst. apply has_member_rules_inv in H1. apply H1.
Qed.

Lemma val_new_typing: forall Gs s x T ds,
  wf_sto Gs s ->
  binds x (val_new T ds) s ->
  ty_trm ty_precise Gs empty (trm_val (val_new T ds)) (typ_bnd T).
Proof.
  introv Hwf Bis.
  assert (exists T, binds x T Gs) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [T0 Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [S [U [t [Bis' [Ht EqT]]]]].
    false.
  - destruct H as [T' [ds' [Bis' [Ht EqT]]]]. subst.
    unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis.
    inversion Bis. subst.
    assumption.
Qed.


Lemma rcd_typ_eq_bounds: forall T A S U,
  record_type T ->
  record_sub T (typ_rcd (dec_typ A S U)) ->
  S = U.
Proof.
  introv Htype Hsub.
  generalize dependent U. generalize dependent S. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Hsub; subst.
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
  - apply IHHtyp with (A:=A); eauto.
Qed.

Lemma has_member_rcd_typ_sub_mut:
  (forall G x T A S U,
    has_member G x T A S U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A S U))) /\
  (forall G x T A S U,
    has_member_rules G x T A S U ->
    record_type T ->
    record_sub T (typ_rcd (dec_typ A S U))).
Proof.
  apply has_mutind; intros.
  - apply H; eauto.
  - apply rs_refl.
  - inversion H0; subst. inversion H1; subst. apply rs_drop.
    apply H; eauto.
    exists ls. assumption.
  - inversion H0; subst. inversion H1; subst. inversion h; subst. inversion H3; subst.
    eapply rs_dropl. eapply rs_refl.
  - inversion H0. inversion H1.
  - inversion H0. inversion H1.
  - destruct H as [ls H]. inversion H.
Qed.

Lemma has_member_tightness: forall G s x T ds A S U,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  has_member G x (typ_bnd T) A S U ->
  S = U.
Proof.
  introv Hwf Bis Hmem.
  assert (record_type T) as Htype. {
    eapply record_new_typing. eapply val_new_typing; eauto.
  }
  assert (record_type (open_typ (in_sto x) T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (has_member G x (open_typ (in_sto x) T) A S U) as Hmemx. {
    inversion Hmem; subst. inversion H0; subst. assumption.
  }
  assert (record_sub (open_typ (in_sto x) T) (typ_rcd (dec_typ A S U))) as Hsub. {
    destruct has_member_rcd_typ_sub_mut as [HL _].
    eapply HL; eauto.
  }
  eapply rcd_typ_eq_bounds. eapply Htypex. eapply Hsub.
Qed.

Lemma has_member_covariance: forall Gs s T1 T2 x A S2 U2,
  wf_sto Gs s ->
  subtyp ty_general Gs empty T1 T2 ->
  ty_trm ty_general Gs empty (trm_var (avar_s x)) T1 ->
  has_member Gs x T2 A S2 U2 ->
  exists S1 U1, has_member Gs x T1 A S1 U1 /\
                subtyp ty_general Gs empty S2 S1 /\
                subtyp ty_general Gs empty U1 U2.
Proof.
  introv Hwf Hsub Hty Hmem.
  generalize dependent U2.
  generalize dependent S2.
  dependent induction Hsub; subst; intros;
  assert (@empty typ ~= @empty typ) as HE by reflexivity.
  - (* top *)
    inversion Hmem; subst. inversion H0.
  - (* bot *)
    exists S2 U2. split.
    apply has_any. assumption. apply has_bot.
    split; apply subtyp_refl.
  - (* refl *)
    exists S2 U2. eauto.
  - (* trans *)
    assert (ty_trm ty_general Gs empty (trm_var (avar_s x)) T) as HS. {
      eapply ty_sub.
      intros Hp. inversion Hp.
      eapply Hty.
      eassumption.
    }
    specialize (IHHsub2 Hwf HE HS S2 U2 Hmem).
    destruct IHHsub2 as [S3 [U3 [Hmem3 [Hsub31 Hsub32]]]].
    specialize (IHHsub1 Hwf HE Hty S3 U3 Hmem3).
    destruct IHHsub1 as [S1 [U1 [Hmem1 [Hsub11 Hsub12]]]].
    exists S1 U1. split. apply Hmem1. split; eauto.
  - (* and11 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and1. assumption.
    split; eauto.
  - (* and12 *)
    exists S2 U2. split.
    inversion Hmem; subst. apply has_any. assumption. eapply has_and2. assumption.
    split; eauto.
  - (* and2 *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1 [T2 [Heq [Hmem | Hmem]]]]; inversions Heq.
      * specialize (IHHsub1 Hwf HE Hty S2 U2 Hmem). apply IHHsub1.
      * specialize (IHHsub2 Hwf HE Hty S2 U2 Hmem). apply IHHsub2.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq _]]]]. inversion Heq.
    + inversion Hmem.
  - (* fld *)
    inversion Hmem; subst. inversion H0; subst.
  - (* typ *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversions Hmem.
      exists S1 T1. split.
      apply has_any. assumption. apply has_refl.
      split; assumption.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq _]]]]. inversion Heq.
    + inversion Hmem.
  - (* sel2 *)
    inversion H; subst.
    false. eapply empty_middle_inv. eassumption.
  - (* sel1 *)
    inversion H; subst.
    false. eapply empty_middle_inv. eassumption.
  - (* sel2 tight *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversions Heq.
      assert (T' = T) as HeqT. {
        eapply unique_tight_bounds; eassumption.
      }
      subst. eauto.
    + inversion Hmem.
  - (* sel1 tight *)
    exists S2 U2. split.
    eapply has_any. assumption. eapply has_sel. eassumption. eassumption.
    eauto.
  - (* all *)
    inversion Hmem; subst. inversion H2; subst.
  - (* bnd *)
    inversion Hmem; subst.
    admit.
Qed.

Lemma has_member_monotonicity: forall Gs s x T0 ds T A S U,
  wf_sto Gs s ->
  binds x (val_new T0 ds) s ->
  has_member Gs x T A S U ->
  exists T1, has_member Gs x (typ_bnd T0) A T1 T1 /\
             subtyp ty_general Gs empty S T1 /\
             subtyp ty_general Gs empty T1 U.
Proof.
  introv Hwf Bis Hmem. inversion Hmem; subst.
  generalize dependent U. generalize dependent S.
  dependent induction H; intros.
  - (* var *)
    destruct (corresponding_types Hwf H).
    destruct H1 as [S0 [U0 [t [Bis' _]]]]. unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversion Bis.
    destruct H1 as [S0 [ds0 [Bis' [Hty Heq]]]]. unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversions Bis'.
    assert (S = U). {
      eapply has_member_tightness. eassumption. eassumption.
      eapply has_any.
      eapply ty_var_s. eassumption.
      eassumption.
    }
    subst.
    exists U. eauto.
  - (* rec_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq _]]. inversions Heq.
      apply IHty_trm; eauto.
      inversions H0. assumption.
      inversions H0. inversions H4. assumption.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* rec_elim *)
    apply IHty_trm; eauto.
    apply has_any. assumption. apply has_bnd. assumption.
    apply has_bnd. assumption.
  - (* and_intro *)
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq [Hmem | Hmem]]]];
      inversions Heq; inversions H1; inversions H9.
      apply IHty_trm1; eauto.
      apply IHty_trm2; eauto. apply has_any; assumption.
      apply IHty_trm1; eauto. apply has_any; assumption.
      apply IHty_trm2; eauto.
    + destruct Hmem as [T1' [Heq _]]. inversion Heq.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  - (* sub *)
    destruct (has_member_covariance Hwf H1 H0 Hmem) as [S' [U' [Hmem' [Hsub1' Hsub2']]]].
    inversion Hmem'; subst.
    assert (@empty typ ~= @empty typ) as HE by reflexivity.
    assert (trm_var (avar_s x) = trm_var (avar_s x)) as HEx by reflexivity.
    specialize (IHty_trm x Hwf Bis HE HEx S' U' Hmem' H4).
    destruct IHty_trm as [T1 [Hmem1 [Hsub1 Hsub2]]].
    exists T1. eauto.
Qed.

(* ###################################################################### *)
(** * Tight bound completeness *)

Lemma has_member_rcd_typ_sub2_mut:
  (forall G x T A S U,
    has_member G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise G empty T (typ_rcd (dec_typ A S U)))  /\
  (forall G x T A S U,
    has_member_rules G x T A S U ->
    record_type T ->
    T = (typ_rcd (dec_typ A S U)) \/ subtyp ty_precise G empty T (typ_rcd (dec_typ A S U))).
Proof.
  apply has_mutind; intros.
  - apply H; eauto.
  - left. reflexivity.
  - inversion H0; subst. inversion H1; subst.
    assert (record_type T1) as Htyp1. { exists ls. assumption. }
    specialize (H Htyp1). destruct H as [H | H].
    + subst. right. apply subtyp_and11.
    + right.
      eapply subtyp_trans. eapply subtyp_and11. apply H.
  - inversion H0; subst. inversion H1; subst. inversion h; subst. inversion H3; subst.
    right. eapply subtyp_and12.
  - inversion H0. inversion H1.
  - inversion H0. inversion H1.
  - destruct H as [ls H]. inversion H.
Qed.

Lemma wf_sto_val_new_in_G: forall G s x T ds,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  binds x (typ_bnd T) G.
Proof.
  introv Hwf Bis.
  assert (exists S, binds x S G) as Bi. {
    eapply sto_binds_to_ctx_binds; eauto.
  }
  destruct Bi as [S Bi].
  destruct (corresponding_types Hwf Bi).
  - destruct H as [? [? [? [Bis' _]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis in Bis'. inversion Bis'.
  - destruct H as [T' [ds' [Bis' [Hty Heq]]]].
    unfold binds in Bis'. unfold binds in Bis. rewrite Bis' in Bis. inversions Bis.
    assumption.
Qed.

(* If G ~ s, s |- x = new(x: T)d, and G |-# x: {A: S..U} then G |-# x.A <: U and G |-# S <: x.A. *)
Lemma tight_bound_completeness: forall G s x T ds A S U,
  wf_sto G s ->
  binds x (val_new T ds) s ->
  ty_trm ty_general G empty (trm_var (avar_s x)) (typ_rcd (dec_typ A S U)) ->
  subtyp ty_general G empty (typ_sel (avar_s x) A) U /\
  subtyp ty_general G empty S (typ_sel (avar_s x) A).
Proof.
  introv Hwf Bis Hty.
  assert (has_member G x (typ_rcd (dec_typ A S U)) A S U) as Hmem. {
    apply has_any. assumption. apply has_refl.
  }
  apply has_member_monotonicity with (s:=s) (ds:=ds) (T0:=T) in Hmem.
  destruct Hmem as [T1 [Hmem [Hsub1 Hsub2]]].
  assert (has_member G x (open_typ (in_sto x) T) A T1 T1) as Hmemx. {
    apply has_member_inv in Hmem.
    repeat destruct Hmem as [Hmem|Hmem].
    + inversion Hmem.
    + destruct Hmem as [T1' [T2' [Heq _]]]. inversion Heq.
    + destruct Hmem as [T1' [Heq Hmem]]. inversions Heq. assumption.
    + destruct Hmem as [y [B [T' [Heq [Htyb Hmem]]]]]. inversion Heq.
    + inversion Hmem.
  }
  assert (record_type T) as Htype. {
    eapply record_new_typing. eapply val_new_typing; eauto.
  }
  assert (record_type (open_typ (in_sto x) T)) as Htypex. {
    apply open_record_type. assumption.
  }
  assert (open_typ (in_sto x) T = (typ_rcd (dec_typ A T1 T1)) \/ subtyp ty_precise G empty (open_typ (in_sto x) T) (typ_rcd (dec_typ A T1 T1))) as Hsub. {
    destruct has_member_rcd_typ_sub2_mut as [HE _].
    eapply HE; eauto.
  }
  assert (ty_trm ty_precise G empty (trm_var (avar_s x)) (open_typ (in_sto x) T)) as Htypx. {
    eapply ty_rec_elim.
    eapply ty_var_s.
    eapply wf_sto_val_new_in_G; eauto.
  }
  assert (ty_trm ty_precise G empty (trm_var (avar_s x)) (typ_rcd (dec_typ A T1 T1))) as Htyp. {
    destruct Hsub as [Heq | Hsub].
    - rewrite Heq in Htypx. apply Htypx.
    - eapply ty_sub.
      intro. eexists. reflexivity.
      eapply Htypx. eapply Hsub.
  }
  split.
  eapply subtyp_trans. eapply subtyp_sel1_tight. eapply Htyp. eapply Hsub2.
  eapply subtyp_trans. eapply Hsub1. eapply subtyp_sel2_tight. eapply Htyp.
  eapply Hwf. eapply Bis.
Qed.

(* ###################################################################### *)
(** * Misc Inversions *)

Lemma all_intro_inversion: forall Gs G S t U,
  ty_trm ty_precise Gs G (trm_val (val_lambda S t)) U ->
  exists T, U = typ_all S T.
Proof.
  intros. dependent induction H.
  - eexists. reflexivity.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
Qed.

Lemma new_intro_inversion: forall Gs G T ds U,
  ty_trm ty_precise Gs G (trm_val (val_new T ds)) U ->
  U = typ_bnd T /\ record_type T.
Proof.
  intros. inversion H; subst.
  - apply record_new_typing in H. split; eauto.
  - assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H0 Heqm1). destruct H0. inversion H0.
Qed.


(* ###################################################################### *)
(** ** The substitution principle *)

Lemma exists_bound_restricted_by: forall x T G,
  binds x T G ->
  exists G', restricted_by x G G'.
Proof.
  intros x T.
  apply (env_ind (fun G => binds x T G -> exists G', restricted_by x G G')).
  - intro Bi. false. eapply binds_empty_inv; eauto.
  - introv IH Bi.
    apply binds_push_inv in Bi. destruct Bi as [[? ?] | [Neq Bi]].
    + subst. eexists. apply lim_ctx with (G2:=empty).
      rewrite concat_empty_r. reflexivity.
    + specialize (IH Bi). destruct IH as [G' IH].
      exists G'. inversion IH; subst. eapply lim_ctx with (G2:=G2 & x0 ~ v).
      rewrite concat_assoc. reflexivity.
Qed.

Lemma precise_fresh_subtyp: forall Gs S U,
  subtyp ty_precise Gs empty S U -> forall y,
    y \notin fv_ctx_types Gs ->
    y \notin fv_typ S ->
    y \notin fv_typ U.
Proof.
  introv Hsub. dependent induction Hsub; intros; eauto;
  try solve [simpl in H0; apply notin_union_r in H0; destruct H0; assumption].
Qed.

Lemma fresh_fv_typ: forall x y,
  y <> x ->
  (forall T, y \notin fv_typ T -> forall i,
    y \notin fv_typ (open_rec_typ i (in_sto x) T)) /\
  (forall d, y \notin fv_dec d -> forall i,
    y \notin fv_dec (open_rec_dec i (in_sto x) d)).
Proof.
  intros. apply typ_mutind; intros; simpl; eauto; try solve [
    simpl in H2; eapply notin_union_r in H2; destruct H2;
    apply notin_union_l; eauto].
  - simpl. unfold open_rec_avar. destruct a.
    case_if.
    + simpl. unfold fv_fvar. simpl. apply notin_singleton. assumption.
    + simpl. eauto.
    + simpl. simpl in H0. assumption.
Qed.

Lemma precise_fresh_ty_trm: forall Gs x T,
  ty_trm ty_precise Gs empty (trm_var (avar_s x)) T -> forall y,
    y \notin fv_ctx_types Gs -> y # Gs ->
    y \notin fv_typ T.
Proof.
  introv Hty. dependent induction Hty; intros; eauto.
  - eapply fv_ctx_types_binds; eauto.
  - destruct (typing_implies_sto_bound Hty) as [Tx Bi].
    assert (x <> y) as A. {
      destruct (classicT (x = y)) as [Eq | Ne].
      + subst. false. eapply binds_fresh_inv; eauto.
      + assumption.
    }
    assert (y \notin fv_typ (typ_bnd T)) as B. {
      eapply IHHty; eauto.
      unfold avar_s. reflexivity.
    }
    eapply fresh_fv_typ; eauto.
  - eapply precise_fresh_subtyp; eauto.
Qed.

Lemma restricted_by_first: forall x T G2 G',
  ok (x ~ T & G2) ->
  restricted_by x (x ~ T & G2) G' ->
  G' = x ~ T.
Proof.
  introv Hok r. inversion r; subst.
  lets Hok': (ok_restricted_by Hok r).
  assert (empty = G1 /\ G2 = G0 /\ T = T0) as A. {
    eapply concat_ok_eq.
    rewrite concat_empty_l. eapply H.
    rewrite concat_empty_l. eapply Hok.
  }
  destruct A as [A1 [A2 AT]]. subst.
  rewrite concat_empty_l. reflexivity.
Qed.

Lemma subst_rules: forall y S,
   (forall m Gs G t T, ty_trm m Gs G t T -> forall s G2 x,
    wf_sto Gs s ->
    G = x ~ S & G2 ->
    ok (x ~ S & G2) ->
    x \notin fv_ctx_types Gs -> x # Gs ->
    ty_trm ty_general Gs empty (trm_var (avar_s y)) (subst_typ x (in_sto y) S) ->
    m = ty_general ->
    ty_trm m Gs (subst_ctx x (in_sto y) G2) (subst_trm x (in_sto y) t) (subst_typ x (in_sto y) T)) /\
  (forall Gs G d D, ty_def Gs G d D -> forall s G2 x,
    wf_sto Gs s ->
    G = x ~ S & G2 ->
    ok (x ~ S & G2) ->
    x \notin fv_ctx_types Gs -> x # Gs ->
    ty_trm ty_general Gs empty (trm_var (avar_s y)) (subst_typ x (in_sto y) S) ->
    ty_def Gs (subst_ctx x (in_sto y) G2) (subst_def x (in_sto y) d) (subst_dec x (in_sto y) D)) /\
  (forall Gs G ds T, ty_defs Gs G ds T -> forall s G2 x,
    wf_sto Gs s ->
    G = x ~ S & G2 ->
    ok (x ~ S & G2) ->
    x \notin fv_ctx_types Gs -> x # Gs ->
    ty_trm ty_general Gs empty (trm_var (avar_s y)) (subst_typ x (in_sto y) S) ->
    ty_defs Gs (subst_ctx x (in_sto y) G2) (subst_defs x (in_sto y) ds) (subst_typ x (in_sto y) T)) /\
  (forall m Gs G T U, subtyp m Gs G T U -> forall s G2 x,
    wf_sto Gs s ->
    G = x ~ S & G2 ->
    ok (x ~ S & G2) ->
    x \notin fv_ctx_types Gs -> x # Gs ->
    ty_trm ty_general Gs empty (trm_var (avar_s y)) (subst_typ x (in_sto y) S) ->
    m = ty_general ->
    subtyp m Gs (subst_ctx x (in_sto y) G2) (subst_typ x (in_sto y) T) (subst_typ x (in_sto y) U)).
Proof.
  intros y S. apply rules_mutind; intros; subst G; try subst m.
  - (* ty_var_s *)
    simpl.
    assert (subst_typ x0 (in_sto y) T = T) as A. {
      apply subst_fresh_typ.
      eapply fv_ctx_types_binds with (G:=Gs); eauto.
    }
    rewrite A.
    apply ty_var_s with (T:=T); eauto.
  - (* ty_var_c *)
    simpl. case_if.
    + assert (T = S) as A. {
        rewrite <- concat_empty_l in b. rewrite concat_assoc in b.
        apply binds_middle_eq_inv in b. subst. reflexivity.
        rewrite concat_empty_l. assumption.
      }
      subst.
      assert ((subst_ctx x0 (in_sto y) G2)=empty & (subst_ctx x0 (in_sto y) G2)) as B. {
        rewrite concat_empty_l. reflexivity.
      }
      rewrite B. apply weaken_ty_trm; eauto. rewrite concat_empty_l.
      apply ok_map. eauto.
    + rewrite <- concat_empty_l in b. rewrite concat_assoc in b.
      apply binds_subst in b. rewrite concat_empty_l in b.
      apply ty_var_c.
      apply binds_map. assumption. assumption.
  - (* ty_all_intro *)
    simpl.
    apply_fresh ty_all_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x (in_sto y) (in_ctx z) = (in_ctx z)) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A.
    rewrite <- subst_open_commute_trm. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x (in_sto y) G2 & z ~ subst_typ x (in_sto y) T = subst_ctx x (in_sto y) (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite B.
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
  - (* ty_all_elim *)
    simpl. rewrite subst_open_commute_typ.
    eapply ty_all_elim.
    eapply H; eauto.
    eapply H0; eauto.
  - (* ty_new_intro *)
    simpl.
    apply_fresh ty_new_intro as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x (in_sto y) (in_ctx z) = (in_ctx z)) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_defs.
    assert (subst_ctx x (in_sto y) G2 & z ~ subst_typ x (in_sto y) (open_typ (in_ctx z) T) = subst_ctx x (in_sto y) (G2 & z ~ open_typ (in_ctx z) T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite B.
    eapply H; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
  - (* ty_new_elim *)
    simpl. apply ty_new_elim.
    eapply H; eauto.
  - (* ty_let *)
    simpl.
    apply_fresh ty_let as z; eauto.
    assert (subst_ctx x (in_sto y) G2 & z ~ subst_typ x (in_sto y) T = subst_ctx x (in_sto y) (G2 & z ~ T)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite B.
    assert (subst_fvar x (in_sto y) (in_ctx z) = (in_ctx z)) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A. rewrite <- subst_open_commute_trm.
    eapply H0 with (x0:=z); eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
  - (* ty_rec_intro *)
    simpl. apply ty_rec_intro.
    rewrite <- subst_open_commute_typ.
    eapply H; eauto.
  - (* ty_rec_elim *)
    simpl. rewrite subst_open_commute_typ.
    apply ty_rec_elim.
    eapply H; eauto.
  - (* ty_and_intro *)
    simpl.
    apply ty_and_intro; eauto.
  - (* ty_sub *)
    eapply ty_sub; eauto 4.
    intro Contra. inversion Contra.
  - (* ty_def_typ *)
    simpl. apply ty_def_typ; eauto.
  - (* ty_def_trm *)
    simpl. apply ty_def_trm; eauto.
  - (* ty_defs_one *)
    simpl. apply ty_defs_one; eauto.
  - (* ty_defs_cons *)
    simpl. apply ty_defs_cons; eauto.
    rewrite <- subst_label_of_def.
    apply subst_defs_hasnt. assumption.
  - (* subtyp_top *)
    apply subtyp_top.
  - (* subtyp_bot *)
    apply subtyp_bot.
  - (* subtyp_refl *)
    apply subtyp_refl.
  - (* subtyp_trans *)
    eapply subtyp_trans; eauto.
  - (* subtyp_and11 *)
    eapply subtyp_and11; eauto.
  - (* subtyp_and12 *)
    eapply subtyp_and12; eauto.
  - (* subtyp_and2 *)
    eapply subtyp_and2; eauto.
  - (* subtyp_fld *)
    eapply subtyp_fld; eauto.
  - (* subtyp_typ *)
    eapply subtyp_typ; eauto.
  - (* subtyp_sel2 *)
    simpl.
    case_if.
    + assert (G' = x0 ~ S) as B. {
        eapply restricted_by_first; eauto.
      }
      subst.
      assert (ty_trm ty_general Gs (subst_ctx x0 (in_sto y) empty)
        (subst_trm x0 (in_sto y) (trm_var (avar_c x0)))
        (subst_typ x0 (in_sto y) (typ_rcd (dec_typ A S0 T)))) as Hg. {
        eapply H; eauto.
        rewrite concat_empty_r. reflexivity.
        rewrite concat_empty_r. eauto.
      }
      simpl in Hg. rewrite If_l in Hg.
      unfold subst_ctx in Hg. rewrite map_empty in Hg.
      assert (avar_f (in_sto y) = (avar_s y)) as C by eauto.
      rewrite C in Hg.
      admit.
      reflexivity.
    + admit.
  - (* subtyp_sel1 *)
    admit.
  - (* subtyp_sel2_tight *)
    simpl. eapply subtyp_sel2_tight; eauto.
    lets B: (precise_fresh_ty_trm t H3 H4); eauto.
    simpl in B. apply notin_union_r in B. destruct B as [B ?].
    assert (subst_typ x0 (in_sto y) T = T) as C. {
      apply subst_fresh_typ.
      assumption.
    }
    rewrite C. assumption.
  - (* subtyp_sel1_tight *)
    simpl. eapply subtyp_sel1_tight; eauto.
    lets B: (precise_fresh_ty_trm t H3 H4); eauto.
    simpl in B. apply notin_union_r in B. destruct B as [B ?].
    assert (subst_typ x0 (in_sto y) T = T) as C. {
      apply subst_fresh_typ.
      assumption.
    }
    rewrite C. assumption.
  - (* subtyp_all *)
    simpl. apply_fresh subtyp_all as z; eauto.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x (in_sto y) (in_ctx z) = (in_ctx z)) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x (in_sto y) G2 & z ~ subst_typ x (in_sto y) S2 = subst_ctx x (in_sto y) (G2 & z ~ S2)) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite B.
    eapply H0; eauto.
    rewrite concat_assoc. reflexivity.
    rewrite concat_assoc. apply ok_push. assumption. eauto.
  - (* subtyp_bnd *)
    simpl. apply_fresh subtyp_bnd as z; eauto 4.
    assert (z \notin L) as FrL by eauto.
    assert (subst_fvar x (in_sto y) (in_ctx z) = (in_ctx z)) as A. {
      unfold subst_fvar. rewrite If_r. reflexivity. eauto.
    }
    rewrite <- A.
    rewrite <- subst_open_commute_typ. rewrite <- subst_open_commute_typ.
    assert (subst_ctx x (in_sto y) G2 & z ~ typ_bnd (subst_typ x (in_sto y) T1) = subst_ctx x (in_sto y) (G2 & z ~ (typ_bnd T1))) as B. {
      unfold subst_ctx. rewrite map_concat. rewrite map_single.
      simpl. reflexivity.
    }
    rewrite B.
    eapply H; eauto using concat_assoc.
    rewrite concat_assoc. apply ok_push; eauto.
Qed.

Lemma subst_ty_trm: forall y S s Gs x t T,
    wf_sto Gs s ->
    ty_trm ty_general Gs (x ~ S) t T -> 
    x \notin fv_ctx_types Gs -> x # Gs ->
    ty_trm ty_general Gs empty (trm_var (avar_s y)) (subst_typ x (in_sto y) S) ->
    ty_trm ty_general Gs empty (subst_trm x (in_sto y) t) (subst_typ x (in_sto y) T).
Proof.
  intros.
  apply (proj51 (subst_rules y S)) with (s:=s) (G2:=empty) (x:=x) in H0; eauto 4.
  unfold subst_ctx in H0. rewrite map_empty in H0. assumption.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. rewrite <- concat_empty_l. eapply ok_push; eauto.
Qed.

Lemma subst_ty_defs: forall y S s Gs x ds T,
    wf_sto Gs s ->
    ty_defs Gs (x ~ S) ds T ->
    x \notin fv_ctx_types Gs -> x # Gs ->
    ty_trm ty_general Gs empty (trm_var (avar_s y)) (subst_typ x (in_sto y) S) ->
    ty_defs Gs empty (subst_defs x (in_sto y) ds) (subst_typ x (in_sto y) T).
Proof.
  intros.
  apply (proj53 (subst_rules y S)) with (s:=s) (G2:=empty) (x:=x) in H0; eauto 4.
  unfold subst_ctx in H0. rewrite map_empty in H0. assumption.
  rewrite concat_empty_r. reflexivity.
  rewrite concat_empty_r. rewrite <- concat_empty_l. eapply ok_push; eauto.
Qed.

(* ###################################################################### *)
(** ** Possible types *)

(*
Definition (Possible types)

For a variable x, non-variable value v, environment G, the set Ts(G, x, v) of possible types of x defined as v in G is the smallest set SS such that:

If v = new(x: T)d then T in SS.
If v = new(x: T)d and {a = t} in d and G |- t: T' then {a: T'} in SS.
If v = new(x: T)d and {A = T'} in d and G |- S <: T', G |- T' <: U then {A: S..U} in SS.
If v = lambda(x: S)t and G, x: S |- t: T and G |- S' <: S and G, x: S' |- T <: T' then all(x: S')T' in SS.
If S1 in SS and S2 in SS then S1 & S2 in SS.
If S in SS and G |-! y: {A: S..S} then y.A in SS.
If S in SS then rec(x: S) in SS.
*)

Inductive possible_types: ctx -> var -> val -> typ -> Prop :=
| pt_top : forall G x v,
  possible_types G x v typ_top
| pt_new : forall G x T ds,
  possible_types G x (val_new T ds) (open_typ (in_sto x) T)
| pt_rcd_trm : forall G x T ds a t T',
  defs_has (open_defs (in_sto x) ds) (def_trm a t) ->
  ty_trm ty_general G empty t T' ->
  possible_types G x (val_new T ds) (typ_rcd (dec_trm a T'))
| pt_rcd_typ : forall G x T ds A T' S U,
  defs_has (open_defs (in_sto x) ds) (def_typ A T') ->
  subtyp ty_general G empty S T' ->
  subtyp ty_general G empty T' U ->
  possible_types G x (val_new T ds) (typ_rcd (dec_typ A S U))
| pt_lambda : forall L G x S t T S' T',
  (forall y, y \notin L ->
   ty_trm ty_general G (y ~ S) (open_trm (in_ctx y) t) (open_typ (in_ctx y) T)) ->
  subtyp ty_general G empty S' S ->
  (forall y, y \notin L ->
   subtyp ty_general G (y ~ S') (open_typ (in_ctx y) T) (open_typ (in_ctx y) T')) ->
  possible_types G x (val_lambda S t) (typ_all S' T')
| pt_and : forall G x v S1 S2,
  possible_types G x v S1 ->
  possible_types G x v S2 ->
  possible_types G x v (typ_and S1 S2)
| pt_sel : forall G x v y A S,
  possible_types G x v S ->
  ty_trm ty_precise G empty (trm_var y) (typ_rcd (dec_typ A S S)) ->
  possible_types G x v (typ_sel y A)
| pt_bnd : forall G x v S S',
  possible_types G x v S ->
  S = open_typ (in_sto x) S' ->
  possible_types G x v (typ_bnd S')
.

Lemma var_new_typing: forall Gs G s x T ds,
  wf_sto Gs s ->
  binds x (val_new T ds) s ->
  ty_trm ty_general Gs G (trm_var (avar_s x)) (open_typ (in_sto x) T).
Proof.
  intros.
  apply ty_rec_elim. apply ty_var_s. eapply wf_sto_val_new_in_G; eauto.
Qed.

Lemma ty_defs_has: forall Gs G ds T d,
  ty_defs Gs G ds T ->
  defs_has ds d ->
  record_type T ->
  exists D, ty_def Gs G d D /\ record_sub T (typ_rcd D).
Proof.
  introv Hdefs Hhas Htype. generalize dependent d. generalize dependent ds.
  inversion Htype; subst. induction H; intros.
  - exists D. split. inversion Hdefs; subst. inversion Hhas; subst.
    case_if. inversions H1. assumption. apply rs_refl.
  - inversion Hdefs; subst.
    unfold defs_has in Hhas. unfold get_def in Hhas.
    case_if.
    + inversions Hhas.
      exists D. split. inversions Hdefs; subst. assumption.
      eapply rs_dropl. eapply rs_refl.
    + assert (exists D0, ty_def Gs G d D0 /\ record_sub T (typ_rcd D0)) as A. {
        eapply IHrecord_typ; eauto.
        exists ls. eassumption.
      }
      destruct A as [D0 [A1 A2]].
      exists D0. split. apply A1. apply rs_drop. apply A2.
Qed.

Lemma new_ty_defs: forall Gs s x T ds,
  wf_sto Gs s ->
  binds x (val_new T ds) s ->
  ty_defs Gs empty (open_defs (in_sto x) ds) (open_typ (in_sto x) T).
Proof.
  introv Hwf Bis.
  lets Htyv: (val_new_typing Hwf Bis).
  inversion Htyv; subst.
  pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
  rewrite subst_intro_defs with (x:=y). rewrite subst_intro_typ with (x:=y).
  rewrite concat_empty_l in H3.
  eapply subst_ty_defs; eauto.
  rewrite <- subst_intro_typ with (x:=y).
  eapply ty_rec_elim. apply ty_var_s. eapply wf_sto_val_new_in_G; eauto.
  eauto. eauto. eauto.
  assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
  specialize (H Heqm1). destruct H as [? Contra]. inversion Contra.
Qed.

Lemma pt_piece_rcd: forall Gs s x T ds d D,
  wf_sto Gs s ->
  binds x (val_new T ds) s ->
  defs_has (open_defs (in_sto x) ds) d ->
  ty_def Gs empty d D ->
  possible_types Gs x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas Hdef.
  inversion Hdef; subst; econstructor; eauto.
Qed.

Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
  record_has (typ_rcd D) D
| rh_andl : forall T D,
  record_has (typ_and T (typ_rcd D)) D
| rh_and : forall T D D',
  record_has T D' ->
  record_has (typ_and T D) D'.

Lemma defs_has_hasnt_neq: forall ds d1 d2,
  defs_has ds d1 ->
  defs_hasnt ds (label_of_def d2) ->
  label_of_def d1 <> label_of_def d2.
Proof.
  introv Hhas Hhasnt.
  unfold defs_has in Hhas.
  unfold defs_hasnt in Hhasnt.
  induction ds.
  - simpl in Hhas. inversion Hhas.
  - simpl in Hhasnt. simpl in Hhas. case_if; case_if.
    + inversions Hhas. assumption.
    + apply IHds; eauto.
Qed.

Lemma record_has_ty_defs: forall Gs G T ds D,
  ty_defs Gs G ds T ->
  record_has T D ->
  exists d, defs_has ds d /\ ty_def Gs G d D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    unfold defs_has. simpl. rewrite If_l. reflexivity. reflexivity.
    assumption.
  - inversion Hhas; subst.
    + exists d. split.
      unfold defs_has. simpl. rewrite If_l. reflexivity. reflexivity.
      assumption.
    + specialize (IHHdefs H4). destruct IHHdefs as [d' [IH1 IH2]].
      exists d'. split.
      unfold defs_has. simpl. rewrite If_r. apply IH1.
      apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      assumption.
Qed.

Lemma pt_rcd_has_piece: forall Gs s x T ds D,
  wf_sto Gs s ->
  binds x (val_new T ds) s ->
  record_has (open_typ (in_sto x) T) D ->
  possible_types Gs x (val_new T ds) (typ_rcd D).
Proof.
  introv Hwf Bis Hhas.
  lets Hdefs: (new_ty_defs Hwf Bis).
  destruct (record_has_ty_defs Hdefs Hhas) as [d [A B]].
  eapply pt_piece_rcd; eauto.
Qed.

Lemma pt_rcd_trm_inversion: forall Gs s x v a T,
  wf_sto Gs s ->
  binds x v s ->
  possible_types Gs x v (typ_rcd (dec_trm a T)) ->
  exists S ds t,
    v = val_new S ds /\
    defs_has (open_defs (in_sto x) ds) (def_trm a t) /\
    ty_trm ty_general Gs empty t T.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T0; simpl in H3; try solve [inversion H3].
    induction d; simpl in H3; try solve [inversion H3].
    unfold open_typ in H3. simpl in H3. inversions H3.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
    unfold open_typ in H3. simpl in H3. inversion H3; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H4; inversion H4; subst.
    assert (ty_trm ty_general Gs empty (open_trm (in_sto x) t1) (open_typ (in_sto x) t0)) as A. {
      rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
      rewrite concat_empty_l in H2.
      eapply subst_ty_trm; eauto.
      simpl. rewrite <- subst_intro_typ with (x:=y).
      lets Htyv: (var_new_typing (@empty typ) Hwf Bis).
      unfold open_typ in Htyv. simpl in Htyv.
      unfold open_typ. apply Htyv.
      eauto.
      apply notin_union_r1 in Fr. apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. apply notin_union_r2 in Fr. apply Fr.
      eauto.
    }
    repeat eexists.
    unfold open_defs. simpl. unfold defs_has. simpl.
    rewrite If_l. reflexivity. reflexivity.
    eapply A.
    assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
  - repeat eexists. eassumption. assumption.
Qed.

Lemma pt_rcd_typ_inversion: forall Gs s x v A S U,
  wf_sto Gs s ->
  binds x v s ->
  possible_types Gs x v (typ_rcd (dec_typ A S U)) ->
  exists T ds T',
    v = val_new T ds /\
    defs_has (open_defs (in_sto x) ds) (def_typ A T') /\
    subtyp ty_general Gs empty S T' /\
    subtyp ty_general Gs empty T' U.
Proof.
  introv Hwf Bis Hp. inversion Hp; subst.
  - induction T; simpl in H3; try solve [inversion H3].
    induction d; simpl in H3; try solve [inversion H3].
    unfold open_typ in H3. simpl in H3. inversions H3.
    lets Hty: (val_new_typing Hwf Bis). inversion Hty; subst.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H3 y FrL).
    unfold open_typ in H3. simpl in H3. inversion H3; subst.
    destruct ds; simpl in H; try solve [inversion H].
    destruct ds; simpl in H; try solve [inversion H].
    unfold open_defs in H. simpl in H. inversions H.
    destruct d0; simpl in H4; inversion H4; subst.
    assert (t2 = t0). {
      apply open_eq_typ with (v:=(in_ctx y)) (x:=y) (i:=0); eauto.
      apply notin_union_r1 in Fr. apply notin_union_r1 in Fr.
      apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. eauto.
    }
    assert (t2 = t1). {
      apply open_eq_typ with (v:=(in_ctx y)) (x:=y) (i:=0); eauto.
      apply notin_union_r1 in Fr. apply notin_union_r1 in Fr.
      apply notin_union_r2 in Fr.
      unfold fv_defs in Fr. eauto.
    }
    subst. subst.
    repeat eexists.
    unfold open_defs. simpl. unfold defs_has. simpl.
    rewrite If_l. reflexivity. reflexivity.
    eapply subtyp_refl. eapply subtyp_refl.
    assert (ty_precise = ty_precise) as Heqm1 by reflexivity.
    specialize (H Heqm1). destruct H. inversion H.
  - repeat eexists. eassumption. eassumption. eassumption.
Qed.

Lemma record_sub_and: forall T T1 T2,
  record_type T ->
  T = typ_and T1 T2 ->
  record_sub T T1 /\ record_sub T T2.
Proof.
  introv Htype Heq. subst.
  destruct Htype as [ls Htyp]. inversion Htyp; subst.
  split.
  - apply rs_drop. apply rs_refl.
  - eapply rs_dropl. apply rs_refl.
Qed.

Lemma record_sub_has: forall T1 T2 D,
  record_has T2 D ->
  record_sub T1 T2 ->
  record_has T1 D.
Proof.
  introv Hhas Hsub. induction Hsub.
  - assumption.
  - inversion Hhas; subst. apply rh_andl.
  - apply rh_and. apply IHHsub. apply Hhas.
  - inversion Hhas; subst.
    + apply rh_andl.
    + apply rh_and. apply IHHsub. assumption.
Qed.

Lemma pt_record_sub_has: forall G x v T1 T2,
  (forall D, record_has T1 D -> possible_types G x v (typ_rcd D)) ->
  record_sub T1 T2 ->
  (forall D, record_has T2 D -> possible_types G x v (typ_rcd D)).
Proof.
  introv HP Hsub. intros D Hhas. apply HP; eauto using record_sub_has.
Qed.

Lemma pt_has_record: forall G x v T,
  (forall D, record_has T D -> possible_types G x v (typ_rcd D)) ->
  record_type T ->
  possible_types G x v T.
Proof.
  introv HP Htype. destruct Htype as [ls Htyp]. induction Htyp.
  - apply HP; eauto. apply rh_one.
  - apply pt_and.
    + apply IHHtyp; eauto.
      intros D0 HH0. apply HP; eauto. apply rh_and; eauto.
    + apply HP; eauto. apply rh_andl.
Qed.

Lemma pt_has_sub: forall G x v T U,
  (forall D, record_has T D -> possible_types G x v (typ_rcd D)) ->
  record_type T ->
  record_sub T U ->
  possible_types G x v U.
Proof.
  introv HP Htype Hsub. induction Hsub.
  - apply pt_has_record; eauto.
  - apply HP; eauto. apply rh_andl.
  - apply IHHsub; eauto. eapply pt_record_sub_has; eauto.
    apply rs_drop. apply rs_refl.
    eapply record_type_sub_closed; eauto.
    apply rs_drop. apply rs_refl.
  - apply pt_and.
    + apply IHHsub; eauto. eapply pt_record_sub_has; eauto.
      apply rs_drop. apply rs_refl.
      eapply record_type_sub_closed; eauto.
      apply rs_drop. apply rs_refl.
    + apply HP; eauto. apply rh_andl.
Qed.

Lemma possible_types_closure_record: forall Gs s x T ds U,
  wf_sto Gs s ->
  binds x (val_new T ds) s ->
  record_sub (open_typ (in_sto x) T) U ->
  possible_types Gs x (val_new T ds) U.
Proof.
  introv Hwf Bis Hsub.
  apply pt_has_sub with (T:=open_typ (in_sto x) T).
  intros D Hhas. eapply pt_rcd_has_piece; eauto.
  apply open_record_type. eapply record_new_typing; eauto. eapply val_new_typing; eauto.
  assumption.
Qed.

Lemma pt_and_inversion: forall Gs s x v T1 T2,
  wf_sto Gs s ->
  binds x v s ->
  possible_types Gs x v (typ_and T1 T2) ->
  possible_types Gs x v T1 /\ possible_types Gs x v T2.
Proof.
  introv Hwf Bis Hp. dependent induction Hp.
  - assert (record_type (open_typ (in_sto x0) T)) as Htype. {
      eapply open_record_type.
      eapply record_new_typing. eapply val_new_typing; eauto.
    }
    destruct (record_sub_and Htype x) as [Hsub1 Hsub2].
    split;
    eapply possible_types_closure_record; eauto.
  - split; assumption.
Qed.

(*
Lemma (Possible types closure)

If G ~ s and G |- x: T and s |- x = v then Ts(G, x, v) is closed wrt G |- _ <: _.

Let SS = Ts(G, x, v). We first show SS is closed wrt G |-# _ <: _.

Assume T0 in SS and G |- T0 <: U0.s We show U0 in SS by an induction on subtyping derivations of G |-# T0 <: U0.
*)

Lemma possible_types_closure_tight: forall Gs s x v T0 U0,
  wf_sto Gs s ->
  binds x v s ->
  possible_types Gs x v T0 ->
  subtyp ty_general Gs empty T0 U0 ->
  possible_types Gs x v U0.
Proof.
  introv Hwf Bis HT0 Hsub. dependent induction Hsub;
  assert (@empty typ ~= @empty typ) as HE by reflexivity.
  - (* Top *) apply pt_top.
  - (* Bot *) inversion HT0; subst.
    lets Htype: (open_record_type (in_sto x) (record_new_typing (val_new_typing Hwf Bis))).
    destruct Htype as [ls Htyp]. rewrite H3 in Htyp. inversion Htyp.
  - (* Refl-<: *) assumption.
  - (* Trans-<: *)
    apply IHHsub2; try assumption.
    apply IHHsub1; assumption.
  - (* And-<: *)
    apply pt_and_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [HT HU].
    assumption.
  - (* And-<: *)
    apply pt_and_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [HT HU].
    assumption.
  - (* <:-And *)
    apply pt_and. apply IHHsub1; assumption. apply IHHsub2; assumption.
  - (* Fld-<:-Fld *)
    apply pt_rcd_trm_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [S [ds [t [Heq [Hhas Hty]]]]].
    subst.
    eapply pt_rcd_trm.
    eassumption.
    apply ty_sub with (T:=T).
    intro Contra. inversion Contra.
    assumption.
    assumption.
  - (* Typ-<:-Typ *)
    apply pt_rcd_typ_inversion with (s:=s) in HT0; eauto.
    destruct HT0 as [T [ds [T' [Heq [Hhas [Hsub1' Hsub2']]]]]].
    subst.
    eapply pt_rcd_typ.
    eassumption.
    eapply subtyp_trans. eassumption. eassumption.
    eapply subtyp_trans. eassumption. eassumption.
  - (* <:-Sel *)
    inversion H; subst. false. eapply empty_middle_inv. eassumption.
  - (* Sel-<: *)
    inversion H; subst. false. eapply empty_middle_inv. eassumption.
  - (* <:-Sel-tight *)
    eapply pt_sel. eassumption. assumption.
  - (* Sel-<:-tight *)
    inversion HT0; subst.
    assert (record_type (open_typ (in_sto x) T0)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H4 in B. destruct B as [? B]. inversion B.
    assert (T = S) as B. {
      eapply unique_tight_bounds; eauto.
    }
    subst. assumption.
  - (* All-<:-All *)
    inversion HT0; subst.
    assert (record_type (open_typ (in_sto x) T)) as B. {
      eapply record_type_new; eassumption.
    }
    rewrite H5 in B. destruct B as [? B]. inversion B.
    apply_fresh pt_lambda as y.
    eapply H3; eauto.
    eapply subtyp_trans. eassumption. eassumption.
    assert (y ~ S2 = empty & (y ~ S2)) as C. {
      rewrite concat_empty_l. eauto.
    }
    eapply subtyp_trans.
    eapply narrow_subtyping. eapply H8; eauto.
    eapply subenv_last_only. eapply Hsub.
    rewrite <- concat_empty_l. eapply ok_push; eauto.
    rewrite C. eapply H; eauto.
  - (* Rec-<:-Rec *)
    admit.
Qed.

(*
Lemma (Possible types completeness for values)

If `G ~ s` and `x = v in s` and  `G |-! v: T` then `T in Ts(G, x, v)`.
 *)

Lemma possible_types_completeness_for_values: forall Gs s x v T,
  wf_sto Gs s ->
  binds x v s ->
  ty_trm ty_precise Gs empty (trm_val v) T ->
  possible_types Gs x v T.
Proof.
  introv Hwf Bis Hty. destruct v as [S ds | S t].
  - apply new_intro_inversion in Hty. destruct Hty as [Heq Htype]. subst.
    eapply pt_bnd. eapply pt_new. reflexivity.
  - remember Hty as Hty'. clear HeqHty'. inversion Hty'; subst.
    + apply all_intro_inversion in Hty. destruct Hty as [T' Heq]. subst.
      apply_fresh pt_lambda as y.
      assert (y ~ S = empty & y ~ S) as A. {
        rewrite concat_empty_l. reflexivity.
      }
      rewrite A. eapply H5; eauto.
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

Lemma possible_types_completeness_tight: forall Gs s x T,
  wf_sto Gs s ->
  ty_trm ty_general Gs empty (trm_var (avar_s x)) T ->
  exists v, binds x v s /\ possible_types Gs x v T.
Proof.
  introv Hwf H. dependent induction H.
  - assert (exists v, binds x v s /\ ty_trm ty_precise Gs empty (trm_val v) T) as A. {
      destruct (ctx_binds_to_sto_binds_raw Hwf H) as [G1 [? [v [? [Bi Hty]]]]].
      exists v. split. apply Bi. subst. rewrite <- concat_assoc.
      eapply weaken_sto_ty_trm. assumption.
      rewrite concat_assoc. eapply wf_sto_to_ok_G. eassumption.
    }
    destruct A as [v [Bis Hty]].
    exists v. split. apply Bis. eapply possible_types_completeness_for_values; eauto.
  - specialize (IHty_trm x Hwf).
    destruct IHty_trm as [v [Bis Hp]].
    eauto. eauto.
    exists v. split. assumption. eapply pt_bnd. eapply Hp. reflexivity.
  - specialize (IHty_trm x Hwf).
    destruct IHty_trm as [v [Bis Hp]]; eauto.
    exists v. split. assumption. inversion Hp; subst.
    + lets Htype: (record_type_new Hwf Bis). rewrite H4 in Htype. inversion Htype. inversion H0.
    + assumption.
  - specialize (IHty_trm1 x Hwf). destruct IHty_trm1 as [v [Bis1 Hp1]]; eauto.
    specialize (IHty_trm2 x Hwf). destruct IHty_trm2 as [v' [Bis2 Hp2]]; eauto.
    unfold binds in Bis1. unfold binds in Bis2. rewrite Bis2 in Bis1. inversions Bis1.
    exists v. split. eauto. apply pt_and; assumption.
  - specialize (IHty_trm x Hwf). destruct IHty_trm as [v [Bis Hp]]; eauto.
    exists v. split. apply Bis. eapply possible_types_closure_tight; eauto.
Qed.

Lemma tight_ty_rcd_typ__new: forall Gs s x A S U,
  wf_sto Gs s ->
  ty_trm ty_general Gs empty (trm_var (avar_s x)) (typ_rcd (dec_typ A S U)) ->
  exists T ds, binds x (val_new T ds) s.
Proof.
  introv Hwf Hty.
  destruct (possible_types_completeness_tight Hwf Hty) as [v [Bis Hpt]].
  inversion Hpt; subst; repeat eexists; eauto.
Qed.

Lemma possible_types_closure: forall Gs s x v S T,
  wf_sto Gs s ->
  binds x v s ->
  possible_types Gs x v S ->
  subtyp ty_general Gs empty S T ->
  possible_types Gs x v T.
Proof.
  intros. eapply possible_types_closure_tight; eauto.
Qed.

Lemma possible_types_completeness: forall Gs s x T,
  wf_sto Gs s ->
  ty_trm ty_general Gs empty (trm_var (avar_s x)) T ->
  exists v, binds x v s /\ possible_types Gs x v T.
Proof.
  intros.
  eapply possible_types_completeness_tight; eauto.
Qed.

Lemma possible_types_lemma: forall Gs s x v T,
  wf_sto Gs s ->
  binds x v s ->
  ty_trm ty_general Gs empty (trm_var (avar_s x)) T ->
  possible_types Gs x v T.
Proof.
  introv Hwf Bis Hty.
  lets A: (possible_types_completeness Hwf Hty).
  destruct A as [v' [Bis' Hp]].
  unfold binds in Bis. unfold binds in Bis'. rewrite Bis' in Bis. inversions Bis.
  assumption.
Qed.

Lemma ctx_binds_to_sto_binds_typing: forall Gs s x T,
  wf_sto Gs s ->
  binds x T Gs ->
  exists v, binds x v s /\ ty_trm ty_precise Gs empty (trm_val v) T.
Proof.
  introv Hwf Bi.
  lets A: (ctx_binds_to_sto_binds_raw Hwf Bi).
  destruct A as [G1 [G2 [v [HeqG [Bis Hty]]]]].
  exists v. split; eauto.
  subst. rewrite <- concat_assoc.
  inversion Hwf; subst.
  apply binds_empty_inv in Bis. inversion Bis.
  eapply weaken_sto_ty_trm. assumption.
  rewrite concat_assoc. eapply wf_sto_to_ok_G. eassumption.
Qed.

(*
Lemma (Canonical forms 1)
If G ~ s and G |- x: all(x: T)U then s(x) = lambda(x: T')t where G |- T <: T' and G, x: T |- t: U.
 *)
Lemma canonical_forms_1: forall Gs s x T U,
  wf_sto Gs s ->
  ty_trm ty_general Gs empty (trm_var (avar_s x)) (typ_all T U) ->
  (exists L T' t, binds x (val_lambda T' t) s /\ subtyp ty_general Gs empty T T' /\
  (forall y, y \notin L -> ty_trm ty_general Gs (y ~ T) (open_trm (in_ctx y) t) (open_typ (in_ctx y) U))).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_sto_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  inversion Hp; subst.
  - lets Htype: (record_type_new Hwf Bis). rewrite H3 in Htype.
    destruct Htype as [ls Htyp]. inversion Htyp.
  - pick_fresh y. exists (dom Gs \u L). exists S0. exists t.
    split. apply Bis. split. assumption.
    intros y0 Fr0.
    eapply ty_sub.
    intros Contra. inversion Contra.
    eapply narrow_typing.
    eapply H1; eauto.
    apply subenv_last_only. apply H5.
    rewrite <- concat_empty_l. apply ok_push; eauto.
    eapply H6; eauto.
Qed.

(*
Lemma (Canonical forms 2)

If G ~ s and G |- x: {a: T} then s(x) = new(x: S)d for some type S, definition d such that G |- d: S and d contains a definition {a = t} where G |- t: T.

*)
Lemma canonical_forms_2: forall Gs s x a T,
  wf_sto Gs s ->
  ty_trm ty_general Gs empty (trm_var (avar_s x)) (typ_rcd (dec_trm a T)) ->
  (exists S ds t, binds x (val_new S ds) s /\ ty_defs Gs empty (open_defs (in_sto x) ds) (open_typ (in_sto x) S) /\ defs_has (open_defs (in_sto x) ds) (def_trm a t) /\ ty_trm ty_general Gs empty t T).
Proof.
  introv Hwf Hty.
  lets Bi: (typing_implies_sto_bound Hty). destruct Bi as [S Bi].
  lets A: (ctx_binds_to_sto_binds_typing Hwf Bi). destruct A as [v [Bis Htyv]].
  lets Hp: (possible_types_lemma Hwf Bis Hty).
  apply pt_rcd_trm_inversion with (s:=s) in Hp; eauto.
  destruct Hp as [S' [ds [t' [Heq [Hdefs Htyd]]]]].
  subst.
  exists S' ds t'.
  split; try split; try split; try assumption.
  eapply new_ty_defs; eauto.
Qed.

(* ###################################################################### *)
(** * Misc *)

Lemma var_typing_implies_avar_f: forall Gs G a T,
  ty_trm ty_general Gs G (trm_var a) T ->
  exists x, a = avar_f x.
Proof.
  intros. dependent induction H; try solve [eexists; reflexivity].
  apply IHty_trm.
Qed.

Lemma var_typing_implies_avar_s: forall Gs v T,
  ty_trm ty_general Gs empty (trm_var (avar_f v)) T ->
  avar_f v = avar_s (var_of v).
Proof.
  intros. dependent induction H; eauto.
  false. apply* binds_empty_inv.
Qed.

Lemma val_typing: forall Gs G v T,
  ty_trm ty_general Gs G (trm_val v) T ->
  exists T', ty_trm ty_precise Gs G (trm_val v) T' /\
             subtyp ty_general Gs G T' T.
Proof.
  intros. dependent induction H.
  - exists (typ_all T U). split.
    apply ty_all_intro with (L:=L); eauto. apply subtyp_refl.
  - exists (typ_bnd T). split.
    apply ty_new_intro with (L:=L); eauto. apply subtyp_refl.
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
  ty_trm ty_general G empty t T ->
  (normal_form t \/ (exists s' t' G' G'', red t s t' s' /\ G' = G & G'' /\ ty_trm ty_general G' empty t' T /\ wf_sto G' s')).
Proof.
  introv Hwf H. dependent induction H; try solve [left; eauto].
  - (* All-E *) right.
    lets Ax: (var_typing_implies_avar_s H).
    lets Az: (var_typing_implies_avar_s H0).
    rewrite Ax in H. rewrite Ax. rewrite Az.
    destruct z as [vz | vz]. simpl.
    lets C: (canonical_forms_1 Hwf H).
    destruct C as [L [T' [t [Bis [Hsub Hty]]]]].
    exists s (open_trm (in_sto vz) t) Gs (@empty typ).
    split.
    apply red_app with (T:=T'). assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    pick_fresh y. assert (y \notin L) as FrL by auto. specialize (Hty y FrL).
    rewrite subst_intro_typ with (x:=y). rewrite subst_intro_trm with (x:=y).
    eapply subst_ty_trm.
    eassumption.
    eapply Hty.
    eauto. eauto.
    rewrite subst_fresh_typ.
    apply ty_sub with (T:=S).
    intro Contra. inversion Contra.
    assumption. apply subtyp_refl.
    eauto. eauto. eauto.
    assumption.
    simpl in Az. unfold avar_s in Az. inversions Az.
  - (* Fld-E *) right.
    lets Ax: (var_typing_implies_avar_s H).
    rewrite Ax in H. rewrite Ax.
    lets C: (canonical_forms_2 Hwf H).
    destruct C as [S [ds [t [Bis [Tyds [Has Ty]]]]]].
    exists s t Gs (@empty typ).
    split.
    apply red_sel with (T:=S) (ds:=ds); try assumption.
    split.
    rewrite concat_empty_r. reflexivity.
    split.
    assumption.
    assumption.
  - (* Let *) right.
    destruct t.
    + (* var *)
      assert (exists x, a = avar_f x) as A. {
        eapply var_typing_implies_avar_f. eassumption.
      }
      destruct A as [x A]. subst a.
      lets Ax: (var_typing_implies_avar_s H).
      rewrite Ax in H. rewrite Ax.
      destruct x as [vx | vx].
      exists s (open_trm (in_sto vx) u) Gs (@empty typ).
      split.
      apply red_let_var.
      split.
      rewrite concat_empty_r. reflexivity.
      split.
      pick_fresh y. assert (y \notin L) as FrL by auto. specialize (H0 y FrL).
      rewrite subst_intro_trm with (x:=y).
      rewrite <- subst_fresh_typ with (x:=y) (y:=(in_sto vx)).
      (*
      eapply subst_ty_trm. eapply H0.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto. eauto.
      rewrite subst_fresh_typ. assumption. eauto. eauto. eauto. eauto.*)
      admit.
      eauto. eauto. eauto.
      simpl in Ax. unfold avar_s in Ax. inversions Ax.
    + lets Hv: (val_typing H).
      destruct Hv as [T' [Htyp Hsub]].
      pick_fresh x. assert (x \notin L) as FrL by auto. specialize (H0 x FrL).
      exists (s & x ~ v) (open_trm (in_sto x) u) (Gs & (x ~ T')) (x ~ T').
      split.
      apply red_let. eauto.
      split. reflexivity. split.
      (*apply narrow_typing with (G:=G & x ~ T).
      assumption.
      apply subenv_last. assumption.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.
      apply ok_push. eapply wf_sto_to_ok_G. eassumption. eauto.*)
      admit.
      apply wf_sto_push. assumption. eauto. eauto. assumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; eauto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply weaken_sto_ty_trm. apply H0. auto.
      eapply wf_sto_to_ok_G. subst. eassumption. eassumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; eauto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply weaken_sto_ty_trm. apply H0. auto.
      eapply wf_sto_to_ok_G. subst. eassumption. eassumption.
    + specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; eauto. inversion IH.
      destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' (trm_let t' u) G' G''.
      split. apply red_let_tgt. assumption.
      split. assumption. split.
      apply ty_let with (L:=L \u dom G') (T:=T); eauto.
      intros. rewrite IH2. eapply weaken_sto_ty_trm. apply H0. auto.
      eapply wf_sto_to_ok_G. subst. eassumption. eassumption.
  - specialize (IHty_trm Hwf). destruct IHty_trm as [IH | IH]; eauto.
    + right. destruct IH as [s' [t' [G' [G'' [IH1 [IH2 [IH3]]]]]]].
      exists s' t' G' G''.
      split; try split; try split; try assumption.
      apply ty_sub with (T:=T).
      intro Contra. inversion Contra.
      assumption.
      rewrite IH2. apply weaken_sto_subtyp. assumption.
      eapply wf_sto_to_ok_G. subst. eassumption.
Qed.