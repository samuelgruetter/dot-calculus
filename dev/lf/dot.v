Set Implicit Arguments.

Require Import LibLN.

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

Inductive ty_trm : tymode -> ctx -> trm -> typ -> Prop :=
| ty_var : forall m G x T,
    binds x T G ->
    ty_trm m G (trm_val (val_var (avar_f x))) T
| ty_all_intro : forall L m G T t U,
    wf_typ G T ->
    (forall x, x \notin L ->
      ty_trm m (G & x ~ T) t (open_typ x U)) ->
    ty_trm m G (trm_val (val_lambda T t)) (typ_all T U)
| ty_all_elim : forall G x z S T,
    ty_trm ty_general G (trm_val (val_var (avar_f x))) (typ_all S T) ->
    ty_trm ty_general G (trm_val (val_var (avar_f z))) S ->
    ty_trm ty_general G (trm_app (avar_f x) (avar_f z)) (open_typ z T)
| ty_new_intro : forall m L G T ds,
    (forall x, x \notin L ->
      wf_typ (G & (x ~ open_typ x T)) (open_typ x T)) ->
    (forall x, x \notin L ->
      ty_defs (G & (x ~ open_typ x T)) (open_defs x ds) (open_typ x T)) ->
    ty_trm m G (trm_val (val_new T ds)) (typ_bnd T)
| ty_new_elim : forall G x m T,
    ty_trm ty_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_trm m T)) ->
    ty_trm ty_general G (trm_sel (avar_f x) m) T
(* | ty_rec_intro (* TODO *) *)
| ty_rec_elim : forall m G x T,
    ty_trm m G (trm_val (val_var (avar_f x))) (typ_bnd T) ->
    ty_trm m G (trm_val (val_var (avar_f x))) (open_typ x T)
| ty_let : forall L G t u T U,
    ty_trm ty_general G t T ->
    (forall x, x \notin L ->
      ty_trm ty_general (G & x ~ T) u U) ->
    wf_typ G U ->
    ty_trm ty_general G (trm_let t u) U
| ty_sub : forall m G t T U,
    ty_trm m G t T ->
    subtyp m G T U ->
    ty_trm m G t U
with ty_def : ctx -> def -> dec -> Prop :=
| ty_def_typ : forall G A T,
    wf_typ G T ->
    ty_def G (def_typ A T) (dec_typ A T T)
| ty_def_trm : forall G a t T,
    ty_trm ty_general G t T ->
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

with subtyp : tymode -> ctx -> typ -> typ -> Prop :=
| subtyp_refl: forall G T,
    subtyp ty_general G T T
| subtyp_trans: forall m G S T U,
    subtyp m G S T ->
    subtyp m G T U ->
    subtyp m G S U
| subtyp_and11: forall m G T U,
    subtyp m G (typ_and T U) T
| subtyp_and12: forall m G T U,
    subtyp m G (typ_and T U) U
| subtyp_and2: forall G S T U,
    subtyp ty_general G S T ->
    subtyp ty_general G S U ->
    subtyp ty_general G S (typ_and T U)
| subtyp_fld: forall G a T U,
    subtyp ty_general G T U ->
    subtyp ty_general G (typ_rcd (dec_trm a T)) (typ_rcd (dec_trm a U))
| subtyp_typ: forall G A S1 T1 S2 T2,
    subtyp ty_general G S2 S1 ->
    subtyp ty_general G T1 T2 ->
    subtyp ty_general G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| subtyp_sel2: forall G x A S T,
    ty_trm ty_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A S T)) ->
    subtyp ty_general G S (typ_sel (avar_f x) A)
| subtyp_sel1: forall G x A S T,
    ty_trm ty_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A S T)) ->
    subtyp ty_general G (typ_sel (avar_f x) A) T
| subtyp_bnd: forall L G T U,
    (forall x, x \notin L ->
       subtyp ty_general (G & x ~ (open_typ x T)) (open_typ x T) (open_typ x U)) ->
    subtyp ty_general G (typ_bnd T) (typ_bnd U)
| subtyp_all: forall L G S1 T1 S2 T2,
    subtyp ty_general G S2 S1 ->
    wf_typ G S2 ->
    (forall x, x \notin L ->
       subtyp ty_general (G & x ~ S2) T1 T2) ->
    subtyp ty_general G (typ_all S1 T1) (typ_all S2 T2)

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
     ty_trm ty_general G (trm_val (val_var (avar_f x))) (typ_rcd (dec_typ A T U)) ->
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