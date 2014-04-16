Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.

(** Utilities **)
(* For some reason,
   the default map on env is opaque, and so
   it cannot be used in recursive definitions. *)
Definition envmap {A B: Type} (f: A -> B) (E: env A): env B :=
  List.map (fun p => (fst p, f (snd p))) E.
Definition EnvForall {A: Type} (P: A -> Prop) (E: env A): Prop :=
  List.Forall (fun p => P (snd p)) E.

(** Syntax **)

Definition label := var.

Inductive avar : Type :=
  | avar_b : nat -> avar
  | avar_f : var -> avar
.

Inductive pth : Type :=
  | pth_var : avar -> pth
  | pth_sel : pth -> label -> pth
.

Inductive typ : Type :=
  | typ_asel : pth -> label -> typ (* select abstract type *)
  | typ_csel : pth -> label -> typ (* select concrete type *)
  | typ_rfn  : typ -> env dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_or   : typ -> typ -> typ
  | typ_top  : typ
  | typ_bot  : typ
with cyp : Type := (* concrete/class type *)
  | cyp_csel : pth -> label -> cyp
  | cyp_rfn  : cyp -> env dec -> cyp
  | cyp_and  : cyp -> cyp -> cyp
  | cyp_top  : cyp
with dec : Type :=
  | dec_typ  : typ -> typ -> dec
  | dec_cyp  : cyp -> dec
  | dec_fld  : typ -> dec
  | dec_mtd  : typ -> typ -> dec
.

Inductive trm : Type :=
  | trm_var  : avar -> trm
  | trm_new  : cyp -> env def -> trm -> trm
  | trm_sel  : trm -> label -> trm
  | trm_cll  : trm -> label -> trm -> trm
with def : Type :=
  | def_fld : avar -> def
  | def_mtd : trm -> def
.

Fixpoint pth2trm (p: pth) { struct p } : trm :=
  match p with
    | pth_var a => trm_var a
    | pth_sel p l => trm_sel (pth2trm p) l
  end.

(* ... opening ...
   replaces in some syntax a bound variable with dangling index (k) by a free variable x
*)

Fixpoint open_rec_avar (k: nat) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end
.

Fixpoint open_rec_pth (k: nat) (u: var) (p: pth) { struct p } : pth :=
  match p with
  | pth_var a => pth_var (open_rec_avar k u a)
  | pth_sel p l => pth_sel (open_rec_pth k u p) l
  end
.

Fixpoint open_rec_typ (k: nat) (u: var) (t: typ) { struct t } : typ :=
  match t with
  | typ_asel p l => typ_asel (open_rec_pth k u p) l
  | typ_csel p l => typ_csel (open_rec_pth k u p) l
  | typ_rfn  t ds => typ_rfn (open_rec_typ k u t) (envmap (open_rec_dec (S k) u) ds)
  | typ_and t1 t2 => typ_and (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_or t1 t2 => typ_or (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_top => typ_top
  | typ_bot => typ_bot
  end
with open_rec_cyp (k: nat) (u: var) (c: cyp) { struct c } : cyp :=
  match c with
  | cyp_csel p l => cyp_csel (open_rec_pth k u p) l
  | cyp_rfn  c ds => cyp_rfn (open_rec_cyp k u c) (envmap (open_rec_dec (S k) u) ds)
  | cyp_and c1 c2 => cyp_and (open_rec_cyp k u c1) (open_rec_cyp k u c2)
  | cyp_top => cyp_top
  end
with open_rec_dec (k: nat) (u: var) (d: dec) { struct d } : dec :=
  match d with
  | dec_typ ts tu => dec_typ (open_rec_typ k u ts) (open_rec_typ k u tu)
  | dec_cyp c => dec_cyp (open_rec_cyp k u c)
  | dec_fld t => dec_fld (open_rec_typ k u t)
  | dec_mtd ts tu => dec_mtd (open_rec_typ k u ts) (open_rec_typ k u tu)
  end
.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var a => trm_var (open_rec_avar k u a)
  | trm_new  c ds t => trm_new (open_rec_cyp k u c) (envmap (open_rec_def (S k) u) ds) (open_rec_trm (S k) u t)
  | trm_sel t l => trm_sel (open_rec_trm k u t) l
  | trm_cll o m a => trm_cll (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: nat) (u: var) (d: def) { struct d } : def :=
  match d with
  | def_fld a => def_fld (open_rec_avar k u a)
  | def_mtd t => def_mtd (open_rec_trm (S k) u t)
  end
.

Definition open_avar a u := open_rec_avar 0 u a.
Definition open_pth p u := open_rec_pth 0 u p.
Definition open_typ t u := open_rec_typ 0 u t.
Definition open_cyp c u := open_rec_cyp 0 u c.
Definition open_dec d u := open_rec_dec 0 u d.
Definition open_trm t u := open_rec_trm 0 u t.
Definition open_def d u := open_rec_def 0 u d.

Inductive fvar : avar -> Prop :=
  | fvar_f : forall x,
      fvar (avar_f x).

Inductive path : pth -> Prop :=
  | path_var : forall a,
      fvar a ->
      path (pth_var a)
  | path_sel : forall p l,
      path p ->
      path (pth_sel p l).

Inductive type : typ -> Prop :=
  | type_asel : forall p l,
      path p ->
      type (typ_asel p l)
  | type_csel : forall p l,
      path p ->
      type (typ_csel p l)
  | type_rfn : forall L t ds,
      type t ->
      (forall x, x \notin L -> EnvForall (fun d => decl (open_dec d x)) ds) ->
      type (typ_rfn t ds)
  | type_and : forall t1 t2,
      type t1 ->
      type t2 ->
      type (typ_and t1 t2)
  | type_or : forall t1 t2,
      type t1 ->
      type t2 ->
      type (typ_or t1 t2)
  | type_top : type (typ_top)
  | type_bot : type (typ_bot)
with cype : cyp -> Prop :=
  | cype_csel : forall p l,
      path p ->
      cype (cyp_csel p l)
  | cype_rfn : forall L c ds,
      cype c ->
      (forall x, x \notin L -> EnvForall (fun d => decl (open_dec d x)) ds) ->
      cype (cyp_rfn c ds)
  | cype_and : forall c1 c2,
      cype c1 ->
      cype c2 ->
      cype (cyp_and c1 c2)
  | cype_top : cype (cyp_top)
with decl : dec -> Prop :=
  | decl_typ  : forall ts tu,
      type ts ->
      type tu ->
      decl (dec_typ ts tu)
  | decl_cyp  : forall c,
      cype c ->
      decl (dec_cyp c)
  | decl_fld : forall t,
      type t ->
      decl (dec_fld t)
  | decl_mtd : forall ts tu,
      type ts ->
      type tu ->
      decl (dec_mtd ts tu)
.

Inductive term : trm -> Prop :=
  | term_var : forall a,
      fvar a ->
      term (trm_var a)
  | term_new : forall L c ds t,
      cype c ->
      (forall x, x \notin L ->
         EnvForall (fun d => defn (open_def d x)) ds /\
         term (open_trm t x)) ->
      term (trm_new c ds t)
  | term_sel : forall t l,
       term t ->
       term (trm_sel t l)
  | term_cll : forall o m a,
       term o ->
       term a ->
       term (trm_cll o m a)
with defn : def -> Prop :=
  | defn_fld : forall a,
       fvar a ->
       defn (def_fld a)
  | defn_mtd : forall L t,
       (forall x, x \notin L -> term (open_trm t x)) ->
       defn (def_mtd t)
.

(** Operational Semantics **)

Definition cds := (cyp * env def) % type.
Definition sto := env cds.

Inductive red : sto -> trm -> sto -> trm -> Prop :=
  (* computation rules *)
  | red_cll : forall s x m y c ds t,
      binds x (c, ds) s ->
      binds m (def_mtd t) ds ->
      red s (trm_cll (trm_var (avar_f x)) m (trm_var (avar_f y))) s (open_trm t y)
  | red_sel : forall s x l c ds y,
      binds x (c, ds) s ->
      binds l (def_fld y) ds ->
      red s (trm_sel (trm_var (avar_f x)) l) s (trm_var y)
  | red_new : forall s c ds t x,
      x # s ->
      red s (trm_new c ds t) (s & x ~ (c, ds)) (open_trm t x)
  (* congruence rules *)
  | red_cll1 : forall s o m a s' o',
      red s o s' o' ->
      red s (trm_cll o m a) s' (trm_cll o' m a)
  | red_cll2 : forall s x m a s' a',
      red s a s' a' ->
      red s (trm_cll (trm_var (avar_f x)) m a) s' (trm_cll (trm_var (avar_f x)) m a')
  | red_sel1 : forall s o l s' o',
      red s o s' o' ->
      red s (trm_sel o l) s' (trm_sel o' l)
.
