Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.

(* Utilities *)
(* For some reason,
   the default map on env is opaque, and so
   it cannot be used in recursive definitions. *)
Definition envmap {A B: Type} (f: A -> B) (E: env A): env B :=
  List.map (fun p => (fst p, f (snd p))) E.
Definition EnvForall {A: Type} (P: A -> Prop) (E: env A): Prop :=
  List.Forall (fun p => P (snd p)) E.

Definition label := var.

Inductive pth : Set :=
  | pth_bvar : nat -> pth
  | pth_fvar : var -> pth
  | pth_sel  : pth -> label -> pth
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
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_new  : cyp -> env def -> trm -> trm
  | trm_sel  : trm -> label -> trm
  | trm_cll  : trm -> label -> trm -> trm
with def : Type :=
  | def_fld : trm -> def
  | def_mtd : trm -> def
.

Fixpoint pth2trm (p: pth) { struct p } : trm :=
  match p with
    | pth_bvar i => trm_bvar i
    | pth_fvar x => trm_fvar x
    | pth_sel p l => trm_sel (pth2trm p) l
  end.

(* Substitutes in path p a bound var with dangling index k by path u. *)
Fixpoint open_rec_pth (k: nat) (u: pth) (p: pth) { struct p } : pth :=
  match p with
  | pth_bvar i => If k = i then u else (pth_bvar i)
  | pth_fvar x => pth_fvar x
  | pth_sel p l => pth_sel (open_rec_pth k u p) l
  end
.

(* Substitutes in type t a bound var with dangling index k by path u. *)
Fixpoint open_rec_typ (k: nat) (u: pth) (t: typ) { struct t } : typ :=
  match t with
  | typ_asel p l => typ_asel (open_rec_pth k u p) l
  | typ_csel p l => typ_csel (open_rec_pth k u p) l
  | typ_rfn  t ds => typ_rfn (open_rec_typ k u t) (envmap (open_rec_dec (S k) u) ds)
  | typ_and t1 t2 => typ_and (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_or t1 t2 => typ_or (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_top => typ_top
  | typ_bot => typ_bot
  end
with open_rec_cyp (k: nat) (u: pth) (c: cyp) { struct c } : cyp :=
  match c with
  | cyp_csel p l => cyp_csel (open_rec_pth k u p) l
  | cyp_rfn  c ds => cyp_rfn (open_rec_cyp k u c) (envmap (open_rec_dec (S k) u) ds)
  | cyp_and c1 c2 => cyp_and (open_rec_cyp k u c1) (open_rec_cyp k u c2)
  | cyp_top => cyp_top
  end
with open_rec_dec (k: nat) (u: pth) (d: dec) { struct d } : dec :=
  match d with
  | dec_typ ts tu => dec_typ (open_rec_typ k u ts) (open_rec_typ k u tu)
  | dec_cyp c => dec_cyp (open_rec_cyp k u c)
  | dec_fld t => dec_fld (open_rec_typ k u t)
  | dec_mtd ts tu => dec_mtd (open_rec_typ k u ts) (open_rec_typ k u tu)
  end
.

(* Substitutes in term t bound var with dangling index k by path u. *)
Fixpoint open_rec_trm (k: nat) (u: pth) (t: trm) { struct t } : trm :=
  match t with
  | trm_bvar i => If k = i then (pth2trm u) else (trm_bvar i)
  | trm_fvar x => trm_fvar x
  | trm_new  c ds t => trm_new (open_rec_cyp k u c) (envmap (open_rec_def (S k) u) ds) (open_rec_trm (S k) u t)
  | trm_sel t l => trm_sel (open_rec_trm k u t) l
  | trm_cll o m a => trm_cll (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: nat) (u: pth) (d: def) { struct d } : def :=
  match d with
  | def_fld t => def_fld (open_rec_trm k u t)
  | def_mtd t => def_mtd (open_rec_trm (S k) u t)
  end
.

Definition open_pth p u := open_rec_pth 0 u p.
Definition open_typ t u := open_rec_typ 0 u t.
Definition open_cyp c u := open_rec_cyp 0 u c.
Definition open_dec d u := open_rec_dec 0 u d.
Definition open_trm t u := open_rec_trm 0 u t.
Definition open_def d u := open_rec_def 0 u d.

Inductive path : pth -> Prop :=
  | path_var : forall x,
      path (pth_fvar x)
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
      (forall x, x \notin L -> EnvForall (fun d => decl (open_dec d (pth_fvar x))) ds) ->
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
      (forall x, x \notin L -> EnvForall (fun d => decl (open_dec d (pth_fvar x))) ds) ->
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
  | term_var : forall x,
      term (trm_fvar x)
  | term_new : forall L c ds t,
      cype c ->
      (forall x, x \notin L ->
         EnvForall (fun d => defn (open_def d (pth_fvar x))) ds /\
         term (open_trm t (pth_fvar x))) ->
      term (trm_new c ds t)
  | term_sel : forall t l,
       term t ->
       term (trm_sel t l)
  | term_cll : forall o m a,
       term o ->
       term a ->
       term (trm_cll o m a)
with defn : def -> Prop :=
  | defn_fld : forall t,
       term t ->
       defn (def_fld t)
  | defn_mtd : forall L t,
       (forall x, x \notin L -> term (open_trm t (pth_fvar x))) ->
       defn (def_mtd t)
.
