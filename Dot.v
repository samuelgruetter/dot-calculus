Set Implicit Arguments.
Require Import LibLN.

Definition label := var.

Inductive pth : Set :=
  | pth_bvar : nat -> pth
  | pth_fvar : var -> pth
  | pth_sel  : pth -> label -> pth
.

Inductive typ : Set :=
  | typ_asel : pth -> label -> typ
  | typ_csel : pth -> label -> typ
  | typ_rfn  : typ -> list dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_or   : typ -> typ -> typ
  | typ_top  : typ
  | typ_bot  : typ
with cyp : Set :=
  | cyp_csel : pth -> label -> cyp
  | cyp_rfn  : cyp -> list dec -> cyp
  | cyp_and  : cyp -> cyp -> cyp
  | cyp_top  : cyp
with dec : Set :=
  | dec_typ  : label -> typ -> typ -> dec
  | dec_cyp  : label -> cyp -> dec
  | dec_field : label -> typ -> dec
  | dec_method : label -> typ -> typ -> dec
.

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_new  : cyp -> list def -> trm -> trm
  | trm_sel  : trm -> label -> trm
  | trm_call : trm -> label -> trm -> trm
with def : Set :=
  | def_field : label -> trm -> def
  | def_method : label -> trm -> def
.

Fixpoint pth2trm (p: pth) { struct p } : trm :=
  match p with
    | pth_bvar i => trm_bvar i
    | pth_fvar x => trm_fvar x
    | pth_sel p l => trm_sel (pth2trm p) l
  end.

Fixpoint open_rec_pth (k: nat) (u: pth) (p: pth) { struct p } : pth :=
  match p with
  | pth_bvar i => If k = i then u else (pth_bvar i)
  | pth_fvar x => pth_fvar x
  | pth_sel p l => pth_sel (open_rec_pth k u p) l
  end
.

Fixpoint open_rec_typ (k: nat) (u: pth) (t: typ) { struct t } : typ :=
  match t with
  | typ_asel p l => typ_asel (open_rec_pth k u p) l
  | typ_csel p l => typ_csel (open_rec_pth k u p) l
  | typ_rfn  t ds => typ_rfn (open_rec_typ k u t) (List.map (open_rec_dec (S k) u) ds)
  | typ_and t1 t2 => typ_and (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_or t1 t2 => typ_or (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_top => typ_top
  | typ_bot => typ_bot
  end
with open_rec_cyp (k: nat) (u: pth) (c: cyp) { struct c } : cyp :=
  match c with
  | cyp_csel p l => cyp_csel (open_rec_pth k u p) l
  | cyp_rfn  c ds => cyp_rfn (open_rec_cyp k u c) (List.map (open_rec_dec (S k) u) ds)
  | cyp_and c1 c2 => cyp_and (open_rec_cyp k u c1) (open_rec_cyp k u c2)
  | cyp_top => cyp_top
  end
with open_rec_dec (k: nat) (u: pth) (d: dec) { struct d } : dec :=
  match d with
  | dec_typ l ts tu => dec_typ l (open_rec_typ k u ts) (open_rec_typ k u tu)
  | dec_cyp l c => dec_cyp l (open_rec_cyp k u c)
  | dec_field l t => dec_field l (open_rec_typ k u t)
  | dec_method m ts tu => dec_method m (open_rec_typ k u ts) (open_rec_typ k u tu)
  end
.

Fixpoint open_rec_trm (k: nat) (u: pth) (t: trm) { struct t } : trm :=
  match t with
  | trm_bvar i => If k = i then (pth2trm u) else (trm_bvar i)
  | trm_fvar x => trm_fvar x
  | trm_new  c ds t => trm_new (open_rec_cyp k u c) (List.map (open_rec_def (S k) u) ds) (open_rec_trm (S k) u t)
  | trm_sel t l => trm_sel (open_rec_trm k u t) l
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: nat) (u: pth) (d: def) { struct d } : def :=
  match d with
  | def_field l t => def_field l (open_rec_trm k u t)
  | def_method m t => def_method m (open_rec_trm (S k) u t)
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
      (forall x, x \notin L -> List.Forall (fun d => decl (open_dec d (pth_fvar x))) ds) ->
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
      (forall x, x \notin L -> List.Forall (fun d => decl (open_dec d (pth_fvar x))) ds) ->
      cype (cyp_rfn c ds)
  | cype_and : forall c1 c2,
      cype c1 ->
      cype c2 ->
      cype (cyp_and c1 c2)
  | cype_top : cype (cyp_top)
with decl : dec -> Prop :=
  | decl_typ  : forall l ts tu,
      type ts ->
      type tu ->
      decl (dec_typ l ts tu)
  | decl_cyp  : forall l c,
      cype c ->
      decl (dec_cyp l c)
  | decl_field : forall l t,
      type t ->
      decl (dec_field l t)
  | decl_method : forall m ts tu,
      type ts ->
      type tu ->
      decl (dec_method m ts tu)
.

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_new : forall L c ds t,
      cype c ->
      (forall x, x \notin L ->
         List.Forall (fun d => defn (open_def d (pth_fvar x))) ds /\
         term (open_trm t (pth_fvar x))) ->
      term (trm_new c ds t)
  | term_sel : forall t l,
       term t ->
       term (trm_sel t l)
  | term_call : forall o m a,
       term o ->
       term a ->
       term (trm_call o m a)
with defn : def -> Prop :=
  | defn_field : forall l t,
       term t ->
       defn (def_field l t)
  | defn_method : forall L m t,
       (forall x, x \notin L -> term (open_trm t (pth_fvar x))) ->
       defn (def_method m t)
.
