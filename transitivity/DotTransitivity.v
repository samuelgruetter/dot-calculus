

Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.

(** Syntax **)

Definition label := var.

(* any var (free or bound) *)
Inductive avar : Type :=
  | avar_b : nat -> avar
  | avar_f : var -> avar
.

(* path *)
Inductive pth : Type :=
  | pth_var : avar -> pth
(*| pth_sel : pth -> label -> pth*)
.

Inductive typ : Type :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_bind : label -> dec -> typ (* { z => one decl } *)
  | typ_asel : pth -> label -> typ (* select on abstract type *)
with dec : Type :=
  | dec_typ  : typ -> typ -> dec
  | dec_fld  : typ -> dec
.

Inductive notsel: typ -> Prop :=
  | notsel_top  : notsel typ_top
  | notsel_bot  : notsel typ_bot
  | notsel_bind : forall l d, notsel (typ_bind l d).


(* ... opening ...
   replaces in some syntax a bound variable with dangling index (k) by a free variable x
*)

Fixpoint open_rec_avar (k: nat) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_pth (k: nat) (u: var) (p: pth) { struct p } : pth :=
  match p with
  | pth_var a => pth_var (open_rec_avar k u a)
(*| pth_sel p l => pth_sel (open_rec_pth k u p) l *)
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (t: typ) { struct t } : typ :=
  match t with
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_bind l d => typ_bind l (open_rec_dec (S k) u d)
  | typ_asel p l => typ_asel (open_rec_pth k u p) l
  end
with open_rec_dec (k: nat) (u: var) (d: dec) { struct d } : dec :=
  match d with
  | dec_typ ts tu => dec_typ (open_rec_typ k u ts) (open_rec_typ k u tu)
  | dec_fld t => dec_fld (open_rec_typ k u t)
  end.

Definition open_avar u a := open_rec_avar 0 u a.
Definition open_pth  u p := open_rec_pth  0 u p.
Definition open_typ  u t := open_rec_typ  0 u t.
Definition open_dec  u d := open_rec_dec  0 u d.


(* ... subtyping ... *)

(* mapping from var to typ_bind (types other than typ_bind are never put into
 the ctx, because we only put self types into the ctx, which are always typ_bind *)
Definition ctx := env typ.

Inductive has : ctx -> pth -> label -> dec -> Prop :=
  | has_var : forall G x l d,
      binds x (typ_bind l d) G ->
      has G (pth_var (avar_f x)) l d.

(* mode = "is transitivity at top level accepted?" *)
Inductive mode : Type := notrans | oktrans.

Inductive subtyp : mode -> ctx -> typ -> typ -> Prop :=
  (* why is there no reflexivity in fsub-mini1h.elf ? *)
  | subtyp_refl : forall G T,
      subtyp notrans G T T
  | subtyp_top : forall G T,
      subtyp notrans G T typ_top
  | subtyp_bot : forall G T,
      subtyp notrans G typ_bot T
  | subtyp_bind : forall G z l d1 d2,
      z # G ->
      subdec oktrans (G & (z ~ (typ_bind l d1))) (open_dec z d1) (open_dec z d2) ->
      subtyp notrans G (typ_bind l d1) (typ_bind l d2)
  | subtyp_asel_l : forall G p L S U T,
      has G p L (dec_typ S U) ->
      subtyp oktrans G U T ->
      subtyp notrans G (typ_asel p L) T
  | subtyp_asel_r : forall G p L S U T,
      has G p L (dec_typ S U) ->
      subtyp oktrans G T S ->
      subtyp notrans G T (typ_asel p L)
  | subtyp_mode : forall G T1 T2,
      subtyp notrans G T1 T2 ->
      subtyp oktrans G T1 T2
  | subtyp_trans : forall G T1 T2 T3,
      subtyp oktrans G T1 T2 ->
      subtyp oktrans G T2 T3 ->
      subtyp oktrans G T1 T3
with subdec : mode -> ctx -> dec -> dec -> Prop :=
  | subdec_typ : forall m G Lo1 Hi1 Lo2 Hi2,
      (* only allow implementable decl *)
      subtyp m G Lo1 Hi1 ->
      subtyp m G Lo2 Hi2 ->
      (* lhs narrower range than rhs *)
      subtyp m G Lo2 Lo1 ->
      subtyp m G Hi1 Hi2 ->
      (* conclusion *)
      subdec m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2)
  | subdec_fld : forall m G T1 T2,
      subtyp m G T1 T2 ->
      subdec m G (dec_fld T1) (dec_fld T2).


(* ... free vars ... *)

Inductive fvar : avar -> Prop :=
  | fvar_f : forall x,
      fvar (avar_f x).

Inductive path : pth -> Prop :=
  | path_var : forall a,
      fvar a ->
      path (pth_var a)
(*| path_sel : forall p l,
      path p ->
      path (pth_sel p l)*).

Inductive type : typ -> Prop :=
  | type_top : type (typ_top)
  | type_bot : type (typ_bot)
  | type_rfn : forall L t l d,
      type t ->
      (forall x, x \notin L -> decl (open_dec x d)) ->
      type (typ_bind l d)
  | type_asel : forall p l,
      path p ->
      type (typ_asel p l)
with decl : dec -> Prop :=
  | decl_typ  : forall ts tu,
      type ts ->
      type tu ->
      decl (dec_typ ts tu)
  | decl_fld : forall t,
      type t ->
      decl (dec_fld t).

Fixpoint fv_avar (a: avar) { struct a } : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_pth (p: pth) { struct p } : vars :=
  match p with
  | pth_var a => fv_avar a
(*| pth_sel p l => fv_pth p*)
  end.

Fixpoint fv_typ (t: typ) { struct t } : vars :=
  match t with
  | typ_top => \{}
  | typ_bot => \{}
  | typ_bind l d => fv_dec d
  | typ_asel p l => fv_pth p
  end
with fv_dec (d: dec) { struct d } : vars :=
  match d with
  | dec_typ ts tu => (fv_typ ts) \u (fv_typ tu)
  | dec_fld t => fv_typ t
  end.


(* ... infrastructure ... *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x        ) in
  let B := gather_vars_with (fun x : var  => \{ x }   ) in
  let C := gather_vars_with (fun x : ctx  => dom x    ) in
  let D := gather_vars_with (fun x : avar => fv_avar x) in
  let E := gather_vars_with (fun x : pth  => fv_pth  x) in
  let F := gather_vars_with (fun x : dec  => fv_dec  x) in
  let G := gather_vars_with (fun x : typ  => fv_typ  x) in
  constr:(A \u B \u C \u D \u E \u F \u G).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Lemma notin_empty: forall z A, z # (@empty A).
Proof.
  intros.
  unfold notin.
  rewrite -> dom_empty.
  rewrite -> in_empty.
  rewrite -> not_False.
  apply I.
Qed.


(* ... examples ... *)

(*    { l1: { l2: Top }} <: { l1: Top }     *)
Definition subtyp_example_1(l1 l2: label): Prop :=
  subtyp notrans empty
    (typ_bind l1 (dec_fld (typ_bind l2 (dec_fld typ_top))))
    (typ_bind l1 (dec_fld typ_top)).

Fact subtyp_example_1_proof: exists l1 l2, subtyp_example_1 l1 l2.
Proof.
  unfold subtyp_example_1.
  pick_fresh l1.
  pick_fresh l2.
  exists l1 l2.
  pick_fresh z.
  apply (@subtyp_bind empty z).
  apply notin_empty.
  apply subdec_fld.
  apply subtyp_mode.
  apply subtyp_top.
Qed.




