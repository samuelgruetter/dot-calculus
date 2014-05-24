

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

Hint Constructors notsel.

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
  (* There's a separate rsdc judgment (reflexive sub-declaration) *)
  | subtyp_refl : forall G T,
      subtyp notrans G T T
  | subtyp_top : forall G T,
      subtyp notrans G T typ_top
  | subtyp_bot : forall G T,
      subtyp notrans G typ_bot T
(*| subtyp_bind : forall L G l d1 d2,
      (forall z, z \notin L ->
        subdec oktrans (G & (z ~ (typ_bind l (open_dec z d1)))) 
                       (open_dec z d1) (open_dec z d2)) ->
      subtyp notrans G (typ_bind l d1) (typ_bind l d2) *)
  | subtyp_bind : forall G l d1 d2,
      (forall z,    ok (G & (z ~ (typ_bind l (open_dec z d1)))) ->
        subdec oktrans (G & (z ~ (typ_bind l (open_dec z d1)))) 
                       (open_dec z d1) (open_dec z d2)) ->
      subtyp notrans G (typ_bind l d1) (typ_bind l d2)
  | subtyp_asel_l : forall G p L S U T,
      has G p L (dec_typ S U) ->
      subtyp oktrans G U T ->
      subtyp notrans G (typ_asel p L) T
  | subtyp_asel_r : forall G p L S U T,
      has G p L (dec_typ S U) ->
      subtyp oktrans G S U -> (* <--- makes proofs a lot easier!! *)
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

Scheme subtyp_mut := Induction for subtyp Sort Prop
with subdec_mut := Induction for subdec Sort Prop.

Combined Scheme subtyp_subdec_mutind from subtyp_mut, subdec_mut.

Hint Constructors subtyp.
Hint Constructors subdec.

(*
Lemma invert_subdec: forall m G d1 d2,
   subdec m G d1 d2 -> (
   (exists Lo1 Hi1 Lo2 Hi2, d1 = (dec_typ Lo1 Hi1) /\ d2 = (dec_typ Lo2 Hi2) /\
     subtyp m G Lo2 Lo1 /\ subtyp m G Hi1 Hi2)
\/ (exists T1 T2, d1 = (dec_fld T1) /\ d2 = (dec_fld T2) /\
     subtyp m G T1 T2)).
Proof.
  intros.
  inversion H.
  left. exists Lo1 Hi1 Lo2 Hi2. subst. auto.
  right. exists T1 T2. subst. auto.
Qed.
*)

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

(* not needed
Lemma notin_empty: forall z A, z # (@empty A).
Proof.
  intros.
  unfold notin.
  rewrite -> dom_empty.
  rewrite -> in_empty.
  rewrite -> not_False.
  apply I.
Qed. *)


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
  apply (@subtyp_bind empty).
  intros.
  apply subdec_fld.
  apply subtyp_mode.
  apply subtyp_top.
Qed.


(* ... transitivity in oktrans mode (trivial) ... *)

Lemma subtyp_trans_oktrans: forall G T1 T2 T3,
  subtyp oktrans G T1 T2 -> subtyp oktrans G T2 T3 -> subtyp oktrans G T1 T3.
Proof.
  introv H12 H23.
  apply (subtyp_trans H12 H23).
Qed.

Lemma subdec_trans_oktrans: forall G d1 d2 d3,
  subdec oktrans G d1 d2 -> subdec oktrans G d2 d3 -> subdec oktrans G d1 d3.
Proof.
  introv H12 H23.
  destruct d2 as [Lo2 Hi2 | T2].
  (* case typ *)
  inversion H12 as [? ? Lo1 Hi1 ?   ?   HLo1Hi1 HLo2Hi2 HLo2Lo1 HHi1Hi2 | ]; subst.
  inversion H23 as [? ? ?   ?   Lo3 Hi3 ?       HLo3Hi3 HLo3Lo2 HHi2Hi3 | ]; subst.
  apply (subdec_typ HLo1Hi1 HLo3Hi3
    (subtyp_trans_oktrans HLo3Lo2 HLo2Lo1)
    (subtyp_trans_oktrans HHi1Hi2 HHi2Hi3)
  ).
  (* case fld *)
  inversion H12 as [ | ? ? T1 ? HT12 ]; subst.
  inversion H23 as [ | ? ? ? T3 HT23 ]; subst.
  apply subdec_fld.
  apply (subtyp_trans HT12 HT23).
Qed.


(* ... helper lemmas ... *)

Lemma has_unique: forall G p X d1 d2, 
  has G p X d1 -> has G p X d2 -> d1 = d2.
Proof.
  introv H1 H2.
  inversion H1. inversion H2. subst.
  injection H8.
  intro; subst.
  assert (typ_bind X d1 = typ_bind X d2) by apply (binds_func H H6).
  injection H0.
  trivial.
Qed.

(* "reflexive subdec", just subdec+reflexivity *)
Definition rsubdec(G: ctx)(d1 d2: dec): Prop :=
  d1 = d2 \/ subdec oktrans G d1 d2.

(* Lemma subdec_refl: forall m G d, subdec m G d d. (* not true if Lo >: Hi *) *)

(* Lemma invert_subtyp_bot: forall m G T, subtyp m G T typ_bot -> T = typ_bot.
   Does not hold because T could be a p.L with lower and upper bound bottom. *)

(* ... weakening lemmas ... *)

Lemma narrow_has: forall G1 G2 z l d1 d2 p L dB,
  ok             (G1 & z ~ typ_bind l d2 & G2) ->
  has            (G1 & z ~ typ_bind l d2 & G2) p L dB ->
  subdec oktrans (G1 & z ~ typ_bind l d1     ) d1 d2 ->
  exists dA, 
    rsubdec (G1 & z ~ typ_bind l d1     ) dA dB 
    /\ has  (G1 & z ~ typ_bind l d1 & G2) p L dA.
Proof.
  introv Hokd2 Hhas Hsd.
  set (Hokd1 := (ok_middle_change (typ_bind l d1) Hokd2)).
  inversion Hhas; unfold rsubdec; subst.
  destruct (classicT (x = z)) as [Heq|Hne].
  (* case x = z *)
  subst.
  set (Heq := (binds_middle_eq_inv H Hokd2)).
  inversion Heq; subst.
  exists d1.
  split.
  right. apply Hsd.
  apply has_var.
  destruct (ok_middle_inv Hokd2) as [_ HzG2].
  apply (binds_middle_eq  _ _ HzG2).  
  (* case x <> z*)
  assert (Hxz: x # z ~ typ_bind l d2).
  unfold notin.
  rewrite -> dom_single. 
  rewrite -> in_singleton.
  assumption.
  assert (HG: binds x (typ_bind L dB) (G1 & G2)).
  apply (binds_remove H Hxz).
  exists dB.
  split. left. trivial.  
  assert (HGz: binds x (typ_bind L dB) (G1 & z ~ typ_bind l d1 & G2)).
  apply (@binds_weaken typ x (typ_bind L dB) G1 (z ~ typ_bind l d1) G2 HG Hokd1).
  apply (has_var HGz).
Qed.

Print Assumptions narrow_has.

Lemma ok_remove_2nd_of_4: forall A G1 G2 G3 G4,
  @ok A (G1 & G2 & G3 & G4) -> ok (G1 & G3 & G4).
Proof.
  intros.
  rewrite <- concat_assoc.
  apply ok_remove with (F := G2).
  rewrite -> concat_assoc.
  assumption.
Qed.

Lemma ok_remove_3rd_of_4: forall A G1 G2 G3 G4,
  @ok A (G1 & G2 & G3 & G4) -> ok (G1 & G2 & G4).
Proof.
  intros.
  apply ok_remove with (F := G3).
  assumption.
Qed.

Lemma weaken_has: forall G1 G2 G3 p L d,
  ok             (G1 & G2 & G3) ->
  has            (G1      & G3) p L d ->
  has            (G1 & G2 & G3) p L d.
Proof.
  introv Hok Hhas.
  inversion Hhas; subst.
  apply has_var.
  apply binds_weaken; assumption.
Qed.

Lemma subtyp_weaken: forall G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp oktrans (G1      & G3) S U ->
  subtyp oktrans (G1 & G2 & G3) S U.
Proof.
  fix IHst 7 with
   (IHsd G1 G2 G3 d1 d2
     (Hok: ok (G1 & G2 & G3))
     (Hsd: subdec oktrans (G1      & G3) d1 d2) {struct Hsd}:
           subdec oktrans (G1 & G2 & G3) d1 d2);
  introv Hok Hst;
  inversion Hst; subst.

  (* subtyp *)
  inversion H; subst.
  (* case refl *)
  apply (subtyp_mode (subtyp_refl _ _)).
  (* case top *)
  apply (subtyp_mode (subtyp_top _ _)).
  (* case bot *)
  apply (subtyp_mode (subtyp_bot _ _)).
  (* case bind *)
  assert (H02: forall z : var,
     ok (G1 & G2 & G3 & z ~ typ_bind l (open_dec z d1)) ->
     subdec oktrans (G1 & G2 & G3 & z ~ typ_bind l (open_dec z d1)) 
                    (open_dec z d1) (open_dec z d2)).
  intros.
  specialize (H0 z (ok_remove_2nd_of_4 H1)).
  rewrite <- concat_assoc in H0.
  rewrite <- concat_assoc in H1.
  rewrite <- concat_assoc.
  apply (IHsd _ _ _ _ _ H1 H0).
  apply (subtyp_mode (@subtyp_bind (G1 & G2 & G3) l d1 d2 H02)).
  (* case asel_l *)
  apply subtyp_mode.
  apply subtyp_asel_l with (S := S0) (U := U0).
  apply weaken_has; assumption.
  apply IHst; assumption.
  (* case asel_r *)
  apply subtyp_mode.
  apply subtyp_asel_r with (S := S0) (U := U0).
  apply weaken_has; assumption.
  apply IHst; assumption.
  apply IHst; assumption.
  (* case trans *)
  apply subtyp_trans with (T2 := T2); 
    apply IHst; assumption.

  (* subdec *)
  (* case subdec_typ *)
  apply subdec_typ; apply IHst; assumption.
  (* case subdec_fld *)
  apply subdec_fld; apply IHst; assumption.
Qed.

Lemma env_add_empty: forall (P: ctx -> Prop) (G: ctx), P G -> P (G & empty).
Proof.
  intros.
  assert ((G & empty) = G) by apply concat_empty_r.
  rewrite -> H0. assumption.
Qed.  

Lemma env_remove_empty: forall (P: ctx -> Prop) (G: ctx), P (G & empty) -> P G.
Proof.
  intros.
  assert ((G & empty) = G) by apply concat_empty_r.
  rewrite <- H0. assumption.
Qed.

Lemma subtyp_weaken_2: forall G1 G2 S U,
  ok (G1 & G2) -> 
  subtyp oktrans G1        S U ->
  subtyp oktrans (G1 & G2) S U.
Proof.
  introv Hok Hst.
  apply (env_remove_empty (fun G0 => subtyp oktrans G0 S U) (G1 & G2)).
  apply subtyp_weaken.
  apply (env_add_empty (fun G0 => ok G0) (G1 & G2) Hok).
  apply (env_add_empty (fun G0 => subtyp oktrans G0 S U) G1 Hst).
Qed.

Lemma subdec_narrow: forall G1 G2 z l d1 d2 dA dB,
  ok             (G1 & z ~ typ_bind l d2 & G2) ->
  subdec oktrans (G1 & z ~ typ_bind l d2 & G2) dA dB ->
  subdec oktrans (G1 & z ~ typ_bind l d1     ) d1 d2 ->
  subdec oktrans (G1 & z ~ typ_bind l d1 & G2) dA dB.
Proof.
  fix IHsd 10 with
   (IHst G1 G2 z l d1 d2 TA TB 
     (Hok: ok             (G1 & z ~ typ_bind l d2 & G2))
     (Hst: subtyp oktrans (G1 & z ~ typ_bind l d2 & G2) TA TB) {struct Hst}:
     subdec oktrans (G1 & z ~ typ_bind l d1     ) d1 d2 ->
     subtyp oktrans (G1 & z ~ typ_bind l d1 & G2) TA TB);
  introv Hokd2 Hsub HG; 
  set (Hokd1 := (ok_middle_change (typ_bind l d1) Hokd2));
  inversion Hsub; subst.

  (* subdec *)
  (* case subdec_typ *)
  apply (subdec_typ (IHst _ _ _ _ _ _ _ _ Hokd2 H  HG) 
                    (IHst _ _ _ _ _ _ _ _ Hokd2 H0 HG)
                    (IHst _ _ _ _ _ _ _ _ Hokd2 H1 HG)
                    (IHst _ _ _ _ _ _ _ _ Hokd2 H2 HG)).
  (* case subdec_fld *)
  apply (subdec_fld (IHst _ _ _ _ _ _ _ _ Hokd2 H HG)).

  (* subtyp *)
  inversion H; subst.
  (* case refl *)
  apply (subtyp_mode (subtyp_refl _ _)).
  (* case top *)
  apply (subtyp_mode (subtyp_top _ _)).
  (* case bot *)
  apply (subtyp_mode (subtyp_bot _ _)).
  (* case bind *)
  assert (Hb: forall z0 : var,
     ok (G1 & z ~ typ_bind l d1 & G2 & z0 ~ typ_bind l0 (open_dec z0 d0)) ->
     subdec oktrans
       (G1 & z ~ typ_bind l d1 & G2 & z0 ~ typ_bind l0 (open_dec z0 d0))
       (open_dec z0 d0) (open_dec z0 d3)).
  introv Hok.
  rewrite <- concat_assoc in Hok.
  specialize (H0 z0).
  rewrite <- concat_assoc in H0.
  set (Hok' := (ok_middle_change (typ_bind l d2) Hok)).
  set (Hsd := (H0 Hok')).
  rewrite <- concat_assoc.
  apply (IHsd _ _ _ _ _ _ _ _ Hok' Hsd HG).
  apply (subtyp_mode (subtyp_bind _ _ Hb)).
  (* case asel_l *)
  set (H1w := (IHst _ _ _ _ _ _ _ _ Hokd2 H1 HG)).
  destruct (narrow_has Hokd2 H0 HG) as [dA [[Heq | Hsd] Hhas]].
    (* case = *)
    subst.
    apply (subtyp_mode (subtyp_asel_l Hhas H1w)).
    (* case subdec *)
    inversion Hsd; subst.
    assert (H10' : subtyp oktrans (G1 & z ~ typ_bind l d1 & G2) Hi1 U)
      by apply (subtyp_weaken_2 Hokd1 H10).
    apply (subtyp_mode (subtyp_asel_l Hhas (subtyp_trans H10' H1w))).
  (* case asel_r *)
  set (H1w := (IHst _ _ _ _ _ _ _ _ Hokd2 H1 HG)).
  set (H2w := (IHst _ _ _ _ _ _ _ _ Hokd2 H2 HG)).
  destruct (narrow_has Hokd2 H0 HG) as [dA [[Heq | Hsd] Hhas]].
    (* case = *)
    subst.
    apply (subtyp_mode (subtyp_asel_r Hhas H1w H2w)).
    (* case subdec *)
    inversion Hsd; subst.
    assert (H10' : subtyp oktrans (G1 & z ~ typ_bind l d1 & G2) S Lo1)
      by apply (subtyp_weaken_2 Hokd1 H10).
    assert (H5' : subtyp oktrans (G1 & z ~ typ_bind l d1 & G2) Lo1 Hi1)
      by apply (subtyp_weaken_2 Hokd1 H5).
    apply (subtyp_trans H2w (subtyp_mode (subtyp_asel_r Hhas H5' H10'))).
  (* case trans *)
  set (Hw := (IHst _ _ _ _ _ _ _ _ Hokd2 H HG)).
  set (H0w := (IHst _ _ _ _ _ _ _ _ Hokd2 H0 HG)).
  apply (subtyp_trans Hw H0w).
Qed.

Lemma subdec_narrow_last: forall G z l d1 d2 dA dB,
  ok             (G & z ~ typ_bind l d2) ->
  subdec oktrans (G & z ~ typ_bind l d2) dA dB ->
  subdec oktrans (G & z ~ typ_bind l d1) d1 d2 ->
  subdec oktrans (G & z ~ typ_bind l d1) dA dB.
Proof.
  introv Hok HAB H12.
  apply (env_remove_empty (fun G0 => subdec oktrans G0 dA dB) (G & z ~ typ_bind l d1)).
  apply subdec_narrow with (d2 := d2).
  apply (env_add_empty (fun G0 => ok G0) (G & z ~ typ_bind l d2) Hok).
  apply (env_add_empty (fun G0 => subdec oktrans G0 dA dB)
                             (G & z ~ typ_bind l d2) HAB).
  assumption.
Qed.

Print Assumptions subdec_narrow_last.

(* ... transitivity in notrans mode, but no p.L in middle ... *)

Lemma subtyp_trans_notrans: forall G T1 T2 T3,
  ok G -> notsel T2 -> subtyp notrans G T1 T2 -> subtyp notrans G T2 T3 -> 
  subtyp notrans G T1 T3.
Proof.
  introv Hok Hnotsel H12 H23.

  inversion Hnotsel (*as [ | | l d2]*); subst.
  (* case top *)
  skip.
  (* case bot *)
  skip. 
  (* case bind *)
  inversion H12; inversion H23; subst; (
    assumption ||
    apply subtyp_refl ||
    apply subtyp_top ||
    apply subtyp_bot ||
    idtac
  ).

  (* bind <: bind <: bind *)
  apply subtyp_bind.
  introv Hok'.
  specialize (H3 z Hok').
  assert (Hok'': ok (G & z ~ typ_bind l (open_dec z d))).
  skip.
  specialize (H7 z Hok'').
  assert (H7': subdec oktrans (G & z ~ typ_bind l (open_dec z (*->*)d1(*<-*))) 
                              (open_dec z d) (open_dec z d3)).
  apply (subdec_narrow_last Hok'' H7 H3).
  apply (subdec_trans_oktrans H3 H7').

  (* bind <: bind <: sel  *)
  assert (H1S: subtyp oktrans G (typ_bind l d1) S).
  apply (subtyp_trans_oktrans (subtyp_mode H12) H6).
  apply (subtyp_asel_r H4 H5 H1S).

  (* sel  <: bind <: bind *)
  assert (HU2: subtyp oktrans G U (typ_bind l d2)).
  apply (subtyp_trans_oktrans H0 (subtyp_mode H23)).
  apply (subtyp_asel_l H HU2). 

  (* sel  <: bind <: sel  *)
  assert (H1S0: subtyp oktrans G (typ_asel p L) S0).
  apply (subtyp_trans_oktrans (subtyp_mode H12) H6).
  apply (subtyp_asel_r H1 H5 H1S0).
Qed.

(*
(notransl G A B) means that there exists a notrans-subtyping chain/list
    A <: T1 <: T2 <: ... <: TN <: B
where no Ti is a p.L
)
Inductive notransl: ctx -> typ -> typ -> Prop :=
  | notransl_nil : forall G A B,
      (* could also just have reflexivity here, but having a subtyp makes 
      top/bot cases easier *)
      subtyp notrans G A B ->
      notransl G A B
  | notransl_cons : forall G A T1 B,
      subtyp notrans G A T1 ->
      notsel T1 ->
      notransl G T1 B ->
      notransl G A B.
*)

(* 
(follow_ub G p1.X1 T) means that there exists a chain
  (p1.X1: _ .. p2.X2), (p2.X2: _ .. p3.X3), ... (pN.XN: _ .. T)
which takes us from p1.X1 to T
*)
Inductive follow_ub : ctx -> typ -> typ -> Prop :=
  | follow_ub_nil : forall G T,
      follow_ub G T T
  | follow_ub_cons : forall G p X Lo Hi T,
      has G p X (dec_typ Lo Hi) ->
      follow_ub G Hi T ->
      follow_ub G (typ_asel p X) T.

(*
(follow_lb G T pN.XN) means that there exists a chain
  (p1.X1: T .. _), (p2.X2: p1.X1 .. _), (p3.X3: p2.X2 .. _),  (pN.XN: pN-1.XN-1 .. _)
which takes us from T to pN.XN
*)
Inductive follow_lb: ctx -> typ -> typ -> Prop :=
  | follow_lb_nil : forall G T,
      follow_lb G T T
  | follow_lb_cons : forall G p X Lo Hi U,
      has G p X (dec_typ Lo Hi) ->
      subtyp oktrans G Lo Hi -> (* <-- realizable bounds *)
      follow_lb G (typ_asel p X) U ->
      follow_lb G Lo U.

Hint Constructors follow_ub.
Hint Constructors follow_lb.

Lemma invert_follow_lb: forall G T1 T2,
  follow_lb G T1 T2 -> 
  T1 = T2 \/ 
    exists p1 X1 p2 X2 Hi, (typ_asel p2 X2) = T2 /\
      has G p1 X1 (dec_typ T1 Hi) /\
      subtyp oktrans G T1 Hi /\
      follow_lb G (typ_asel p1 X1) (typ_asel p2 X2).
Proof.
  intros.
  induction H.
  auto.
  destruct IHfollow_lb as [IH | IH].
  subst.
  right. exists p X p X Hi. auto.
  right.
  destruct IH as [p1 [X1 [p2 [X2 [Hi' [Heq [IH1 [IH2 IH3]]]]]]]].
  subst.  
  exists p X p2 X2 Hi.
  auto.
Qed.

Lemma invert_follow_lb_OLD: forall G T1 T2,
  follow_lb G T1 T2 -> 
  T1 = T2 \/ exists p2 X2, (typ_asel p2 X2) = T2.
Proof.
  intros.
  induction H.
  auto.
  destruct IHfollow_lb as [IH | IH].
  subst.
  right. exists p X. trivial.
  right. assumption.
Qed.

(* not needed because inversion is smart enough
Lemma invert_follow_ub: forall G T1 T2,
  follow_ub G T1 T2 ->
  T1 = T2 \/ exists p1 X1, (typ_asel p1 X1) = T1.
Proof.
  intros.
  inversion H; subst.
  auto.
  right. exists p X. trivial.
Qed.*)

Lemma follow_ub_top: forall G T, follow_ub G typ_top T -> T = typ_top.
Proof.
  intros.
  inversion H.
  trivial.
Qed.

Lemma follow_ub_bind: forall G l d T, 
  follow_ub G (typ_bind l d) T -> T = (typ_bind l d).
Proof.
  intros.
  inversion H.
  trivial.
Qed.

(*
Lemma follow_ub_bot: forall G T,
  follow_ub G T typ_bot -> T = typ_bot.
does not hold (can have a p.X:bot..bot, and follow_ub_nil bot) 
*)

(*
Inductive st_middle: ctx -> typ -> typ -> Prop :=
  | st_middle_0: forall G T,
      st_middle G T T
  | st_middle_1: forall G T1 T2,
      notsel T1 ->
      subtyp notrans G T1 T2 ->
      st_middle G T1 T2.
*)


Definition st_middle (G: ctx) (B C: typ): Prop :=
  B = C \/ (notsel B /\ notsel C /\ subtyp notrans G B C).


(* linearize a derivation that uses transitivity *)

Definition chain (G: ctx) (A D: typ): Prop :=
   (exists B C, follow_ub G A B /\ st_middle G B C /\ follow_lb G C D).

Lemma empty_chain: forall G T, chain G T T.
Proof.
  intros.
  unfold chain. unfold st_middle.
  exists T T.
  auto.
Qed.


Lemma chain3subtyp: forall G C1 C2 D, 
  subtyp notrans G C1 C2 ->
  follow_lb G C2 D -> 
  subtyp notrans G C1 D.
Proof.
  introv Hst Hflb.
  induction Hflb.
  assumption.
  apply IHHflb.
  apply (subtyp_asel_r H H0 (subtyp_mode Hst)).
Qed.

Lemma chain2subtyp: forall G B1 B2 C D,
  ok G ->
  subtyp notrans G B1 B2 ->
  st_middle G B2 C ->
  follow_lb G C D ->
  subtyp notrans G B1 D.
Proof.
  introv Hok Hst Hm Hflb.
  inversion Hm; subst.
  apply (chain3subtyp Hst Hflb).
  destruct H as [H1 [H2 H3]].
  apply (chain3subtyp (subtyp_trans_notrans Hok H1 Hst H3) Hflb).
Qed.


Lemma chain1subtyp: forall G A B C D,
  ok G ->
  follow_ub G A B ->
  st_middle G B C ->
  follow_lb G C D ->
  subtyp notrans G A D.
Proof.
  introv Hok Hfub Hm Hflb.
  induction Hfub.
  apply (chain2subtyp Hok (subtyp_refl G T) Hm Hflb).
  apply (subtyp_asel_l H).
  apply subtyp_mode.
  apply (IHHfub Hok Hm Hflb).
Qed.


Lemma chain1subtyp: forall G A1 A2 B C D,
  ok G ->
  subtyp notrans G A1 A2 ->
  follow_ub G A2 B ->
  st_middle G B C ->
  follow_lb G C D ->
  subtyp notrans G A1 D.
Proof.
  fix 9.
  introv Hok Hst Hfub Hm Hflb.
  inversion Hfub; subst.
  (* base *)
  apply (chain2subtyp Hok Hst Hm Hflb).
  (* step *)
  


  introv Hok Hst Hfub Hm Hflb.
  induction Hfub.
  apply (chain2subtyp Hok Hst Hm Hflb).
  inversion Hm; subst.
  apply (IHHfub Hok).
  apply (

Qed.


  introv Hok Hst Hfub Hm Hflb.
  induction Hfub.
  apply (chain2subtyp Hok Hst Hm Hflb).
  apply (IHHfub Hok). clear IHHfub.
  inversion Hst; subst.
  apply (subtyp_asel_l H (subtyp_mode (subtyp_refl _ _))).
  apply (subtyp_bot _ _). 
  skip.
  assumption.
  assumption.
Qed.
  

Lemma chain2subtyp: forall G A1 A2 D, 
  subtyp notrans G A1 A2 ->
  chain G A2 D -> 
  subtyp notrans G A1 D.
Proof.
  fix 6.
  introv Hst Hch.
  unfold chain in *. unfold st_middle in *.
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]];
    destruct Hch2 as [Hch2 | [Hch2a [Hch2b Hch2c]]];
    inversion Hch1;
    (*destruct (invert_follow_lb Hch3) as [Heq | [pD [XD Heq]]]; *)
    destruct (invert_follow_lb Hch3) as 
      [Heq | [p1 [X1 [p2 [X2 [U [Heq [Hch3a [Hch3b Hch3c]]]]]]]]];
    inversion Hst;
    subst;
    auto.
  
  set (Hst' := (subtyp_asel_r Hch3a Hch3b (subtyp_mode (subtyp_refl _ _)))).
  apply (chain2subtyp G C (typ_asel p1 X1) (typ_asel p2 X2) Hst').
  Guarded.

  exists (typ_asel p1 X1) (typ_asel p1 X1).
  Guarded.
  split. auto. Guarded.
  auto.
  

  Guarded.
  
exists C (typ_asel p1 X1).
  Check (subtyp_asel_r Hch3a Hch3b (subtyp_mode (subtyp_refl _ _))).


skip.

  apply (subtyp_asel_l H2).


  apply (chain2subtyp G C D).
  exists C C.
  auto. Guarded.
  exists (typ_asel p X) (typ_asel p X).
  
  apply (subtyp_asel_l H2).


  Guarded.
*)

(*
Lemma notransl_head: forall G A C,
  notransl G A C ->
  (exists B, notsel B /\ subtyp notrans G A B /\ notransl G B C) \/
  (subtyp notrans G A C).
Proof.
  introv Hn.
  inversion Hn; subst.
  (* case notransl_nil *)
  right. assumption.
  (* case notransl_cons *)
  left.
  exists T1. auto.
Qed.
*)
(*
Lemma notransl_asel_head: forall G p L C S U, 
  notransl G (typ_asel p L) C ->
  has G p L (dec_typ S U) ->
  (notransl G U C \/ C = (typ_asel p L)).
Proof.
  introv Hn Hh.
  inversion Hn; subst.
  (* case notransl_nil *)
  inversion H; subst.
  right. trivial.
  left. apply (notransl_nil (subtyp_top _ _)).
  skip.
  skip.
  (* case notransl_cons *)
  inversion H; subst.
*)  

(* prepend an oktrans to chain ("utrans0*") *)
Lemma prepend_chain: forall G A1 A2 D,
  ok G ->
  subtyp oktrans G A1 A2 ->
  chain G A2 D ->
  chain G A1 D.
Proof.
  fix 6.
  introv Hok Hokt Hch.
  unfold chain in *. unfold st_middle in *.
  inversion Hokt; inversion H; subst.
  (* case refl *)
  assumption.
  (* case top *)
  (*
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  exists A1 C.
  split. apply follow_ub_nil.
  apply follow_ub_top in Hch1. subst.
  split. apply (subtyp_trans_notrans Hok notsel_top H Hch2).
  apply Hch3.
  *)
  skip.
  (* case bot *)
  (*
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  exists typ_bot C.
  split. apply follow_ub_nil.
  split. apply (subtyp_bot G C).
  apply Hch3.
  *)
  skip.
  (* case bind *)
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  assert (B = typ_bind l d2) by apply (follow_ub_bind Hch1); subst.
  exists (typ_bind l d1) C.
  destruct Hch2 as [Hch2 | [Hch2a [Hch2b Hch2c]]].
  subst.
  split. auto.
  split; auto.
  set (Hst := (subtyp_trans_notrans Hok (notsel_bind _ _) H Hch2c)).
  split. auto.
  split; auto.
  (* case asel_l *)
  set (IH := (prepend_chain G U A2 D Hok H4 Hch)).
  destruct IH as [B [C [IH1 [IH2 IH3]]]].
  exists B C.
  split. 
  apply (follow_ub_cons H0 IH1).
  split; assumption.
  (* case asel_r *) 
  set (Hch' := Hch).
  destruct Hch' as [B [C [Hch1 [Hch2 Hch3]]]].
  inversion Hch1; subst.
    (* case follow_ub_nil *)
    destruct Hch2 as [Hch2 | [Hch2a [Hch2b Hch2c]]].
    subst.
    apply (prepend_chain G A1 S D Hok H5).
    exists S S. 
    set (Hflb := (follow_lb_cons H0 H4 Hch3)).
    auto.
    inversion Hch2a. (* contradiction *)
    (* case follow_ub_cons *)
    apply (prepend_chain G A1 S D Hok H5).
    apply (prepend_chain G S U D Hok H4).
    assert (HdecEq: dec_typ Lo Hi = dec_typ S U) by apply (has_unique H6 H0).
    injection HdecEq; intros; subst.
    exists B C.
    split. assumption. split. assumption. assumption.
  (* case mode *)
  apply (prepend_chain G _ _ _ Hok H (prepend_chain G _ _ _ Hok H0 Hch)).
  (* case trans *)
  apply (prepend_chain G _ _ _ Hok H (prepend_chain G _ _ _ Hok H0 Hch)).
Qed.

Print Assumptions prepend_chain.

  (* subtyp cases: *)
  (* case refl *)
  skip.
  (* case top *)
  skip.
  (* case bot *)
  skip.
  (* case bind *)
  skip.
  (* case asel_l *)
  skip.
  (* case asel_r *)
  skip.
  (* case trans *)
  skip.





  (* try to make a follow_lb_cons *)
    (* A2 = p.L, problem: need to have p.L = start of follow_lb list, no 
       subtyp notrans stuff in middle *)
    (* "valid middles":
          B=C
          subtyp notrans G B_notsel C
          --> doesn't work too well either
          --> chain1, chain2, chain3 approach
    *)
    skip.
    (*
    destruct C as [| | l d | pC LC].
      (* case top *)
      exists A1 typ_top. auto.
      (* case bot *)
      (* inversion Hch2; inversion H7; subst.*)
      skip.
      (* case bind *)
      skip.
      (* case asel *)
      inversion Hch3; subst.
        (* case follow_lb_nil *)
        skip.
        (* case follow_lb_cons *)
    skip. skip. skip. skip.
    *)
    (*
    inversion Hch3; subst.
    (* case nil *)
    exists S D.
    assert (subtyp notrans G S D).
    apply (subtyp_asel
    
    (* case cons *)
    exists S S.
    *)
    (*
    inversion Hch2; subst.
      (* case refl *)
      apply (prepend_chain G A1 S D H5).
      exists S S.
      assert (follow_lb G S D). apply (follow_lb_cons H0 Hch3). auto.
      (* case top *)
      skip.
      (* case asel_l *)
      skip.
      (* case asel_r *)
      skip.
    *)