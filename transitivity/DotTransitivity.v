

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
  | typ_bind : env dec -> typ (* { z => decs } *)
  | typ_asel : pth -> label -> typ (* select on abstract type *)
with dec : Type :=
  | dec_typ  : typ -> typ -> dec
  | dec_fld  : typ -> dec
.

(* mapping from label to dec *)
Definition decs := env dec.

Inductive notsel: typ -> Prop :=
  | notsel_top  : notsel typ_top
  | notsel_bot  : notsel typ_bot
  | notsel_bind : forall ds, notsel (typ_bind ds).

Hint Constructors notsel.

(* map and env_map are the same, except that for env_map, we have a definition which
   works in recursive definitions (decreasing measure...).
   Note that map has map_def, but rhs of map_def doesn't work either *)

Definition env_map {A B: Type} (f: A -> B) (E: env A): env B :=
  List.map (fun p => (fst p, f (snd p))) E.

Lemma env_map_is_map: forall A B (E: env A) (f: A -> B),
  env_map f E = map f E.
Proof.
  intros.
  rewrite -> map_def.
  unfold env_map.
  unfold env in *.
  induction E.
  (* case nil *)
  auto.
  (* case cons *)
  rewrite -> LibList.map_cons.
  simpl.
  rewrite -> IHE.
  trivial.
Qed.

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
  | typ_bind ds => typ_bind (env_map (open_rec_dec (S k) u) ds)
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
  | has_var : forall G x ds l d,
      binds x (typ_bind ds) G ->
      binds l d ds ->
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
  | subtyp_bind : forall G ds1 ds2,
      (forall z,     ok (G & (z ~ (typ_bind (map (open_dec z) ds1)))) ->
        subdecs oktrans (G & (z ~ (typ_bind (map (open_dec z) ds1))))
                        (map (open_dec z) ds1) (map (open_dec z) ds2)) ->
      subtyp notrans G (typ_bind ds1) (typ_bind ds2)
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
      subdec m G (dec_fld T1) (dec_fld T2)
with subdecs : mode -> ctx -> decs -> decs -> Prop :=
  | subdecs_empty : forall m G ds,
      subdecs m G ds empty
  | subdecs_push : forall m G l ds1 ds2 d1 d2,
      binds l d1 ds1 ->
      subdec m G d1 d2 ->
      subdecs m G ds1 ds2 ->
      subdecs m G ds1 (ds2 & l ~ d2)
.

Scheme subtyp_mut  := Induction for subtyp  Sort Prop
with   subdec_mut  := Induction for subdec  Sort Prop
with   subdecs_mut := Induction for subdecs Sort Prop.

Combined Scheme subtyp_subdec_mutind from subtyp_mut, subdec_mut, subdecs_mut.

Hint Constructors subtyp.
Hint Constructors subdec.

Lemma subtyp_refl_allmodes: forall m G T, subtyp m G T T.
Proof.
  intros.
  destruct m; auto.
Qed.
Hint Resolve subtyp_refl_allmodes.

(* does not hold because maybe we don't have Lo <: Hi *)
Lemma subdec_refl_allmodes: forall m G d, subdec m G d d.
Proof.
Abort.

(* Alternative definition of subdecs which is sometimes more useful *)
Definition subdecs_alt (m: mode) (G: ctx) (ds1 ds2: decs): Prop :=
  forall l d2, binds l d2 ds2 -> 
               (exists d1, binds l d1 ds1 /\ subdec m G d1 d2).

(* Alternative and primary definition are equivalent *)
Lemma subdecs_eq: forall m G ds1 ds2, ok ds2 ->
  (subdecs_alt m G ds1 ds2 <-> subdecs m G ds1 ds2).
Proof.
  introv Hok.
  induction ds2.
  (* base case *)
  rewrite <- empty_def.
  split; intros.
  apply subdecs_empty.
  unfold subdecs_alt.
  intros.
  contradiction (binds_empty_inv H0).
  (* step *)
  destruct a as [l d2].
  rewrite -> cons_to_push in *.
  destruct (ok_push_inv Hok) as [Hok' _].
  split.
  (* -> *)
  unfold subdecs_alt.
  intro Halt.
  destruct (Halt l d2 (binds_push_eq _ _ _)) as [d1 [Hb1 Hsd]].
  apply (subdecs_push Hb1 Hsd).
  apply (IHds2 Hok').
  unfold subdecs_alt.
  introv Hb2.
  assert (Hb0: binds l0 d0 (ds2 & l ~ d2)).
  destruct (classicT (l0 = l)) as [Heq|Hne].
  (* l0 = l *)
  subst.
  destruct (ok_push_inv Hok) as [_ Hnotin].
  contradiction (binds_fresh_inv Hb2 Hnotin).
  (* l0 <> l *)
  apply (binds_push_neq d2 Hb2 Hne).
  apply (Halt l0 d0 Hb0).
  (* <- *)
  intro Hsd.
  inversion Hsd. 
  contradiction (empty_push_inv H3).
  apply eq_push_inv in H.
  destruct H as [Heq1 [Heq2 Heq3]].
  subst.
  unfold subdecs_alt.
  introv Hb.
  destruct (classicT (l0 = l)) as [Heq|Hne].
  (* case l0 = l *)
  subst.
  apply binds_push_eq_inv in Hb.
  subst.
  exists d1.
  auto.
  (* case l0 <> l *)
  set (Hb' := binds_push_neq_inv Hb Hne).
  destruct (IHds2 Hok') as [_ IH].
  set (IH' := IH H5).
  unfold subdecs_alt in IH'.
  apply (IH' l0 d0 Hb').
Qed.

(* ... free vars ... *)

Inductive fvar : avar -> Prop :=
  | fvar_f : forall x,
      fvar (avar_f x).

(*
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
  | typ_bind ds => fv_decs ds
  | typ_asel p l => fv_pth p
  end
with fv_dec (d: dec) { struct d } : vars :=
  match d with
  | dec_typ ts tu => (fv_typ ts) \u (fv_typ tu)
  | dec_fld t => fv_typ t
  end
with fv_decs (ds: decs) { struct ds } : vars := \{} (* TODO *).
*)

(* path/type locally closed (no avar_b, only avar_f) *)

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
  | type_bind : forall L ds,
      (forall x, x \notin L -> decls (map (open_dec x) ds)) ->
      type (typ_bind ds)
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
      decl (dec_fld t)
with decls : decs -> Prop :=
  | decls_emtpy : 
      decls (@empty dec)
  | decls_push : forall ds l d,
      decl d ->
      l # ds ->
      decls (ds & l ~ d).


(* ... infrastructure ... *)

(*
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
*)

Lemma ok_single: forall A x (v: A), ok (x ~ v).
Proof.
  intros.
  apply ok_concat_inv_r with (E := empty).
  apply ok_push.
  apply ok_empty.
  apply get_none_inv.
  apply get_empty.
Qed.

(* ... examples ... *)

Fact type_test_1: forall l1 l2,
  type (typ_bind (l1 ~ (dec_fld (typ_bind (l2 ~ (dec_fld typ_top)))))).
Proof.
  intros.
  apply type_bind with (L := \{}).
  intros.
  rewrite -> map_single.
  rewrite <- concat_empty_l.
  apply decls_push.
  unfold open_dec.
  unfold open_rec_dec.
  rewrite -> env_map_is_map.
  rewrite -> map_single.
  apply decl_fld.
  apply type_bind with (L := \{}).
  intros.
  rewrite -> map_single.
  rewrite <- concat_empty_l.
  apply decls_push.
  unfold open_dec.
  unfold open_rec_dec.
  apply decl_fld.
  apply type_top.
  auto. auto.
Qed.

(*    { l1: { l2: Top }} <: { l1: Top }     *)
Definition subtyp_example_1(l1 l2: label): Prop :=
  subtyp notrans empty
    (typ_bind (l1 ~ (dec_fld (typ_bind (l2 ~ (dec_fld typ_top))))))
    (typ_bind (l1 ~ (dec_fld typ_top))).

Fact subtyp_example_1_proof: forall l1 l2, subtyp_example_1 l1 l2.
Proof.
  intros.
  unfold subtyp_example_1.
  apply (@subtyp_bind empty).
  intros.
  apply (subdecs_eq oktrans _ _);
  rewrite -> map_single in *.
  apply ok_single.
  unfold subdecs_alt.
  intros.
  rewrite -> map_single in H0.
  destruct (binds_single_inv H0) as [Heq1 Heq2].
  clear H0.
  subst.
  exists (open_dec z (dec_fld (typ_bind (l2 ~ dec_fld typ_top)))).
  split.
  apply binds_single_eq.
  apply subdec_fld.
  apply subtyp_mode.
  apply (subtyp_top _ _).
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
  injection H10; intro; subst.
  injection (binds_func H7 H); intro; subst.
  apply (binds_func H0 H8).
Qed.

(* "reflexive subdec", just subdec+reflexivity *)
Definition rsubdec(G: ctx)(d1 d2: dec): Prop :=
  d1 = d2 \/ subdec oktrans G d1 d2.

Lemma subdec_refl: forall m G d, subdec m G d d.
Proof.
  (* not true if Lo >: Hi *)
Abort.

Lemma invert_subtyp_bot: forall m G T, subtyp m G T typ_bot -> T = typ_bot.
Proof.
  (* Does not hold because T could be a p.L with lower and upper bound bottom. *)
Abort.

(* ... weakening lemmas ... *)

Lemma narrow_has_alt: forall G1 G2 z ds1 ds2 p L dB,
  ok                  (G1 & z ~ typ_bind ds2 & G2) ->
  has                 (G1 & z ~ typ_bind ds2 & G2) p L dB ->
  subdecs_alt oktrans (G1 & z ~ typ_bind ds1     ) ds1 ds2 ->
  exists dA, 
    rsubdec (G1 & z ~ typ_bind ds1     ) dA dB 
    /\ has  (G1 & z ~ typ_bind ds1 & G2) p L dA.
Proof.
  introv Hokds2 Hhas Hsd.
  set (Hokds1 := (ok_middle_change (typ_bind ds1) Hokds2)).
  inversion Hhas; unfold rsubdec; subst.
  destruct (classicT (x = z)) as [Heq|Hne].
  (* case x = z *)
  subst.
  set (Heq := (binds_middle_eq_inv H Hokds2)).
  inversion_clear Heq; subst.
  unfold subdecs_alt in Hsd.
  set (H1 := Hsd).
  destruct (ok_middle_inv Hokds2) as [_ HzG2].
  injection (binds_middle_eq_inv H Hokds2); intro. subst.
  destruct (H1 L dB H0) as [dA [Hb1 H1B]].
  exists dA.
  split.
  right. apply H1B.
  apply (has_var (binds_middle_eq G1 (typ_bind ds1) HzG2) Hb1).
  (* case x <> z *)
  assert (Hxz: x # z ~ typ_bind ds2).
  unfold notin.
  rewrite -> dom_single. 
  rewrite -> in_singleton.
  assumption.
  assert (HG: binds x (typ_bind ds) (G1 & G2)).
  apply (binds_remove H Hxz).
  exists dB.
  split. left. trivial.  
  assert (HGz: binds x (typ_bind ds) (G1 & z ~ typ_bind ds1 & G2)).
  apply (@binds_weaken typ x (typ_bind ds) G1 (z ~ typ_bind ds1) G2 HG Hokds1).
  apply (has_var HGz H0).
Qed.

Lemma narrow_has: forall G1 G2 z ds1 ds2 p L dB,
  ok              (G1 & z ~ typ_bind ds2 & G2) ->
  has             (G1 & z ~ typ_bind ds2 & G2) p L dB ->
  subdecs oktrans (G1 & z ~ typ_bind ds1     ) ds1 ds2 ->
  exists dA, 
    rsubdec (G1 & z ~ typ_bind ds1     ) dA dB 
    /\ has  (G1 & z ~ typ_bind ds1 & G2) p L dA.
Proof.
  intros.
  refine (narrow_has_alt _ H0 _).
  assumption.
  assert (Hokds2: ok ds2). skip.
  apply (subdecs_eq _ _ _ Hokds2).
  assumption.
Qed.

Lemma weaken_has: forall G1 G2 G3 p L d,
  ok             (G1 & G2 & G3) ->
  has            (G1      & G3) p L d ->
  has            (G1 & G2 & G3) p L d.
Proof.
  introv Hok Hhas.
  inversion Hhas; subst.
  refine (@has_var _ x ds L d _ H0).
  apply binds_weaken; assumption.
Qed.

Lemma subdec_mode: forall G d1 d2,
  subdec notrans G d1 d2 -> subdec oktrans G d1 d2.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma subtyp_and_subdec_and_subdecs_weaken:
   (forall m G T1 T2 (Hst : subtyp m G T1 T2),
      forall G1 G2 G3, ok (G1 & G2 & G3) ->
                       G1 & G3 = G ->
                       subtyp oktrans (G1 & G2 & G3) T1 T2)
/\ (forall m G d1 d2 (Hsd : subdec m G d1 d2),
      forall G1 G2 G3, ok (G1 & G2 & G3) ->
                       G1 & G3 = G ->
                       subdec oktrans (G1 & G2 & G3) d1 d2)
/\ (forall m G ds1 ds2 (Hsds : subdecs m G ds1 ds2),
      forall G1 G2 G3, ok (G1 & G2 & G3) ->
                       G1 & G3 = G ->
                       subdecs oktrans (G1 & G2 & G3) ds1 ds2).
Proof.
  apply subtyp_subdec_mutind.

  (* subtyp *)
  (* case refl *)
  introv Hok123 Heq; subst.
  apply (subtyp_mode (subtyp_refl _ _)).
  (* case top *)
  introv Hok123 Heq; subst.
  apply (subtyp_mode (subtyp_top _ _)).
  (* case bot *)
  introv Hok123 Heq; subst.
  apply (subtyp_mode (subtyp_bot _ _)).
  (* case bind *)
  introv Hc IH Hok123 Heq; subst.
  refine (subtyp_mode (@subtyp_bind (G1 & G2 & G3) ds1 ds2 _)).
  intros.
  rewrite <- concat_assoc.
  refine (IH z _ G1 G2 (G3 & z ~ typ_bind (map (open_dec z) ds1)) _ _).
  rewrite <- concat_assoc.
  apply ok_remove with (F := G2).
  rewrite -> concat_assoc.
  assumption.
  rewrite -> concat_assoc.
  assumption.
  apply concat_assoc.
  (* case asel_l *)
  introv Hhas Hst IH Hok123 Heq; subst.
  apply subtyp_mode.
  apply subtyp_asel_l with (S := S) (U := U).
  apply weaken_has; assumption.
  apply (IH G1 G2 G3 Hok123).
  trivial.
  (* case asel_r *)
  introv Hhas Hst_SU IH_SU Hst_TS IH_TS Hok123 Heq; subst.
  apply subtyp_mode.
  apply subtyp_asel_r with (S := S) (U := U).
  apply weaken_has; assumption.
  apply IH_SU; auto.
  apply IH_TS; auto.
  (* case trans *)
  introv Hst IH Hok Heq.
  apply subtyp_trans with (T2 := T2).
  apply IH; auto.
  apply (subtyp_mode (subtyp_refl _ T2)).
  (* case mode *)
  introv Hst12 IH12 Hst23 IH23 Hok123 Heq.
  specialize (IH12 G1 G2 G3 Hok123 Heq).
  specialize (IH23 G1 G2 G3 Hok123 Heq).
  apply (subtyp_trans IH12 IH23).

  (* subdec *)
  (* case subdec_typ *)
  intros.
  apply subdec_typ; gen G1 G2 G3; assumption.
  (* case subdec_fld *)
  intros.
  apply subdec_fld; gen G1 G2 G3; assumption.

  (* subdecs *)
  (* case subdecs_empty *)
  intros.
  apply subdecs_empty.
  (* case subdecs_push *)
  introv Hb Hsd IHsd Hsds IHsds Hok123 Heq.
  apply (subdecs_push Hb).
  apply (IHsd _ _ _ Hok123 Heq).
  apply (IHsds _ _ _ Hok123 Heq).
Qed.

Lemma subtyp_weaken: forall G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp oktrans (G1      & G3) S U ->
  subtyp oktrans (G1 & G2 & G3) S U.
Proof.
  destruct subtyp_and_subdec_and_subdecs_weaken as [W _].
  introv Hok123 Hst.
  specialize (W oktrans (G1 & G3) S U Hst).
  specialize (W G1 G2 G3 Hok123).
  apply W.
  trivial.
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


Lemma subtyp_and_subdec_and_subdecs_narrow:
   (forall m G T1 T2 (Hst : subtyp m G T1 T2),
      forall G1 G2 z dsA dsB, 
         ok              (G1 & z ~ typ_bind dsB & G2)         ->
         G       =       (G1 & z ~ typ_bind dsB & G2)         ->
         subdecs oktrans (G1 & z ~ typ_bind dsA     ) dsA dsB ->
         subtyp  oktrans (G1 & z ~ typ_bind dsA & G2) T1 T2)
/\ (forall m G d1 d2 (Hsd : subdec m G d1 d2),
      forall G1 G2 z dsA dsB, 
         ok              (G1 & z ~ typ_bind dsB & G2)         ->
         G       =       (G1 & z ~ typ_bind dsB & G2)         ->
         subdecs oktrans (G1 & z ~ typ_bind dsA     ) dsA dsB ->
         subdec  oktrans (G1 & z ~ typ_bind dsA & G2) d1 d2)
/\ (forall m G ds1 ds2 (Hsds : subdecs m G ds1 ds2),
      forall G1 G2 z dsA dsB, 
         ok              (G1 & z ~ typ_bind dsB & G2)         ->
         G       =       (G1 & z ~ typ_bind dsB & G2)         ->
         subdecs oktrans (G1 & z ~ typ_bind dsA     ) dsA dsB ->
         subdecs oktrans (G1 & z ~ typ_bind dsA & G2) ds1 ds2).
Proof.
  apply subtyp_subdec_mutind; try (intros; progress auto).

  (* subtyp *)
  (* cases refl, top, bot: auto *)
  (* case bind *)
  introv Hc IH Hok123 Heq HAB; subst.
  refine (subtyp_mode (@subtyp_bind (G1 & z ~ typ_bind dsA & G2) ds1 ds2 _)).
  intros.
  rewrite <- concat_assoc.
  refine (IH z0 _ G1 (G2 & z0 ~ typ_bind (map (open_dec z0) ds1)) _ dsA dsB _ _ _).
  rewrite <- concat_assoc.
  rewrite <- concat_assoc in H.
  apply (ok_middle_change _ H).
  rewrite <- concat_assoc in H.
  apply (ok_middle_change _ H).
  rewrite -> concat_assoc.
  trivial.
  assumption.
  (* case asel_l *)
  introv Hhas Hst IH Hok Heq HAB; subst.
  apply subtyp_mode.
  set (Hn := @narrow_has _ _ _ dsA dsB _ _ _ Hok Hhas HAB).
  destruct Hn as [dA [Hrsd Hh]].
    (* case refl *)
    inversion Hrsd; subst.
    apply subtyp_asel_l with (S := S) (U := U). assumption.
    apply IH with (dsB0 := dsB); auto.
    (* case not-refl *)
    inversion H; subst.
    apply subtyp_asel_l with (S := Lo1) (U := Hi1).
    assumption.
    assert (Hok': ok (G1 & z ~ typ_bind dsA & G2)).
    apply (ok_middle_change _ Hok).
    refine (subtyp_trans (subtyp_weaken_2 Hok' H8) _).
    apply IH with (dsB0 := dsB); auto.
  (* case asel_r *)
  introv Hhas Hst_SU IH_SU Hst_TS IH_TS Hok Heq HAB; subst.
  apply subtyp_mode.
  assert (Hok': ok (G1 & z ~ typ_bind dsA & G2)).
  apply (ok_middle_change _ Hok).
  set (Hn := @narrow_has _ _ _ dsA dsB _ _ _ Hok Hhas HAB).
  destruct Hn as [dA [Hrsd Hh]].
  inversion Hrsd; subst.
    (* case refl *)
    apply subtyp_asel_r with (S := S) (U := U). assumption.
    apply IH_SU with (dsB0 := dsB); auto.
    apply IH_TS with (dsB0 := dsB); auto.
    (* case not-refl *)
    inversion H; subst.
    apply subtyp_asel_r with (S := Lo1) (U := Hi1).
    assumption.
    apply (subtyp_weaken_2 Hok' H2).
    refine (subtyp_trans _ (subtyp_weaken_2 Hok' H7)).
    apply IH_TS with (dsB0 := dsB); auto.
  (* case trans *)
  introv Hst IH Hok Heq HAB.
  apply subtyp_trans with (T2 := T2).
  apply IH with (dsB := dsB); auto.
  apply (subtyp_mode (subtyp_refl _ T2)).
  (* case mode *)
  introv Hst12 IH12 Hst23 IH23 Hok123 Heq HAB.
  specialize (IH12 G1 G2 z dsA dsB Hok123 Heq HAB).
  specialize (IH23 G1 G2 z dsA dsB Hok123 Heq HAB).
  apply (subtyp_trans IH12 IH23).

  (* subdec *)
  (* case subdec_typ *)
  intros.
  apply subdec_typ; gen G1 G2 z dsA dsB; assumption.
  (* case subdec_fld *)
  intros.
  apply subdec_fld; gen G1 G2 z dsA dsB; assumption.

  (* subdecs *)
  (* case subdecs_empty *)
  intros.
  apply subdecs_empty.
  (* case subdecs_push *)
  introv Hb Hsd IHsd Hsds IHsds Hok123 Heq HAB.
  apply (subdecs_push Hb).
  apply (IHsd  _ _ _ _ _ Hok123 Heq HAB).
  apply (IHsds _ _ _ _ _ Hok123 Heq HAB).
Qed.

Lemma subdec_narrow: forall G1 G2 z ds1 ds2 dA dB,
  ok              (G1 & z ~ typ_bind ds2 & G2) ->
  subdec  oktrans (G1 & z ~ typ_bind ds2 & G2) dA dB ->
  subdecs oktrans (G1 & z ~ typ_bind ds1     ) ds1 ds2 ->
  subdec  oktrans (G1 & z ~ typ_bind ds1 & G2) dA dB.
Proof.
  introv Hok HAB Hsds.
  destruct subtyp_and_subdec_and_subdecs_narrow as [_ [N _]].
  specialize (N oktrans (G1 & z ~ typ_bind ds2 & G2) dA dB).
  specialize (N HAB G1 G2 z ds1 ds2 Hok).
  apply N.
  trivial.
  assumption.
Qed.

Lemma subdecs_narrow: forall G1 G2 z ds1 ds2 dsA dsB,
  ok              (G1 & z ~ typ_bind ds2 & G2) ->
  subdecs oktrans (G1 & z ~ typ_bind ds2 & G2) dsA dsB ->
  subdecs oktrans (G1 & z ~ typ_bind ds1     ) ds1 ds2 ->
  subdecs oktrans (G1 & z ~ typ_bind ds1 & G2) dsA dsB.
Proof.
  introv Hok HAB Hsds.
  destruct subtyp_and_subdec_and_subdecs_narrow as [_ [_ N]].
  specialize (N oktrans (G1 & z ~ typ_bind ds2 & G2) dsA dsB).
  specialize (N HAB G1 G2 z ds1 ds2 Hok).
  apply N.
  trivial.
  assumption.
Qed.

Lemma subdec_narrow_last: forall G z ds1 ds2 dA dB,
  ok              (G & z ~ typ_bind ds2) ->
  subdec  oktrans (G & z ~ typ_bind ds2) dA dB ->
  subdecs oktrans (G & z ~ typ_bind ds1) ds1 ds2 ->
  subdec  oktrans (G & z ~ typ_bind ds1) dA dB.
Proof.
  introv Hok HAB H12.
  apply (env_remove_empty (fun G0 => subdec oktrans G0 dA dB) (G & z ~ typ_bind ds1)).
  apply subdec_narrow with (ds2 := ds2).
  apply (env_add_empty (fun G0 => ok G0) (G & z ~ typ_bind ds2) Hok).
  apply (env_add_empty (fun G0 => subdec oktrans G0 dA dB)
                             (G & z ~ typ_bind ds2) HAB).
  assumption.
Qed.

Print Assumptions subdec_narrow_last.

Lemma subdecs_narrow_last: forall G z ds1 ds2 dsA dsB,
  ok              (G & z ~ typ_bind ds2) ->
  subdecs oktrans (G & z ~ typ_bind ds2) dsA dsB ->
  subdecs oktrans (G & z ~ typ_bind ds1) ds1 ds2 ->
  subdecs oktrans (G & z ~ typ_bind ds1) dsA dsB.
Proof.
  introv Hok H2AB H112.
  apply (env_remove_empty (fun G0 => subdecs oktrans G0 dsA dsB) (G & z ~ typ_bind ds1)).
  apply subdecs_narrow with (ds2 := ds2).
  apply (env_add_empty (fun G0 => ok G0) (G & z ~ typ_bind ds2) Hok).
  apply (env_add_empty (fun G0 => subdecs oktrans G0 dsA dsB)
                             (G & z ~ typ_bind ds2) H2AB).
  assumption.
Qed.

Lemma subdecs_trans: forall G ds1 ds2 ds3,
  ok ds1 -> ok ds2 -> ok ds3 ->
  subdecs oktrans G ds1 ds2 ->
  subdecs oktrans G ds2 ds3 ->
  subdecs oktrans G ds1 ds3.
Proof.
  introv Hok1 Hok2 Hok3 Hds12 Hds23.
  apply (subdecs_eq _ _ _ Hok3).
  rewrite <- (subdecs_eq _ _ _ Hok2) in Hds12.
  rewrite <- (subdecs_eq _ _ _ Hok3) in Hds23.
  unfold subdecs_alt in *. 
  introv Hb3.
  specialize (Hds23 l d2 Hb3).
  destruct Hds23 as [d1 [Hb2 Hsd12]].
  specialize (Hds12 l d1 Hb2).
  destruct Hds12 as [d [Hb Hsd]].
  exists d.
  split. assumption.
  apply (subdec_trans_oktrans Hsd Hsd12).
Qed.

(* ... transitivity in notrans mode, but no p.L in middle ... *)

Lemma subtyp_trans_notrans: forall G T1 T2 T3,
  ok G -> notsel T2 -> subtyp notrans G T1 T2 -> subtyp notrans G T2 T3 -> 
  subtyp notrans G T1 T3.
Proof.
  introv Hok Hnotsel H12 H23.

  inversion Hnotsel; subst.
  (* case top *)
  inversion H23; subst.
  apply (subtyp_top G T1).
  apply (subtyp_top G T1).
  apply (subtyp_asel_r H H0 (subtyp_trans (subtyp_mode H12) H1)).
  (* case bot *)
  inversion H12; subst.
  apply (subtyp_bot G T3).
  apply (subtyp_bot G T3).
  apply (subtyp_asel_l H (subtyp_trans H0 (subtyp_mode H23))).
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
  assert (Hok'': ok (G & z ~ typ_bind (map (open_dec z) ds))).
  destruct (ok_push_inv Hok') as [_ Hnotin].
  apply ok_push; assumption.
  specialize (H0 z Hok').
  specialize (H4 z Hok'').
  set (H4' := subdecs_narrow_last Hok'' H4 H0). 
  refine (subdecs_trans _ _ _ H0 H4').
  skip. skip. skip.

  (* bind <: bind <: sel  *)
  assert (H1S: subtyp oktrans G (typ_bind ds1) S).
  apply (subtyp_trans_oktrans (subtyp_mode H12) H5).
  apply (subtyp_asel_r H3 H4 H1S).

  (* sel  <: bind <: bind *)
  assert (HU2: subtyp oktrans G U (typ_bind ds2)).
  apply (subtyp_trans_oktrans H0 (subtyp_mode H23)).
  apply (subtyp_asel_l H HU2). 

  (* sel  <: bind <: sel  *)
  assert (H1S0: subtyp oktrans G (typ_asel p L) S0).
  apply (subtyp_trans_oktrans (subtyp_mode H12) H6).
  apply (subtyp_asel_r H1 H5 H1S0).
Qed.

Print Assumptions subtyp_trans_notrans.

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

(* Note: No need for a invert_follow_ub lemma because inversion is smart enough. *)

Definition st_middle (G: ctx) (B C: typ): Prop :=
  B = C \/
  subtyp notrans G typ_top C \/
  (notsel B /\ subtyp notrans G B C).

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
  unfold st_middle in Hm.
  destruct Hm as [Hm | [Hm | [Hm1 Hm2]]]; subst.
  apply (chain3subtyp Hst Hflb).
  apply (chain3subtyp (subtyp_trans_notrans Hok notsel_top (subtyp_top G B1) Hm) Hflb).
  apply (chain3subtyp (subtyp_trans_notrans Hok Hm1 Hst Hm2) Hflb).
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
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  inversion Hch1; subst.
  destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]]; subst.
  exists A1 typ_top.
  auto 10.
  exists A1 C.
  auto 10.
  exists A1 C.
  auto 10.
  (* case bot *)
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  exists typ_bot C.
  auto 10.
  (* case bind *)
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  inversion Hch1; subst.
  exists (typ_bind ds1) C.
  destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
  subst.
  auto 10. (* <- search depth *)
  auto 10.
  set (Hst := (subtyp_trans_notrans Hok (notsel_bind _) H Hch2b)).
  auto 10.
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
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
    subst.
    apply (prepend_chain G A1 S D Hok H5).
    exists S S. 
    set (Hflb := (follow_lb_cons H0 H4 Hch3)).
    auto.
    exists A1 C.
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

Lemma oktrans_to_notrans: forall G T1 T3,
  ok G -> subtyp oktrans G T1 T3 -> subtyp notrans G T1 T3.
Proof.
  introv Hok Hst.
  inversion Hst; subst.
  assumption.
  set (Hch := (prepend_chain Hok H (prepend_chain Hok H0 (empty_chain _ _)))).
  unfold chain in Hch.
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  apply (chain1subtyp Hok Hch1 Hch2 Hch3).
Qed.

Print Assumptions oktrans_to_notrans.

(* TODO
Lemma invert_bind: forall G l1 d1 l2 d2,
  ok G ->
  subtyp oktrans G (typ_bind l1 d1) (typ_bind l2 d2) ->
  forall z, z # G -> 
    subdec oktrans (G & z ~ typ_bind l2 (open_dec z d1)) 
      (open_dec z d1) (open_dec z d2).
Proof.
  introv Hok Hst12.
  introv Hnotin.
  apply (oktrans_to_notrans Hok) in Hst12.
  inversion Hst12; subst.
  (* case refl *)
  destruct d2 as [Lo Hi|T].
    (* case typ *)
    (* need Lo <: Hi also in case of refl, and need that opening preserves <: *)
    skip.
    (* case fld *)
    apply (subdec_fld (subtyp_mode (subtyp_refl _ _))).
  (* case bind *)
  apply (H3 z (ok_push (typ_bind l2 (open_dec z d1)) Hok Hnotin)).
Qed.
*)

(*
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
  (* case mode *)
  skip.
*)
