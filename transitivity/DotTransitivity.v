

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
  (* There's a separate rsdc judgment (reflexive sub-declaration) *)
  | subtyp_refl : forall G T,
      subtyp notrans G T T
  | subtyp_top : forall G T,
      subtyp notrans G T typ_top
  | subtyp_bot : forall G T,
      subtyp notrans G typ_bot T
  | subtyp_bind : forall L G l d1 d2,
      (forall z, z \notin L ->
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
  apply (@subtyp_bind \{} empty).
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

(* Lemma invert_subtyp_bot: forall m G T, subtyp m G T typ_bot -> T = typ_bot.
   Does not hold because T could be a p.L with lower and upper bound bottom. *)

(* ... weakening lemmas ... *)

Lemma subdec_weaken_last: forall G z l d1 d2 dA dB,
  subdec oktrans (G & z ~ typ_bind l d2) dA dB ->
  subdec oktrans (G & z ~ typ_bind l d1) d1 d2 ->
  subdec oktrans (G & z ~ typ_bind l d1) dA dB.
Proof.
  (* TODO ;-) *)
Admitted.


(* ... transitivity in notrans mode, but no p.L in middle ... *)

Lemma subtyp_trans_notrans: forall G T1 T2 T3,
  notsel T2 -> subtyp notrans G T1 T2 -> subtyp notrans G T2 T3 -> subtyp notrans G T1 T3.
Proof.
  introv Hnotsel H12 H23.

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
  apply (@subtyp_bind (L \u L0)).
  intros.
  assert (HzL: z \notin L) by notin_solve.
  assert (HzL0: z \notin L0) by notin_solve.
  specialize (H3 z HzL).
  specialize (H7 z HzL0).
  assert (H7': subdec oktrans (G & z ~ typ_bind l (open_dec z (*->*)d1(*<-*))) 
                              (open_dec z d) (open_dec z d3)).
  apply (subdec_weaken_last H7 H3).
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
      follow_lb G (typ_asel p X) U ->
      follow_lb G Lo U.

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

(* linearize a derivation that uses transitivity *)

Definition chain (G: ctx) (A D: typ): Prop := exists B C, 
  follow_ub G A B /\
  subtyp notrans G B C /\
  follow_lb G C D /\
  ((notsel B /\ notsel C) \/ B = typ_bot \/ C = typ_top).

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

Lemma top_sub_notsel: forall G C, 
  subtyp notrans G typ_top C -> notsel C -> C = typ_top.
Proof.
  introv Hs Hn.
  inversion Hs; subst; trivial.
  inversion Hn.
Qed.

(* prepend an oktrans to chain ("utrans0*") *)
Lemma prepend_chain: forall G A1 A2 D,
  subtyp oktrans G A1 A2 ->
  chain G A2 D ->
  chain G A1 D.
Proof.
  fix 5.
  introv Hokt Hch.
  unfold chain in *.
  inversion Hokt; inversion H; set (Hch' := Hch); 
     destruct Hch' as [B [C [Hch1 [Hch2 [Hch3 Hch4]]]]]; subst.
  (* case refl *)
  assumption.
  (* case top *)
  apply follow_ub_top in Hch1; subst.
  exists A1 typ_top.
  split. apply follow_ub_nil.
  split. assumption.
  assert (HCTop: C = typ_top). apply (top_sub_notsel Hch2).
  destruct Hch4 as [[Hch41 Hch42] | [Hch4 | Hch4]].
  assumption. discriminate Hch4. subst. apply notsel_top.
  subst. auto.
  (* case bot *)
  exists typ_bot C.
  split. apply follow_ub_nil.
  split. apply (subtyp_bot G C).
  split. assumption. auto.
  (* case bind *)
  assert (B = typ_bind l d2) by apply (follow_ub_bind Hch1); subst.
  exists (typ_bind l d1) C.
  split. apply follow_ub_nil.
  split. apply (subtyp_trans_notrans (notsel_bind _ _) H Hch2).
  split. assumption.
  left. split. apply notsel_bind.
  destruct Hch4 as [[Hch41 Hch42] | [Hch4 | Hch4]].
    assumption.
    discriminate Hch4.
    subst. apply notsel_top.
  (* case asel_l *)
  set (IH := (prepend_chain G U A2 D H4 Hch)).
  clear Hch1 Hch2 Hch3 Hch4 B C.
  destruct IH as [B [C [IH1 [IH2 IH3]]]].
  exists B C.
  split. 
  apply (follow_ub_cons H0 IH1).
  split; assumption.
  (* case asel_r *)
  inversion Hch1; subst.
    (* case follow_ub_nil *)
    skip.

    (* inverting Hch2 not a good idea because `subtyp oktrans` it contains are 
       not < Hokt => cannot apply IH *
    inversion Hch2; subst.
      (* case subtyp_refl *)
      exists A1 (typ_asel p L).
      split. apply follow_ub_nil. 
      split; assumption.
      (* case subtyp_top *)
      exists A1 typ_top.
      split. apply follow_ub_nil.
      split. apply subtyp_top. assumption. 
      (* case subtyp_asel_l *)
      assert (HdecEq: dec_typ S0 U0 = dec_typ S U) by apply (has_unique H3 H0).
      injection HdecEq; intros; subst.
      apply (prepend_chain G A1 S D H5).
      apply (prepend_chain G S U D H4).
      apply (prepend_chain G U C D H7). Guarded.
      (* case subtyp_asel_r *)
      skip.

   destruct (notransl_head Hch2) as [[M [Hn [Hs Hch2']]] | Hs].
      (* case notransl_cons *)
      inversion Hs; subst.
      (* case notransl_nil *)

    (*inversion Hch2; subst.*)

  
    inversion Hch3; subst.
      (* case follow_lb_nil *)
      (*inversion Hch2; subst.*)

      skip.
      (* case follow_lb_cons *)
      skip.*)
    (* case follow_ub_cons *)
    apply (prepend_chain G A1 S D H5).
    apply (prepend_chain G S U D H4).
    assert (HdecEq: dec_typ Lo Hi = dec_typ S U) by apply (has_unique H6 H0).
    injection HdecEq; intros; subst.
    exists B C.
    split. assumption. split. assumption. split. assumption. assumption.
  (* case mode *)
  apply (prepend_chain G _ _ _ H (prepend_chain G _ _ _ H0 Hch)).
  (* case trans *)
  apply (prepend_chain G _ _ _ H (prepend_chain G _ _ _ H0 Hch)).
Qed.
