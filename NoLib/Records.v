
Require Export List.
Require Export Arith.Peano_dec.
Require Export Program.Syntax. (* eg for multiple exists tactic *)
Require Import Numbers.Natural.Peano.NPeano.
Require Import Arith.Compare_dec.
Require Import Omega.

Set Implicit Arguments.

(* List notation with head on the right *)
Notation "E '&' F" := (app F E) (at level 31, left associativity).
Notation " E  ;; x " := (cons x E) (at level 29, left associativity).

(* Testing the list notations: *)
Module ListNotationTests.
Definition head(l: list nat) := match l with
| nil => 777
| cons x xs => x
end.
Eval compute in nil ;; 1 ;; 2 ;; 3.
Eval compute in head (nil ;; 1 ;; 2 ;; 3).
Eval compute in head ((nil ;; 1 ;; 2 ;; 3) & (nil ;; 4 ;; 5)).
Eval compute in nil ;; 1 ;; 2 & nil ;; 3 ;; 4 & nil ;; 5 ;; 6. 
(* Unset Printing Notations. (* or by CoqIDE menu *) *)
Check (nil ;; 0 & nil ;; 0 ;; 0 & nil ;; 0 ;; 0 ;; 0).
End ListNotationTests.

Definition var := nat.

(* If it's clear whether a field or method is meant, we use nat, if not, we use label: *)
Inductive label: Type :=
| label_fld: nat -> label
| label_mtd: nat -> label.

Lemma eq_label_dec: forall l1 l2: label, {l1 = l2} + {l1 <> l2}.
Proof.
  intros. 
  destruct l1 as [n1|n1]; destruct l2 as [n2|n2]; 
  destruct (eq_nat_dec n1 n2); solve [
     (left; f_equal; assumption) |
     (right; unfold not; intro H; inversion H; rewrite H1 in n; apply n; reflexivity)].
Qed.

Inductive avar : Type :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to tenv or venv *)

Inductive typ : Type :=
  | typ_rcd  : list ndec -> typ (* record type *)
with ndec : Type := (* named declaration *)
  | ndec_fld : nat -> typ -> ndec
  | ndec_mtd : nat -> typ -> typ -> ndec.
Inductive dec : Type := (* declaration without name *)
  | dec_fld  : typ -> dec
  | dec_mtd  : typ -> typ -> dec.

Inductive trm : Type :=
  | trm_var  : avar -> trm
  | trm_new  : list nini -> trm -> trm
  | trm_sel  : trm -> nat -> trm
  | trm_call : trm -> nat -> trm -> trm
with nini : Type :=
  | nini_fld : nat -> avar -> nini (* cannot have term here, need to assign first *)
  | nini_mtd : nat -> typ -> trm -> nini.
Inductive ini : Type :=
  | ini_fld : avar -> ini
  | ini_mtd : typ -> trm -> ini.

(* Syntactic sugar *)
Definition trm_fun(T: typ)(body: trm) := trm_new (nil ;; nini_mtd 0 T body)
                                                 (trm_var (avar_b 0)).
Definition trm_app(func arg: trm) := trm_call func 0 arg.
Definition trm_let(T: typ)(rhs body: trm) := trm_app (trm_fun T body) rhs.
Definition trm_upcast(T: typ)(e: trm) := trm_app (trm_fun T (trm_var (avar_b 0))) e.
Definition typ_arrow(T1 T2: typ) := typ_rcd (nil ;; ndec_mtd 0 T1 T2).

(* ... opening ...
   replaces in some syntax a bound variable with dangling index (k) by a free variable x
*)

Fixpoint open_rec_avar (k: nat) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => if eq_nat_dec k i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

(* The only binders are trm_new and (n)ini_mtd, which cannot be inside a typ or
   inside a dec, so we don't need opening for typ and dec *)

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var  a     => trm_var (open_rec_avar k u a)
  | trm_new  is e  => trm_new (map (open_rec_nini (S k) u) is) (open_rec_trm (S k) u e)
  | trm_sel  e n   => trm_sel (open_rec_trm k u e) n
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_nini (k: nat) (u: var) (i: nini) { struct i } : nini :=
  match i with
  | nini_fld n a   => nini_fld n (open_rec_avar k u a)
  | nini_mtd n T e => nini_mtd n T (open_rec_trm (S k) u e)
  end.

Definition open_avar u a := open_rec_avar 0 u a.
Definition open_trm  u e := open_rec_trm  0 u e.
Definition open_nini u i := open_rec_nini 0 u i.

Inductive fvar : avar -> Prop :=
  | fvar_f : forall x,
      fvar (avar_f x).

(* 
Environment requirements:
   * Want to use the same definitions and lemmas for
     - decs
     - inis
     - tenv
     - venv
   * Intersection of two dec lists must be total, i.e. if we have
     (m: T -> U) in ds1 and (m: T) in ds2,
     then (ds1 /\ ds2) must be defined and contain both declarations.
     This requires that method labels be distinct from field labels, or that
     the environment data structure allows two decs with the same name if they
     are of a different kind.
   * Want to have generic dec (dec_typ, dec_mtd, dec_fld), and treat dec lists as
     as mappings from dec name to dec, instead of having three separate lists.
Hopefully, this module system approach satisfies the requirements.
*)

Module Type EnvParams.
Parameter K : Type.
Parameter V : Type.
Parameter B : Type.
Parameter key: B -> K.
Parameter value: B -> V. 
Axiom eq_key_dec: forall k1 k2: K, {k1 = k2} + {k1 <> k2}.
Axiom key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
End EnvParams.

Ltac inv H := inversion H; clear H; subst.

(* General environment *)
Module Env (params: EnvParams).
Import params.
Definition key := key.
Definition value := value.
Definition t := list B.
Fixpoint get(k: K)(E: t): option V := match E with
  | nil => None
  | bs ;; b => if eq_key_dec k (key b) then Some (value b) else get k bs
  end.
Definition binds(k: K)(v: V)(E: t): Prop := (get k E = Some v).
Definition unbound(k: K)(E: t): Prop := (get k E = None).

Ltac empty_binds_contradiction := match goal with
| H: binds _ _ [] |- _ => inversion H
end.
(*
Tactic Notation "unfoldg" reference(I)             := unfold I, get; fold get.
Tactic Notation "unfoldg" reference(I) "in" hyp(H) := unfold I, get in H; fold get in H.
*)
Ltac unfoldg I := unfold I, get in *; fold get in *.
Ltac destruct_key_if := match goal with
| H:   context[if eq_key_dec ?k1 ?k2 then _ else _] |- _ => destruct (eq_key_dec k1 k2)
|   |- context[if eq_key_dec ?k1 ?k2 then _ else _]      => destruct (eq_key_dec k1 k2)
end.
Ltac compare_keys := match goal with
| _ :  context[binds _ _ (?E ;; ?b)] |- _ => unfoldg binds;   destruct_key_if
|   |- context[binds _ _ (?E ;; ?b)]      => unfoldg binds;   destruct_key_if
| _ :  context[unbound _ (?E ;; ?b)] |- _ => unfoldg unbound; destruct_key_if
|   |- context[unbound _ (?E ;; ?b)]      => unfoldg unbound; destruct_key_if
end. (* We don't just put destruct_key_if 1x here, because if it fails, match has to try
        the next branch 
Ltac compare_keys := match goal with
| _ :  context[binds _ _ (?E ;; ?b)] |- _ => unfoldg binds
|   |- context[binds _ _ (?E ;; ?b)]      => unfoldg binds
| _ :  context[unbound _ (?E ;; ?b)] |- _ => unfoldg unbound
|   |- context[unbound _ (?E ;; ?b)]      => unfoldg unbound
end; destruct_key_if. *)

Lemma map_head: forall (E: t) (b: B) (f: B -> B), map f (E ;; b) = (map f E) ;; (f b).
Proof.
  intros. simpl. reflexivity.
Qed.
Lemma concat_cons_assoc: forall (E1: t) (E2: t) (b: B), E1 & (E2 ;; b) = (E1 & E2) ;; b.
Proof.
  intros. simpl. reflexivity.
Qed.
Lemma concat_assoc: forall (E1 E2 E3: t), (E1 & E2) & E3 = E1 & (E2 & E3).
Proof. intros. apply app_assoc. Qed. 
Lemma binds_unbound_head_inv: forall E b, unbound (key b) (E ;; b) -> False.
Proof.
  intros. compare_keys.
  + discriminate H.
  + apply n. reflexivity.
Qed.
Lemma unbound_cons_inv: forall E k b, unbound k (E ;; b) -> unbound k E.
Proof.
  intros. compare_keys.
  + inversion H.
  + assumption.
Qed.
Lemma binds_push_eq_inv: forall E a b,
  binds (key a) (value b) (E ;; a) -> value a = value b.
Proof.
  intros. compare_keys.
  + inversion H. reflexivity.
  + contradiction n. reflexivity.
Qed.
Lemma binds_binding_inv: forall k v E, binds k v E -> exists b, key b = k /\ value b = v.
Proof.
  intros k v E. induction E; intros.
  + empty_binds_contradiction.
  + compare_keys.
    - inversion H. rewrite -> H1. exists a. symmetry in e. split; assumption.
    - unfold binds in IHE. apply IHE. assumption.
Qed.
Lemma binds_map: forall b (f : B -> B) E,
  (forall a, key (f a) = key a) ->
  binds (key b) (value b) E -> 
  binds (key (f b)) (value (f b)) (map f E).
Proof.
  intros. induction E.
  + empty_binds_contradiction.
  + simpl. unfoldg binds. rewrite -> (H a). rewrite -> (H b). destruct_key_if.
    - inv H0. do 3 f_equal. symmetry in e. apply key_val_eq_eq; assumption.
    - rewrite -> (H b) in IHE. apply (IHE H0).
Qed.
Lemma unbound_map: forall k (f : B -> B) E,
  (forall a, key (f a) = key a) ->
  unbound k E -> 
  unbound k (map f E).
Proof.
  intros. induction E.
  + simpl. assumption.
  + simpl. unfoldg unbound. fold get. rewrite -> (H a). destruct_key_if.
    - discriminate H0.
    - apply IHE. assumption.
Qed.
Lemma binds_concat_right : forall k v E1 E2,
  binds k v E2 ->
  binds k v (E1 & E2).
Proof.
  intros. induction E2.
  + empty_binds_contradiction.
  + rewrite -> concat_cons_assoc. compare_keys.
    - assumption.
    - apply IHE2. assumption.
Qed.
Lemma binds_concat_left_inv : forall k v E1 E2,
  unbound k E2 ->
  binds k v (E1 & E2) ->
  binds k v E1.
Proof.
  intros. induction E2.
  + simpl in H0. assumption.
  + rewrite -> concat_cons_assoc in H0. compare_keys.
    - exfalso. rewrite -> e in H. apply (binds_unbound_head_inv H).
    - apply IHE2. apply (unbound_cons_inv H). assumption.
Qed.
Lemma binds_concat_left : forall k v E1 E2,
  binds k v E1 ->
  unbound k E2 ->
  binds k v (E1 & E2).
Proof.
  intros. induction E2.
  + simpl. assumption.
  + rewrite -> concat_cons_assoc. compare_keys.
    - exfalso. rewrite -> e in H0. apply (binds_unbound_head_inv H0).
    - apply IHE2. apply (unbound_cons_inv H0).
Qed.
Lemma binds_unbound_inv : forall k v E,
  binds k v E -> unbound k E -> False.
Proof.
  intros. induction E.
  + inv H.
  + compare_keys.
    - subst. apply (binds_unbound_head_inv H0).
    - apply IHE. assumption. apply (unbound_cons_inv H0).
Qed.
Lemma binds_unique : forall k v1 v2 E,
  binds k v1 E -> binds k v2 E -> v1 = v2.
Proof.
  intros. induction E.
  + inv H.
  + compare_keys.
    - inv H. inv H0. reflexivity.
    - inv H. inv H0. apply IHE; assumption.
Qed.
Lemma build_unbound: forall k E, (forall k' v, binds k' v E -> k' <> k) -> unbound k E.
Proof.
  intros. induction E.
  + reflexivity.
  + compare_keys.
    - specialize (H k (value a)). compare_keys.
      * specialize (H eq_refl). contradiction H. reflexivity.
      * contradiction n. 
    - apply IHE. intros. destruct (eq_key_dec k' (key a)) eqn: Hdestr.
      * rewrite <- e in n. intro. symmetry in H1. contradiction H1.
      * apply H with v. unfoldg binds. rewrite -> Hdestr. assumption.
Qed.
Lemma expose_two_binds: forall b1 b2 E,
  binds (key b1) (value b1) E -> 
  binds (key b2) (value b2) E -> (
    (exists F G H, E = F ;; b1 & G ;; b2 & H /\ 
                   key b1 <> key b2 /\
                   unbound (key b1) (G ;; b2 & H) /\
                   unbound (key b2) H) \/
    (exists F G,   E = F ;; b1 & G /\ 
                   b1 = b2 /\
                   unbound (key b1) G) \/
    (exists F G H, E = F ;; b2 & G ;; b1 & H /\ 
                   key b1 <> key b2 /\
                   unbound (key b1) H /\
                   unbound (key b2) (G ;; b1 & H))
  ).
Proof. Admitted.
End Env.

(* Module decs: For lists of declarations: [list ndec] or [label => dec] *)
Module decsParams <: EnvParams.
Definition K := label.
Definition V := dec.
Definition B := ndec.
Definition key(d: ndec): label := match d with
| ndec_fld n T => label_fld n
| ndec_mtd n T U => label_mtd n
end.
Definition value(d: ndec): dec := match d with
| ndec_fld n T => dec_fld T
| ndec_mtd n T U => dec_mtd T U
end.
Definition eq_key_dec := eq_label_dec.
Lemma key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2.
  + inv H. inv H0. reflexivity.
  + inv H.
  + inv H.
  + inv H. inv H0. reflexivity.
Qed.
End decsParams.
Module decs := Env(decsParams).

(* Module inis: For lists of initialisations: [list nini] or [label => ini] *)
Module inisParams <: EnvParams.
Definition K := label.
Definition V := ini.
Definition B := nini.
Definition key(i: nini): label := match i with
| nini_fld n T => label_fld n
| nini_mtd n T e => label_mtd n
end.
Definition value(i: nini): ini := match i with
| nini_fld n T => ini_fld T
| nini_mtd n T e => ini_mtd T e
end.
Definition eq_key_dec := eq_label_dec.
Lemma key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2.
  + inv H. inv H0. reflexivity.
  + inv H.
  + inv H.
  + inv H. inv H0. reflexivity.
Qed.
End inisParams.
Module inis := Env(inisParams).

(* Module tenv: For type environments: [var => typ] *)
Module tenvParams <: EnvParams.
Definition K := var.
Definition V := typ.
Definition B := (var * typ)%type.
Definition key := @fst var typ.
Definition value := @snd var typ.
Definition eq_key_dec := eq_nat_dec.
Lemma key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2. unfold key, fst, value, snd in *. subst. reflexivity.
Qed.
End tenvParams.
Module tenv := Env(tenvParams).

(* Module venv: For value environments: [var => inis] *)
Module venvParams <: EnvParams.
Definition K := var.
Definition V := inis.t.
Definition B := (var * inis.t)%type.
Definition key := @fst var inis.t.
Definition value := @snd var inis.t.
Definition eq_key_dec := eq_nat_dec.
Lemma key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2. unfold key, fst, value, snd in *. subst. reflexivity.
Qed.
End venvParams.
Module venv := Env(venvParams).

Module Type IntersectionPreview.

(* Will be part of syntax: *)
Parameter t_and: typ -> typ -> typ.
Parameter t_or:  typ -> typ -> typ.

(* Left as an exercise for the reader ;-) We define intersection by the spec below. *)
Parameter intersect: decs.t -> decs.t -> decs.t.

Axiom intersect_spec_1: forall l d ds1 ds2,
  decs.binds   l d ds1 ->
  decs.unbound l ds2 ->
  decs.binds   l d (intersect ds1 ds2).

Axiom intersect_spec_2: forall l d ds1 ds2,
  decs.unbound l ds1 ->
  decs.binds   l d ds2 ->
  decs.binds   l d (intersect ds1 ds2).

Axiom intersect_spec_12_fld: forall n T1 T2 ds1 ds2,
  decs.binds (label_fld n) (dec_fld T1) ds1 ->
  decs.binds (label_fld n) (dec_fld T2) ds2 ->
  decs.binds (label_fld n) (dec_fld (t_and T1 T2)) (intersect ds1 ds2).

Axiom intersect_spec_12_mtd: forall n S1 T1 S2 T2 ds1 ds2,
  decs.binds (label_mtd n) (dec_mtd S1 T1) ds1 ->
  decs.binds (label_mtd n) (dec_mtd S2 T2) ds2 ->
  decs.binds (label_mtd n) (dec_mtd (t_or S1 S2) (t_and T1 T2)) (intersect ds1 ds2).

End IntersectionPreview.

(* Exercise: Give any implementation of `intersect`, and prove that it satisfies
   the specification. Happy hacking! ;-) *)
Module IntersectionPreviewImpl <: IntersectionPreview.

(* Will be part of syntax: *)
Parameter t_and: typ -> typ -> typ.
Parameter t_or:  typ -> typ -> typ.

Fixpoint get_fld(n: nat)(ds: decs.t): option typ := match ds with
  | nil => None
  | tail ;; d => match d with
      | ndec_fld m T => if eq_nat_dec n m then Some T else get_fld n tail
      | _ => get_fld n tail
      end
  end.
(*
Lemma get_fld_spec: forall n ds, decs.get (label_fld n) ds = dec_fld (get_fld n ds).
Proof.
*)

Fixpoint refine_dec(d1: ndec)(ds2: decs.t): ndec := match ds2 with
| nil => d1
| tail2 ;; d2 => match d1, d2 with
    | ndec_fld n1 T1   , ndec_fld n2 T2    => if eq_nat_dec n1 n2
                                              then ndec_fld n1 (t_and T1 T2) 
                                              else refine_dec d1 tail2
    | ndec_mtd n1 T1 S1, ndec_mtd n2 T2 S2 => if eq_nat_dec n1 n2
                                              then ndec_mtd n1 (t_or T1 T2) (t_and S1 S2) 
                                              else refine_dec d1 tail2
    | _, _ => refine_dec d1 tail2
    end
end.

Ltac destruct_matchee :=
  match goal with
  | [ Hm: match ?e1 with _ => _ end = _ |- _ ]  => 
      remember e1 as mExpr; destruct mExpr
  | [ Hm: if ?e1 then _ else _ = _ |- _ ]  => 
      remember e1 as mExpr; destruct mExpr
  end.

Lemma refine_dec_spec_fld: forall ds2 n T1 T2,
  decs.binds (label_fld n) (dec_fld T2) ds2 ->
  (refine_dec (ndec_fld n T1) ds2) = (ndec_fld n (t_and T1 T2)).
Proof. 
  intro ds2. induction ds2; intros.
  + decs.empty_binds_contradiction.
  + decs.compare_keys.
    - inv H. unfold decs.value, decsParams.value in H1. destruct a eqn: Heqa.
      * inv H1. inversion e. subst. simpl. destruct (eq_nat_dec n0 n0). reflexivity.
        contradiction n. reflexivity.
      * inv H1.
    - simpl. destruct a eqn: Heqa. 
      * assert (Hnn: n <> n1). unfold not in *. intro. apply n0. simpl. f_equal. assumption.
        destruct (eq_nat_dec n n1). contradiction Hnn.
        apply IHds2. unfold decs.binds, decs.get. unfold decs.key, decsParams.key.
        assumption.
      * apply IHds2. unfold decs.binds, decs.get. unfold decs.key, decsParams.key.
        assumption.
Qed.

Lemma refine_dec_spec_mtd: forall ds2 n T1 S1 T2 S2,
  decs.binds (label_mtd n) (dec_mtd T2 S2) ds2 ->
  (refine_dec (ndec_mtd n T1 S1) ds2) = (ndec_mtd n (t_or T1 T2) (t_and S1 S2)).
Proof. 
  intro ds2. induction ds2; intros.
  + decs.empty_binds_contradiction.
  + decs.compare_keys.
    - inv H. destruct a eqn: Heqa.
      * inv H1.
      * inv H1. inversion e. subst. simpl. destruct (eq_nat_dec n0 n0). reflexivity.
        contradiction n. reflexivity.
    - simpl. destruct a eqn: Heqa. 
      * apply IHds2. assumption.
      * assert (Hnn: n <> n1). unfold not in *. intro. apply n0. simpl. f_equal. assumption.
        destruct (eq_nat_dec n n1). contradiction Hnn.
        apply IHds2. assumption.
Qed.

Lemma refine_dec_spec_label: forall d1 ds2, decs.key d1 = decs.key (refine_dec d1 ds2).
Proof.
  intros.
  induction ds2.
  + simpl. reflexivity.
  + unfold decs.key, decsParams.key. unfold refine_dec. destruct a; destruct d1.
    - destruct (eq_nat_dec n0 n).
      * simpl. reflexivity.
      * fold refine_dec. unfold decs.key, decsParams.key in IHds2.
        rewrite <- IHds2. reflexivity.
    - fold refine_dec. unfold decs.key, decsParams.key in IHds2.
        rewrite <- IHds2. reflexivity.
    - fold refine_dec. unfold decs.key, decsParams.key in IHds2.
        rewrite <- IHds2. reflexivity.
    - destruct (eq_nat_dec n0 n).
      * simpl. reflexivity.
      * fold refine_dec. unfold decs.key, decsParams.key in IHds2.
        rewrite <- IHds2. reflexivity.
Qed.

Lemma refine_dec_spec_unbound: forall d1 ds2, 
  decs.unbound (decs.key d1) ds2 ->
  decs.value (refine_dec d1 ds2) = decs.value d1.
Proof.
  intros.
  induction ds2.
  + simpl. reflexivity.
  + unfold decs.key, decsParams.key. unfold refine_dec. destruct a; destruct d1.
    - destruct (eq_nat_dec n0 n) eqn: Hn0ndec.
      * subst. 
        assert (Hkeq: (decs.key (ndec_fld n t0)) = (decs.key (ndec_fld n t)))
          by reflexivity.
        rewrite -> Hkeq in H.
        exfalso. apply (decs.binds_unbound_head_inv H).
      * fold refine_dec. apply IHds2.
        inv H. unfold decsParams.eq_key_dec in H1. 
        destruct (eq_label_dec (label_fld n0) (label_fld n)).
        { inv e. contradiction n1. reflexivity. }
        { unfold decs.unbound. unfold decs.key, decsParams.key. assumption. }
    - fold refine_dec. unfold decs.key, decsParams.key in *.
      apply decs.unbound_cons_inv in H. apply (IHds2 H).
    - fold refine_dec. unfold decs.key, decsParams.key in *.
      apply decs.unbound_cons_inv in H. apply (IHds2 H).
    - destruct (eq_nat_dec n0 n) eqn: Hn0ndec.
      * subst. 
        assert (Hkeq: (decs.key (ndec_mtd n t1 t2)) = (decs.key (ndec_mtd n t t0)))
          by reflexivity.
        rewrite -> Hkeq in H.
        exfalso. apply (decs.binds_unbound_head_inv H).
      * fold refine_dec. apply IHds2.
        inv H. unfold decsParams.eq_key_dec in H1. 
        destruct (eq_label_dec (label_mtd n0) (label_mtd n)).
        { inv e. contradiction n1. reflexivity. }
        { unfold decs.unbound. unfold decs.key, decsParams.key. assumption. }
Qed.

Definition refine_decs(ds1: decs.t)(ds2: decs.t): decs.t := 
  map (fun d1 => refine_dec d1 ds2) ds1.

Lemma refine_decs_spec_unbound: forall l d ds1 ds2,
  decs.binds   l d ds1 ->
  decs.unbound l ds2 ->
  decs.binds   l d (refine_decs ds1 ds2).
Proof.
  intros. unfold refine_decs.
  assert (Hex: exists nd, decs.key nd = l /\ decs.value nd = d).
    apply (@decs.binds_binding_inv l d ds1 H).
  destruct Hex as [nd [Hl Hd]]. subst.
  remember (fun d1 => refine_dec d1 ds2) as f.
  assert (Hk: (decs.key nd) = decs.key (f nd)).
    subst. apply (refine_dec_spec_label nd ds2).
  rewrite -> Hk.
  assert (Hv: (decs.value nd) = decs.value (f nd)).
    subst. symmetry. apply (refine_dec_spec_unbound _ H0).
  rewrite -> Hv.
  apply decs.binds_map. 
    intro. rewrite -> Heqf. symmetry. apply refine_dec_spec_label.
    assumption.
Qed.

Lemma refine_decs_spec_unbound_preserved: forall l ds1 ds2,
  decs.unbound l ds1 ->
  decs.unbound l (refine_decs ds1 ds2).
Proof.
  intros. unfold refine_decs. remember (fun d1 => refine_dec d1 ds2) as f.
  refine (@decs.unbound_map l f ds1 _ H).
  subst. intro. symmetry. apply refine_dec_spec_label.
Qed.

Lemma refine_decs_spec_fld: forall n ds1 ds2 T1 T2,
  decs.binds (label_fld n) (dec_fld T1) ds1 ->
  decs.binds (label_fld n) (dec_fld T2) ds2 ->
  decs.binds (label_fld n) (dec_fld (t_and T1 T2)) (refine_decs ds1 ds2).
Proof.
  intros n ds1 ds2 T1 T2 H. induction ds1; intros.
  + decs.empty_binds_contradiction.
  + unfold decs.binds, decs.get in H. destruct a eqn: Heqa.
    - fold decs.get in H. unfold decs.key, decsParams.key in H.
      destruct (decsParams.eq_key_dec (label_fld n) (label_fld n0)).
      * inv H. inv e.
        unfold decs.binds, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 T1) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_fld n0) (label_fld n0)). {
          f_equal. rewrite -> (@refine_dec_spec_fld ds2 n0 T1 T2 H0).
          simpl. reflexivity. 
        } { contradiction n. reflexivity. }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.binds, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 t) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_fld n) (label_fld n0)). {
          inv e. contradiction Hnn. reflexivity.
        } {
          unfold decs.binds in *. apply IHds1; assumption.
        }
    - fold decs.get in H. unfold decs.key, decsParams.key in H.
      destruct (decsParams.eq_key_dec (label_fld n) (label_fld n0)).
      * inv H. inv e.
        unfold decs.binds, decs.get. simpl. fold decs.get.
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 t t0) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_fld n0) (label_mtd n0)). {
          inv H2.
        } {
          unfold decs.binds in *. apply IHds1; assumption.
        }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.binds, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 t t0) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_fld n) (label_fld n0)). {
          inv e. contradiction Hnn. reflexivity.
        } {
          destruct (decsParams.eq_key_dec (label_fld n) (label_mtd n0)).
          + inv e.
          + unfold decs.binds in *. apply IHds1; assumption.
        }
Qed.

Lemma refine_decs_spec_mtd: forall n ds1 ds2 T1 S1 T2 S2,
  decs.binds (label_mtd n) (dec_mtd T1 S1) ds1 ->
  decs.binds (label_mtd n) (dec_mtd T2 S2) ds2 ->
  decs.binds (label_mtd n) (dec_mtd (t_or T1 T2) (t_and S1 S2)) (refine_decs ds1 ds2).
Proof.
  intros n ds1 ds2 T1 S1 T2 S2 H. induction ds1; intros.
  + decs.empty_binds_contradiction.
  + unfold decs.binds, decs.get in H. destruct a eqn: Heqa.
    - fold decs.get in H. unfold decs.key, decsParams.key in H.
      destruct (decsParams.eq_key_dec (label_mtd n) (label_mtd n0)).
      * inv H. inv e.
        unfold decs.binds, decs.get. simpl. fold decs.get.
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 t) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_mtd n0) (label_fld n0)). {
          inv H2.
        } {
          unfold decs.binds in *. apply IHds1; assumption.
        }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.binds, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 t) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_mtd n) (label_mtd n0)). {
          inv e. contradiction Hnn. reflexivity.
        } {
          destruct (decsParams.eq_key_dec (label_mtd n) (label_fld n0)).
          + inv e.
          + unfold decs.binds in *. apply IHds1; assumption.
        }
    - fold decs.get in H. unfold decs.key, decsParams.key in H.
      destruct (decsParams.eq_key_dec (label_mtd n) (label_mtd n0)).
      * inv H. inv e.
        unfold decs.binds, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 T1 S1) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_mtd n0) (label_mtd n0)). {
          f_equal. rewrite -> (@refine_dec_spec_mtd ds2 n0 T1 S1 T2 S2 H0).
          simpl. reflexivity. 
        } { contradiction n. reflexivity. }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.binds, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 t t0) ds2).
        unfold decs.key, decsParams.key.
        destruct (decsParams.eq_key_dec (label_mtd n) (label_mtd n0)). {
          inv e. contradiction Hnn. reflexivity.
        } {
          unfold decs.binds in *. apply IHds1; assumption.
        } 
Qed.


(* refined decs shadow the outdated decs of ds2 *)
Definition intersect(ds1 ds2: decs.t): decs.t := ds2 & (refine_decs ds1 ds2).

Lemma intersect_spec_1: forall l d ds1 ds2,
  decs.binds   l d ds1 ->
  decs.unbound l ds2 ->
  decs.binds   l d (intersect ds1 ds2).
Proof.
  intros. unfold intersect. apply decs.binds_concat_right.
  apply refine_decs_spec_unbound; assumption.
Qed.

Lemma intersect_spec_2: forall l d ds1 ds2,
  decs.unbound l ds1 ->
  decs.binds   l d ds2 ->
  decs.binds   l d (intersect ds1 ds2).
Proof.
  intros. unfold intersect.
  apply (@decs.binds_concat_left l d ds2 (refine_decs ds1 ds2) H0). 
  apply (@refine_decs_spec_unbound_preserved l ds1 ds2 H). 
Qed.

Lemma intersect_spec_12_fld: forall n T1 T2 ds1 ds2,
  decs.binds (label_fld n) (dec_fld T1) ds1 ->
  decs.binds (label_fld n) (dec_fld T2) ds2 ->
  decs.binds (label_fld n) (dec_fld (t_and T1 T2)) (intersect ds1 ds2).
Proof.
  intros. unfold intersect. apply decs.binds_concat_right.
  apply refine_decs_spec_fld; assumption.
Qed.

Lemma intersect_spec_12_mtd: forall n S1 T1 S2 T2 ds1 ds2,
  decs.binds (label_mtd n) (dec_mtd S1 T1) ds1 ->
  decs.binds (label_mtd n) (dec_mtd S2 T2) ds2 ->
  decs.binds (label_mtd n) (dec_mtd (t_or S1 S2) (t_and T1 T2)) (intersect ds1 ds2).
Proof.
  intros. unfold intersect. apply decs.binds_concat_right.
  apply refine_decs_spec_mtd; assumption.
Qed.

End IntersectionPreviewImpl.


(** Operational Semantics **)
(* Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
   Whenever we introduce a new avar_f (only happens in red_new), we choose one
   which is not in the store, so we never have name clashes. *) 
Inductive red : venv.t -> trm -> venv.t -> trm -> Prop :=
  (* computation rules *)
  | red_call : forall (s: venv.t) (x y: var) (m: nat) (T: typ) (is: inis.t) (body: trm),
      venv.binds x is s ->
      inis.binds (label_mtd m) (ini_mtd T body) is ->
      red s (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) 
          s (open_trm y body)
  | red_sel : forall (s: venv.t) (x: var) (y: avar) (l: nat) (is: inis.t),
      venv.binds x is s ->
      inis.binds (label_fld l) (ini_fld y) is ->
      red s (trm_sel (trm_var (avar_f x)) l) s 
            (trm_var y)
  | red_new : forall (s: venv.t) (is: inis.t) (e: trm) (x: var),
      venv.unbound x s ->
      red s (trm_new is e)
          (s ;; (x, is)) (open_trm x e)
  (* congruence rules *)
  | red_call1 : forall s o m a s' o',
      red s o s' o' ->
      red s  (trm_call o  m a) 
          s' (trm_call o' m a)
  | red_call2 : forall s x m a s' a',
      red s a s' a' ->
      red s  (trm_call (trm_var (avar_f x)) m a ) 
          s' (trm_call (trm_var (avar_f x)) m a')
  | red_sel1 : forall s o l s' o',
      red s o s' o' ->
      red s  (trm_sel o  l)
          s' (trm_sel o' l).

(* The store is not an argument of the typing judgment because
   * it's only needed in typing_trm_var_s
   * we must allow types in Gamma to depend on values in the store, which seems complicated
   * how can we ensure that the store is well-formed? By requiring it in the "leaf"
     typing rules (those without typing assumptions)? Typing rules become unintuitive,
     and maybe to prove that store is wf, we need to prove what we're about to prove...
*)

(* Term typing *)
Inductive has : tenv.t -> trm -> label -> dec -> Prop :=
  | has_dec : forall G e l d ds,
      typing_trm G e (typ_rcd ds) ->
      decs.binds l d ds ->
      has G e l d
with typing_trm : tenv.t -> trm -> typ -> Prop :=
  | typing_trm_var : forall G x T,
      tenv.binds x T G ->
      typing_trm G (trm_var (avar_f x)) T
  | typing_trm_sel : forall G e l T,
      has G e (label_fld l) (dec_fld T) ->
      typing_trm G (trm_sel e l) T
  | typing_trm_call : forall G t m U V u,
      has G t (label_mtd m) (dec_mtd U V) ->
      typing_trm G u U ->
      typing_trm G (trm_call t m u) V
  | typing_trm_new : forall G nis ds t T,
      typing_inis G nis ds -> (* no self reference yet, no recursion *)
      (forall x, tenv.unbound x G ->
                 typing_trm (G ;; (x, typ_rcd ds)) (open_trm x t) T) ->
      typing_trm G (trm_new nis t) T
with typing_ini : tenv.t -> nini -> ndec -> Prop :=
  | typing_ini_fld : forall G l v T,
      typing_trm G (trm_var v) T ->
      typing_ini G (nini_fld l v) (ndec_fld l T)
  | typing_ini_mtd : forall G m S T t,
      (forall x, tenv.unbound x G ->
                 typing_trm (G ;; (x, S)) (open_trm x t) T) ->
      typing_ini G (nini_mtd m S t) (ndec_mtd m S T)
with typing_inis : tenv.t -> inis.t -> decs.t -> Prop :=
  | typing_inis_nil : forall G,
      typing_inis G nil nil
  | typing_inis_cons : forall G is i ds d,
      typing_inis G is ds ->
      typing_ini  G i d ->
      typing_inis G (is ;; i) (ds ;; d).

Scheme has_mut         := Induction for has         Sort Prop
with   typing_trm_mut  := Induction for typing_trm  Sort Prop
with   typing_ini_mut  := Induction for typing_ini  Sort Prop
with   typing_inis_mut := Induction for typing_inis Sort Prop.

Combined Scheme typing_mutind from has_mut, typing_trm_mut, typing_ini_mut, typing_inis_mut.

Inductive wf_venv: venv.t -> tenv.t -> Prop :=
  | wf_venv_nil : wf_venv nil nil
  | wf_venv_cons : forall s g x is ds,
      wf_venv s g ->
      venv.unbound x s ->
      tenv.unbound x g ->
      typing_inis g is ds ->
      wf_venv (s ;; (x, is)) (g ;; (x, (typ_rcd ds))).

Lemma invert_wf_venv_cons: forall s G x is ds,
  wf_venv (s ;; (x, is)) (G ;; (x, typ_rcd ds)) ->
  wf_venv s G /\ venv.unbound x s /\ tenv.unbound x G /\ typing_inis G is ds.
Proof.
  intros. inv H. auto.
Qed.

Lemma invert_has: forall G e l d,
  has G e l d ->
  exists ds, typing_trm G e (typ_rcd ds) /\ decs.binds l d ds.
Proof.
  intros. inv H. eauto.
Qed.

Lemma invert_typing_trm_var: forall G x T,
  typing_trm G (trm_var (avar_f x)) T ->
  tenv.binds x T G.
Proof.
  intros. inv H. assumption.
Qed.

Lemma invert_typing_trm_call: forall G t m V u,
  typing_trm G (trm_call t m u) V ->
  exists U, has G t (label_mtd m) (dec_mtd U V) /\ typing_trm G u U.
Proof.
  intros. inv H. eauto.
Qed.

(*
Lemma invert_typing_var_s: forall s x ds,
  typing_trm nil s (trm_var (avar_f x)) (typ_rcd ds) ->
  exists is, venv.binds x is s /\ typing_inis nil s is ds.
Proof.
  intros. inv H.
  + tenv.empty_binds_contradiction.
  + eauto.
Qed.

Lemma invert_typing_var_s_with_given_inis: forall G s x is ds,
  typing_trm G s (trm_var (avar_f x)) (typ_rcd ds) ->
  venv.binds x is s ->
  typing_inis nil s is ds.
Proof.
  intros G s x is ds Hty Hbv.
  inversion Hty; subst.
  (* typing_var_g *)
  + exfalso. apply (@venv.binds_unbound_inv x is s); assumption.
  (* typing_var_s *)
  + assert (is0 = is) by apply (venv.binds_unique H4 Hbv). subst. assumption.
Qed.
*)

Lemma invert_typing_ini_key: forall G i d, 
  typing_ini G i d -> inis.key i = decs.key d.
Proof.
  intros. inv H; reflexivity.
Qed.

Lemma invert_typing_ini_cases: forall G i d, 
  typing_ini G i d ->
  (exists l x T, i = (nini_fld l x) /\ d = (ndec_fld l T)) \/
  (exists m e T U, i = (nini_mtd m T e) /\ d = (ndec_mtd m T U)).
Proof.
  intros. inv H.
  + left. exists l v T. split; reflexivity.
  + right. exists m t S T. split; reflexivity.
Qed.

Lemma invert_typing_ini: forall G i d, 
  typing_ini G i d ->
  exists k iv dv, inis.key i = k /\ inis.value i = iv /\ 
                  decs.key d = k /\ decs.value d = dv.
Proof.
  intros. destruct (invert_typing_ini_cases H)
    as [[l [x [T [Heq1 Heq2]]]] | [m [e [T [U [Heq1 Heq2]]]]]].
  + exists (label_fld l) (ini_fld x) (dec_fld T). subst. auto.
  + exists (label_mtd m) (ini_mtd T e) (dec_mtd T U). subst. auto.
Qed.

Lemma venv_gen_gt : forall s, exists x, forall y i, venv.binds y i s -> y < x.
Proof.
  intros. induction s.
  + exists 0. intros. venv.empty_binds_contradiction.
  + destruct IHs as [x IH].
    destruct (le_lt_dec x (venv.key a)) as [Hc | Hc].
    - exists (S (venv.key a)). intros.
      unfold venv.binds, venv.get in H. fold venv.get in H. 
      unfold venvParams.eq_key_dec in H.
      destruct (eq_nat_dec y (venv.key a)).
      * omega.
      * unfold venv.binds in IH. specialize (IH y i H). omega.
    - exists x. intros.
      unfold venv.binds, venv.get in H. fold venv.get in H. 
      unfold venvParams.eq_key_dec in H.
      destruct (eq_nat_dec y (venv.key a)).
      * omega.
      * apply (IH y i). unfold venv.binds. assumption.
Qed.

Lemma venv_gen_fresh : forall s, exists x, venv.unbound x s.
Proof.
  intros. destruct (venv_gen_gt s) as [x H]. exists x.
  apply venv.build_unbound. intros. specialize (H k' v H0). omega.
Qed.

Lemma decs_binds_to_inis_binds: forall G l d is ds,
  typing_inis G is ds ->
  decs.binds l d ds ->
  exists i, inis.binds l i is.
Proof.
  intros l d is ds s Hty Hbi. induction Hty.
  + decs.empty_binds_contradiction.
  + inis.compare_keys.
    - subst. exists (inis.value i). reflexivity.
    - destruct (invert_typing_ini H) as [k [iv [dv [Hik [Hiv [Hdk Hdv]]]]]]. subst.
      decs.compare_keys.
      * rewrite <- Hdk in n. contradiction e.
      * apply IHHty. assumption.
Qed.

Lemma inis_binds_fld_sync_val: forall n v is,
  inis.binds (label_fld n) v is -> exists x, v = (ini_fld x).
Proof.
  intros. induction is.
  + inis.empty_binds_contradiction.
  + inis.unfoldg inis.binds. destruct a; simpl in H; inis.destruct_key_if.
      * inv H. exists a. reflexivity.
      * apply IHis. unfold inis.binds. assumption.
      * inv e. (* contradiction *)
      * apply IHis. unfold inis.binds. assumption.
Qed.

Lemma inis_binds_mtd_sync_val: forall n v is,
  inis.binds (label_mtd n) v is -> exists T e, v = (ini_mtd T e).
Proof.
  intros. induction is.
  + inis.empty_binds_contradiction.
  + inis.unfoldg inis.binds. destruct a; simpl in H; inis.destruct_key_if.
      * inv e. (* contradiction *)
      * apply IHis. unfold inis.binds. assumption.
      * inv H. exists t t0. reflexivity.
      * apply IHis. unfold inis.binds. assumption.
Qed.

(*
Lemma decs_binds_fld_to_inis_binds_fld: forall l d is ds s,
  typing_inis nil s is ds ->
  decs.binds l (dec_fld T ds ->
  exists i, inis.binds l i is.
Proof.
*)

Definition progress_for(s: venv.t)(e: trm) :=
  (* can step *)
  (exists s' e', red s e s' e') \/
  (* or is a value *)
  (exists x is, e = (trm_var (avar_f x)) /\ venv.binds x is s).

Ltac auto_specialize :=
  repeat match goal with
  | Impl: ?Cond ->            _ |- _ => let HC := fresh in 
      assert (HC: Cond) by auto; specialize (Impl HC); clear HC
  | Impl: forall (_ : ?Cond), _ |- _ => match goal with
      | p: Cond |- _ => specialize (Impl p)
      end
  end.

Ltac rewrite_with EqT := match goal with
| H: EqT |- _ => rewrite H in *; clear H
end.

Lemma tenv_binds_to_venv_binds: forall s G x T,
  wf_venv s G ->
  tenv.binds x T G ->
  exists is, venv.binds x is s.
Admitted.

Lemma invert_wf_venv: forall s G,
  wf_venv s G -> 
    forall x is ds, 
      venv.binds x is s -> 
      tenv.binds x (typ_rcd ds) G ->
      typing_inis G is ds.
Admitted.

Lemma expose_two_binds_in_wf_venv: forall s G x y isx isy dsx dsy,
  wf_venv s G ->
  venv.binds x isx s ->
  tenv.binds x (typ_rcd dsx) G ->
  venv.binds y isy s ->
  tenv.binds y (typ_rcd dsy) G -> (
    (exists s1 s2 s3 G1 G2 G3,
       s = s1 ;; (x,     isx      ) & s2 ;; (y,     isy      ) & s3 /\
       G = G1 ;; (x, (typ_rcd dsx)) & G2 ;; (y, (typ_rcd dsy)) & G3 /\
       x <> y /\
       venv.unbound x (s2 ;; (y,     isy      ) & s3) /\
       tenv.unbound x (G2 ;; (y, (typ_rcd dsy)) & G3) /\
       venv.unbound y s3 /\
       tenv.unbound y G3) \/
    (exists s1 s2 G1 G2,
       s = s1 ;; (x,      isx     ) & s2 /\
       G = G1 ;; (x, (typ_rcd dsx)) & G2 /\
       x = y /\
       isx = isy /\
       dsx = dsy /\
       venv.unbound x s2 /\
       tenv.unbound x G2) \/
    (exists s1 s2 s3 G1 G2 G3,
       s = s1 ;; (y,     isy      ) & s2 ;; (x,     isx      ) & s3 /\
       G = G1 ;; (y, (typ_rcd dsy)) & G2 ;; (x, (typ_rcd dsx)) & G3 /\
       x <> y /\
       venv.unbound y (s2 ;; (x,     isx      ) & s3) /\
       tenv.unbound y (G2 ;; (x, (typ_rcd dsx)) & G3) /\
       venv.unbound x s3 /\
       tenv.unbound x G3)
  ).
Admitted.

Lemma shrink_wf_venv: forall s G x is T,
  wf_venv s G ->
  venv.binds x is s ->
  tenv.binds x  T G ->
  exists (s1 s2: venv.t) (G1 G2: tenv.t), 
    s = s1 ;; (x, is) & s2 /\
    G = G1 ;; (x,  T) & G2 /\
    wf_venv (s1 ;; (x, is)) (G1 ;; (x, T)).
Admitted.

(*
Lemma shrink_wf_venv: forall s G y T,
  wf_venv s G ->
  tenv.binds y T G ->
  exists (s1 s2: venv.t) (G1 G2: tenv.t) (is: inis.t), 
    s = s1 ;; (y, is) & s2 /\
    G = G1 ;; (y,  T) & G2 /\
    wf_venv (s1 ;; (y, is)) (G1 ;; (y, T)).
Admitted.
*)

Lemma restrict_wf_venv: forall s G1 G2,
  wf_venv s (G1 & G2) ->
  exists s1 s2, s = s1 & s2 /\ wf_venv s1 G1.
Admitted.

(*Lemma invert_wf_venv_cons*)

Tactic Notation "keep" constr(E) "as" ident(H) :=
    let Temp := type of E in assert (H: Temp) by apply E.

Lemma progress_proof: forall G e T,
  typing_trm G e T -> forall s, wf_venv s G -> progress_for s e.
Proof.
  Definition P_has :=         fun G e l d (Hhas: has G e l d)   
                              => forall s, wf_venv s G -> progress_for s e.
  Definition P_typing_trm :=  fun G e T (Hty: typing_trm G e T)
                              => forall s, wf_venv s G -> progress_for s e.
  Definition P_typing_ini :=  fun G i d (Htyp: typing_ini G i d)
                              => True.
  Definition P_typing_inis := fun G is ds (Htyp: typing_inis G is ds)
                              => True.
  apply (typing_trm_mut P_has P_typing_trm P_typing_ini P_typing_inis);
    unfold P_has, P_typing_trm, P_typing_ini, P_typing_inis, progress_for;
    intros;
    try apply I;
    auto_specialize.
  (* case has_dec *)
  + assumption. 
  (* case typing_trm_var *)
  + right. destruct (tenv_binds_to_venv_binds H b) as [is Hbv].
    exists x is. split. reflexivity. assumption.
  (* case typing_trm_sel *)
  + left. destruct H as [IH | IH].
    (* receiver is an expression *)
    - destruct IH as [s' [e' IH]]. do 2 eexists. apply (red_sel1 l IH). 
    (* receiver is a var *)
    - destruct IH as [x [is [Heq Hbv]]]. subst.
      destruct (invert_has h) as [ds [Hty Hbd]].
      keep (invert_typing_trm_var Hty) as Hbt.
      keep (invert_wf_venv H0 Hbv Hbt) as Hty2.
      destruct (decs_binds_to_inis_binds Hty2 Hbd) as [i Hbi].
      destruct (inis_binds_fld_sync_val Hbi) as [y Heq]. subst.
      exists s (trm_var y).
      apply (red_sel Hbv Hbi).
  (* case typing_trm_call *)
  + left. destruct H as [IHrec | IHrec].
    (* case receiver is an expression *)
    - destruct IHrec as [s' [e' IHrec]]. do 2 eexists. apply (red_call1 m _ IHrec).
    (* case receiver is  a var *)
    - destruct IHrec as [x [is [Heqx Hbv]]]. subst.
      destruct H0 as [IHarg | IHarg].
      (* arg is an expression *)
      * destruct IHarg as [s' [e' IHarg]]. do 2 eexists. apply (red_call2 x m IHarg).
      (* arg is a var *)
      * destruct IHarg as [y [is' [Heqy Hbv']]]. subst. 
        destruct (invert_has h) as [ds [Hty Hbd]].
        keep (invert_typing_trm_var Hty) as Hbt.
        keep (invert_wf_venv H1 Hbv Hbt) as Hty2.
        destruct (decs_binds_to_inis_binds Hty2 Hbd) as [i Hbi].
        destruct (inis_binds_mtd_sync_val Hbi) as [U' [e Heq]]. subst.
        exists s (open_trm y e).
        apply (red_call y Hbv Hbi).
  (* case typing_trm_new *)
  + left. destruct (venv_gen_fresh s) as [x Hxub].
    exists (s ;; (x, nis)) (open_trm x t).
    apply red_new. assumption.
Qed.

Theorem progress: forall s G e T,
  wf_venv s G ->
  typing_trm G e T -> 
  (
    (* can step *)
    (exists s' e', red s e s' e') \/
    (* or is a value *)
    (exists x is, e = (trm_var (avar_f x)) /\ venv.binds x is s)
  ).
Proof.
  intros.
  keep (progress_proof H0 H) as P. unfold progress_for in P. apply P.
Qed.

Print Assumptions progress.

Lemma extract_typing_ini_from_typing_inis: forall G l i is d ds,
  typing_inis G is ds ->
  inis.binds l (inis.value i) is ->
  decs.binds l (decs.value d) ds ->
  typing_ini G i d.
Proof.
Admitted.

Lemma invert_typing_mtd_ini_inside_typing_inis: forall G is ds m S1 S2 T body,
  typing_inis G is ds ->
  inis.binds (label_mtd m) (ini_mtd S1 body) is ->
  decs.binds (label_mtd m) (dec_mtd S2 T) ds ->
  (* conclusion is the premise needed to construct a typing_mtd_ini: *)
  (forall y, tenv.unbound y G -> typing_trm (G ;; (y, S2)) (open_trm y body) T).
Proof.
Admitted.

(* TODO need also y unbound in s2 
Lemma split_store_in_typing_trm_var_s: forall G y ds,
  typing_trm G (trm_var (avar_f y)) (typ_rcd ds) ->
  exists s1 s2 is, s = (s1 ;; (y, is) & s2) /\
                   typing_inis nil s1 is ds.
Admitted. *)

(*
  venv.unbound y s1 ->
  venv.unbound y s2 -> 
  typing_trm (nil ;; (y, S)) (s1 & s2) e T ->
  typing_trm (s1 ;; (y, S) & s2) e T
*)

(*
Lemma strengthen_typing_trm

typing_trm G (trm_var (avar_f x)) (typ_rcd ds)
wf_venv s G <-- don't mix this in
and just use "expose"
*)

Ltac unfoldp :=
  unfold venvParams.K, venvParams.V, venvParams.B,
         tenvParams.K, tenvParams.V, tenvParams.B  in *.

Theorem preservation: forall s G e T s' e',
  wf_venv s G -> typing_trm G e T -> red s e s' e' ->
  (exists G', wf_venv s' G' /\ typing_trm G' e' T).
Proof.
  intros s G e T s' e' Hwf Hty Hred. induction Hred.
  (* red_call *)
  + rename H into Hvbx. rename H0 into Hibm.
    exists G. split. apply Hwf.
    apply invert_typing_trm_call in Hty. 
    destruct Hty as [S [Hhas Htyy]].
    apply invert_typing_trm_var in Htyy. rename Htyy into Htby.
    apply invert_has in Hhas. 
    destruct Hhas as [ds [Htyx Hdbm]].
    apply invert_typing_trm_var in Htyx. rename Htyx into Htbx.
    destruct (shrink_wf_venv Hwf Hvbx Htbx) as [s1 [s2 [G1 [G2 [Heqs [HeqG Hwf']]]]]].
    destruct (invert_wf_venv_cons Hwf') as [_ [Hvux [Htux Hisds]]].
    keep (invert_typing_mtd_ini_inside_typing_inis Hisds Hibm Hdbm) as Hmtd.

    (* G1 is G until (but excluding) x. If y is after x, then y is unbound in G1,
       and we can specialize Hmtd, and then weaken it, and we're done.
       But what if y is before x?
         i.e. what if typechecking 'body' requires bindings defined after y?

         Suppose we used Chargueraud's L/pick_fresh framework:
         Then the typing_ini_mtd rule inversion would not give us 

         Hmtd: forall y : tenvParams.K,
               tenv.unbound y G1 -> typing_trm (G1 ;; (y, S)) (open_trm y body) T

         but

         L: fset var
         Hmtd: forall y : tenvParams.K,
               y \notin L -> typing_trm (G1 ;; (y, S)) (open_trm y body) T

         We could pick a fresh y' not in L, and get

         typing_trm (G1 ;; (y', S)) (open_trm y' body) T

         but we need to prove `typing_trm G (open_trm y body) T`, not with y'.
     *)


  (* red_call *)
  + rename H into Hvbx. rename H0 into Hibm. rename is into isx.
    exists G. split. apply Hwf.
    apply invert_typing_trm_call in Hty. 
    destruct Hty as [S [Hhas Htyy]].
    apply invert_typing_trm_var in Htyy. rename Htyy into Htby.
    apply invert_has in Hhas.
    destruct Hhas as [dsx [_ Hdbm]].
    destruct (tenv_binds_to_venv_binds Hwf Htby) as [isy Hvby].
    destruct (shrink_wf_venv Hwf Hvby Htby) as [s1 [s2 [G1 [G2 [Heqs [HeqG Hwf']]]]]].
    destruct S as [dsy].
    destruct (invert_wf_venv_cons Hwf') as [_ [Hvuy [Htuy Hisds]]].
    keep (invert_typing_mtd_ini_inside_typing_inis Hisds Hibm Hdbm) as Hmtd.
       (* do this with x, not with y! *)










  (* red_call *)
  + rename H into Hvbx. rename H0 into Hibm. rename is into isx.
    exists G. split. apply Hwf.
    destruct (invert_typing_trm_call Hty) as [S [Hhas Htyy]]. clear Hty.
    keep (invert_typing_trm_var Htyy) as Htby.
    destruct (invert_has Hhas) as [dsx [Htyx Hdbm]]. clear Hhas.
    keep (invert_typing_trm_var Htyx) as Htbx.
    destruct (tenv_binds_to_venv_binds Hwf Htby) as [isy Hvby].
    destruct S as [dsy].
    destruct (expose_two_binds_in_wf_venv Hwf Hvbx Htbx Hvby Htby) 
      as [Hsplit | [Hsplit | Hsplit]].
    * destruct Hsplit as [s1 [s2 [s3 [G1 [G2 [G3 Hsplit]]]]]].
      destruct Hsplit as [Heqs [HeqG [Hxy [Hvux [Htux [Hvuy Htuy]]]]]].
      (* Restrict tenv in Htbx, Htby *)
      rewrite -> HeqG in Htbx.
      keep (tenv.concat_assoc (G1 ;; (x, typ_rcd dsx)) (G2 ;; (y, typ_rcd dsy)) G3) as Ha.
      unfoldp.
      rewrite -> Ha in Htbx. clear Ha.
      apply (tenv.binds_concat_left_inv (G1 ;; (x, typ_rcd dsx)) Htux) in Htbx.
      rewrite -> HeqG in Htby.
      apply (tenv.binds_concat_left_inv (G1 ;; (x, typ_rcd dsx) & G2 ;; (y, typ_rcd dsy))
                                        Htuy) in Htby.

      assert (Hisxdsx: typing_inis G1 isx dsx). admit.
        (* keep (invert_wf_venv Hwf Hbv Hbtx) as Hisxdsx. *)
      (* ---> The point of this whole story is that we apply this inversion lemma
              on the restricted environment (G1 ;; (y, typ_rcd dsy)), instead of
              applying it on the whole G: *)
      keep (invert_typing_mtd_ini_inside_typing_inis Hisxdsx Hibm Hdbm) as Hmtd.
      assert (HtuyG1: tenv.unbound y G1). admit. (* since no envs have multiple mappings *)
      specialize (Hmtd y HtuyG1).
      (* now weaken Hmtd to get goal *)
      admit.
    * (* similar *) admit.
    * (* similar *) admit.
  (* red_sel *)
  + admit.
  (* red_new *)
  + admit.
  (* red_call1 *)
  + admit.
  (* red_call2 *)
  + admit.
  (* red_sel1 *)
  + admit.
Qed.

(* garbage .............. *)



(*
what's below is not needed because simpler:
assign everything first to a var -> no need to evaluate fields of record
and one type for record construction / fully evaluated record
*)

(* Value (: [list nslot] or [label => slot] *)
Module val <: env.
Definition K := loc.
Definition V := slot.
Definition B := nslot.
Definition t := list nslot.
Definition key(s: nslot): loc := match s with
| nslot_fld n lo => label_fld n
| nslot_mtd n T e => label_mtd n
end.
Definition value(s: nslot): slot := match s with
| nslot_fld n lo => slot_fld lo
| nslot_mtd n T e => slot_mtd T e
end.
End val.

(* fully evaluated record member *)
Inductive slot : Type :=
  | slot_fld : loc -> slot
  | slot_mtd : typ -> trm -> slot.

(* named slot *)
Inductive nslot : Type :=
  | nslot_fld : nat -> loc -> nslot
  | nslot_mtd : nat -> typ -> trm -> nslot.

(* Import List.ListNotations. *)

(*
theories/Lists/List, Module ListNotations:
Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

theories/Init/Datatypes:
Infix "++" := app (right associativity, at level 60) : list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
*)

