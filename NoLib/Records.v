(** * DOT *)

(* ###################################################################### *)
(** * Setup *)

Require Export List.
Require Export Arith.Peano_dec.
Require Export Program.Syntax. (* eg for multiple exists tactic *)
Require Import Numbers.Natural.Peano.NPeano.
Require Import Arith.Compare_dec.
Require Import Omega.

Set Implicit Arguments.

(** ** List notation with head on the right *)
Notation "E '&' F" := (app F E) (at level 31, left associativity).
Notation " E  ;; x " := (cons x E) (at level 29, left associativity).

(** For reference: Here's how list notations are usually defined:

        theories/Lists/List, Module ListNotations:
        Notation " [ ] " := nil : list_scope.
        Notation " [ x ] " := (cons x nil) : list_scope.
        Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

        theories/Init/Datatypes:
        Infix "++" := app (right associativity, at level 60) : list_scope.
        Infix "::" := cons (at level 60, right associativity) : list_scope.
*)

(** ** Testing the list notations: *)

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

(** ** Some tactics *)

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

Tactic Notation "keep" constr(E) "as" ident(H) :=
    let Temp := type of E in assert (H: Temp) by apply E.

Ltac destruct_matchee :=
  match goal with
  | [ Hm: match ?e1 with _ => _ end = _ |- _ ]  => 
      remember e1 as mExpr; destruct mExpr
  | [ Hm: if ?e1 then _ else _ = _ |- _ ]  => 
      remember e1 as mExpr; destruct mExpr
  end.


(* ###################################################################### *)
(** * Syntax *)

Definition var := nat.

(** If it's clear whether a field or method is meant, we use nat, if not, we use label: *)
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

(** ** Syntactic sugar *)
Definition trm_fun(T: typ)(body: trm) := trm_new (nil ;; nini_mtd 0 T body)
                                                 (trm_var (avar_b 0)).
Definition trm_app(func arg: trm) := trm_call func 0 arg.
Definition trm_let(T: typ)(rhs body: trm) := trm_app (trm_fun T body) rhs.
Definition trm_upcast(T: typ)(e: trm) := trm_app (trm_fun T (trm_var (avar_b 0))) e.
Definition typ_arrow(T1 T2: typ) := typ_rcd (nil ;; ndec_mtd 0 T1 T2).


(* ###################################################################### *)
(** * Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k) 
   by a free variable x. *)

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


(* ###################################################################### *)
(** * Environments *)

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


(* ###################################################################### *)
(** ** General environment *)

Module Env (params: EnvParams).
Import params.
Definition key := key.
Definition value := value.
Definition t := list B.
Definition empty : t := nil. (* to avoid having to write (@nil ...) *)
Fixpoint get(k: K)(E: t): option V := match E with
  | nil => None
  | bs ;; b => if eq_key_dec k (key b) then Some (value b) else get k bs
  end.
Definition binds(k: K)(v: V)(E: t): Prop := (get k E = Some v).
Definition unbound(k: K)(E: t): Prop := (get k E = None).
Inductive ok : t -> Prop :=
| ok_nil  : ok nil
| ok_cons : forall E b, ok E -> unbound (key b) E -> ok (E ;; b).
Lemma invert_ok_cons: forall E b, ok (E ;; b) -> ok E /\ unbound (key b) E.
Proof. intros. inv H. split; assumption. Qed.

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
        the next branch *)

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
Lemma unbound_concat_inv: forall k E1 E2, 
  unbound k (E1 & E2) -> unbound k E1 /\ unbound k E2.
Proof.
  intros. induction E2. 
  + simpl in *. split. assumption. unfoldg unbound. reflexivity.
  + rewrite -> concat_cons_assoc in *. compare_keys.
    - discriminate H.
    - apply (IHE2 H).
Qed.
Lemma unbound_concat: forall k E1 E2,
  unbound k E1 -> unbound k E2 -> unbound k (E1 & E2).
Proof.
  intros. induction E2.
  + simpl in *. assumption.
  + rewrite -> concat_cons_assoc. compare_keys.
    - assumption.
    - apply IHE2. assumption.
Qed.
Lemma unbound_remove_middle: forall k E1 E2 E3,
  unbound k (E1 & E2 & E3) -> unbound k (E1 & E3).
Proof.
  intros.
  destruct (unbound_concat_inv _ _ H) as [Hub12 Hub3].
  destruct (unbound_concat_inv _ _ Hub12) as [Hub1 Hub2].
  apply (unbound_concat Hub1 Hub3).
Qed.
Lemma invert_ok_concat: forall E1 E2, ok (E1 & E2) -> ok E1 /\ ok E2.
Proof.
  intros. induction E2. 
  + simpl in *. split. assumption. apply ok_nil.
  + rewrite -> concat_cons_assoc in *. destruct (invert_ok_cons H) as [H1 H2].
    specialize (IHE2 H1). destruct IHE2 as [Hok1 Hok2]. split.
    - assumption.
    - destruct (unbound_concat_inv _ _ H2) as [Hu1 Hu2]. apply (ok_cons Hok2 Hu2).
Qed.
Lemma ok_remove_middle: forall E1 E2 E3, ok (E1 & E2 & E3) -> ok (E1 & E3).
Proof.
  intros. induction E3.
  + simpl in *. destruct (invert_ok_concat _ _ H) as [Hok1 _]. assumption.
  + rewrite -> concat_cons_assoc in H.
    destruct (invert_ok_cons H) as [Hok123 Hub].
    rewrite -> concat_cons_assoc.
    apply ok_cons.
    - apply IHE3. assumption.
    - apply (unbound_remove_middle E1 E2 E3 Hub).
Qed.
Lemma binds_push_eq : forall b E, binds (key b) (value b) (E ;; b).
Proof.
  intros. compare_keys. reflexivity. contradiction n. reflexivity.
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
End Env.

(* ###################################################################### *)
(** ** List of declarations *)

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

(* ###################################################################### *)
(** ** List of initialisations *)

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

(* ###################################################################### *)
(** ** Typing environment ("Gamma") *)

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

Lemma tenv_gen_gt : forall G, exists x, forall y T, tenv.binds y T G -> y < x.
Proof.
  intros. induction G.
  + exists 0. intros. tenv.empty_binds_contradiction.
  + destruct IHG as [x IH].
    destruct (le_lt_dec x (tenv.key a)) as [Hc | Hc].
    - exists (S (tenv.key a)). intros. tenv.compare_keys.
      * omega.
      * specialize (IH y T H). omega.
    - exists x. intros. tenv.compare_keys.
      * omega.
      * apply (IH y T H).
Qed.

Lemma tenv_gen_fresh : forall G, exists x, tenv.unbound x G.
Proof.
  intros. destruct (tenv_gen_gt G) as [x H]. exists x.
  apply tenv.build_unbound. intros. specialize (H k' v H0). omega.
Qed.

(* ###################################################################### *)
(** ** Value environment ("store") *)

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

Ltac unfoldp :=
  unfold venvParams.K, venvParams.V, venvParams.B,
         tenvParams.K, tenvParams.V, tenvParams.B,
         inisParams.K, inisParams.V, inisParams.B,
         decsParams.K, decsParams.V, decsParams.B  in *.

(* ###################################################################### *)
(** * Preview: How intersection will work *)

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

(* Refined decs shadow the outdated decs of ds2.
   So [decs.ok (intersect ds1 ds2)] usually does not hold. *)
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


(* ###################################################################### *)
(** * Operational Semantics *)

(** Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
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


(* ###################################################################### *)
(** * Typing *)

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


(* ###################################################################### *)
(** * Well-formed store ([wf_venv]) *)

Inductive wf_venv: venv.t -> tenv.t -> Prop :=
  | wf_venv_nil : wf_venv nil nil
  | wf_venv_cons : forall s G x is ds,
      wf_venv s G ->
      venv.unbound x s ->
      tenv.unbound x G ->
      typing_inis G is ds ->
      wf_venv (s ;; (x, is)) (G ;; (x, (typ_rcd ds))).

(** ** Inversion lemmas for [wf_venv] *)

Lemma invert_wf_venv_cons: forall s G x is ds,
  wf_venv (s ;; (x, is)) (G ;; (x, typ_rcd ds)) ->
  wf_venv s G /\ venv.unbound x s /\ tenv.unbound x G /\ typing_inis G is ds.
Proof.
  intros. inv H. auto.
Qed.

Lemma wf_venv_to_ok: forall s G,
  wf_venv s G -> venv.ok s /\ tenv.ok G.
Proof.
  intros. induction H.
  + split. apply venv.ok_nil. apply tenv.ok_nil.
  + destruct IHwf_venv as [IH1 IH2]. split.
    apply venv.ok_cons; assumption. apply tenv.ok_cons; assumption.
Qed.

Lemma tenv_binds_to_venv_binds: forall s G x T,
  wf_venv s G ->
  tenv.binds x T G ->
  exists is, venv.binds x is s.
Proof.
  assert (P: forall s G (Hwf: wf_venv s G) x T (Hb: tenv.binds x T G),
             exists is, venv.binds x is s).
  * intros s G Hwf. induction Hwf; intros.
    + tenv.empty_binds_contradiction.
    + tenv.compare_keys.
      - exists is. simpl in e. subst. venv.compare_keys. reflexivity.
        simpl in n. contradiction n. reflexivity.
      - specialize (IHHwf x0 T Hb). destruct IHHwf as [is0 Hvb]. exists is0.
        venv.compare_keys. simpl in *. contradiction n. assumption.
  * intros s G x T Hwf Hb. apply (P s G Hwf x T Hb).
Qed.

Lemma venv_unbound_to_tenv_unbound: forall s G x,
  wf_venv s G ->
  venv.unbound x s ->
  tenv.unbound x G.
Admitted.


(* ###################################################################### *)
(** * Inversion lemmas for typing *)

(** **** Inverting [has] *)

Lemma invert_has: forall G e l d,
  has G e l d ->
  exists ds, typing_trm G e (typ_rcd ds) /\ decs.binds l d ds.
Proof. intros. inv H. eauto. Qed.


(** **** Inverting [typing_trm] *)

Lemma invert_typing_trm_var: forall G x T,
  typing_trm G (trm_var (avar_f x)) T ->
  tenv.binds x T G.
Proof. intros. inv H. assumption. Qed.

Lemma invert_typing_trm_sel: forall G e l T,
  typing_trm G (trm_sel e l) T ->
  has G e (label_fld l) (dec_fld T).
Proof. intros. inv H. assumption. Qed.

Lemma invert_typing_trm_call: forall G t m V u,
  typing_trm G (trm_call t m u) V ->
  exists U, has G t (label_mtd m) (dec_mtd U V) /\ typing_trm G u U.
Proof. intros. inv H. eauto. Qed.

Lemma invert_typing_trm_new: forall G is t T,
  typing_trm G (trm_new is t) T ->
  exists ds, typing_inis G is ds /\
             (forall x, tenv.unbound x G ->
                        typing_trm (G ;; (x, typ_rcd ds)) (open_trm x t) T).
Proof. intros. inv H. eauto. Qed.


(** **** Inverting [typing_ini] *)

Lemma invert_typing_ini_key: forall G i d, 
  typing_ini G i d -> inis.key i = decs.key d.
Proof. intros. inv H; reflexivity. Qed.

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


(** **** Inverting [typing_inis] *)

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

Lemma invert_typing_fld_ini_inside_typing_inis: forall G is ds l v T,
  typing_inis G is ds ->
  inis.binds (label_fld l) (ini_fld v) is ->
  decs.binds (label_fld l) (dec_fld T) ds ->
  (* conclusion is the premise needed to construct a typing_ini_fld: *)
  typing_trm G (trm_var v) T.
Proof.
Admitted.

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


(* ###################################################################### *)
(** * Weakening lemmas *)

Lemma weaken_binds: forall x T G H,
  tenv.ok (G & H) -> tenv.binds x T G -> tenv.binds x T (G & H).
Proof.
  intros x T G H. induction H; intros Hok Hb.
  + simpl. assumption.
  + rewrite -> tenv.concat_cons_assoc in *. 
    destruct (tenv.invert_ok_cons Hok) as [Hok' Hub].
    auto_specialize.
    tenv.compare_keys.
    - unfold tenv.unbound in Hub. rewrite -> e in IHlist. symmetry in Hub.
      assert (C: None = Some T). transitivity (tenv.get (tenv.key a) (G & H)); assumption.
      discriminate C.
    - assumption.
Qed.

Lemma weaken_binds_middle: forall x T G1 G2 G3,
  tenv.ok (G1 & G2 & G3) -> tenv.binds x T (G1 & G3) -> tenv.binds x T (G1 & G2 & G3).
Proof.
  intros x T G1 G2 G3. induction G3; intros Hok Hb.
  + simpl in *. apply (weaken_binds _ Hok Hb).
  + rewrite -> tenv.concat_cons_assoc in *. 
    destruct (tenv.invert_ok_cons Hok) as [Hok' Hub].
    tenv.compare_keys.
    - assumption.
    - apply (IHG3 Hok' Hb).
Qed.

(* If we only weaken at the end, i.e. from [G1] to [G1 & G2], the IH for the 
   [typing_trm_new] case adds G2 to the end, so it takes us from [G1, x: ds] 
   to [G1, x: ds, G2], but we need [G1, G2, x: ds].
   So we need to weaken in the middle, i.e. from [G1 & G3] to [G1 & G2 & G3].
   Then, the IH for the [typing_trm_new] case inserts G2 in the middle, so it
   takes us from [G1 & G3, x: ds] to [G1 & G2 & G3, x: ds], which is what we
   need. *)

Lemma weakening:
   (forall G e l d (Hhas: has G e l d)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: tenv.ok (G1 & G2 & G3)),
           has (G1 & G2 & G3) e l d ) 
/\ (forall G e T (Hty: typing_trm G e T)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: tenv.ok (G1 & G2 & G3)),
           typing_trm (G1 & G2 & G3) e T) 
/\ (forall G i d (Hty: typing_ini G i d)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: tenv.ok (G1 & G2 & G3)), 
           typing_ini (G1 & G2 & G3) i d)
/\ (forall G is ds (Hisds: typing_inis G is ds)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: tenv.ok (G1 & G2 & G3)), 
           typing_inis (G1 & G2 & G3) is ds).
Proof.
  apply typing_mutind; intros; unfoldp; 
    repeat match goal with
    | H: forall (_ _ _ : list (var * typ)), _ |- _ => 
        specialize (H G1 G2 G3 Heq Hok123); let IH := fresh IH in rename H into IH
    end;
    subst.
  + apply has_dec with ds; assumption.
  + apply typing_trm_var. apply weaken_binds_middle; assumption.
  + apply typing_trm_sel. assumption.
  + apply typing_trm_call with U; assumption.
  + apply (typing_trm_new _ IH).
    intros.
    assert (Hub13: tenv.unbound x (G1 & G3)) by 
      (apply (tenv.unbound_remove_middle G1 G2 G3); assumption).
    rewrite <- tenv.concat_cons_assoc.
    specialize (H0 x Hub13 G1 G2 (G3 ;; (x, typ_rcd ds))).
    apply H0.
    - reflexivity.
    - rewrite -> tenv.concat_cons_assoc. apply (tenv.ok_cons Hok123).
      simpl. assumption.
  + apply typing_ini_fld. assumption.
  + apply typing_ini_mtd.
    intros.
    assert (Hub13: tenv.unbound x (G1 & G3)) by 
      (apply (tenv.unbound_remove_middle G1 G2 G3); assumption).
    rewrite <- tenv.concat_cons_assoc.
    specialize (H x Hub13 G1 G2 (G3 ;; (x, S))).
    apply H.
    - reflexivity.
    - rewrite -> tenv.concat_cons_assoc. apply (tenv.ok_cons Hok123).
      simpl. assumption.
  + apply typing_inis_nil.
  + apply typing_inis_cons; assumption.
Qed.

Print Assumptions weakening.

Lemma weaken_has: forall G1 G2 e l d,
  has G1 e l d -> tenv.ok (G1 & G2) -> has (G1 & G2) e l d.
Proof.
  intros.
  destruct weakening as [W _].
  change (has (G1 & G2 & nil) e l d).
  apply (W (G1 & nil)); trivial.
Qed.

Lemma weaken_typing_trm: forall G1 G2 e T,
  typing_trm G1 e T -> tenv.ok (G1 & G2) -> typing_trm (G1 & G2) e T.
Proof.
  intros.
  destruct weakening as [_ [W _]].
  change (typing_trm (G1 & G2 & nil) e T).
  apply (W (G1 & nil)); trivial.
Qed.

Lemma weaken_typing_ini: forall G1 G2 i d,
  typing_ini G1 i d -> tenv.ok (G1 & G2) -> typing_ini (G1 & G2) i d.
Proof.
  intros.
  destruct weakening as [_ [_ [W _]]].
  change (typing_ini (G1 & G2 & nil) i d).
  apply (W (G1 & nil)); trivial.
Qed.

Lemma weaken_typing_inis: forall G1 G2 is ds,
  typing_inis G1 is ds -> tenv.ok (G1 & G2) -> typing_inis (G1 & G2) is ds.
Proof.
  intros.
  destruct weakening as [_ [_ [_ W]]].
  change (typing_inis (G1 & G2 & nil) is ds).
  apply (W (G1 & nil)); trivial.
Qed.

Lemma weaken_typing_inis_1: forall G x T is ds,
  typing_inis G is ds -> tenv.ok (G ;; (x, T)) -> typing_inis (G ;; (x, T)) is ds.
Proof.
  intros.
  change (typing_inis (G & nil ;; (x, T)) is ds).
  apply weaken_typing_inis; assumption.
Qed.

(* ###################################################################### *)
(** * Inversion lemmas which depend on weakening *)

Lemma invert_wf_venv: forall s G,
  wf_venv s G -> 
    forall x is ds, 
      venv.binds x is s -> 
      tenv.binds x (typ_rcd ds) G ->
      typing_inis G is ds.
Proof.
  intros s G Hwf. induction Hwf; intros.
  + tenv.empty_binds_contradiction.
  + unfoldp. rename H into Hvb, H0 into Htb, H1 into Hisds, H2 into Hvb0, H3 into Htb0.
    venv.compare_keys; tenv.compare_keys; simpl in *.    
    - inv e. inv Hvb0. inv Htb0.
      apply (weaken_typing_inis_1 Hisds).
      apply tenv.ok_cons.
      * destruct (wf_venv_to_ok Hwf) as [_ Hok]. assumption.
      * simpl. assumption.
    - contradiction n.
    - contradiction n.
    - specialize (IHHwf x0 is0 ds0 Hvb0 Htb0).
      apply (weaken_typing_inis_1 IHHwf).
      apply tenv.ok_cons.
      * destruct (wf_venv_to_ok Hwf) as [_ Hok]. assumption.
      * simpl. assumption.
Qed.


(* ###################################################################### *)
(** * Progress *)

Definition progress_for(s: venv.t)(e: trm) :=
  (* can step *)
  (exists s' e', red s e s' e') \/
  (* or is a value *)
  (exists x is, e = (trm_var (avar_f x)) /\ venv.binds x is s).

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


(* ###################################################################### *)
(** * The substitution principle *)

(*
The well-known substitution principle, usually written like

                  G, x: S |- e : T      G |- u : S
                 ----------------------------------
                            G |- [u/x]e : T

becomes the following in locally nameless style:

   G, x: S |- (open_trm x e) : T       G |- (trm_var (avar_f u)) : S
  -------------------------------------------------------------------
                       G |- (open_trm u e) : T

Note that in general, u is a term, but for our purposes, it suffices to consider
the special case where u is a variable.
*)


Lemma destruct_trm_var_eq_open_trm: forall z x e,
  trm_var (avar_f z) = open_trm x e ->
  (z = x /\ (e = trm_var (avar_b 0) \/ e = trm_var (avar_f z)))
  \/ z <> x.
Proof.
  intros. unfold open_trm, open_rec_trm in H. destruct e; try discriminate H.
  inversion H.
  unfold open_rec_avar in H1. destruct a.
  + destruct (eq_nat_dec 0 n).
    - inv H1. left. split. reflexivity. left. reflexivity.
    - discriminate H1.
  + inv H1. destruct (eq_nat_dec v x).
    - subst. left. split. reflexivity. right. reflexivity.
    - right. assumption.
Qed.

(*
Lemma destruct_trm_var_eq_open_trm: forall z x e,
  trm_var (avar_f z) = open_trm x e ->
  (e = trm_var (avar_b 0) /\ z = x) \/
  (e = trm_var (avar_f z)).
Proof.
  intros. unfold open_trm, open_rec_trm in H. destruct e; try discriminate H.
  inversion H.
  unfold open_rec_avar in H1. destruct a.
  + destruct (eq_nat_dec 0 n).
    - inv H1. left; split; reflexivity.
    - discriminate H1.
  + inv H1. right; reflexivity.
Qed.
*)

Lemma raw_subst_principles: 
  forall G1 G2 y S, typing_trm (G1 & G2) (trm_var (avar_f y)) S ->
  (forall (G0 : tenv.t) (e0 : trm) (l : label) (d : dec) (Hhas : has G0 e0 l d),
    (fun G0 e0 l d (Hhas: has G0 e0 l d) => 
      forall x e, G0 = (G1 ;; (x, S) & G2) ->
                  tenv.ok (G1 ;; (x, S) & G2) ->
                  e0 = (open_trm x e) -> 
                  has (G1 & G2) (open_trm y e) l d)
    G0 e0 l d Hhas) /\
  (forall (G0 : tenv.t) (e0 : trm) (T : typ) (Hty : typing_trm G0 e0 T),
    (fun G0 e0 T (Hty: typing_trm G0 e0 T) => 
      forall x e, G0 = (G1 ;; (x, S) & G2) ->
                  tenv.ok (G1 ;; (x, S) & G2) ->
                  e0 = (open_trm x e) -> 
                  typing_trm (G1 & G2) (open_trm y e) T)
    G0 e0 T Hty) /\
  (forall (G0 : tenv.t) (i0 : nini) (d : ndec) (Hty : typing_ini G0 i0 d),
    (fun G i0 d (Htyp: typing_ini G i0 d) => 
      forall x i, G0 = (G1 ;; (x, S) & G2) ->
                  tenv.ok (G1 ;; (x, S) & G2) ->
                  i0 = (open_nini x i) -> 
                  typing_ini (G1 & G2) (open_nini y i) d)
    G0 i0 d Hty) /\
  (forall (G0 : tenv.t) (is0 : inis.t) (ds : decs.t) (Hty : typing_inis G0 is0 ds),
    (fun G is0 ds (Hty: typing_inis G is0 ds) => 
      forall x is, G0 = (G1 ;; (x, S) & G2) ->
                   tenv.ok (G1 ;; (x, S) & G2) ->
                   is0 = (map (open_nini y) is) -> 
                   typing_inis (G1 & G2) (map (open_nini y) is) ds)
    G0 is0 ds Hty).
Proof.
  intros G1 G2 y S Htyy.
  apply typing_mutind; intros;
  (* renaming: *)
  lazymatch goal with
    (* 2 IHs *)
    | H1: forall _ _, _, H2: forall _ _, _  |- _ => rename H1 into IH1, H2 into IH2
    (* 1 IH *)
    | H : forall _ _, _ |- _ => rename H into IH
    (* no IH *)
    | _ => idtac
  end;
  match goal with
    | H: @eq tenv.t _ _ |- _ => rename H into EqG
  end;
  match goal with
    | H: @eq trm    _ _ |- _ => rename H into EqTrm
    | H: @eq nini   _ _ |- _ => rename H into EqIni
    | H: @eq inis.t _ _ |- _ => rename H into EqInis
  end;
  match goal with
    | H: tenv.ok _ |- _ => rename H into Hok
  end.
  (* case has_dec *)
  + specialize (IH _ _ EqG Hok EqTrm).
    apply has_dec with ds; assumption.
  (* case typing_trm_var *)
  + subst. rename x into z, x0 into x.
    destruct (destruct_trm_var_eq_open_trm _ _ EqTrm) as [[EqTrm' [EqV | EqV]] | Neq].
    (* case z = x and e bound var *)
    - subst. assert (EqST: S = T) by admit. subst.
      unfold open_trm, open_rec_trm. simpl.
      apply Htyy.
    (* case z = x and e free var z *)
    - subst. assert (EqST: S = T) by admit. subst. admit.
    (* case z <> x *)
    - admit.
  (* case typing_trm_sel *)
  + admit.
  (* case typing_trm_call *)
  + admit.
  (* case typing_trm_new *)
  + admit.
  (* case typing_ini_fld *)
  + admit.
  (* case typing_ini_mtd *)
  + admit.
  (* case typing_inis_nil *)
  + admit.
  (* case typing_inis_cons *)
  + admit.
Qed.

(* Does not hold if e = trm_var (avar_f x), because opening e with y results
   in trm_var (avar_f x), which does not typecheck in an environment where we removed x.
   Maybe need x notin FV(e) ? *)
Lemma subst_principle: forall G x y e S T,
  typing_trm (G ;; (x, S)) (open_trm x e) T ->
  typing_trm G (trm_var (avar_f y)) S ->
  typing_trm G (open_trm y e) T.
Proof.
  intros G x y e S T He Hy.
  destruct (raw_subst_principles G tenv.empty Hy) as [_ [P _]].
  assert (Hok: tenv.ok (G ;; (x, S))). admit.
  apply (P _ _ _ He _ _ eq_refl Hok eq_refl).
Qed.


(* ###################################################################### *)
(** * Preservation *)

Theorem preservation_proof:
  forall s e s' e' (Hred: red s e s' e') G T (Hwf: wf_venv s G) (Hty: typing_trm G e T),
  (exists H, wf_venv s' (G & H) /\ typing_trm (G & H) e' T).
Proof.
  intros s e s' e' Hred. induction Hred; intros.
  (* red_call *)
  + rename H into Hvbx. rename H0 into Hibm. rename T0 into U.
    exists tenv.empty. simpl. split. apply Hwf.
    (* Grab "tenv binds x" hypothesis: *)
    apply invert_typing_trm_call in Hty. 
    destruct Hty as [T' [Hhas Htyy]].
    apply invert_has in Hhas. 
    destruct Hhas as [ds [Htyx Hdbm]].
    apply invert_typing_trm_var in Htyx. rename Htyx into Htbx.
    (* Feed "venv binds x" and "tenv binds x" to invert_wf_venv: *)
    keep (invert_wf_venv Hwf Hvbx Htbx) as Hisds.
    keep (invert_typing_mtd_ini_inside_typing_inis Hisds Hibm Hdbm) as Hmtd.
    destruct (tenv_gen_fresh G) as [y' Htuy'].
    specialize (Hmtd y' Htuy').
    apply (subst_principle _ Hmtd Htyy).
  (* red_sel *)
  + rename H into Hvbx. rename H0 into Hibl.
    exists tenv.empty. simpl. split. apply Hwf.
    apply invert_typing_trm_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [ds [Htyx Hdbl]].
    apply invert_typing_trm_var in Htyx. rename Htyx into Htbx.
    (* Feed "venv binds x" and "tenv binds x" to invert_wf_venv: *)
    keep (invert_wf_venv Hwf Hvbx Htbx) as Hisds.
    apply (invert_typing_fld_ini_inside_typing_inis Hisds Hibl Hdbl).
  (* red_new *)
  + rename H into Hvux.
    apply invert_typing_trm_new in Hty.
    destruct Hty as [ds [Hisds Htye]].
    keep (venv_unbound_to_tenv_unbound Hwf Hvux) as Htux.
    exists (tenv.empty ;; (x, typ_rcd ds)). simpl. split.
    - apply (wf_venv_cons Hwf Hvux Htux Hisds).
    - apply (Htye x Htux).
  (* red_call1 *)
  + rename T into Tr.
    apply invert_typing_trm_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    apply invert_has in Hhas.
    destruct Hhas as [ds [Htyo Hdbm]].
    specialize (IHHred G (typ_rcd ds) Hwf Htyo).
    destruct IHHred as [H [Hwf' Htyo']].
    exists H. split. assumption. apply (@typing_trm_call (G & H) o' m Ta Tr a).
    - apply (has_dec Htyo' Hdbm).
    - destruct (wf_venv_to_ok Hwf') as [_ Hok].
      apply (weaken_typing_trm _ Htya Hok).
  (* red_call2 *)
  + rename T into Tr.
    apply invert_typing_trm_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    specialize (IHHred G Ta Hwf Htya).
    destruct IHHred as [H [Hwf' Htya']].
    exists H. split. assumption. apply (@typing_trm_call (G & H) _ m Ta Tr a').
    - destruct (wf_venv_to_ok Hwf') as [_ Hok].
      apply (weaken_has _ Hhas Hok).
    - assumption.
  (* red_sel1 *)
  + apply invert_typing_trm_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [ds [Htyo Hdbl]].
    specialize (IHHred G (typ_rcd ds) Hwf Htyo).
    destruct IHHred as [H [Hwf' Htyo']].
    exists H. split. assumption. apply (@typing_trm_sel (G & H) o' l T).
    apply (has_dec Htyo' Hdbl).
Qed.

Theorem preservation: forall s G e T s' e',
  wf_venv s G -> typing_trm G e T -> red s e s' e' ->
  (exists G', wf_venv s' G' /\ typing_trm G' e' T).
Proof.
  intros s G e T s' e' Hwf Hty Hred.
  destruct (preservation_proof Hred Hwf Hty) as [H [Hwf' Hty']].
  exists (G & H). split; assumption.
Qed.

Print Assumptions preservation.
