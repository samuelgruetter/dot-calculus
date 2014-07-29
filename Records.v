
Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.
(*Require Import LibList.*)

(** ** Some tactics *)

Ltac auto_specialize :=
  repeat match goal with
  | Impl: ?Cond ->            _ |- _ => let HC := fresh in 
      assert (HC: Cond) by auto; specialize (Impl HC); clear HC
  | Impl: forall (_ : ?Cond), _ |- _ => match goal with
      | p: Cond |- _ => specialize (Impl p)
      end
  end.

(* ###################################################################### *)
(** * Syntax *)

(** If it's clear whether a field or method is meant, we use nat, if not, we use label: *)
Inductive label: Type :=
| label_fld: nat -> label
| label_mtd: nat -> label.

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
  | trm_new  : list ndef -> trm -> trm
  | trm_sel  : trm -> nat -> trm
  | trm_call : trm -> nat -> trm -> trm
with ndef : Type :=
  | ndef_fld : nat -> avar -> ndef (* cannot have term here, need to assign first *)
  | ndef_mtd : nat -> typ -> trm -> ndef.
Inductive def : Type :=
  | def_fld : avar -> def
  | def_mtd : typ -> trm -> def.

(** ** Syntactic sugar *)
Definition trm_fun(T: typ)(body: trm) := trm_new (ndef_mtd 0 T body :: nil)
                                                 (trm_var (avar_b 0)).
Definition trm_app(func arg: trm) := trm_call func 0 arg.
Definition trm_let(T: typ)(rhs body: trm) := trm_app (trm_fun T body) rhs.
Definition trm_upcast(T: typ)(e: trm) := trm_app (trm_fun T (trm_var (avar_b 0))) e.
Definition typ_arrow(T1 T2: typ) := typ_rcd (ndec_mtd 0 T1 T2 :: nil).


(* ###################################################################### *)
(** * Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k) 
   by a free variable x. *)

Fixpoint open_rec_avar (k: nat) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

(* The only binders are trm_new and (n)def_mtd, which cannot be inside a typ or
   inside a dec, so we don't need opening for typ and dec *)

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var a => trm_var (open_rec_avar k u a)
  | trm_new ds e => trm_new (List.map (open_rec_ndef (S k) u) ds) (open_rec_trm (S k) u e)
  | trm_sel e n => trm_sel (open_rec_trm k u e) n
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_ndef (k: nat) (u: var) (i: ndef) { struct i } : ndef :=
  match i with
  | ndef_fld n a   => ndef_fld n (open_rec_avar k u a)
  | ndef_mtd n T e => ndef_mtd n T (open_rec_trm (S k) u e)
  end.

Definition open_avar u a := open_rec_avar 0 u a.
Definition open_trm  u e := open_rec_trm  0 u e.
Definition open_ndef u i := open_rec_ndef 0 u i.


(* ###################################################################### *)
(** * Free variables *)

Fixpoint fv_avar (a: avar) { struct a } : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

(* It's a bit tricky to convince Coq that these fv functions terminate.
   One solution is to inline fv_ndefs. See http://cs.stackexchange.com/questions/104. *)
Fixpoint fv_trm (t: trm) : vars :=
  let fv_ndefs := (fix fv_ndefs (ds: list ndef) : vars := match ds with
  | nil => \{}
  | cons d rest => (fv_ndef d) \u (fv_ndefs rest)
  end) in
  match t with
  | trm_var x => fv_avar x
  | trm_new ds t => (fv_ndefs ds) \u (fv_trm t)
  | trm_sel t l => fv_trm t
  | trm_call t1 m t2 => (fv_trm t1) \u (fv_trm t2)
  end
with fv_ndef (d: ndef) : vars :=
  match d with
  | ndef_fld l x => fv_avar x
  | ndef_mtd m T u => fv_trm u
  end.
Fixpoint fv_ndefs (ds: list ndef) : vars := 
  match ds with
  | nil => \{}
  | cons d rest => (fv_ndef d) \u (fv_ndefs rest)
  end.

Definition fv_def (d: def) : vars :=
  match d with
  | def_fld x => fv_avar x
  | def_mtd T u => fv_trm u
  end.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : env typ   => dom x     ) in
  let D := gather_vars_with (fun x : avar      => fv_avar  x) in
  let E := gather_vars_with (fun x : trm       => fv_trm   x) in
  let F := gather_vars_with (fun x : ndef      => fv_ndef  x) in
  let G := gather_vars_with (fun x : list ndef => fv_ndefs x) in
  let H := gather_vars_with (fun x : def       => fv_def   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).


(* ###################################################################### *)
(** * Var-by-var substitution *)

Fixpoint subst_avar (z: var) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = z then (avar_f u) else (avar_f x)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  let subst_defs := 
  (fix subst_defs (z: var) (u: var) (ds: list ndef) : list ndef := match ds with
  | nil => nil
  | cons d rest => cons (subst_def z u d) (subst_defs z u rest)
  end) in
  match t with
  | trm_var x => trm_var (subst_avar z u x)
  | trm_new ds t => trm_new (subst_defs z u ds) (subst_trm z u t)
  | trm_sel t l => trm_sel (subst_trm z u t) l
  | trm_call t1 m t2 => trm_call (subst_trm z u t1) m (subst_trm z u t2)
  end
with subst_def (z: var) (u: var) (d: ndef) : ndef :=
  match d with
  | ndef_fld l x => ndef_fld l (subst_avar z u x)
  | ndef_mtd m T b => ndef_mtd m T (subst_trm z u b)
  end.


(* ###################################################################### *)
(** * Environments *)

(* 
Environment requirements:
   * ...
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

Module Type DMapParams.
Parameter K : Type.
Parameter V : Type.
Parameter B : Type.
Parameter key: B -> K.
Parameter value: B -> V.
Axiom key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
End DMapParams.


(* ###################################################################### *)
(** ** General environment *)

Module DMap (params: DMapParams).
Import params.
Definition t := list B.
Definition empty : t := nil. (* to avoid having to write (@nil ...) *)
Fixpoint get(k: K)(E: t): option V := match E with
  | nil => None
  | cons b bs => If k = (key b) then Some (value b) else get k bs
  end.
Definition has(E: t)(k: K)(v: V): Prop := (get k E = Some v).
Definition hasnt(E: t)(k: K): Prop := (get k E = None).

Lemma get_cons : forall k b E,
  get k (cons b E) = If k = key b then Some (value b) else get k E.
Proof.
  intros. unfold get. case_if~.
Qed.

(*
Inductive ok : t -> Prop :=
| ok_nil  : ok nil
| ok_cons : forall E b, ok E -> unbound (key b) E -> ok (b::E).
Lemma invert_ok_cons: forall E b, ok (E ;; b) -> ok E /\ unbound (key b) E.
Proof. intros. inversions H. split; assumption. Qed.
*)
Ltac empty_binds_contradiction := match goal with
| H: has nil _ _ |- _ => inversion H
end.
(*
Tactic Notation "unfoldg" reference(I)             := unfold I, get; fold get.
Tactic Notation "unfoldg" reference(I) "in" hyp(H) := unfold I, get in H; fold get in H.
*)
Ltac unfoldg I := unfold I, get in *; fold get in *.
(*
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
    - inversions H0. do 3 f_equal. symmetry in e. apply key_val_eq_eq; assumption.
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
Qed. *)
Lemma has_append_right : forall k v E1 E2,
  has E2                     k v ->
  has (LibList.append E1 E2) k v.
Proof. Admitted. (*
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
Qed.*)
Lemma has_append_left : forall k v E1 E2,
  has   E1 k v ->
  hasnt E2 k ->
  has   (LibList.append E1 E2) k v.
Proof. Admitted. (*
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
  + inversions H.
  + compare_keys.
    - subst. apply (binds_unbound_head_inv H0).
    - apply IHE. assumption. apply (unbound_cons_inv H0).
Qed.
Lemma binds_unique : forall k v1 v2 E,
  binds k v1 E -> binds k v2 E -> v1 = v2.
Proof.
  intros. induction E.
  + inversions H.
  + compare_keys.
    - inversions H. inversions H0. reflexivity.
    - inversions H. inversions H0. apply IHE; assumption.
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
Qed.*)
End DMap.

(* ###################################################################### *)
(** ** List of declarations *)

(* Module decs: For lists of declarations: [list ndec] or [label => dec] *)
Module decs.
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
Lemma key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2.
  + inversions H. inversions H0. reflexivity.
  + inversions H.
  + inversions H.
  + inversions H. inversions H0. reflexivity.
Qed.
Include DMap.
End decs.

(* ###################################################################### *)
(** ** List of definitions ("initialisations") *)

(* Module defs: For lists of definitions: [list ndef] or [label => def] *)
Module defs.
Definition K := label.
Definition V := def.
Definition B := ndef.
Definition key(i: ndef): label := match i with
| ndef_fld n T => label_fld n
| ndef_mtd n T e => label_mtd n
end.
Definition value(i: ndef): def := match i with
| ndef_fld n T => def_fld T
| ndef_mtd n T e => def_mtd T e
end.
Lemma key_val_eq_eq: forall b1 b2, key b1 = key b2 -> value b1 = value b2 -> b1 = b2.
Proof.
  intros. destruct b1, b2.
  + inversions H. inversions H0. reflexivity.
  + inversions H.
  + inversions H.
  + inversions H. inversions H0. reflexivity.
Qed.
Include DMap.
End defs.

Lemma defs_binds_fld_sync_val: forall n v ds,
  defs.has ds (label_fld n) v -> exists x, v = (def_fld x).
Proof. Admitted. (*
  intros. induction ds.
  + defs.empty_binds_contradiction.
  + defs.unfoldg defs.has. destruct a; simpl in H; defs.destruct_key_if.
      * inversions H. exists a. reflexivity.
      * apply IHis. unfold defs.has. assumption.
      * inversions e. (* contradiction *)
      * apply IHis. unfold defs.has. assumption.
Qed.*)

Lemma defs_binds_mtd_sync_val: forall n v ds,
  defs.has ds (label_mtd n) v -> exists T e, v = (def_mtd T e).
Proof. Admitted. (*
  intros. induction is.
  + defs.empty_binds_contradiction.
  + defs.unfoldg defs.binds. destruct a; simpl in H; defs.destruct_key_if.
      * inversions e. (* contradiction *)
      * apply IHis. unfold defs.binds. assumption.
      * inversions H. exists t t0. reflexivity.
      * apply IHis. unfold defs.binds. assumption.
Qed.*)

Ltac unfoldp :=
  unfold defs.K, defs.V, defs.B,
         decs.K, decs.V, decs.B  in *.


(** ** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** ** Value environment ("store") *)
Definition sto := env defs.t.


(* ###################################################################### *)
(** * Preview: How intersection will work *)

Module Type IntersectionPreview.

(* Will be part of syntax: *)
Parameter t_and: typ -> typ -> typ.
Parameter t_or:  typ -> typ -> typ.

(* Left as an exercise for the reader ;-) We define intersection by the spec below. *)
Parameter intersect: decs.t -> decs.t -> decs.t.

Axiom intersect_spec_1: forall l D Ds1 Ds2,
  decs.has    Ds1                l D ->
  decs.hasnt  Ds2                l   ->
  decs.has   (intersect Ds1 Ds2) l D .

Axiom intersect_spec_2: forall l D Ds1 Ds2,
  decs.hasnt Ds1                 l   ->
  decs.has   Ds2                 l D ->
  decs.has   (intersect Ds1 Ds2) l D.

Axiom intersect_spec_12_fld: forall n T1 T2 Ds1 Ds2,
  decs.has Ds1                 (label_fld n) (dec_fld T1) ->
  decs.has Ds2                 (label_fld n) (dec_fld T2) ->
  decs.has (intersect Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).

Axiom intersect_spec_12_mtd: forall n S1 T1 S2 T2 Ds1 Ds2,
  decs.has Ds1                 (label_mtd n) (dec_mtd S1 T1) ->
  decs.has Ds2                 (label_mtd n) (dec_mtd S2 T2) ->
  decs.has (intersect Ds1 Ds2) (label_mtd n) (dec_mtd (t_or S1 S2) (t_and T1 T2)).

End IntersectionPreview.

(* Exercise: Give any implementation of `intersect`, and prove that it satisfies
   the specification. Happy hacking! ;-) *)
Module IntersectionPreviewImpl <: IntersectionPreview.

(* Will be part of syntax: *)
Parameter t_and: typ -> typ -> typ.
Parameter t_or:  typ -> typ -> typ.

(*
Fixpoint get_fld(n: nat)(ds: decs.t): option typ := match Ds with
  | nil => None
  | tail ;; d => match d with
      | ndec_fld m T => if eq_nat_dec n m then Some T else get_fld n tail
      | _ => get_fld n tail
      end
  end.
*)

Fixpoint refine_dec(D1: ndec)(Ds2: decs.t): ndec := match Ds2 with
| nil => D1
| cons D2 tail2 => match D1, D2 with
    | ndec_fld n1 T1   , ndec_fld n2 T2    => If n1 = n2
                                              then ndec_fld n1 (t_and T1 T2) 
                                              else refine_dec D1 tail2
    | ndec_mtd n1 T1 S1, ndec_mtd n2 T2 S2 => If n1 = n2
                                              then ndec_mtd n1 (t_or T1 T2) (t_and S1 S2) 
                                              else refine_dec D1 tail2
    | _, _ => refine_dec D1 tail2
    end
end.

Lemma refine_dec_spec_fld: forall Ds2 n T1 T2,
  decs.has Ds2 (label_fld n) (dec_fld T2) ->
  (refine_dec (ndec_fld n T1) Ds2) = (ndec_fld n (t_and T1 T2)).
Proof. Admitted. (* 
  intro Ds2. induction Ds2; intros.
  + decs.empty_binds_contradiction.
  + decs.compare_keys.
    - inversions H. unfold decs.value in H1. destruct a eqn: Heqa.
      * inversions H1. inversion e. subst. simpl. destruct (eq_nat_dec n0 n0). reflexivity.
        contradiction n. reflexivity.
      * inversions H1.
    - simpl. destruct a eqn: Heqa. 
      * assert (Hnn: n <> n1). unfold not in *. intro. apply n0. simpl. f_equal. assumption.
        destruct (eq_nat_dec n n1). contradiction Hnn.
        apply IHDs2. unfold decs.has, decs.get. unfold decs.key.
        assumption.
      * apply IHDs2. unfold decs.has, decs.get. unfold decs.key.
        assumption.
Qed.*)

Lemma refine_dec_spec_mtd: forall Ds2 n T1 S1 T2 S2,
  decs.has Ds2 (label_mtd n) (dec_mtd T2 S2) ->
  (refine_dec (ndec_mtd n T1 S1) Ds2) = (ndec_mtd n (t_or T1 T2) (t_and S1 S2)).
Proof. Admitted. (*
  intro Ds2. induction Ds2; intros.
  + decs.empty_binds_contradiction.
  + decs.compare_keys.
    - inversions H. destruct a eqn: Heqa.
      * inversions H1.
      * inversions H1. inversion e. subst. simpl. destruct (eq_nat_dec n0 n0). reflexivity.
        contradiction n. reflexivity.
    - simpl. destruct a eqn: Heqa. 
      * apply IHDs2. assumption.
      * assert (Hnn: n <> n1). unfold not in *. intro. apply n0. simpl. f_equal. assumption.
        destruct (eq_nat_dec n n1). contradiction Hnn.
        apply IHDs2. assumption.
Qed.*)

Lemma refine_dec_spec_label: forall D1 Ds2, decs.key D1 = decs.key (refine_dec D1 Ds2).
Proof. Admitted. (*
  intros.
  induction Ds2.
  + simpl. reflexivity.
  + unfold decs.key. unfold refine_dec. destruct a; destruct D1.
    - destruct (eq_nat_dec n0 n).
      * simpl. reflexivity.
      * fold refine_dec. unfold decs.key in IHDs2.
        rewrite <- IHDs2. reflexivity.
    - fold refine_dec. unfold decs.key in IHDs2.
        rewrite <- IHDs2. reflexivity.
    - fold refine_dec. unfold decs.key in IHDs2.
        rewrite <- IHDs2. reflexivity.
    - destruct (eq_nat_dec n0 n).
      * simpl. reflexivity.
      * fold refine_dec. unfold decs.key in IHDs2.
        rewrite <- IHDs2. reflexivity.
Qed.*)

Lemma refine_dec_spec_unbound: forall D1 Ds2, 
  decs.hasnt Ds2 (decs.key D1) ->
  decs.value (refine_dec D1 Ds2) = decs.value D1.
Proof. Admitted. (*
  intros.
  induction Ds2.
  + simpl. reflexivity.
  + unfold decs.key. unfold refine_dec. destruct a; destruct D1.
    - destruct (eq_nat_dec n0 n) eqn: Hn0ndec.
      * subst. 
        assert (Hkeq: (decs.key (ndec_fld n t0)) = (decs.key (ndec_fld n t)))
          by reflexivity.
        rewrite -> Hkeq in H.
        exfalso. apply (decs.has Ds_unbound_head_inv H).
      * fold refine_dec. apply IHDs2.
        inversions H. unfold decs.eq_key_dec in H1.
        destruct (eq_label_dec (label_fld n0) (label_fld n)).
        { inversions e. contradiction n1. reflexivity. }
        { unfold decs.hasnt. unfold decs.key. assumption. }
    - fold refine_dec. unfold decs.key in *.
      apply decs.hasnt Ds_cons_inv in H. apply (IHDs2 H).
    - fold refine_dec. unfold decs.key in *.
      apply decs.hasnt Ds_cons_inv in H. apply (IHDs2 H).
    - destruct (eq_nat_dec n0 n) eqn: Hn0ndec.
      * subst. 
        assert (Hkeq: (decs.key (ndec_mtd n t1 t2)) = (decs.key (ndec_mtd n t t0)))
          by reflexivity.
        rewrite -> Hkeq in H.
        exfalso. apply (decs.has Ds_unbound_head_inv H).
      * fold refine_dec. apply IHDs2.
        inversions H. unfold decs.eq_key_dec in H1. 
        destruct (eq_label_dec (label_mtd n0) (label_mtd n)).
        { inversions e. contradiction n1. reflexivity. }
        { unfold decs.hasnt. unfold decs.key. assumption. }
Qed.*)

Definition refine_decs(Ds1: decs.t)(Ds2: decs.t): decs.t := 
  List.map (fun D1 => refine_dec D1 Ds2) Ds1.

Lemma refine_decs_spec_unbound: forall l D Ds1 Ds2,
  decs.has    Ds1                  l D ->
  decs.hasnt  Ds2                  l   ->
  decs.has   (refine_decs Ds1 Ds2) l D .
Proof. Admitted. (*
  intros. unfold refine_decs.
  assert (Hex: exists nd, decs.key nd = l /\ decs.value nd = d).
    apply (@decs.has Ds_binding_inv l d Ds1 H).
  destruct Hex as [nd [Hl Hd]]. subst.
  remember (fun D1 => refine_dec D1 Ds2) as f.
  assert (Hk: (decs.key nd) = decs.key (f nd)).
    subst. apply (refine_dec_spec_label nd Ds2).
  rewrite -> Hk.
  assert (Hv: (decs.value nd) = decs.value (f nd)).
    subst. symmetry. apply (refine_dec_spec_unbound _ H0).
  rewrite -> Hv.
  apply decs.has Ds_map. 
    intro. rewrite -> Heqf. symmetry. apply refine_dec_spec_label.
    assumption.
Qed.*)

Lemma refine_decs_spec_unbound_preserved: forall l Ds1 Ds2,
  decs.hasnt Ds1                   l ->
  decs.hasnt (refine_decs Ds1 Ds2) l .
Proof. Admitted. (*
  intros. unfold refine_decs. remember (fun D1 => refine_dec D1 Ds2) as f.
  refine (@decs.hasnt Ds_map l f Ds1 _ H).
  subst. intro. symmetry. apply refine_dec_spec_label.
Qed.*)

Lemma refine_decs_spec_fld: forall n Ds1 Ds2 T1 T2,
  decs.has  Ds1                  (label_fld n) (dec_fld T1) ->
  decs.has  Ds2                  (label_fld n) (dec_fld T2) ->
  decs.has (refine_decs Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).
Proof. Admitted. (*
  intros n Ds1 Ds2 T1 T2 H. induction Ds1; intros.
  + decs.empty_binds_contradiction.
  + unfold decs.has, decs.get in H. destruct a eqn: Heqa.
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_fld n) (label_fld n0)).
      * inversions H. inversions e.
        unfold decs.has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 T1) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n0) (label_fld n0)). {
          f_equal. rewrite -> (@refine_dec_spec_fld Ds2 n0 T1 T2 H0).
          simpl. reflexivity. 
        } { contradiction n. reflexivity. }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 t) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n) (label_fld n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          unfold decs.has in *. apply IHDs1; assumption.
        }
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_fld n) (label_fld n0)).
      * inversions H. inversions e.
        unfold decs.has, decs.get. simpl. fold decs.get.
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 t t0) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n0) (label_mtd n0)). {
          inversions H2.
        } {
          unfold decs.has in *. apply IHDs1; assumption.
        }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 t t0) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n) (label_fld n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          destruct (decs.eq_key_dec (label_fld n) (label_mtd n0)).
          + inversions e.
          + unfold decs.has in *. apply IHDs1; assumption.
        }
Qed.*)

Lemma refine_decs_spec_mtd: forall n Ds1 Ds2 T1 S1 T2 S2,
  decs.has  Ds1                  (label_mtd n) (dec_mtd T1 S1) ->
  decs.has  Ds2                  (label_mtd n) (dec_mtd T2 S2) ->
  decs.has (refine_decs Ds1 Ds2) (label_mtd n) (dec_mtd (t_or T1 T2) (t_and S1 S2)).
Proof. Admitted. (*
  intros n Ds1 Ds2 T1 S1 T2 S2 H. induction Ds1; intros.
  + decs.empty_binds_contradiction.
  + unfold decs.has, decs.get in H. destruct a eqn: Heqa.
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)).
      * inversions H. inversions e.
        unfold decs.has, decs.get. simpl. fold decs.get.
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 t) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n0) (label_fld n0)). {
          inversions H2.
        } {
          unfold decs.has in *. apply IHDs1; assumption.
        }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_fld n0 t) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          destruct (decs.eq_key_dec (label_mtd n) (label_fld n0)).
          + inversions e.
          + unfold decs.has in *. apply IHDs1; assumption.
        }
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)).
      * inversions H. inversions e.
        unfold decs.has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 T1 S1) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n0) (label_mtd n0)). {
          f_equal. rewrite -> (@refine_dec_spec_mtd Ds2 n0 T1 S1 T2 S2 H0).
          simpl. reflexivity. 
        } { contradiction n. reflexivity. }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs.has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (ndec_mtd n0 t t0) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          unfold decs.has in *. apply IHDs1; assumption.
        } 
Qed.*)

(* Refined decs shadow the outdated decs of Ds2.
   So [decs.ok (intersect Ds1 Ds2)] usually does not hold. *)
Definition intersect(Ds1 Ds2: decs.t): decs.t := LibList.append Ds2 (refine_decs Ds1 Ds2).

Lemma intersect_spec_1: forall l D Ds1 Ds2,
  decs.has    Ds1                l D ->
  decs.hasnt  Ds2                l   ->
  decs.has   (intersect Ds1 Ds2) l D .
Proof.
  intros. unfold intersect. apply decs.has_append_right.
  apply refine_decs_spec_unbound; assumption.
Qed.

Lemma intersect_spec_2: forall l D Ds1 Ds2,
  decs.hasnt Ds1                 l   ->
  decs.has   Ds2                 l D ->
  decs.has   (intersect Ds1 Ds2) l D.
Proof.
  intros. unfold intersect.
  apply (@decs.has_append_left l D Ds2 (refine_decs Ds1 Ds2) H0). 
  apply (@refine_decs_spec_unbound_preserved l Ds1 Ds2 H). 
Qed.

Lemma intersect_spec_12_fld: forall n T1 T2 Ds1 Ds2,
  decs.has Ds1                 (label_fld n) (dec_fld T1) ->
  decs.has Ds2                 (label_fld n) (dec_fld T2) ->
  decs.has (intersect Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).
Proof.
  intros. unfold intersect. apply decs.has_append_right.
  apply refine_decs_spec_fld; assumption.
Qed.

Lemma intersect_spec_12_mtd: forall n S1 T1 S2 T2 Ds1 Ds2,
  decs.has Ds1                 (label_mtd n) (dec_mtd S1 T1) ->
  decs.has Ds2                 (label_mtd n) (dec_mtd S2 T2) ->
  decs.has (intersect Ds1 Ds2) (label_mtd n) (dec_mtd (t_or S1 S2) (t_and T1 T2)).
Proof.
  intros. unfold intersect. apply decs.has_append_right.
  apply refine_decs_spec_mtd; assumption.
Qed.

End IntersectionPreviewImpl.


(* ###################################################################### *)
(** * Operational Semantics *)

(** Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
    Whenever we introduce a new avar_f (only happens in red_new), we choose one
    which is not in the store, so we never have name clashes. *) 
Inductive red : sto -> trm -> sto -> trm -> Prop :=
  (* computation rules *)
  | red_call : forall (s: sto) (x y: var) (m: nat) (T: typ) (ds: defs.t) (body: trm),
      binds x ds s ->
      defs.has ds (label_mtd m) (def_mtd T body) ->
      red s (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) 
          s (open_trm y body)
  | red_sel : forall (s: sto) (x: var) (y: avar) (l: nat) (ds: defs.t),
      binds x ds s ->
      defs.has ds (label_fld l) (def_fld y) ->
      red s (trm_sel (trm_var (avar_f x)) l) 
          s (trm_var y)
  | red_new : forall (s: sto) (ds: defs.t) (e: trm) (x: var),
      x # s ->
      red s (trm_new ds e)
          (s & x ~ ds) (open_trm x e)
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
Inductive has : ctx -> trm -> label -> dec -> Prop :=
  | has_dec : forall G e l D Ds,
      typing_trm G e (typ_rcd Ds) ->
      decs.has Ds l D ->
      has G e l D
with typing_trm : ctx -> trm -> typ -> Prop :=
  | typing_trm_var : forall G x T,
      binds x T G ->
      typing_trm G (trm_var (avar_f x)) T
  | typing_trm_sel : forall G e l T,
      has G e (label_fld l) (dec_fld T) ->
      typing_trm G (trm_sel e l) T
  | typing_trm_call : forall G t m U V u,
      has G t (label_mtd m) (dec_mtd U V) ->
      typing_trm G u U ->
      typing_trm G (trm_call t m u) V
  | typing_trm_new : forall G nis Ds t T,
      typing_defs G nis Ds -> (* no self reference yet, no recursion *)
      (forall x, x # G ->
                 typing_trm (G & x ~ typ_rcd Ds) (open_trm x t) T) ->
      typing_trm G (trm_new nis t) T
with typing_def : ctx -> ndef -> ndec -> Prop :=
  | typing_def_fld : forall G l v T,
      typing_trm G (trm_var v) T ->
      typing_def G (ndef_fld l v) (ndec_fld l T)
  | typing_def_mtd : forall G m S T t,
      (forall x, x # G ->
                 typing_trm (G & x ~ S) (open_trm x t) T) ->
      typing_def G (ndef_mtd m S t) (ndec_mtd m S T)
with typing_defs : ctx -> defs.t -> decs.t -> Prop :=
  | typing_defs_nil : forall G,
      typing_defs G nil nil
  | typing_defs_cons : forall G ds d Ds D,
      typing_defs G ds Ds ->
      typing_def  G d D ->
      typing_defs G (cons d ds) (cons D Ds).

Scheme has_mut         := Induction for has         Sort Prop
with   typing_trm_mut  := Induction for typing_trm  Sort Prop
with   typing_def_mut  := Induction for typing_def  Sort Prop
with   typing_defs_mut := Induction for typing_defs Sort Prop.

Combined Scheme typing_mutind from has_mut, typing_trm_mut, typing_def_mut, typing_defs_mut.


(* ###################################################################### *)
(** * Well-formed store ([wf_venv]) *)

Inductive wf_sto: sto -> ctx -> Prop :=
  | wf_sto_empty : wf_sto empty empty
  | wf_sto_push : forall s G x ds Ds,
      wf_sto s G ->
      x # s ->
      x # G ->
      typing_defs G ds Ds ->
      wf_sto (s & x ~ ds) (G & x ~ (typ_rcd Ds)).

(** ** Inversion lemmas for [wf_sto] *)

(*
Lemma invert_wf_sto_push: forall s G x ds Ds,
  wf_sto (s & x ~ ds) (G & x ~ typ_rcd Ds) ->
  wf_sto s G /\ x # s /\ x # G /\ typing_defs G ds Ds.
Proof.
  intros. inversions H. auto.
Qed.
*)

Lemma wf_sto_to_ok_s: forall s G,
  wf_sto s G -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto s G -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds: forall s G x T,
  wf_sto s G ->
  binds x T G ->
  exists ds, binds x ds s.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - eauto.
    - eauto.
Qed.

Lemma sto_unbound_to_ctx_unbound: forall s G x,
  wf_sto s G ->
  x # s ->
  x # G.
Admitted.


(* ###################################################################### *)
(** * Inversion lemmas for typing *)

(** **** Inverting [has] *)

Lemma invert_has: forall G e l d,
  has G e l d ->
  exists Ds, typing_trm G e (typ_rcd Ds) /\ decs.has Ds l d.
Proof. intros. inversions H. eauto. Qed.


(** **** Inverting [typing_trm] *)

Lemma invert_typing_trm_var: forall G x T,
  typing_trm G (trm_var (avar_f x)) T ->
  binds x T G.
Proof. intros. inversions H. assumption. Qed.

Lemma invert_typing_trm_sel: forall G e l T,
  typing_trm G (trm_sel e l) T ->
  has G e (label_fld l) (dec_fld T).
Proof. intros. inversions H. assumption. Qed.

Lemma invert_typing_trm_call: forall G t m V u,
  typing_trm G (trm_call t m u) V ->
  exists U, has G t (label_mtd m) (dec_mtd U V) /\ typing_trm G u U.
Proof. intros. inversions H. eauto. Qed.

Lemma invert_typing_trm_new: forall G is t T,
  typing_trm G (trm_new is t) T ->
  exists Ds, typing_defs G is Ds /\
             (forall x, x # G ->
                        typing_trm (G & x ~ typ_rcd Ds) (open_trm x t) T).
Proof. intros. inversions H. eauto. Qed.


(** **** Inverting [typing_def] *)

Lemma invert_typing_def_key: forall G i d, 
  typing_def G i d -> defs.key i = decs.key d.
Proof. intros. inversions H; reflexivity. Qed.

Lemma invert_typing_def_cases: forall G i d, 
  typing_def G i d ->
  (exists l x T, i = (ndef_fld l x) /\ d = (ndec_fld l T)) \/
  (exists m e T U, i = (ndef_mtd m T e) /\ d = (ndec_mtd m T U)).
Proof.
  intros. inversions H.
  + left. exists l v T. split; reflexivity.
  + right. exists m t S T. split; reflexivity.
Qed.

Lemma invert_typing_def: forall G i d, 
  typing_def G i d ->
  exists k iv dv, defs.key i = k /\ defs.value i = iv /\ 
                  decs.key d = k /\ decs.value d = dv.
Proof.
  intros. destruct (invert_typing_def_cases H)
    as [[l [x [T [Heq1 Heq2]]]] | [m [e [T [U [Heq1 Heq2]]]]]].
  + exists (label_fld l) (def_fld x) (dec_fld T). subst. auto.
  + exists (label_mtd m) (def_mtd T e) (dec_mtd T U). subst. auto.
Qed.


(** **** Inverting [typing_defs] *)

Lemma extract_typing_def_from_typing_defs: forall G l d ds D Ds,
  typing_defs G ds Ds ->
  defs.has ds l (defs.value d) ->
  decs.has Ds l (decs.value D) ->
  typing_def G d D.
Proof.
Admitted.

Lemma invert_typing_mtd_def_inside_typing_defs: forall G ds Ds m S1 S2 T body,
  typing_defs G ds Ds ->
  defs.has ds (label_mtd m) (def_mtd S1 body) ->
  decs.has Ds (label_mtd m) (dec_mtd S2 T) ->
  (* conclusion is the premise needed to pushtruct a typing_mtd_def: *)
  (forall y, y # G -> typing_trm (G & y ~ S2) (open_trm y body) T).
Proof.
Admitted.

Lemma invert_typing_fld_def_inside_typing_defs: forall G ds Ds l v T,
  typing_defs G ds Ds ->
  defs.has ds (label_fld l) (def_fld v) ->
  decs.has Ds (label_fld l) (dec_fld T) ->
  (* conclusion is the premise needed to pushtruct a typing_def_fld: *)
  typing_trm G (trm_var v) T.
Proof.
Admitted.

Lemma decs_has_to_defs_has: forall G l ds Ds D,
  typing_defs G ds Ds ->
  decs.has Ds l D ->
  exists d, defs.has ds l d.
Proof.
  introv Ty Bi. induction Ty.
  + decs.empty_binds_contradiction.
  + unfold decs.has, defs.has in *. rewrite decs.get_cons, defs.get_cons in *. case_if.
    - exists (defs.value d). reflexivity.
    - destruct (invert_typing_def H) as [k [dv [Dv [Hik [Hiv [Hdk Hdv]]]]]]. subst.
      case_if. apply (IHTy Bi).
Qed.


(* ###################################################################### *)
(** * Weakening lemmas *)

(*
Lemma weaken_binds: forall x T G H,
  ok (G & H) -> binds x T G -> binds x T (G & H).
Proof.
  intros x T G H. induction H; intros Hok Hb.
  + simpl. assumption.
  + rewrite -> ctx.concat_push_assoc in *. 
    destruct (ctx.invert_ok_push Hok) as [Hok' Hub].
    auto_specialize.
    ctx.compare_keys.
    - unfold ctx.unbound in Hub. rewrite -> e in IHlist. symmetry in Hub.
      assert (C: None = Some T). transitivity (ctx.get (ctx.key a) (G & H)); assumption.
      discriminate C.
    - assumption.
Qed.

Lemma weaken_binds_middle: forall x T G1 G2 G3,
  ok (G1 & G2 & G3) -> binds x T (G1 & G3) -> binds x T (G1 & G2 & G3).
Proof.
  intros x T G1 G2 G3. induction G3; intros Hok Hb.
  + simpl in *. apply (weaken_binds _ Hok Hb).
  + rewrite -> ctx.concat_push_assoc in *. 
    destruct (ctx.invert_ok_push Hok) as [Hok' Hub].
    ctx.compare_keys.
    - assumption.
    - apply (IHG3 Hok' Hb).
Qed.
*)

(* If we only weaken at the end, i.e. from [G1] to [G1 & G2], the IH for the 
   [typing_trm_new] case adds G2 to the end, so it takes us from [G1, x: Ds] 
   to [G1, x: Ds, G2], but we need [G1, G2, x: Ds].
   So we need to weaken in the middle, i.e. from [G1 & G3] to [G1 & G2 & G3].
   Then, the IH for the [typing_trm_new] case inserts G2 in the middle, so it
   takes us from [G1 & G3, x: Ds] to [G1 & G2 & G3, x: Ds], which is what we
   need. *)

Lemma weakening:
   (forall G e l d (Hhas: has G e l d)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)),
           has (G1 & G2 & G3) e l d ) 
/\ (forall G e T (Hty: typing_trm G e T)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)),
           typing_trm (G1 & G2 & G3) e T) 
/\ (forall G i d (Hty: typing_def G i d)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)), 
           typing_def (G1 & G2 & G3) i d)
/\ (forall G is Ds (Hisds: typing_defs G is Ds)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)), 
           typing_defs (G1 & G2 & G3) is Ds).
Proof.
  apply typing_mutind; intros; unfoldp;
    repeat match goal with
    | H: forall (_ _ _ : env typ), _ |- _ => 
        specialize (H G1 G2 G3 Heq Hok123); let IH := fresh IH in rename H into IH
    end;
    subst.
  + apply* has_dec.
  + apply typing_trm_var. apply* binds_weaken.
  + apply* typing_trm_sel.
  + apply* typing_trm_call.
  + apply (typing_trm_new _ IH). intros.
    assert (Hub13: x # (G1 & G3)) by auto.
    rewrite <- concat_assoc.
    apply H0.
    - assumption.
    - rewrite -> concat_assoc. reflexivity.
    - rewrite -> concat_assoc. auto.
  + apply* typing_def_fld.
  + apply typing_def_mtd.
    intros.
    assert (Hub13: x # (G1 & G3)) by auto.
    rewrite <- concat_assoc.
    apply H.
    - assumption.
    - rewrite -> concat_assoc. reflexivity.
    - rewrite -> concat_assoc. auto.
  + apply typing_defs_nil.
  + apply* typing_defs_cons.
Qed.

Print Assumptions weakening.

Lemma weaken_has: forall G1 G2 e l d,
  has G1 e l d -> ok (G1 & G2) -> has (G1 & G2) e l d.
Proof.
  intros.
  destruct weakening as [W _].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_typing_trm: forall G1 G2 e T,
  typing_trm G1 e T -> ok (G1 & G2) -> typing_trm (G1 & G2) e T.
Proof.
  intros.
  destruct weakening as [_ [W _]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_typing_def: forall G1 G2 i d,
  typing_def G1 i d -> ok (G1 & G2) -> typing_def (G1 & G2) i d.
Proof.
  intros.
  destruct weakening as [_ [_ [W _]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_typing_defs: forall G1 G2 is Ds,
  typing_defs G1 is Ds -> ok (G1 & G2) -> typing_defs (G1 & G2) is Ds.
Proof.
  intros.
  destruct weakening as [_ [_ [_ W]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.


(* ###################################################################### *)
(** * Inversion lemmas which depend on weakening *)

Lemma invert_wf_sto: forall s G,
  wf_sto s G -> 
    forall x ds Ds, 
      binds x ds s -> 
      binds x (typ_rcd Ds) G ->
      typing_defs G ds Ds.
Proof.
  intros s G Wf. induction Wf; intros.
  + false* binds_empty_inv.
  + unfoldp. (*rename H into Hvb, H0 into Htb, H1 into Hisds, H2 into Hvb0, H3 into Htb0.*)
    unfold binds in *. rewrite get_push in *.
    case_if.
    - inversions H2. inversions H3. apply* weaken_typing_defs.
    - apply* weaken_typing_defs.
Qed.

(* ###################################################################### *)
(** * Progress *)

Theorem progress: forall s G e T,
  wf_sto s G ->
  typing_trm G e T -> 
  (
    (* can step *)
    (exists s' e', red s e s' e') \/
    (* or is a value *)
    (exists x is, e = (trm_var (avar_f x)) /\ binds x is s)
  ).
Proof.
  introv Wf Ty. gen G e T Ty s Wf.
  set (progress_for := fun s e =>
                         (exists s' e', red s e s' e') \/
                         (exists x is, e = (trm_var (avar_f x)) /\ binds x is s)).
  apply (typing_trm_mut
    (fun G e l d (Hhas: has G e l d)         => forall s, wf_sto s G -> progress_for s e)
    (fun G e T   (Hty: typing_trm G e T)     => forall s, wf_sto s G -> progress_for s e)
    (fun G i d   (Htyp: typing_def G i d)    => True)
    (fun G is Ds (Htyp: typing_defs G is Ds) => True));
  unfold progress_for; clear progress_for; intros; try apply I; auto_specialize.
  (* case has_dec *)
  + assumption. 
  (* case typing_trm_var *)
  + right. destruct (ctx_binds_to_sto_binds H b) as [is Hbv].
    exists x is. auto.
  (* case typing_trm_sel *)
  + left. destruct H as [IH | IH].
    (* receiver is an expression *)
    - destruct IH as [s' [e' IH]]. do 2 eexists. apply (red_sel1 l IH). 
    (* receiver is a var *)
    - destruct IH as [x [is [Heq Hbv]]]. subst.
      destruct (invert_has h) as [ds [Hty Hbd]].
      lets Hbt: (invert_typing_trm_var Hty).
      lets Hty2: (invert_wf_sto H0 Hbv Hbt).
      destruct (decs_has_to_defs_has Hty2 Hbd) as [i Hbi].
      destruct (defs_binds_fld_sync_val Hbi) as [y Heq]. subst.
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
        lets Hbt: (invert_typing_trm_var Hty).
        lets Hty2: (invert_wf_sto H1 Hbv Hbt).
        destruct (decs_has_to_defs_has Hty2 Hbd) as [i Hbi].
        destruct (defs_binds_mtd_sync_val Hbi) as [U' [e Heq]]. subst.
        exists s (open_trm y e).
        apply (red_call y Hbv Hbi).
  (* case typing_trm_new *)
  + left. (* TODO pick_fresh *) admit. (*
    destruct (sto_gen_fresh s) as [x Hxub].
    exists (s ;; (x, nis)) (open_trm x t).
    apply red_new. assumption.*)
Qed.

Print Assumptions progress.

(* ###################################################################### *)
(** * The substitution principle *)

(* TODO: first define substitution... *)

(*

                  G, x: S |- e : T      G |- u : S
                 ----------------------------------
                            G |- [u/x]e : T

Note that in general, u is a term, but for our purposes, it suffices to consider
the special case where u is a variable.
*)

(*
Lemma destruct_trm_var_eq_open_trm: forall z x e,
  trm_var (avar_f z) = open_trm x e ->
  (z = x /\ (e = trm_var (avar_b 0) \/ e = trm_var (avar_f z)))
  \/ z <> x.
Proof.
  intros. unfold open_trm, open_rec_trm in H. destruct e; try discriminate H.
  inversion H.
  unfold open_rec_avar in H1. destruct a.
  + destruct (eq_nat_dec 0 n).
    - inversions H1. left. split. reflexivity. left. reflexivity.
    - discriminate H1.
  + inversions H1. destruct (eq_nat_dec v x).
    - subst. left. split. reflexivity. right. reflexivity.
    - right. assumption.
Qed.
*)

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
    - inversions H1. left; split; reflexivity.
    - discriminate H1.
  + inversions H1. right; reflexivity.
Qed.
*)

Lemma raw_subst_principles: 
  forall G1 G2 y S, typing_trm (G1 & G2) (trm_var (avar_f y)) S ->
  (forall (G0 : ctx) (e0 : trm) (l : label) (d : dec) (Hhas : has G0 e0 l d),
    (fun G0 e0 l d (Hhas: has G0 e0 l d) => 
      forall x e, G0 = (G1 ;; (x, S) & G2) ->
                  ok (G1 ;; (x, S) & G2) ->
                  e0 = (open_trm x e) -> 
                  has (G1 & G2) (open_trm y e) l d)
    G0 e0 l d Hhas) /\
  (forall (G0 : ctx) (e0 : trm) (T : typ) (Hty : typing_trm G0 e0 T),
    (fun G0 e0 T (Hty: typing_trm G0 e0 T) => 
      forall x e, G0 = (G1 ;; (x, S) & G2) ->
                  ok (G1 ;; (x, S) & G2) ->
                  e0 = (open_trm x e) -> 
                  typing_trm (G1 & G2) (open_trm y e) T)
    G0 e0 T Hty) /\
  (forall (G0 : ctx) (i0 : ndef) (d : ndec) (Hty : typing_def G0 i0 d),
    (fun G i0 d (Htyp: typing_def G i0 d) => 
      forall x i, G0 = (G1 ;; (x, S) & G2) ->
                  ok (G1 ;; (x, S) & G2) ->
                  i0 = (open_ndef x i) -> 
                  typing_def (G1 & G2) (open_ndef y i) d)
    G0 i0 d Hty) /\
  (forall (G0 : ctx) (is0 : defs.t) (ds : decs.t) (Hty : typing_defs G0 is0 Ds),
    (fun G is0 Ds (Hty: typing_defs G is0 Ds) => 
      forall x is, G0 = (G1 ;; (x, S) & G2) ->
                   ok (G1 ;; (x, S) & G2) ->
                   is0 = (map (open_ndef y) is) -> 
                   typing_defs (G1 & G2) (map (open_ndef y) is) Ds)
    G0 is0 Ds Hty).
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
    | H: @eq ctx _ _ |- _ => rename H into EqG
  end;
  match goal with
    | H: @eq trm    _ _ |- _ => rename H into EqTrm
    | H: @eq ndef   _ _ |- _ => rename H into EqIni
    | H: @eq defs.t _ _ |- _ => rename H into EqInis
  end;
  match goal with
    | H: ok _ |- _ => rename H into Hok
  end.
  (* case has_dec *)
  + specialize (IH _ _ EqG Hok EqTrm).
    apply has_dec with Ds; assumption.
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
  (* case typing_def_fld *)
  + admit.
  (* case typing_def_mtd *)
  + admit.
  (* case typing_defs_empty *)
  + admit.
  (* case typing_defs_push *)
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
  destruct (raw_subst_principles G empty Hy) as [_ [P _]].
  assert (Hok: ok (G ;; (x, S))). admit.
  apply (P _ _ _ He _ _ eq_refl Hok eq_refl).
Qed.


(* ###################################################################### *)
(** * Preservation *)

Theorem preservation_proof:
  forall s e s' e' (Hred: red s e s' e') G T (Hwf: wf_sto s G) (Hty: typing_trm G e T),
  (exists H, wf_sto s' (G & H) /\ typing_trm (G & H) e' T).
Proof.
  intros s e s' e' Hred. induction Hred; intros.
  (* red_call *)
  + rename H into Hvbx. rename H0 into Hibm. rename T0 into U.
    exists empty. simpl. split. apply Hwf.
    (* Grab "ctx binds x" hypothesis: *)
    apply invert_typing_trm_call in Hty. 
    destruct Hty as [T' [Hhas Htyy]].
    apply invert_has in Hhas. 
    destruct Hhas as [ds [Htyx Hdbm]].
    apply invert_typing_trm_var in Htyx. rename Htyx into Htbx.
    (* Feed "binds x" and "ctx binds x" to invert_wf_sto: *)
    keep (invert_wf_sto Hwf Hvbx Htbx) as Hisds.
    keep (invert_typing_mtd_def_inside_typing_defs Hisds Hibm Hdbm) as Hmtd.
    destruct (ctx_gen_fresh G) as [y' Htuy'].
    specialize (Hmtd y' Htuy').
    apply (subst_principle _ Hmtd Htyy).
  (* red_sel *)
  + rename H into Hvbx. rename H0 into Hibl.
    exists empty. simpl. split. apply Hwf.
    apply invert_typing_trm_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [ds [Htyx Hdbl]].
    apply invert_typing_trm_var in Htyx. rename Htyx into Htbx.
    (* Feed "binds x" and "ctx binds x" to invert_wf_sto: *)
    keep (invert_wf_sto Hwf Hvbx Htbx) as Hisds.
    apply (invert_typing_fld_def_inside_typing_defs Hisds Hibl Hdbl).
  (* red_new *)
  + rename H into Hvux.
    apply invert_typing_trm_new in Hty.
    destruct Hty as [ds [Hisds Htye]].
    keep (sto_unbound_to_ctx_unbound Hwf Hvux) as Htux.
    exists (empty ;; (x, typ_rcd Ds)). simpl. split.
    - apply (wf_sto_push Hwf Hvux Htux Hisds).
    - apply (Htye x Htux).
  (* red_call1 *)
  + rename T into Tr.
    apply invert_typing_trm_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    apply invert_has in Hhas.
    destruct Hhas as [ds [Htyo Hdbm]].
    specialize (IHHred G (typ_rcd Ds) Hwf Htyo).
    destruct IHHred as [H [Hwf' Htyo']].
    exists H. split. assumption. apply (@typing_trm_call (G & H) o' m Ta Tr a).
    - apply (has_dec Htyo' Hdbm).
    - destruct (wf_sto_ok Hwf') as [_ Hok].
      apply (weaken_typing_trm _ Htya Hok).
  (* red_call2 *)
  + rename T into Tr.
    apply invert_typing_trm_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    specialize (IHHred G Ta Hwf Htya).
    destruct IHHred as [H [Hwf' Htya']].
    exists H. split. assumption. apply (@typing_trm_call (G & H) _ m Ta Tr a').
    - destruct (wf_sto_ok Hwf') as [_ Hok].
      apply (weaken_has _ Hhas Hok).
    - assumption.
  (* red_sel1 *)
  + apply invert_typing_trm_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [ds [Htyo Hdbl]].
    specialize (IHHred G (typ_rcd Ds) Hwf Htyo).
    destruct IHHred as [H [Hwf' Htyo']].
    exists H. split. assumption. apply (@typing_trm_sel (G & H) o' l T).
    apply (has_dec Htyo' Hdbl).
Qed.

Theorem preservation: forall s G e T s' e',
  wf_sto s G -> typing_trm G e T -> red s e s' e' ->
  (exists G', wf_sto s' G' /\ typing_trm G' e' T).
Proof.
  intros s G e T s' e' Hwf Hty Hred.
  destruct (preservation_proof Hred Hwf Hty) as [H [Hwf' Hty']].
  exists (G & H). split; assumption.
Qed.

Print Assumptions preservation.
