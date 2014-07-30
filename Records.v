
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
  | typ_rcd  : decs -> typ (* record type *)
with dec : Type :=
  | dec_fld : typ -> dec
  | dec_mtd : typ -> typ -> dec
with decs : Type :=
  | decs_nil : decs
  | decs_cons : nat -> dec -> decs -> decs.

Inductive trm : Type :=
  | trm_var  : avar -> trm
  | trm_new  : defs -> trm -> trm
  | trm_sel  : trm -> nat -> trm
  | trm_call : trm -> nat -> trm -> trm
with def : Type :=
  | def_fld : avar -> def (* cannot have term here, need to assign first *)
  | def_mtd : typ -> trm -> def
with defs : Type :=
  | defs_nil : defs
  | defs_cons : nat -> def -> defs -> defs.

Scheme trm_mut  := Induction for trm  Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, def_mut, defs_mut.

Definition label_for_def(n: nat)(d: def): label := match d with
| def_fld _ => label_fld n
| def_mtd _ _ => label_mtd n
end.

Fixpoint get_def(l: label)(ds: defs): option def := match ds with
| defs_nil => None
| defs_cons n d ds' => If l = label_for_def n d then Some d else get_def l ds'
end.

Definition label_for_dec(n: nat)(D: dec): label := match D with
| dec_fld _ => label_fld n
| dec_mtd _ _ => label_mtd n
end.

Fixpoint get_dec(l: label)(Ds: decs): option dec := match Ds with
| decs_nil => None
| decs_cons n D Ds' => If l = label_for_dec n D then Some D else get_dec l Ds'
end.

Definition defs_has(ds: defs)(l: label)(d: def): Prop := (get_def l ds = Some d).
Definition defs_hasnt(ds: defs)(l: label): Prop := (get_def l ds = None).

Definition decs_has(Ds: decs)(l: label)(D: dec): Prop := (get_dec l Ds = Some D).
Definition decs_hasnt(Ds: decs)(l: label): Prop := (get_dec l Ds = None).

(** ** Syntactic sugar *)
Definition trm_fun(T: typ)(body: trm) := trm_new (defs_cons 0 (def_mtd T body) defs_nil)
                                                 (trm_var (avar_b 0)).
Definition trm_app(func arg: trm) := trm_call func 0 arg.
Definition trm_let(T: typ)(rhs body: trm) := trm_app (trm_fun T body) rhs.
Definition trm_upcast(T: typ)(e: trm) := trm_app (trm_fun T (trm_var (avar_b 0))) e.
Definition typ_arrow(T1 T2: typ) := typ_rcd (decs_cons 0 (dec_mtd T1 T2) decs_nil).


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
  | trm_new ds e => trm_new (open_rec_defs (S k) u ds) (open_rec_trm (S k) u e)
  | trm_sel e n => trm_sel (open_rec_trm k u e) n
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: nat) (u: var) (d: def) { struct d } : def :=
  match d with
  | def_fld a   => def_fld (open_rec_avar k u a)
  | def_mtd T e => def_mtd T (open_rec_trm (S k) u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs) { struct ds } : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons n d tl => defs_cons n (open_rec_def k u d) (open_rec_defs k u tl)
  end.

Definition open_avar  u a := open_rec_avar  0 u a.
Definition open_trm   u e := open_rec_trm   0 u e.
Definition open_def  u d := open_rec_def  0 u d.
Definition open_defs u l := open_rec_defs 0 u l.


(* ###################################################################### *)
(** * Free variables *)

Fixpoint fv_avar (a: avar) { struct a } : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

(*
(* It's a bit tricky to convince Coq that these fv functions terminate.
   One solution is to inline fv_defs. See http://cs.stackexchange.com/questions/104. *)
Fixpoint fv_trm (t: trm) : vars :=
  let fv_defs := (fix fv_defs (ds: list def) : vars := match ds with
  | nil => \{}
  | cons d rest => (fv_def d) \u (fv_defs rest)
  end) in
  match t with
  | trm_var x => fv_avar x
  | trm_new ds t => (fv_defs ds) \u (fv_trm t)
  | trm_sel t l => fv_trm t
  | trm_call t1 m t2 => (fv_trm t1) \u (fv_trm t2)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_fld l x => fv_avar x
  | def_mtd m T u => fv_trm u
  end.
Fixpoint fv_defs (ds: list def) : vars := 
  match ds with
  | nil => \{}
  | cons d rest => (fv_def d) \u (fv_defs rest)
  end.
*)

(* If we define defs ourselves instead of using [list def], we don't have any
   termination proof problems: *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var x => fv_avar x
  | trm_new ds t => (fv_defs ds) \u (fv_trm t)
  | trm_sel t l => fv_trm t
  | trm_call t1 m t2 => (fv_trm t1) \u (fv_trm t2)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_fld x => fv_avar x
  | def_mtd T u => fv_trm u
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil => \{}
  | defs_cons n d tl => (fv_def d) \u (fv_defs tl)
  end.


(* ###################################################################### *)
(** * Var-by-var substitution *)

Fixpoint subst_avar (z: var) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = z then (avar_f u) else (avar_f x)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x => trm_var (subst_avar z u x)
  | trm_new ds t => trm_new (subst_defs z u ds) (subst_trm z u t)
  | trm_sel t l => trm_sel (subst_trm z u t) l
  | trm_call t1 m t2 => trm_call (subst_trm z u t1) m (subst_trm z u t2)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_fld x => def_fld (subst_avar z u x)
  | def_mtd T b => def_mtd T (subst_trm z u b)
  end
with subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons n d rest => defs_cons n (subst_def z u d) (subst_defs z u rest)
  end.

(* Hint Constructors avar trm def defs def. *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh: forall x y,
  (forall t : trm  , x \notin fv_trm   t  -> subst_trm  x y t  = t ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*; apply* subst_fresh_avar.
Qed.

Definition subst_fvar(x y z: var): var := If x = z then y else z.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: nat,
    subst_avar x y (open_rec_avar n u a) 
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute: forall x y u,
  (forall t : trm, forall n: nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall d : def , forall n: nat, 
     subst_def x y (open_rec_def n u d)
     = open_rec_def n (subst_fvar x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: nat, 
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*; apply* subst_open_commute_avar.
Qed.

Lemma subst_id_avar: forall x,
  (forall a : avar, subst_avar x x a  = a).
Proof.
  intros. unfold subst_avar. destruct* a. case_var*.
Qed.

Lemma subst_id_not_needed: forall x,
  (forall t : trm  , subst_trm  x x t  = t ) /\
  (forall d : def , subst_def  x x d  = d ) /\
  (forall ds: defs, subst_defs x x ds = ds).
Proof.
  intro x. apply trm_mutind; intros; unfold subst_trm, subst_def, subst_defs;
  f_equal*; apply* subst_id_avar.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm.
  destruct (@subst_open_commute x u x) as [P _]. rewrite* (P t 0).
  destruct (@subst_fresh x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Print Assumptions subst_intro_trm.


(* ###################################################################### *)

(** ** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** ** Value environment ("store") *)
Definition sto := env defs.


(* ###################################################################### *)
(** * Preview: How intersection will work *)

Module Type IntersectionPreview.

(* Will be part of syntax: *)
Parameter t_and: typ -> typ -> typ.
Parameter t_or:  typ -> typ -> typ.

(* Left as an exercise for the reader ;-) We define intersection by the spec below. *)
Parameter intersect: decs -> decs -> decs.

Axiom intersect_spec_1: forall l D Ds1 Ds2,
  decs_has    Ds1                l D ->
  decs_hasnt  Ds2                l   ->
  decs_has   (intersect Ds1 Ds2) l D .

Axiom intersect_spec_2: forall l D Ds1 Ds2,
  decs_hasnt Ds1                 l   ->
  decs_has   Ds2                 l D ->
  decs_has   (intersect Ds1 Ds2) l D.

Axiom intersect_spec_12_fld: forall n T1 T2 Ds1 Ds2,
  decs_has Ds1                 (label_fld n) (dec_fld T1) ->
  decs_has Ds2                 (label_fld n) (dec_fld T2) ->
  decs_has (intersect Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).

Axiom intersect_spec_12_mtd: forall n S1 T1 S2 T2 Ds1 Ds2,
  decs_has Ds1                 (label_mtd n) (dec_mtd S1 T1) ->
  decs_has Ds2                 (label_mtd n) (dec_mtd S2 T2) ->
  decs_has (intersect Ds1 Ds2) (label_mtd n) (dec_mtd (t_or S1 S2) (t_and T1 T2)).

End IntersectionPreview.

(* Exercise: Give any implementation of `intersect`, and prove that it satisfies
   the specification. Happy hacking! ;-) *)
Module IntersectionPreviewImpl <: IntersectionPreview.

(* Will be part of syntax: *)
Parameter t_and: typ -> typ -> typ.
Parameter t_or:  typ -> typ -> typ.

Fixpoint refine_dec(n1: nat)(D1: dec)(Ds2: decs): dec := match Ds2 with
| decs_nil => D1
| decs_cons n2 D2 tail2 => match D1, D2 with
    | dec_fld T1   , dec_fld T2    => If n1 = n2
                                      then dec_fld (t_and T1 T2) 
                                      else refine_dec n1 D1 tail2
    | dec_mtd T1 S1, dec_mtd T2 S2 => If n1 = n2
                                      then dec_mtd (t_or T1 T2) (t_and S1 S2) 
                                      else refine_dec n1 D1 tail2
    | _, _ => refine_dec n1 D1 tail2
    end
end.

Lemma refine_dec_spec_fld: forall Ds2 n T1 T2,
  decs_has Ds2 (label_fld n) (dec_fld T2) ->
  (refine_dec n (dec_fld T1) Ds2) = (dec_fld (t_and T1 T2)).
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
        apply IHDs2. unfold decs_has, decs.get. unfold decs.key.
        assumption.
      * apply IHDs2. unfold decs_has, decs.get. unfold decs.key.
        assumption.
Qed.*)

Lemma refine_dec_spec_mtd: forall Ds2 n T1 S1 T2 S2,
  decs_has Ds2 (label_mtd n) (dec_mtd T2 S2) ->
  (refine_dec n (dec_mtd T1 S1) Ds2) = (dec_mtd (t_or T1 T2) (t_and S1 S2)).
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

Lemma refine_dec_spec_unbound: forall n D1 Ds2, 
  decs_hasnt Ds2 (label_for_dec n D1) ->
  (refine_dec n D1 Ds2) = D1.
Proof. Admitted. (*
  intros.
  induction Ds2.
  + simpl. reflexivity.
  + unfold decs.key. unfold refine_dec. destruct a; destruct D1.
    - destruct (eq_nat_dec n0 n) eqn: Hn0dec.
      * subst. 
        assert (Hkeq: (decs.key (dec_fld n t0)) = (decs.key (dec_fld n t)))
          by reflexivity.
        rewrite -> Hkeq in H.
        exfalso. apply (decs_has Ds_unbound_head_inv H).
      * fold refine_dec. apply IHDs2.
        inversions H. unfold decs.eq_key_dec in H1.
        destruct (eq_label_dec (label_fld n0) (label_fld n)).
        { inversions e. contradiction n1. reflexivity. }
        { unfold decs_hasnt. unfold decs.key. assumption. }
    - fold refine_dec. unfold decs.key in *.
      apply decs_hasnt Ds_cons_inv in H. apply (IHDs2 H).
    - fold refine_dec. unfold decs.key in *.
      apply decs_hasnt Ds_cons_inv in H. apply (IHDs2 H).
    - destruct (eq_nat_dec n0 n) eqn: Hn0dec.
      * subst. 
        assert (Hkeq: (decs.key (dec_mtd n t1 t2)) = (decs.key (dec_mtd n t t0)))
          by reflexivity.
        rewrite -> Hkeq in H.
        exfalso. apply (decs_has Ds_unbound_head_inv H).
      * fold refine_dec. apply IHDs2.
        inversions H. unfold decs.eq_key_dec in H1. 
        destruct (eq_label_dec (label_mtd n0) (label_mtd n)).
        { inversions e. contradiction n1. reflexivity. }
        { unfold decs_hasnt. unfold decs.key. assumption. }
Qed.*)

Fixpoint refine_decs(Ds1: decs)(Ds2: decs): decs := match Ds1 with
| decs_nil => decs_nil
| decs_cons n D1 Ds1tail => decs_cons n (refine_dec n D1 Ds2) (refine_decs Ds1tail Ds2)
end.

Lemma refine_decs_spec_unbound: forall l D Ds1 Ds2,
  decs_has    Ds1                  l D ->
  decs_hasnt  Ds2                  l   ->
  decs_has   (refine_decs Ds1 Ds2) l D .
Proof. Admitted. (*
  intros. unfold refine_decs.
  assert (Hex: exists nd, decs.key nd = l /\ decs.value nd = d).
    apply (@decs_has Ds_binding_inv l d Ds1 H).
  destruct Hex as [nd [Hl Hd]]. subst.
  remember (fun D1 => refine_dec D1 Ds2) as f.
  assert (Hk: (decs.key nd) = decs.key (f nd)).
    subst. apply (refine_dec_spec_label nd Ds2).
  rewrite -> Hk.
  assert (Hv: (decs.value nd) = decs.value (f nd)).
    subst. symmetry. apply (refine_dec_spec_unbound _ H0).
  rewrite -> Hv.
  apply decs_has Ds_map. 
    intro. rewrite -> Heqf. symmetry. apply refine_dec_spec_label.
    assumption.
Qed.*)

Lemma refine_decs_spec_unbound_preserved: forall l Ds1 Ds2,
  decs_hasnt Ds1                   l ->
  decs_hasnt (refine_decs Ds1 Ds2) l .
Proof. Admitted. (*
  intros. unfold refine_decs. remember (fun D1 => refine_dec D1 Ds2) as f.
  refine (@decs_hasnt Ds_map l f Ds1 _ H).
  subst. intro. symmetry. apply refine_dec_spec_label.
Qed.*)

Lemma refine_decs_spec_fld: forall n Ds1 Ds2 T1 T2,
  decs_has  Ds1                  (label_fld n) (dec_fld T1) ->
  decs_has  Ds2                  (label_fld n) (dec_fld T2) ->
  decs_has (refine_decs Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).
Proof. Admitted. (*
  intros n Ds1 Ds2 T1 T2 H. induction Ds1; intros.
  + decs.empty_binds_contradiction.
  + unfold decs_has, decs.get in H. destruct a eqn: Heqa.
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_fld n) (label_fld n0)).
      * inversions H. inversions e.
        unfold decs_has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (dec_fld n0 T1) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n0) (label_fld n0)). {
          f_equal. rewrite -> (@refine_dec_spec_fld Ds2 n0 T1 T2 H0).
          simpl. reflexivity. 
        } { contradiction n. reflexivity. }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs_has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (dec_fld n0 t) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n) (label_fld n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          unfold decs_has in *. apply IHDs1; assumption.
        }
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_fld n) (label_fld n0)).
      * inversions H. inversions e.
        unfold decs_has, decs.get. simpl. fold decs.get.
        rewrite <- (@refine_dec_spec_label (dec_mtd n0 t t0) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n0) (label_mtd n0)). {
          inversions H2.
        } {
          unfold decs_has in *. apply IHDs1; assumption.
        }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs_has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (dec_mtd n0 t t0) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_fld n) (label_fld n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          destruct (decs.eq_key_dec (label_fld n) (label_mtd n0)).
          + inversions e.
          + unfold decs_has in *. apply IHDs1; assumption.
        }
Qed.*)

Lemma refine_decs_spec_mtd: forall n Ds1 Ds2 T1 S1 T2 S2,
  decs_has  Ds1                  (label_mtd n) (dec_mtd T1 S1) ->
  decs_has  Ds2                  (label_mtd n) (dec_mtd T2 S2) ->
  decs_has (refine_decs Ds1 Ds2) (label_mtd n) (dec_mtd (t_or T1 T2) (t_and S1 S2)).
Proof. Admitted. (*
  intros n Ds1 Ds2 T1 S1 T2 S2 H. induction Ds1; intros.
  + decs.empty_binds_contradiction.
  + unfold decs_has, decs.get in H. destruct a eqn: Heqa.
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)).
      * inversions H. inversions e.
        unfold decs_has, decs.get. simpl. fold decs.get.
        rewrite <- (@refine_dec_spec_label (dec_fld n0 t) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n0) (label_fld n0)). {
          inversions H2.
        } {
          unfold decs_has in *. apply IHDs1; assumption.
        }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs_has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (dec_fld n0 t) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          destruct (decs.eq_key_dec (label_mtd n) (label_fld n0)).
          + inversions e.
          + unfold decs_has in *. apply IHDs1; assumption.
        }
    - fold decs.get in H. unfold decs.key in H.
      destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)).
      * inversions H. inversions e.
        unfold decs_has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (dec_mtd n0 T1 S1) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n0) (label_mtd n0)). {
          f_equal. rewrite -> (@refine_dec_spec_mtd Ds2 n0 T1 S1 T2 S2 H0).
          simpl. reflexivity. 
        } { contradiction n. reflexivity. }
      * assert (Hnn: n <> n0). unfold not in *. intro. apply n1. f_equal. assumption.
        unfold decs_has, decs.get. simpl. fold decs.get. 
        rewrite <- (@refine_dec_spec_label (dec_mtd n0 t t0) Ds2).
        unfold decs.key.
        destruct (decs.eq_key_dec (label_mtd n) (label_mtd n0)). {
          inversions e. contradiction Hnn. reflexivity.
        } {
          unfold decs_has in *. apply IHDs1; assumption.
        } 
Qed.*)

Fixpoint decs_concat(Ds1 Ds2: decs) {struct Ds1}: decs := match Ds1 with
| decs_nil => Ds2
| decs_cons n D1 Ds1tail => decs_cons n D1 (decs_concat Ds1tail Ds2)
end.

(* Refined decs shadow the outdated decs of Ds2.
   So [decs.ok (intersect Ds1 Ds2)] usually does not hold. *)
Definition intersect(Ds1 Ds2: decs): decs := decs_concat Ds2 (refine_decs Ds1 Ds2).

Lemma decs_has_concat_right : forall k v E1 E2,
  decs_has E2                     k v ->
  decs_has (decs_concat E1 E2) k v.
Proof. Admitted.

Lemma decs_has_concat_left : forall k v E1 E2,
  decs_has   E1 k v ->
  decs_hasnt E2 k ->
  decs_has   (decs_concat E1 E2) k v.
Proof. Admitted.

Lemma intersect_spec_1: forall l D Ds1 Ds2,
  decs_has    Ds1                l D ->
  decs_hasnt  Ds2                l   ->
  decs_has   (intersect Ds1 Ds2) l D .
Proof.
  intros. unfold intersect. apply decs_has_concat_right.
  apply refine_decs_spec_unbound; assumption.
Qed.

Lemma intersect_spec_2: forall l D Ds1 Ds2,
  decs_hasnt Ds1                 l   ->
  decs_has   Ds2                 l D ->
  decs_has   (intersect Ds1 Ds2) l D.
Proof.
  intros. unfold intersect.
  apply (@decs_has_concat_left l D Ds2 (refine_decs Ds1 Ds2) H0). 
  apply (@refine_decs_spec_unbound_preserved l Ds1 Ds2 H). 
Qed.

Lemma intersect_spec_12_fld: forall n T1 T2 Ds1 Ds2,
  decs_has Ds1                 (label_fld n) (dec_fld T1) ->
  decs_has Ds2                 (label_fld n) (dec_fld T2) ->
  decs_has (intersect Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).
Proof.
  intros. unfold intersect. apply decs_has_concat_right.
  apply refine_decs_spec_fld; assumption.
Qed.

Lemma intersect_spec_12_mtd: forall n S1 T1 S2 T2 Ds1 Ds2,
  decs_has Ds1                 (label_mtd n) (dec_mtd S1 T1) ->
  decs_has Ds2                 (label_mtd n) (dec_mtd S2 T2) ->
  decs_has (intersect Ds1 Ds2) (label_mtd n) (dec_mtd (t_or S1 S2) (t_and T1 T2)).
Proof.
  intros. unfold intersect. apply decs_has_concat_right.
  apply refine_decs_spec_mtd; assumption.
Qed.

End IntersectionPreviewImpl.


(* ###################################################################### *)

Lemma defs_has_fld_sync: forall n d ds,
  defs_has ds (label_fld n) d -> exists x, d = (def_fld x).
Proof.
  introv Hhas. induction ds; unfolds defs_has, get_def. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_def in H. destruct* d. discriminate.
    - apply* IHds.
Qed.

Lemma defs_has_mtd_sync: forall n d ds,
  defs_has ds (label_mtd n) d -> exists T e, d = (def_mtd T e).
Proof.
  introv Hhas. induction ds; unfolds defs_has, get_def. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_def in H. destruct* d. discriminate.
    - apply* IHds.
Qed.


(* ###################################################################### *)
(** * Operational Semantics *)

(** Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
    Whenever we introduce a new avar_f (only happens in red_new), we choose one
    which is not in the store, so we never have name clashes. *) 
Inductive red : sto -> trm -> sto -> trm -> Prop :=
  (* computation rules *)
  | red_call : forall (s: sto) (x y: var) (m: nat) (T: typ) (ds: defs) (body: trm),
      binds x ds s ->
      defs_has ds (label_mtd m) (def_mtd T body) ->
      red s (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) 
          s (open_trm y body)
  | red_sel : forall (s: sto) (x: var) (y: avar) (l: nat) (ds: defs),
      binds x ds s ->
      defs_has ds (label_fld l) (def_fld y) ->
      red s (trm_sel (trm_var (avar_f x)) l) 
          s (trm_var y)
  | red_new : forall (s: sto) (ds: defs) (e: trm) (x: var),
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
      decs_has Ds l D ->
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
  | typing_trm_new : forall G ds Ds t T x,
      typing_defs G ds Ds -> (* no self reference yet, no recursion *)
      x # G ->
      typing_trm (G & x ~ typ_rcd Ds) (open_trm x t) T ->
      typing_trm G (trm_new ds t) T
with typing_def : ctx -> def -> dec -> Prop :=
  | typing_def_fld : forall G v T,
      typing_trm G (trm_var v) T ->
      typing_def G (def_fld v) (dec_fld T)
  | typing_def_mtd : forall G S T t x,
      x # G ->
      typing_trm (G & x ~ S) (open_trm x t) T ->
      typing_def G (def_mtd S t) (dec_mtd S T)
with typing_defs : ctx -> defs -> decs -> Prop :=
  | typing_defs_nil : forall G,
      typing_defs G defs_nil decs_nil
  | typing_defs_cons : forall G ds d Ds D n,
      typing_defs G ds Ds ->
      typing_def  G d D ->
      typing_defs G (defs_cons n d ds) (decs_cons n D Ds).

Scheme has_mut         := Induction for has         Sort Prop
with   typing_trm_mut  := Induction for typing_trm  Sort Prop
with   typing_def_mut  := Induction for typing_def  Sort Prop
with   typing_defs_mut := Induction for typing_defs Sort Prop.

Combined Scheme typing_mutind from has_mut, typing_trm_mut, typing_def_mut, typing_defs_mut.


(* ###################################################################### *)
(** * Instantiation of tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => dom x     ) in
  let D := gather_vars_with (fun x : sto       => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : def      => fv_def  x) in
  let H := gather_vars_with (fun x : defs     => fv_defs x) in
  let I := gather_vars_with (fun x : def       => fv_def   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).


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

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.

Lemma sto_unbound_to_ctx_unbound: forall s G x,
  wf_sto s G ->
  x # s ->
  x # G.
Proof.
  introv Wf Ub_s.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub_s). 
    - auto.
Qed.

Lemma ctx_unbound_to_sto_unbound: forall s G x,
  wf_sto s G ->
  x # G ->
  x # s.
Proof.
  introv Wf Ub.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub). 
    - auto.
Qed.

Lemma invert_wf_sto: forall s G,
  wf_sto s G -> 
    forall x ds Ds, 
      binds x ds s -> 
      binds x (typ_rcd Ds) G ->
      exists G1 G2, G = G1 & G2 /\ typing_defs G1 ds Ds.
Proof.
  intros s G Wf. induction Wf; intros.
  + false* binds_empty_inv.
  + (*rename H into Hvb, H0 into Htb, H1 into Hisds, H2 into Hvb0, H3 into Htb0.*)
    unfold binds in *. rewrite get_push in *.
    case_if.
    - inversions H2. inversions H3. exists G (x ~ typ_rcd Ds0). auto.
    - specialize (IHWf x0 ds0 Ds0 H2 H3).
      destruct IHWf as [G1 [G2 [Eq Ty]]]. rewrite Eq.
      exists G1 (G2 & x ~ typ_rcd Ds).
      rewrite concat_assoc. auto.
Qed.


(* ###################################################################### *)
(** * Inversion lemmas for typing *)

(** **** Inverting [has] *)

Lemma invert_has: forall G e l d,
  has G e l d ->
  exists Ds, typing_trm G e (typ_rcd Ds) /\ decs_has Ds l d.
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
  exists x Ds, typing_defs G is Ds /\ 
               x # G /\
               typing_trm (G & x ~ typ_rcd Ds) (open_trm x t) T.
Proof. intros. inversions H. eauto. Qed.


(** **** Inverting [typing_def] *)

Lemma typing_def_to_label_for_eq: forall G d D n, 
  typing_def G d D ->
  label_for_def n d = label_for_dec n D.
Proof.
  intros. inversions H; reflexivity.
Qed.

(** **** Inverting [typing_defs] *)

Lemma extract_typing_def_from_typing_defs: forall G l d ds D Ds,
  typing_defs G ds Ds ->
  defs_has ds l d ->
  decs_has Ds l D ->
  typing_def G d D.
Proof.
Admitted.

Lemma invert_typing_mtd_def_inside_typing_defs: forall G ds Ds m S1 S2 T body,
  typing_defs G ds Ds ->
  defs_has ds (label_mtd m) (def_mtd S1 body) ->
  decs_has Ds (label_mtd m) (dec_mtd S2 T) ->
  (* conclusion is the premise needed to construct a typing_mtd_def: *)
  (forall y, y # G -> typing_trm (G & y ~ S2) (open_trm y body) T).
Proof.
Admitted.

Lemma invert_typing_fld_def_inside_typing_defs: forall G ds Ds l v T,
  typing_defs G ds Ds ->
  defs_has ds (label_fld l) (def_fld v) ->
  decs_has Ds (label_fld l) (dec_fld T) ->
  (* conclusion is the premise needed to pushtruct a typing_def_fld: *)
  typing_trm G (trm_var v) T.
Proof.
Admitted.

Lemma get_def_cons : forall l n d ds,
  get_def l (defs_cons n d ds) = If l = (label_for_def n d) then Some d else get_def l ds.
Proof.
  intros. unfold get_def. case_if~.
Qed.

Lemma get_dec_cons : forall l n D Ds,
  get_dec l (decs_cons n D Ds) = If l = (label_for_dec n D) then Some D else get_dec l Ds.
Proof.
  intros. unfold get_dec. case_if~.
Qed.

Lemma decs_has_to_defs_has: forall G l ds Ds D,
  typing_defs G ds Ds ->
  decs_has Ds l D ->
  exists d, defs_has ds l d.
Proof.
  introv Ty Bi. induction Ty; unfolds decs_has, get_dec. 
  + discriminate.
  + unfold defs_has. folds get_dec. rewrite get_def_cons. case_if.
    - exists d. reflexivity.
    - rewrite <- (typing_def_to_label_for_eq n H) in Bi. case_if. apply (IHTy Bi).
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
      destruct (invert_wf_sto H0 Hbv Hbt) as [G1 [G2 [Eq Hty2]]].
      destruct (decs_has_to_defs_has Hty2 Hbd) as [i Hbi].
      destruct (defs_has_fld_sync Hbi) as [y Heq]. subst.
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
        destruct (invert_wf_sto H1 Hbv Hbt) as [G1 [G2 [Eq Hty2]]].
        destruct (decs_has_to_defs_has Hty2 Hbd) as [i Hbi].
        destruct (defs_has_mtd_sync Hbi) as [U' [e Heq]]. subst.
        exists s (open_trm y e).
        apply (red_call y Hbv Hbi).
  (* case typing_trm_new *)
  + left.
    exists (s & x ~ ds) (open_trm x t).
    apply red_new.
    apply (ctx_unbound_to_sto_unbound H1 n).
Qed.

Print Assumptions progress.


(* ###################################################################### *)
(** * Weakening lemmas *)

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
Proof. Admitted. (*
  apply typing_mutind; intros;
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
Qed.*)

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

Lemma invert_wf_sto_with_weakening: forall s G,
  wf_sto s G -> 
    forall x ds Ds, 
      binds x ds s -> 
      binds x (typ_rcd Ds) G ->
      typing_defs G ds Ds.
Proof.
  intros s G Wf. induction Wf; intros.
  + false* binds_empty_inv.
  + unfold binds in *. rewrite get_push in *.
    case_if.
    - inversions H2. inversions H3. apply* weaken_typing_defs.
    - apply* weaken_typing_defs.
Qed.


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

Lemma raw_subst_principles: forall y S,
  (forall (G0 : ctx) (t : trm) (l : label) (d : dec) (Hhas : has G0 t l d),
    (fun G0 e0 l d (Hhas: has G0 e0 l d) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      typing_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      has (G1 & G2) (subst_trm x y t) l d)
    G0 t l d Hhas) /\
  (forall (G0 : ctx) (t : trm) (T : typ) (Hty : typing_trm G0 t T),
    (fun G0 t T (Hty: typing_trm G0 t T) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      typing_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      typing_trm (G1 & G2) (subst_trm x y t) T)
    G0 t T Hty) /\
  (forall (G0 : ctx) (d : def) (D : dec) (Hty : typing_def G0 d D),
    (fun G d D (Htyp: typing_def G d D) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      typing_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      typing_def (G1 & G2) (subst_def x y d) D)
    G0 d D Hty) /\
  (forall (G0 : ctx) (ds : defs) (Ds : decs) (Hty : typing_defs G0 ds Ds),
    (fun G ds Ds (Hty: typing_defs G ds Ds) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      typing_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      typing_defs (G1 & G2) (subst_defs x y ds) Ds)
    G0 ds Ds Hty).
Proof.
  intros y S.
  apply typing_mutind; intros;
  (* renaming: *)
  lazymatch goal with
    (* 2 IHs *)
    | H1: context[forall (_ _ : env typ) (_ : var), _], 
      H2: context[forall (_ _ : env typ) (_ : var), _] |- _ 
      => rename H1 into IH1, H2 into IH2
    (* 1 IH *)
    | H : context[forall (_ _ : env typ) (_ : var), _] |- _ 
      => rename H into IH
    (* no IH *)
    | _ => idtac
  end;
  match goal with
    | H: @eq ctx _ _ |- _ => rename H into EqG
  end;
  match goal with
    | H: ok _ |- _ => rename H into Hok
  end.
  (* case has_dec *)
  + apply* has_dec.
  (* case typing_trm_var *)
  + subst. rename x into z, x0 into x. unfold subst_trm, subst_avar. case_var.
    (* case z = x *)
    - assert (EqST: T = S) by apply (binds_middle_eq_inv b Hok). subst. assumption.
    (* case z <> x *)
    - apply typing_trm_var. apply* binds_remove.
  (* case typing_trm_sel *)
  + apply* typing_trm_sel.
  (* case typing_trm_call *)
  + apply* typing_trm_call.
  (* case typing_trm_new *)
  + apply typing_trm_new with Ds. 
    (* If we had cofinite quantification, we could choose L := (dom G) \u \{ x },
       and after introducing z, we could not only have z # G, but also x <> z *)
    - fold subst_defs. apply* IH1.
    - fold subst_trm. intros z Ub. assert (xUbG: z # G). rewrite EqG.
      assert (z <> x). admit. (* That's why we need cofinite quantification! *) auto.
      rewrite <- concat_assoc.
      destruct (@subst_open_commute x y z) as [C _]. specialize (C t 0).
      unfolds open_trm. unfold subst_fvar in C.
      assert (z <> x). admit. (* Again! *)
      case_var. rewrite <- C.
      specialize (IH2 z xUbG G1 (G2 & z ~ typ_rcd Ds) x).
      subst. apply* IH2; rewrite* concat_assoc.
      apply weaken_typing_trm.
      * assumption.
      * auto. (* again needs x <> z *)
  (* case typing_def_fld *)
  + apply* typing_def_fld.
  (* case typing_def_mtd *)
  + apply typing_def_mtd. 
    fold subst_trm. intros z Ub. assert (xUbG: z # G). rewrite EqG.
    assert (z <> x). admit. (* That's why we need cofinite quantification! *) auto.
    rewrite <- concat_assoc.
    destruct (@subst_open_commute x y z) as [C _]. specialize (C t 0).
    unfolds open_trm. unfold subst_fvar in C.
    assert (z <> x). admit. (* Again! *)
    case_var. rewrite <- C.
    specialize (IH z xUbG G1 (G2 & z ~ S0) x).
    subst. apply* IH; rewrite* concat_assoc.
    apply weaken_typing_trm.
    * assumption.
    * auto. (* again needs x <> z *)
  (* case typing_defs_nil *)
  + apply typing_defs_nil.
  (* case typing_defs_cons *)
  + apply* typing_defs_cons.
Qed.

Print Assumptions raw_subst_principles.

Lemma subst_principle: forall G x y t S T,
  ok (G & x ~ S) ->
  typing_trm (G & x ~ S) t T ->
  typing_trm G (trm_var (avar_f y)) S ->
  typing_trm G (subst_trm x y t) T.
Proof.
  introv Hok tTy yTy. destruct (raw_subst_principles y S) as [_ [P _]].
  specialize (P _ t T tTy G empty x).
  repeat (progress (rewrite concat_empty_r in P)).
  apply* P.
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
    exists (@empty typ). rewrite concat_empty_r. split. apply Hwf.
    (* Grab "ctx binds x" hypothesis: *)
    apply invert_typing_trm_call in Hty. 
    destruct Hty as [T' [Hhas Htyy]].
    apply invert_has in Hhas. 
    destruct Hhas as [Ds [Htyx Hdbm]].
    apply invert_typing_trm_var in Htyx. rename Htyx into Htbx.
    (* Feed "binds x" and "ctx binds x" to invert_wf_sto: *)
    lets HdsDs: (invert_wf_sto Hwf Hvbx Htbx).
    lets Hmtd: (invert_typing_mtd_def_inside_typing_defs HdsDs Hibm Hdbm).
    pick_fresh y'.
    rewrite* (@subst_intro_trm y' y body).
    apply* (@subst_principle G y' y ((open_trm y' body)) T' U).
  (* red_sel *)
  + rename H into Hvbx. rename H0 into Hibl.
    exists (@empty typ). rewrite concat_empty_r. split. apply Hwf.
    apply invert_typing_trm_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [Ds [Htyx Hdbl]].
    apply invert_typing_trm_var in Htyx. rename Htyx into Htbx.
    (* Feed "binds x" and "ctx binds x" to invert_wf_sto: *)
    lets HdsDs: (invert_wf_sto Hwf Hvbx Htbx).
    apply (invert_typing_fld_def_inside_typing_defs HdsDs Hibl Hdbl).
  (* red_new *)
  + rename H into Hvux.
    apply invert_typing_trm_new in Hty.
    destruct Hty as [Ds [Hisds Htye]].
    lets Htux: (sto_unbound_to_ctx_unbound Hwf Hvux).
    exists (x ~ typ_rcd Ds). split.
    - apply (wf_sto_push Hwf Hvux Htux Hisds).
    - apply (Htye x Htux).
  (* red_call1 *)
  + rename T into Tr.
    apply invert_typing_trm_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    apply invert_has in Hhas.
    destruct Hhas as [Ds [Htyo Hdbm]].
    specialize (IHHred G (typ_rcd Ds) Hwf Htyo).
    destruct IHHred as [H [Hwf' Htyo']].
    exists H. split. assumption. apply (@typing_trm_call (G & H) o' m Ta Tr a).
    - apply (has_dec Htyo' Hdbm).
    - lets Hok: wf_sto_to_ok_G Hwf'.
      apply (weaken_typing_trm Htya Hok).
  (* red_call2 *)
  + rename T into Tr.
    apply invert_typing_trm_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    specialize (IHHred G Ta Hwf Htya).
    destruct IHHred as [H [Hwf' Htya']].
    exists H. split. assumption. apply (@typing_trm_call (G & H) _ m Ta Tr a').
    - lets Hok: wf_sto_to_ok_G Hwf'.
      apply (weaken_has Hhas Hok).
    - assumption.
  (* red_sel1 *)
  + apply invert_typing_trm_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [Ds [Htyo Hdbl]].
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
