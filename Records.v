
Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.


(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

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
  | trm_new  : defs -> trm
  | trm_sel  : trm -> nat -> trm
  | trm_call : trm -> nat -> trm -> trm
with def : Type :=
  | def_fld : avar -> def (* cannot have term here, need to assign first *)
  | def_mtd : typ -> trm -> def
with defs : Type :=
  | defs_nil : defs
  | defs_cons : nat -> def -> defs -> defs.


(** *** Syntactic sugar *)
Definition trm_fun(T: typ)(body: trm) := trm_new (defs_cons 0 (def_mtd T body) defs_nil).
Definition trm_app(func arg: trm) := trm_call func 0 arg.
Definition trm_let(T: typ)(rhs body: trm) := trm_app (trm_fun T body) rhs.
Definition trm_upcast(T: typ)(e: trm) := trm_app (trm_fun T (trm_var (avar_b 0))) e.
Definition typ_arrow(T1 T2: typ) := typ_rcd (decs_cons 0 (dec_mtd T1 T2) decs_nil).


(* ###################################################################### *)
(** ** Declaration and definition lists *)

Definition label_for_def(n: nat)(d: def): label := match d with
| def_fld _ => label_fld n
| def_mtd _ _ => label_mtd n
end.
Definition label_for_dec(n: nat)(D: dec): label := match D with
| dec_fld _ => label_fld n
| dec_mtd _ _ => label_mtd n
end.

Fixpoint get_def(l: label)(ds: defs): option def := match ds with
| defs_nil => None
| defs_cons n d ds' => If l = label_for_def n d then Some d else get_def l ds'
end.
Fixpoint get_dec(l: label)(Ds: decs): option dec := match Ds with
| decs_nil => None
| decs_cons n D Ds' => If l = label_for_dec n D then Some D else get_dec l Ds'
end.

Definition defs_has(ds: defs)(l: label)(d: def): Prop := (get_def l ds = Some d).
Definition decs_has(Ds: decs)(l: label)(D: dec): Prop := (get_dec l Ds = Some D).

Definition defs_hasnt(ds: defs)(l: label): Prop := (get_def l ds = None).
Definition decs_hasnt(Ds: decs)(l: label): Prop := (get_dec l Ds = None).


(* ###################################################################### *)
(** ** Opening *)

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
  | trm_new ds => trm_new (open_rec_defs (S k) u ds)
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
(** ** Free variables *)

Fixpoint fv_avar (a: avar) { struct a } : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

(* Since we define defs ourselves instead of using [list def], we don't have any
   termination proof problems: *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var x => fv_avar x
  | trm_new ds => (fv_defs ds)
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
(** ** Environments *)

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env defs.


(* ###################################################################### *)
(** ** Operational Semantics *)

(** Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
    Whenever we introduce a new avar_f (only happens in red_new), we choose one
    which is not in the store, so we never have name clashes. *) 
Inductive red : trm -> sto -> trm -> sto -> Prop :=
  (* computation rules *)
  | red_call : forall s x y m T ds body,
      binds x ds s ->
      defs_has ds (label_mtd m) (def_mtd T body) ->
      red (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) s
          (open_trm y body) s
  | red_sel : forall s x y l ds,
      binds x ds s ->
      defs_has ds (label_fld l) (def_fld y) ->
      red (trm_sel (trm_var (avar_f x)) l) s
          (trm_var y) s
  | red_new : forall s ds x,
      x # s ->
      red (trm_new ds) s
          (trm_var (avar_f x)) (s & x ~ (open_defs x ds))
  (* congruence rules *)
  | red_call1 : forall s o m a s' o',
      red o s o' s' ->
      red (trm_call o  m a) s
          (trm_call o' m a) s'
  | red_call2 : forall s x m a s' a',
      red a s a' s' ->
      red (trm_call (trm_var (avar_f x)) m a ) s
          (trm_call (trm_var (avar_f x)) m a') s'
  | red_sel1 : forall s o l s' o',
      red o s o' s' ->
      red (trm_sel o  l) s
          (trm_sel o' l) s'.


(* ###################################################################### *)
(** ** Specification of declaration intersection (not yet used) *)

Module Type Decs.

(* Will be part of syntax: *)
Parameter t_and: typ -> typ -> typ.
Parameter t_or:  typ -> typ -> typ.

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

Axiom intersect_spec_hasnt: forall l Ds1 Ds2,
  decs_hasnt Ds1 l ->
  decs_hasnt Ds2 l ->
  decs_hasnt (intersect Ds1 Ds2) l.

End Decs.


(* ###################################################################### *)
(** ** Typing *)

(* The store is not an argument of the typing judgment because
   * it's only needed in typing_trm_var_s
   * we must allow types in Gamma to depend on values in the store, which seems complicated
   * how can we ensure that the store is well-formed? By requiring it in the "leaf"
     typing rules (those without typing assumptions)? Typing rules become unintuitive,
     and maybe to prove that store is wf, we need to prove what we're about to prove...
*)

(* Term typing *)
Inductive has : ctx -> trm -> label -> dec -> Prop :=
  | has_trm : forall G e l D Ds,
      ty_trm G e (typ_rcd Ds) ->
      decs_has Ds l D ->
      has G e l D
with ty_trm : ctx -> trm -> typ -> Prop :=
  | ty_var : forall G x T,
      binds x T G ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_sel : forall G e l T,
      has G e (label_fld l) (dec_fld T) ->
      ty_trm G (trm_sel e l) T
  | ty_call : forall G t m U V u,
      has G t (label_mtd m) (dec_mtd U V) ->
      ty_trm G u U ->
      ty_trm G (trm_call t m u) V
  | ty_new : forall L G ds Ds,
      (forall x, x \notin L -> ty_defs (G & x ~ typ_rcd Ds) (open_defs x ds) Ds) ->
      ty_trm G (trm_new ds) (typ_rcd Ds)
with ty_def : ctx -> def -> dec -> Prop :=
  | ty_fld : forall G v T,
      ty_trm G (trm_var v) T ->
      ty_def G (def_fld v) (dec_fld T)
  | ty_mtd : forall L G S T t,
      (forall x, x \notin L -> ty_trm (G & x ~ S) (open_trm x t) T) ->
      ty_def G (def_mtd S t) (dec_mtd S T)
with ty_defs : ctx -> defs -> decs -> Prop :=
  | ty_dsnil : forall G,
      ty_defs G defs_nil decs_nil
  | ty_dscons : forall G ds d Ds D n,
      ty_defs G ds Ds ->
      ty_def  G d D ->
      ty_defs G (defs_cons n d ds) (decs_cons n D Ds).

(** *** Well-formed store *)
Inductive wf_sto: sto -> ctx -> Prop :=
  | wf_sto_empty : wf_sto empty empty
  | wf_sto_push : forall s G x ds Ds,
      wf_sto s G ->
      x # s ->
      x # G ->
      ty_defs (G & x ~ (typ_rcd Ds)) ds Ds ->
      wf_sto (s & x ~ ds) (G & x ~ (typ_rcd Ds)).


(* ###################################################################### *)
(** ** Statements we want to prove *)

Definition progress := forall s G e T,
  wf_sto s G ->
  ty_trm G e T -> 
  (
    (* can step *)
    (exists e' s', red e s e' s') \/
    (* or is a value *)
    (exists x ds, e = (trm_var (avar_f x)) /\ binds x ds s)
  ).

Definition preservation := forall s G e T e' s',
  wf_sto s G -> ty_trm G e T -> red e s e' s' ->
  (exists G', wf_sto s' G' /\ ty_trm G' e' T).


(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme trm_mut  := Induction for trm  Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, def_mut, defs_mut.

Scheme has_mut     := Induction for has     Sort Prop
with   ty_trm_mut  := Induction for ty_trm  Sort Prop
with   ty_def_mut  := Induction for ty_def  Sort Prop
with   ty_defs_mut := Induction for ty_defs Sort Prop.

Combined Scheme ty_mutind from has_mut, ty_trm_mut, ty_def_mut, ty_defs_mut.


(* ###################################################################### *)
(** ** Tactics *)

Ltac auto_specialize :=
  repeat match goal with
  | Impl: ?Cond ->            _ |- _ => let HC := fresh in 
      assert (HC: Cond) by auto; specialize (Impl HC); clear HC
  | Impl: forall (_ : ?Cond), _ |- _ => match goal with
      | p: Cond |- _ => specialize (Impl p)
      end
  end.

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

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.


(* ###################################################################### *)
(** ** Definition of var-by-var substitution *)

(** Note that substitution is not part of the definitions, because for the
    definitions, opening is sufficient. For the proofs, however, we also
    need substitution, but only var-by-var substitution, not var-by-term
    substitution. That's why we don't need a judgment asserting that a term
    is locally closed. *)

Fixpoint subst_avar (z: var) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = z then (avar_f u) else (avar_f x)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x => trm_var (subst_avar z u x)
  | trm_new ds => trm_new (subst_defs z u ds)
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


(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

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

Lemma subst_open_commute_trm: forall x y u t,
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros.
  destruct (@subst_open_commute x y u) as [P _]. specialize (P t 0).
  unfold open_trm. assumption.
Qed.

Lemma subst_open_commute_defs: forall x y u ds,
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros.
  destruct (@subst_open_commute x y u) as [_ [_ P]]. specialize (P ds 0).
  unfold open_def. assumption.
Qed.

Lemma subst_id_avar: forall x,
  (forall a : avar, subst_avar x x a  = a).
Proof.
  intros. unfold subst_avar. destruct* a. case_var*.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_defs.
  destruct (@subst_fresh x u) as [_ [_ Q]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.


(* ###################################################################### *)
(** ** Helper lemmas for definition/declaration lists *)

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

Lemma decs_has_fld_sync: forall n d ds,
  decs_has ds (label_fld n) d -> exists x, d = (dec_fld x).
Proof.
  introv Hhas. induction ds; unfolds decs_has, get_dec. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_dec in H. destruct* d. discriminate.
    - apply* IHds.
Qed.

Lemma decs_has_mtd_sync: forall n d ds,
  decs_has ds (label_mtd n) d -> exists T e, d = (dec_mtd T e).
Proof.
  introv Hhas. induction ds; unfolds decs_has, get_dec. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_dec in H. destruct* d. discriminate.
    - apply* IHds.
Qed.


(* ###################################################################### *)
(** ** Implementation of declaration intersection *)

(* Exercise: Give any implementation of `intersect`, and prove that it satisfies
   the specification. Happy hacking! ;-) *)
Module DecsImpl : Decs.

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
  refine_dec n (dec_fld T1) Ds2 = dec_fld (t_and T1 T2).
Proof.
  intro Ds2. induction Ds2; intros.
  + inversion H.
  + unfold decs_has, get_dec in H. case_if; fold get_dec in H.
    - inversions H. unfold label_for_dec in H0. inversions H0. simpl. case_if. reflexivity.
    - simpl. destruct d.
      * simpl in H0. case_if.
        apply IHDs2. unfold decs_has. assumption.
      * apply IHDs2. unfold decs_has. assumption.
Qed.

Lemma refine_dec_spec_mtd: forall Ds2 n T1 S1 T2 S2,
  decs_has Ds2 (label_mtd n) (dec_mtd T2 S2) ->
  refine_dec n (dec_mtd T1 S1) Ds2 = dec_mtd (t_or T1 T2) (t_and S1 S2).
Proof. 
  intro Ds2. induction Ds2; intros.
  + inversion H.
  + unfold decs_has, get_dec in H. case_if; fold get_dec in H.
    - inversions H. unfold label_for_dec in H0. inversions H0. simpl. case_if. reflexivity.
    - simpl. destruct d.
      * apply IHDs2. unfold decs_has. assumption.
      * simpl in H0. case_if.
        apply IHDs2. unfold decs_has. assumption.
Qed.

Lemma refine_dec_spec_unbound: forall n D1 Ds2, 
  decs_hasnt Ds2 (label_for_dec n D1) ->
  refine_dec n D1 Ds2 = D1.
Proof. 
  intros. induction Ds2.
  + reflexivity.
  + unfold decs_hasnt, get_dec in H. fold get_dec in H. case_if. destruct D1.
    - destruct d; simpl in H0; unfold refine_dec.
      * case_if. fold refine_dec. apply IHDs2. assumption.
      * destruct Ds2. reflexivity. unfold refine_dec in IHDs2. apply IHDs2. assumption.
    - destruct d; simpl in H0; unfold refine_dec.
      * fold refine_dec. apply IHDs2. assumption.
      * case_if. fold refine_dec. apply IHDs2. assumption.
Qed.

Lemma refine_dec_preserves_label: forall n D1 Ds2,
  label_for_dec n (refine_dec n D1 Ds2) = label_for_dec n D1.
Proof.
  intros. induction Ds2.
  + reflexivity.
  + destruct D1; destruct d; unfold refine_dec in *; fold refine_dec in *.
    - case_if. reflexivity. assumption.
    - assumption.
    - assumption.
    - case_if. reflexivity. assumption.
Qed.

Fixpoint refine_decs(Ds1: decs)(Ds2: decs): decs := match Ds1 with
| decs_nil => decs_nil
| decs_cons n D1 Ds1tail => decs_cons n (refine_dec n D1 Ds2) (refine_decs Ds1tail Ds2)
end.

Lemma refine_decs_spec_unbound: forall l D Ds1 Ds2,
  decs_has    Ds1                  l D ->
  decs_hasnt  Ds2                  l   ->
  decs_has   (refine_decs Ds1 Ds2) l D .
Proof.
  intros l D Ds1 Ds2. induction Ds1; introv Has Hasnt.
  + inversion Has.
  + unfold refine_decs; fold refine_decs. rename d into D'. unfold decs_has, get_dec.
    rewrite refine_dec_preserves_label. case_if.
    - unfold decs_has, get_dec in Has. case_if.
      inversions Has. f_equal. apply refine_dec_spec_unbound. assumption.
    - fold get_dec. unfold decs_has in *. unfold get_dec in Has. case_if.
      fold get_dec in Has. apply* IHDs1. 
Qed.

Lemma refine_decs_spec_unbound_preserved: forall l Ds1 Ds2,
  decs_hasnt Ds1                   l ->
  decs_hasnt (refine_decs Ds1 Ds2) l .
Proof. 
  introv Hasnt. induction Ds1.
  + simpl. assumption.
  + unfold refine_decs; fold refine_decs. rename d into D'. unfold decs_hasnt, get_dec.
    rewrite refine_dec_preserves_label. case_if.
    - unfold decs_hasnt, get_dec in Hasnt. case_if. (* contradiction *)
    - fold get_dec. unfold decs_has in *. apply IHDs1.
      unfold decs_hasnt, get_dec in Hasnt. case_if. fold get_dec in Hasnt. apply Hasnt.
Qed.

Lemma refine_decs_spec_fld: forall n Ds1 Ds2 T1 T2,
  decs_has  Ds1                  (label_fld n) (dec_fld T1) ->
  decs_has  Ds2                  (label_fld n) (dec_fld T2) ->
  decs_has (refine_decs Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).
Proof. 
  introv Has1 Has2. induction Ds1.
  + inversion Has1.
  + unfold decs_has, get_dec in Has1. case_if.
    - inversions Has1. simpl in H. inversions H. simpl. 
      rewrite (refine_dec_spec_fld _ Has2). unfold decs_has, get_dec. simpl.
      case_if. reflexivity.
    - fold get_dec in Has1. simpl. unfold decs_has, get_dec.
      rewrite refine_dec_preserves_label. case_if. fold get_dec.
      unfold decs_has in IHDs1. apply IHDs1. assumption.
Qed.

Lemma refine_decs_spec_mtd: forall n Ds1 Ds2 T1 S1 T2 S2,
  decs_has  Ds1                  (label_mtd n) (dec_mtd T1 S1) ->
  decs_has  Ds2                  (label_mtd n) (dec_mtd T2 S2) ->
  decs_has (refine_decs Ds1 Ds2) (label_mtd n) (dec_mtd (t_or T1 T2) (t_and S1 S2)).
Proof.
  introv Has1 Has2. induction Ds1.
  + inversion Has1.
  + unfold decs_has, get_dec in Has1. case_if.
    - inversions Has1. simpl in H. inversions H. simpl. 
      rewrite (refine_dec_spec_mtd _ _ Has2). unfold decs_has, get_dec. simpl.
      case_if. reflexivity.
    - fold get_dec in Has1. simpl. unfold decs_has, get_dec.
      rewrite refine_dec_preserves_label. case_if. fold get_dec.
      unfold decs_has in IHDs1. apply IHDs1. assumption.
Qed.

Fixpoint decs_concat(Ds1 Ds2: decs) {struct Ds1}: decs := match Ds1 with
| decs_nil => Ds2
| decs_cons n D1 Ds1tail => decs_cons n D1 (decs_concat Ds1tail Ds2)
end.

(* Refined decs shadow the outdated decs of Ds2. *)
Definition intersect(Ds1 Ds2: decs): decs := decs_concat (refine_decs Ds1 Ds2) Ds2.

Lemma decs_has_concat_left : forall l D Ds1 Ds2,
  decs_has Ds1 l D ->
  decs_has (decs_concat Ds1 Ds2) l D.
Proof.
  introv Has. induction Ds1.
  + inversion Has.
  + simpl. unfold decs_has, get_dec in *. fold get_dec in *. case_if.
    - assumption.
    - apply IHDs1. assumption.
Qed. 

Lemma decs_has_concat_right : forall l D Ds1 Ds2,
  decs_hasnt Ds1 l ->
  decs_has Ds2 l D ->
  decs_has (decs_concat Ds1 Ds2) l D.
Proof.
  introv Hasnt Has. induction Ds1.
  + simpl. assumption.
  + simpl. unfold decs_has, get_dec. case_if.
    - unfold decs_hasnt, get_dec in Hasnt. case_if. (* contradiction *)
    - fold get_dec. apply IHDs1. unfold decs_hasnt, get_dec in Hasnt. case_if.
      apply Hasnt.
Qed.

Lemma decs_hasnt_concat : forall l Ds1 Ds2,
  decs_hasnt Ds1 l ->
  decs_hasnt Ds2 l ->
  decs_hasnt (decs_concat Ds1 Ds2) l.
Proof.
  introv Hasnt1 Hasnt2. induction Ds1.
  + simpl. assumption.
  + simpl. unfold decs_hasnt, get_dec. case_if.
    - unfold decs_hasnt, get_dec in Hasnt1. case_if. (* contradiction *)
    - fold get_dec. apply IHDs1. unfold decs_hasnt, get_dec in Hasnt1. case_if.
      apply Hasnt1.
Qed.

Lemma intersect_spec_1: forall l D Ds1 Ds2,
  decs_has    Ds1                l D ->
  decs_hasnt  Ds2                l   ->
  decs_has   (intersect Ds1 Ds2) l D .
Proof.
  intros. unfold intersect. apply decs_has_concat_left.
  apply refine_decs_spec_unbound; assumption.
Qed.

Lemma intersect_spec_2: forall l D Ds1 Ds2,
  decs_hasnt Ds1                 l   ->
  decs_has   Ds2                 l D ->
  decs_has   (intersect Ds1 Ds2) l D.
Proof.
  introv Hasnt Has. unfold intersect.
  apply (@decs_has_concat_right l D (refine_decs Ds1 Ds2) Ds2).
  apply (@refine_decs_spec_unbound_preserved l Ds1 Ds2 Hasnt).
  assumption. 
Qed.

Lemma intersect_spec_12_fld: forall n T1 T2 Ds1 Ds2,
  decs_has Ds1                 (label_fld n) (dec_fld T1) ->
  decs_has Ds2                 (label_fld n) (dec_fld T2) ->
  decs_has (intersect Ds1 Ds2) (label_fld n) (dec_fld (t_and T1 T2)).
Proof.
  intros. unfold intersect. apply decs_has_concat_left.
  apply refine_decs_spec_fld; assumption.
Qed.

Lemma intersect_spec_12_mtd: forall n S1 T1 S2 T2 Ds1 Ds2,
  decs_has Ds1                 (label_mtd n) (dec_mtd S1 T1) ->
  decs_has Ds2                 (label_mtd n) (dec_mtd S2 T2) ->
  decs_has (intersect Ds1 Ds2) (label_mtd n) (dec_mtd (t_or S1 S2) (t_and T1 T2)).
Proof.
  intros. unfold intersect. apply decs_has_concat_left.
  apply refine_decs_spec_mtd; assumption.
Qed.

Lemma intersect_spec_hasnt: forall l Ds1 Ds2,
  decs_hasnt Ds1 l ->
  decs_hasnt Ds2 l ->
  decs_hasnt (intersect Ds1 Ds2) l.
Proof.
  introv Hasnt1 Hasnt2. unfold intersect. apply decs_hasnt_concat.
  + apply (refine_decs_spec_unbound_preserved _ Hasnt1).
  + apply Hasnt2.
Qed.

End DecsImpl.


(* ###################################################################### *)
(** ** Inversion lemmas *)

(** *** Inversion lemmas for [wf_sto] *)

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
      exists G1 G2, G = G1 & x ~ (typ_rcd Ds) & G2 /\ 
                    ty_defs (G1 & x ~ (typ_rcd Ds)) ds Ds.
Proof.
  intros s G Wf. induction Wf; intros.
  + false* binds_empty_inv.
  + unfold binds in *. rewrite get_push in *.
    case_if.
    - inversions H2. inversions H3. exists G (@empty typ). rewrite concat_empty_r. auto.
    - specialize (IHWf x0 ds0 Ds0 H2 H3).
      destruct IHWf as [G1 [G2 [Eq Ty]]]. rewrite Eq.
      exists G1 (G2 & x ~ typ_rcd Ds).
      rewrite concat_assoc. auto.
Qed.


(** *** Inverting [has] *)

Lemma invert_has: forall G e l d,
  has G e l d ->
  exists Ds, ty_trm G e (typ_rcd Ds) /\ decs_has Ds l d.
Proof. intros. inversions H. eauto. Qed.


(** *** Inverting [ty_trm] *)

Lemma invert_ty_var: forall G x T,
  ty_trm G (trm_var (avar_f x)) T ->
  binds x T G.
Proof. intros. inversions H. assumption. Qed.

Lemma invert_ty_sel: forall G e l T,
  ty_trm G (trm_sel e l) T ->
  has G e (label_fld l) (dec_fld T).
Proof. intros. inversions H. assumption. Qed.

Lemma invert_ty_call: forall G t m V u,
  ty_trm G (trm_call t m u) V ->
  exists U, has G t (label_mtd m) (dec_mtd U V) /\ ty_trm G u U.
Proof. intros. inversions H. eauto. Qed.

Lemma invert_ty_new: forall G ds T,
  ty_trm G (trm_new ds) T ->
  exists L Ds, T = typ_rcd Ds /\
               (forall x, x \notin L -> 
                          ty_defs (G & x ~ typ_rcd Ds) (open_defs x ds) Ds).
Proof. intros. destruct T as [Ds]. inversions H. eauto. Qed.


(** *** Inverting [ty_def] *)

Lemma ty_def_to_label_for_eq: forall G d D n, 
  ty_def G d D ->
  label_for_def n d = label_for_dec n D.
Proof.
  intros. inversions H; reflexivity.
Qed.

(** *** Inverting [ty_defs] *)

Lemma extract_ty_def_from_ty_defs: forall G l d ds D Ds,
  ty_defs G ds Ds ->
  defs_has ds l d ->
  decs_has Ds l D ->
  ty_def G d D.
Proof.
  introv HdsDs. induction HdsDs.
  + intros. inversion H.
  + introv dsHas DsHas. unfolds defs_has, decs_has, get_def, get_dec. 
    rewrite (ty_def_to_label_for_eq n H) in dsHas. case_if.
    - inversions dsHas. inversions DsHas. assumption.
    - apply* IHHdsDs.
Qed.

Lemma invert_ty_mtd_inside_ty_defs: forall G ds Ds m S1 S2 T body,
  ty_defs G ds Ds ->
  defs_has ds (label_mtd m) (def_mtd S1 body) ->
  decs_has Ds (label_mtd m) (dec_mtd S2 T) ->
  (* conclusion is the premise needed to construct a ty_mtd: *)
  exists L, forall x, x \notin L -> ty_trm (G & x ~ S2) (open_trm x body) T.
Proof.
  introv HdsDs dsHas DsHas.
  lets H: (extract_ty_def_from_ty_defs HdsDs dsHas DsHas).
  inversions* H. 
Qed.

Lemma invert_ty_fld_inside_ty_defs: forall G ds Ds l v T,
  ty_defs G ds Ds ->
  defs_has ds (label_fld l) (def_fld v) ->
  decs_has Ds (label_fld l) (dec_fld T) ->
  (* conclusion is the premise needed to construct a ty_fld: *)
  ty_trm G (trm_var v) T.
Proof.
  introv HdsDs dsHas DsHas.
  lets H: (extract_ty_def_from_ty_defs HdsDs dsHas DsHas).
  inversions* H. 
Qed.

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
  ty_defs G ds Ds ->
  decs_has Ds l D ->
  exists d, defs_has ds l d.
Proof.
  introv Ty Bi. induction Ty; unfolds decs_has, get_dec. 
  + discriminate.
  + unfold defs_has. folds get_dec. rewrite get_def_cons. case_if.
    - exists d. reflexivity.
    - rewrite <- (ty_def_to_label_for_eq n H) in Bi. case_if. apply (IHTy Bi).
Qed.


(* ###################################################################### *)
(* ###################################################################### *)
(** * Soundness Proofs *)

(* ###################################################################### *)
(** ** Progress *)

Theorem progress_result: progress.
Proof.
  introv Wf Ty. gen G e T Ty s Wf.
  set (progress_for := fun s e =>
                         (exists e' s', red e s e' s') \/
                         (exists x ds, e = (trm_var (avar_f x)) /\ binds x ds s)).
  apply (ty_trm_mut
    (fun G e l d (Hhas: has G e l d)         => forall s, wf_sto s G -> progress_for s e)
    (fun G e T   (Hty: ty_trm G e T)     => forall s, wf_sto s G -> progress_for s e)
    (fun G i d   (Htyp: ty_def G i d)    => True)
    (fun G is Ds (Htyp: ty_defs G is Ds) => True));
  unfold progress_for; clear progress_for; intros; try apply I; auto_specialize.
  (* case has_trm *)
  + assumption. 
  (* case ty_var *)
  + right. destruct (ctx_binds_to_sto_binds H b) as [is Hbv].
    exists x is. auto.
  (* case ty_sel *)
  + left. destruct H as [IH | IH].
    (* receiver is an expression *)
    - destruct IH as [s' [e' IH]]. do 2 eexists. apply (red_sel1 l IH). 
    (* receiver is a var *)
    - destruct IH as [x [is [Heq Hbv]]]. subst.
      destruct (invert_has h) as [ds [Hty Hbd]].
      lets Hbt: (invert_ty_var Hty).
      destruct (invert_wf_sto H0 Hbv Hbt) as [G1 [G2 [Eq Hty2]]].
      destruct (decs_has_to_defs_has Hty2 Hbd) as [i Hbi].
      destruct (defs_has_fld_sync Hbi) as [y Heq]. subst.
      exists (trm_var y) s.
      apply (red_sel Hbv Hbi).
  (* case ty_call *)
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
        lets Hbt: (invert_ty_var Hty).
        destruct (invert_wf_sto H1 Hbv Hbt) as [G1 [G2 [Eq Hty2]]].
        destruct (decs_has_to_defs_has Hty2 Hbd) as [i Hbi].
        destruct (defs_has_mtd_sync Hbi) as [U' [e Heq]]. subst.
        exists (open_trm y e) s.
        apply (red_call y Hbv Hbi).
  (* case ty_new *)
  + left. pick_fresh x.
    exists (trm_var (avar_f x)) (s & x ~ (open_defs x ds)).
    apply* red_new.
Qed.

Print Assumptions progress_result.


(* ###################################################################### *)
(** ** Weakening lemmas *)

(* If we only weaken at the end, i.e. from [G1] to [G1 & G2], the IH for the 
   [ty_new] case adds G2 to the end, so it takes us from [G1, x: Ds] 
   to [G1, x: Ds, G2], but we need [G1, G2, x: Ds].
   So we need to weaken in the middle, i.e. from [G1 & G3] to [G1 & G2 & G3].
   Then, the IH for the [ty_new] case inserts G2 in the middle, so it
   takes us from [G1 & G3, x: Ds] to [G1 & G2 & G3, x: Ds], which is what we
   need. *)

Lemma weakening:
   (forall G e l d (Hhas: has G e l d)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)),
           has (G1 & G2 & G3) e l d ) 
/\ (forall G e T (Hty: ty_trm G e T)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)),
           ty_trm (G1 & G2 & G3) e T) 
/\ (forall G i d (Hty: ty_def G i d)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)), 
           ty_def (G1 & G2 & G3) i d)
/\ (forall G is Ds (Hisds: ty_defs G is Ds)
           G1 G2 G3 (Heq: G = G1 & G3) (Hok123: ok (G1 & G2 & G3)), 
           ty_defs (G1 & G2 & G3) is Ds).
Proof.
  apply ty_mutind; intros; subst.
  + apply* has_trm.
  + apply ty_var. apply* binds_weaken.
  + apply* ty_sel.
  + apply* ty_call.
  + apply_fresh ty_new as x.
    rewrite <- concat_assoc.
    refine (H x _ G1 G2 (G3 & x ~ typ_rcd Ds) _ _).
    - auto.
    - rewrite concat_assoc. reflexivity.
    - rewrite concat_assoc. auto.
  + apply* ty_fld.
  + rename H into IH.
    apply_fresh ty_mtd as x.
    rewrite <- concat_assoc.
    refine (IH x _ G1 G2 (G3 & x ~ S) _ _).
    - auto.
    - symmetry. apply concat_assoc.
    - rewrite concat_assoc. auto.
  + apply ty_dsnil.
  + apply* ty_dscons.
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

Lemma weaken_ty_trm: forall G1 G2 e T,
  ty_trm G1 e T -> ok (G1 & G2) -> ty_trm (G1 & G2) e T.
Proof.
  intros.
  destruct weakening as [_ [W _]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_def: forall G1 G2 i d,
  ty_def G1 i d -> ok (G1 & G2) -> ty_def (G1 & G2) i d.
Proof.
  intros.
  destruct weakening as [_ [_ [W _]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_defs: forall G1 G2 is Ds,
  ty_defs G1 is Ds -> ok (G1 & G2) -> ty_defs (G1 & G2) is Ds.
Proof.
  intros.
  destruct weakening as [_ [_ [_ W]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.


(* ###################################################################### *)
(** ** Inversion lemmas which depend on weakening *)

Lemma invert_wf_sto_with_weakening: forall s G,
  wf_sto s G -> 
    forall x ds Ds, 
      binds x ds s -> 
      binds x (typ_rcd Ds) G ->
      ty_defs G ds Ds.
Proof.
  introv Wf Bs BG.
  lets P: (invert_wf_sto Wf).
  specialize (P x ds Ds Bs BG).
  destruct P as [G1 [G2 [Eq Ty]]]. subst.
  apply* weaken_ty_defs.
Qed.


(* ###################################################################### *)
(** ** The substitution principle *)


(*

                  G, x: S |- e : T      G |- u : S
                 ----------------------------------
                            G |- [u/x]e : T

Note that in general, u is a term, but for our purposes, it suffices to consider
the special case where u is a variable.
*)

Lemma raw_subst_principles: forall y S,
  (forall (G0 : ctx) (t : trm) (l : label) (d : dec) (Hhas : has G0 t l d),
    (fun G0 e0 l d (Hhas: has G0 e0 l d) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      ty_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      has (G1 & G2) (subst_trm x y t) l d)
    G0 t l d Hhas) /\
  (forall (G0 : ctx) (t : trm) (T : typ) (Hty : ty_trm G0 t T),
    (fun G0 t T (Hty: ty_trm G0 t T) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      ty_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      ty_trm (G1 & G2) (subst_trm x y t) T)
    G0 t T Hty) /\
  (forall (G0 : ctx) (d : def) (D : dec) (Hty : ty_def G0 d D),
    (fun G d D (Htyp: ty_def G d D) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      ty_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      ty_def (G1 & G2) (subst_def x y d) D)
    G0 d D Hty) /\
  (forall (G0 : ctx) (ds : defs) (Ds : decs) (Hty : ty_defs G0 ds Ds),
    (fun G ds Ds (Hty: ty_defs G ds Ds) => 
      forall G1 G2 x, G0 = (G1 & (x ~ S) & G2) ->
                      ty_trm (G1 & G2) (trm_var (avar_f y)) S ->
                      ok (G1 & (x ~ S) & G2) ->
                      ty_defs (G1 & G2) (subst_defs x y ds) Ds)
    G0 ds Ds Hty).
Proof.
  intros y S.
  apply ty_mutind; intros;
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
  (* case has_trm *)
  + apply* has_trm.
  (* case ty_var *)
  + subst. rename x into z, x0 into x. unfold subst_trm, subst_avar. case_var.
    (* case z = x *)
    - assert (EqST: T = S) by apply (binds_middle_eq_inv b Hok). subst. assumption.
    (* case z <> x *)
    - apply ty_var. apply* binds_remove.
  (* case ty_sel *)
  + apply* ty_sel.
  (* case ty_call *)
  + apply* ty_call.
  (* case ty_new *)
  + apply_fresh ty_new as z.
    fold subst_defs.
    lets C: (@subst_open_commute_defs x y z ds).
    unfolds open_defs. unfold subst_fvar in C. case_var.
    rewrite <- C.
    rewrite <- concat_assoc.
    subst G.
    assert (zL: z \notin L) by auto.
    refine (IH z zL G1 (G2 & z ~ typ_rcd Ds) x _ _ _); rewrite concat_assoc.
    - reflexivity.
    - apply* weaken_ty_trm.
    - auto.
  (* case ty_fld *)
  + apply* ty_fld.
  (* case ty_mtd *)
  + apply_fresh ty_mtd as z. fold subst_trm.
    lets C: (@subst_open_commute_trm x y z t).
    unfolds open_trm. unfold subst_fvar in C. case_var.
    rewrite <- C.
    rewrite <- concat_assoc.
    refine (IH z _ G1 (G2 & z ~ S0) _ _ _ _).
    - auto.
    - subst. rewrite concat_assoc. reflexivity.
    - subst. rewrite concat_assoc.
      apply* weaken_ty_trm.
    - rewrite concat_assoc. auto.
  (* case ty_dsnil *)
  + apply ty_dsnil.
  (* case ty_dscons *)
  + apply* ty_dscons.
Qed.

Print Assumptions raw_subst_principles.

Lemma subst_principle: forall G x y t S T,
  ok (G & x ~ S) ->
  ty_trm (G & x ~ S) t T ->
  ty_trm G (trm_var (avar_f y)) S ->
  ty_trm G (subst_trm x y t) T.
Proof.
  introv Hok tTy yTy. destruct (raw_subst_principles y S) as [_ [P _]].
  specialize (P _ t T tTy G empty x).
  repeat (progress (rewrite concat_empty_r in P)).
  apply* P.
Qed.

Lemma ty_open_trm_change_var: forall x y G e S T,
  ok (G & x ~ S) ->
  ok (G & y ~ S) ->
  x \notin fv_trm e ->
  ty_trm (G & x ~ S) (open_trm x e) T ->
  ty_trm (G & y ~ S) (open_trm y e) T.
Proof.
  introv Hokx Hoky xFr Ty.
  destruct (classicT (x = y)) as [Eq | Ne]. subst. assumption.
  assert (Hokxy: ok (G & x ~ S & y ~ S)) by destruct* (ok_push_inv Hoky).
  assert (Ty': ty_trm (G & x ~ S & y ~ S) (open_trm x e) T).
  apply (weaken_ty_trm Ty Hokxy).
  rewrite* (@subst_intro_trm x y e).
  lets yTy: (ty_var (binds_push_eq y S G)).
  destruct (raw_subst_principles y S) as [_ [P _]].
  apply (P _ (open_trm x e) T Ty' G (y ~ S) x eq_refl yTy Hokxy).
Qed.

Lemma ty_open_defs_change_var: forall x y G ds S T,
  ok (G & x ~ S) ->
  ok (G & y ~ S) ->
  x \notin fv_defs ds ->
  ty_defs (G & x ~ S) (open_defs x ds) T ->
  ty_defs (G & y ~ S) (open_defs y ds) T.
Proof.
  introv Hokx Hoky xFr Ty.
  destruct (classicT (x = y)) as [Eq | Ne]. subst. assumption.
  assert (Hokxy: ok (G & x ~ S & y ~ S)) by destruct* (ok_push_inv Hoky).
  assert (Ty': ty_defs (G & x ~ S & y ~ S) (open_defs x ds) T).
  apply (weaken_ty_defs Ty Hokxy).
  rewrite* (@subst_intro_defs x y ds).
  lets yTy: (ty_var (binds_push_eq y S G)).
  destruct (raw_subst_principles y S) as [_ [_ [_ P]]].
  apply (P _ (open_defs x ds) T Ty' G (y ~ S) x eq_refl yTy Hokxy).
Qed.


(* ###################################################################### *)
(** ** Preservation *)

Theorem preservation_proof:
  forall e s e' s' (Hred: red e s e' s') G T (Hwf: wf_sto s G) (Hty: ty_trm G e T),
  (exists H, wf_sto s' (G & H) /\ ty_trm (G & H) e' T).
Proof.
  intros s e s' e' Hred. induction Hred; intros.
  (* red_call *)
  + rename H into Hvbx. rename H0 into Hibm. rename T0 into U.
    exists (@empty typ). rewrite concat_empty_r. split. apply Hwf.
    (* Grab "ctx binds x" hypothesis: *)
    apply invert_ty_call in Hty. 
    destruct Hty as [T' [Hhas Htyy]].
    apply invert_has in Hhas. 
    destruct Hhas as [Ds [Htyx Hdbm]].
    apply invert_ty_var in Htyx. rename Htyx into Htbx.
    (* Feed "binds x" and "ctx binds x" to invert_wf_sto: *)
    lets HdsDs: (invert_wf_sto_with_weakening Hwf Hvbx Htbx).
    destruct (invert_ty_mtd_inside_ty_defs HdsDs Hibm Hdbm) as [L Hmtd].
    pick_fresh y'.
    rewrite* (@subst_intro_trm y' y body).
    apply* (@subst_principle G y' y ((open_trm y' body)) T' U).
  (* red_sel *)
  + rename H into Hvbx. rename H0 into Hibl.
    exists (@empty typ). rewrite concat_empty_r. split. apply Hwf.
    apply invert_ty_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [Ds [Htyx Hdbl]].
    apply invert_ty_var in Htyx. rename Htyx into Htbx.
    (* Feed "binds x" and "ctx binds x" to invert_wf_sto: *)
    lets HdsDs: (invert_wf_sto_with_weakening Hwf Hvbx Htbx).
    apply (invert_ty_fld_inside_ty_defs HdsDs Hibl Hdbl).
  (* red_new *)
  + rename H into Hvux.
    apply invert_ty_new in Hty.
    destruct Hty as [L [Ds [Eq HdsDs]]]. subst T.
    exists (x ~ typ_rcd Ds).
    pick_fresh x'. assert (Frx': x' \notin L) by auto.
    specialize (HdsDs x' Frx').
    assert (xG: x # G) by apply* sto_unbound_to_ctx_unbound.
    split.
    - apply (wf_sto_push Hwf Hvux xG). apply* (@ty_open_defs_change_var x').
    - apply ty_var. apply binds_push_eq.
  (* red_call1 *)
  + rename T into Tr.
    apply invert_ty_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    apply invert_has in Hhas.
    destruct Hhas as [Ds [Htyo Hdbm]].
    specialize (IHHred G (typ_rcd Ds) Hwf Htyo).
    destruct IHHred as [H [Hwf' Htyo']].
    exists H. split. assumption. apply (@ty_call (G & H) o' m Ta Tr a).
    - apply (has_trm Htyo' Hdbm).
    - lets Hok: wf_sto_to_ok_G Hwf'.
      apply (weaken_ty_trm Htya Hok).
  (* red_call2 *)
  + rename T into Tr.
    apply invert_ty_call in Hty.
    destruct Hty as [Ta [Hhas Htya]].
    specialize (IHHred G Ta Hwf Htya).
    destruct IHHred as [H [Hwf' Htya']].
    exists H. split. assumption. apply (@ty_call (G & H) _ m Ta Tr a').
    - lets Hok: wf_sto_to_ok_G Hwf'.
      apply (weaken_has Hhas Hok).
    - assumption.
  (* red_sel1 *)
  + apply invert_ty_sel in Hty.
    apply invert_has in Hty.
    destruct Hty as [Ds [Htyo Hdbl]].
    specialize (IHHred G (typ_rcd Ds) Hwf Htyo).
    destruct IHHred as [H [Hwf' Htyo']].
    exists H. split. assumption. apply (@ty_sel (G & H) o' l T).
    apply (has_trm Htyo' Hdbl).
Qed.

Theorem preservation_result: preservation.
Proof.
  introv Hwf Hty Hred.
  destruct (preservation_proof Hred Hwf Hty) as [H [Hwf' Hty']].
  exists (G & H). split; assumption.
Qed.

Print Assumptions preservation_result.
