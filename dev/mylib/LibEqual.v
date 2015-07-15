(**************************************************************************
* TLC: A library for Coq                                                  *
* Equality                                                                  *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibAxioms.
Generalizable Variables A.


(* ********************************************************************** *)
(** * Partial application of Leibnitz' equality *)

(** [= x] is a unary predicate which holds of values equal to [x].
    It simply denotes the partial application of equality.
    [= x :> A] allows to specify the type. *)

Notation "'=' x :> A" := (fun y => y = x :> A) 
  (at level 71, x at next level).
Notation "'=' x" := (fun y => y = x) 
  (at level 71).

(** [<> x] is a unary predicate which holds of values disequal to [x].
    It simply denotes the partial application of disequality.
    [<> x :> A] allows to specify the type. *)

Notation "'<>' x :> A" := (fun y => y <> x :> A) 
  (at level 71, x at next level).
Notation "'<>' x" := (fun y => y <> x) 
  (at level 71).


(* ********************************************************************** *)
(** * Functional extensionality *)

(* ---------------------------------------------------------------------- *)
(** ** Dependent functional extensionality *)

Section FuncExtDep.
Variables
  (A1 : Type) 
  (A2 : forall (x1 : A1), Type) 
  (A3 : forall (x1 : A1) (x2 : A2 x1), Type)
  (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type)
  (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type)
  (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma func_ext_dep_1 : forall (f g : forall (x1:A1), A2 x1),
  (forall x1, f x1 = g x1) -> f = g.
Proof. repeat (intros; apply func_ext_dep). auto. Qed.

Lemma func_ext_dep_2 : forall (f g : forall (x1:A1) (x2:A2 x1), A3 x2),
  (forall x1 x2, f x1 x2 = g x1 x2) -> f = g.
Proof. repeat (intros; apply func_ext_dep). auto. Qed.

Lemma func_ext_dep_3 : forall (f g : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), A4 x3),
  (forall x1 x2 x3, f x1 x2 x3 = g x1 x2 x3) -> f = g.
Proof. repeat (intros; apply func_ext_dep). auto. Qed.

Lemma func_ext_dep_4 : forall (f g: forall (x1:A1) (x2:A2 x1) (x3:A3 x2) 
 (x4:A4 x3), A5 x4),
  (forall x1 x2 x3 x4, f x1 x2 x3 x4 = g x1 x2 x3 x4) -> f = g.
Proof. repeat (intros; apply func_ext_dep). auto. Qed.

End FuncExtDep.

(* ---------------------------------------------------------------------- *)
(** ** Non-dependent functional extensionality *)

Lemma func_ext_1 : forall A1 B (f g : A1 -> B),
  (forall x1, f x1 = g x1) -> f = g.
Proof. intros. apply~ func_ext_dep_1. Qed.

Lemma func_ext_2 : forall A1 A2 B (f g : A1 -> A2 -> B),
  (forall x1 x2, f x1 x2 = g x1 x2) -> f = g.
Proof. intros. apply~ func_ext_dep_2. Qed.

Lemma func_ext_3 : forall A1 A2 A3 B (f g : A1 -> A2 -> A3 -> B),
  (forall x1 x2 x3, f x1 x2 x3 = g x1 x2 x3) -> f = g.
Proof. intros. apply~ func_ext_dep_3. Qed.

Lemma func_ext_4 : forall A1 A2 A3 A4 B (f g : A1 -> A2 -> A3 -> A4 -> B),
  (forall x1 x2 x3 x4, f x1 x2 x3 x4 = g x1 x2 x3 x4) -> f = g.
Proof. intros. apply~ func_ext_dep_4. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Eta-conversion *)

Lemma func_eta_dep : forall (A:Type) (B:A->Type) (f : forall x, B x),
  (fun x1 => f x1) = f.
Proof. intros. apply~ func_ext_dep. Qed.

Lemma func_eta_1 : forall A1 B (f : A1 -> B),
  (fun x1 => f x1) = f.
Proof. intros. apply~ func_ext_1. Qed.

Lemma func_eta_2 : forall A1 A2 B (f : A1 -> A2 -> B),
  (fun x1 x2 => f x1 x2) = f.
Proof. intros. apply~ func_ext_2. Qed.

Lemma func_eta_3 : forall A1 A2 A3 B (f : A1 -> A2 -> A3 -> B),
  (fun x1 x2 x3 => f x1 x2 x3) = f.
Proof. intros. apply~ func_ext_3. Qed.

Lemma func_eta_4 : forall A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B),
  (fun x1 x2 x3 x4 => f x1 x2 x3 x4) = f.
Proof. intros. apply~ func_ext_4. Qed.

Hint Rewrite func_eta_1 func_eta_2 func_eta_3 func_eta_4 : rew_eta.



(* ********************************************************************** *)
(** * Predicate extensionality *)


(* ---------------------------------------------------------------------- *)
(** ** Dependend predicates *)

Section PropExt.
Variables
  (A1 : Type) 
  (A2 : forall (x1 : A1), Type) 
  (A3 : forall (x1 : A1) (x2 : A2 x1), Type)
  (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type)
  (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type)
  (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma prop_ext_1 : forall (P Q : forall (x1:A1), Prop),
  (forall x1, P x1 <-> Q x1) -> P = Q.
Proof. repeat (intros; apply func_ext_dep). intros. apply~ prop_ext. Qed.

Lemma prop_ext_2 : forall (P Q : forall (x1:A1) (x2:A2 x1), Prop),
  (forall x1 x2, P x1 x2 <-> Q x1 x2) -> P = Q.
Proof. repeat (intros; apply func_ext_dep). intros. apply~ prop_ext. Qed.

Lemma prop_ext_3 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), Prop),
  (forall x1 x2 x3, P x1 x2 x3 <-> Q x1 x2 x3) -> P = Q.
Proof. repeat (intros; apply func_ext_dep). intros. apply~ prop_ext. Qed.

Lemma prop_ext_4 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2) 
 (x4:A4 x3), Prop),
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 <-> Q x1 x2 x3 x4) -> P = Q.
Proof. repeat (intros; apply func_ext_dep). intros. apply~ prop_ext. Qed.

Lemma prop_ext_5 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2) 
 (x4:A4 x3) (x5:A5 x4), Prop),
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 <-> Q x1 x2 x3 x4 x5) -> P = Q.
Proof. repeat (intros; apply func_ext_dep). intros. apply~ prop_ext. Qed.

Lemma prop_ext_6 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2) 
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5), Prop),
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 <-> Q x1 x2 x3 x4 x5 x6) -> P = Q.
Proof. repeat (intros; apply func_ext_dep). intros. apply~ prop_ext. Qed.

End PropExt.

(* ---------------------------------------------------------------------- *)
(** ** Non-dependend predicates *)

Lemma prop_ext_nd_1 : forall A1 (P Q : A1 -> Prop),
  (forall x1, P x1 <-> Q x1) -> P = Q.
Proof. intros. apply~ prop_ext_1. Qed. 

Lemma prop_ext_nd_2 : forall A1 A2 (P Q : A1 -> A2 -> Prop),
  (forall x1 x2, P x1 x2 <-> Q x1 x2) -> P = Q.
Proof. intros. apply~ prop_ext_2. Qed.

Lemma prop_ext_nd_3 : forall A1 A2 A3 (P Q : A1 -> A2 -> A3 -> Prop),
  (forall x1 x2 x3, P x1 x2 x3 <-> Q x1 x2 x3) -> P = Q.
Proof. intros. apply~ prop_ext_3. Qed.

Lemma prop_ext_nd_4 : forall A1 A2 A3 A4 (P Q : A1 -> A2 -> A3 -> A4 -> Prop),
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 <-> Q x1 x2 x3 x4) -> P = Q.
Proof. intros. apply~ prop_ext_4. Qed.



(* ********************************************************************** *)
(** * Proof Irrelevance *)

(** The proof irrelevance lemma states that two proofs of a same 
    proposition are always equal. *)

(* ---------------------------------------------------------------------- *)
(** ** Proof of the proof-irrelevance result *)

(** Proof irrelevance is a consequence of propositional extensionality. *)

(* TODO: simplify and beautify the proof *)

Module PIfromExt.
  Notation Local inhabited A := A (only parsing).

  Lemma prop_ext_to_eq_arrow :  
    forall (A:Prop), inhabited A -> (A -> A) = A.
  Proof. intros. apply* prop_ext. Qed.

  Record retract (A B : Prop) : Prop := 
  { retract_f1 : A -> B; 
    retract_f2 : B -> A; 
    retract_comp : forall x, retract_f1 (retract_f2 x) = x }.

  Lemma prop_ext_retract_A_A_imp_A :
    forall (A:Prop), inhabited A -> retract A (A -> A).
  Proof.
  intros A a. rewrite (prop_ext_to_eq_arrow a).
  apply~ (@Build_retract A A (fun x => x) (fun x => x)).
  Qed.

  Record has_fixpoint (A:Prop) : Prop := 
    { has_fixpoint_F : (A -> A) -> A; 
      has_fixpoint_fix : forall f, has_fixpoint_F f = f (has_fixpoint_F f) }.

  Lemma ext_prop_fixpoint :
    forall (A:Prop), inhabited A -> has_fixpoint A.
  Proof.
  intros A a. destruct (prop_ext_retract_A_A_imp_A a) as [g1 g2 Fix].
  set (Y := fun f => (fun x => f (g1 x x)) (g2 (fun x => f (g1 x x)))).
  exists Y. intros f. unfold Y at 1. rewrite~ Fix.
  Qed.

 Inductive boolP : Prop :=
    | trueP : boolP
    | falseP : boolP.
  Definition boolP_elim_redl (C:Prop) (c1 c2:C) :
    c1 = boolP_ind c1 c2 trueP := refl_equal c1.
  Definition boolP_elim_redr (C:Prop) (c1 c2:C) :
    c2 = boolP_ind c1 c2 falseP := refl_equal c2.
  Scheme boolP_indd := Induction for boolP Sort Prop.

 Lemma aux : trueP = falseP.
  Proof.
    case (@ext_prop_fixpoint boolP trueP); intros G Gfix.
    set (neg := fun b:boolP => @boolP_ind boolP falseP trueP b).
    generalize (refl_equal (G neg)).
    pattern (G neg) at 1 in |- *.
    apply boolP_indd with (b := G neg); intro Heq.
    rewrite (boolP_elim_redl falseP trueP).
    change (trueP = neg trueP) in |- *. rewrite Heq. apply Gfix.
    rewrite (boolP_elim_redr falseP trueP).
    change (neg falseP = falseP) in |- *; rewrite Heq; symmetry  in |- *;
      apply Gfix.
  Qed.

  Lemma proof_irrelevance : 
    forall (P : Prop) (p q : P), p = q.
  Proof.
  intros A a1 a2.
  set (f := fun b:boolP => match b with trueP => a1 | _ => a2 end). 
  (* set (f := fun b:boolP => boolP_ind a1 a2 b). *)
  rewrite (boolP_elim_redl a1 a2).
  change (f trueP = a2) in |- *.
  rewrite (boolP_elim_redr a1 a2).
  change (f trueP = f falseP) in |- *.
  rewrite (aux).
    reflexivity.
  Qed.

End PIfromExt.

Lemma proof_irrelevance : 
  forall (P : Prop) (p q : P), p = q. 
Proof. exact PIfromExt.proof_irrelevance. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Consequences of proof irrelevance *)

(** Uniqueness of identity proofs *)

Lemma identity_proofs_unique : 
  forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof. intros. apply proof_irrelevance. Qed. 

(** Uniqueness of reflexive identity proofs *)

Lemma refl_identity_proofs_unique : 
  forall (A : Type) (x : A) (p : x = x), 
  p = refl_equal x.
Proof. intros. apply proof_irrelevance. Qed. 

(** Invariance by substitution of reflexive equality proofs *)

Lemma eq_rect_eq : 
  forall (A : Type) (p : A) (Q : A -> Type) (x : Q p) (h : p = p),
  eq_rect p Q x p h = x.
Proof. intros. rewrite~ (refl_identity_proofs_unique h). Qed.

(** Streicher's axiom K *)

Lemma streicher_K : forall (A : Type) (x : A) (P : x = x -> Prop),
  P (refl_equal x) -> forall (p : x = x), P p.
Proof. intros. rewrite~ (refl_identity_proofs_unique p). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Injectivity of equality on dependent pairs *)

(** This section establishes that [existT P p x = existT P p y] implies
    that [x] is equal to [y]. It indirectly results from the proof 
    irrelevance property. *)

(** Definition of dependent equality, with non-dependent return type *)

Inductive eq_dep_nd (A : Type) (P : A -> Type) 
    (p : A) (x : P p) (q : A) (y : P q) : Prop :=
 | eq_dep_nd_intro : forall (h : q = p), 
    x = eq_rect q P y p h -> eq_dep_nd P p x q y.

Implicit Arguments eq_dep_nd [A P p q].
Implicit Arguments eq_dep_nd_intro [A P p q x y].

(** Reflexivity of [eq_dep_nd] *)

Lemma eq_dep_nd_direct : forall (A : Type) (P : A -> Type) (p : A) (x : P p),
  eq_dep_nd x x.
Proof. intros. apply (eq_dep_nd_intro (refl_equal p)). auto. Qed.

(** Injectivity of [eq_dep_nd] *)

Lemma eq_dep_nd_eq :
  forall (A : Type) (P : A -> Type) (p : A) (x y : P p), 
  eq_dep_nd x y -> x = y.
Proof. introv H. inversions H. rewrite~ eq_rect_eq. Qed.

(** Equality on dependent pairs implies [eq_dep_nd] *)

Lemma eq_sigT_eq_dep_nd :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q),
  existT P p x = existT P q y -> eq_dep_nd x y.
Proof. introv E. dependent rewrite E. simpl. apply eq_dep_nd_direct. Qed. 

(** Injectivity of equality on dependent pairs *)

Lemma eq_sigT_to_eq : 
  forall (A : Type) (P : A -> Type) (p : A) (x y : P p),
  existT P p x = existT P p y -> x = y.
Proof. intros. apply eq_dep_nd_eq. apply~ eq_sigT_eq_dep_nd. Qed.


(* ---------------------------------------------------------------------- *)
(** Irrelevance of the membership property for subsets types *)

(** This is another consequence of proof irrelevance *)

Scheme eq_indd := Induction for eq Sort Prop.

Lemma exist_eq :
  forall (A : Type) (P : A->Prop) (x y : A) (p : P x) (q : P y),
    x = y -> exist P x p = exist P y q.
Proof.
  intros. rewrite (proof_irrelevance q (eq_rect x P p y H)).
  elim H using eq_indd. reflexivity.
Qed.

Lemma existT_eq :
  forall (U:Type) (P:U->Prop) (x y:U) (p:P x) (q:P y),
    x = y -> existT P x p = existT P y q.
Proof.
  intros. rewrite (proof_irrelevance q (eq_rect x P p y H)).
  elim H using eq_indd. reflexivity.
Qed.


(* ********************************************************************** *)
(** * Dependent equality *)

(** In this section, we prove that [eq_dep x y] implies [x = y]. *)

(** Definition of [eq_dep] (copied from the LibPrelude) *)

Inductive eq_dep (A : Type) (P : A -> Type) (p : A) (x : P p)
  : forall q, P q -> Prop :=
  | eq_dep_refl : eq_dep P p x p x.

Implicit Arguments eq_dep [A P p q].

(** Symmetry of [eq_dep] *)

Lemma eq_dep_sym : forall (A : Type) (P : A -> Type) 
 (p q : A) (x : P p) (y : P q), 
  eq_dep x y -> eq_dep y x.
Proof. introv E. destruct E. constructor. Qed.

(** Transitivity of [eq_dep] *)

Lemma eq_dep_trans : forall (A : Type) (P : A -> Type) 
 (p q r : A) (y : P q) (x : P p) (z : P r), 
  eq_dep x y -> eq_dep y z -> eq_dep x z.
Proof. introv E F. destruct~ E. Qed.

(** Proof of equivalence between [eq_dep_nd] and [eq_dep] *)

Scheme eq_induction := Induction for eq Sort Prop.

Lemma eq_dep_nd_to_eq_dep :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q), 
  eq_dep_nd x y -> eq_dep x y.
Proof.
  introv E. destruct E as (h,H). 
  destruct h using eq_induction. subst~. constructor.
Qed.

Lemma eq_dep_to_eq_dep_nd :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q), 
  eq_dep x y -> eq_dep_nd x y.
Proof. introv H. destruct H. apply (eq_dep_nd_intro (refl_equal p)); auto. Qed. 

(** Injectivity of dependent equality *)

Lemma eq_dep_eq : 
  forall (A : Type) (P : A -> Type) (p : A) (x y : P p), 
  eq_dep x y -> x = y.
Proof. introv R. inversion R. apply eq_dep_nd_eq. apply~ eq_dep_to_eq_dep_nd. Qed.

(** Equality on dependent pairs implies dependent equality *)

Lemma eq_sigT_eq_dep :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q),
  existT P p x = existT P q y -> eq_dep x y.
Proof. introv E. dependent rewrite E. simple~. constructor. Qed.


(* ********************************************************************** *)
(** * John Major's equality *)

(** In this section, we prove that [JMeq x y] implies [x = y]
    when both [x] and [y] have the same type. *)

Require Import JMeq.

(** Symmetry, transitivity of [JMeq] *)

Lemma JMeq_sym : forall (A B : Type) (x : A) (y : B), 
  JMeq x y -> JMeq y x.
Proof. introv E. destruct~ E. Qed.

Lemma JMeq_trans : forall (A B C : Type) (y : B) (x : A) (z : C),
  JMeq x y -> JMeq y z -> JMeq x z.
Proof. introv E F. destruct~ E. Qed.

Local Hint Immediate JMeq_sym.

(** Relation between [JMeq] and [eq_dep] *)

Lemma JMeq_to_eq_dep : forall (A B : Type) (x : A) (y : B), 
  JMeq x y -> @eq_dep Type (fun T => T) A x B y.
Proof. introv E. destruct E. constructor. Qed.

Lemma eq_dep_to_JMeq : forall (A B : Type) (x : A) (y : B), 
  @eq_dep Type (fun T => T) A x B y -> JMeq x y.
Proof. introv E. destruct~ E. Qed.

(** Injectivity of [JMeq] *)

Lemma JMeq_eq : forall (A : Type) (x y : A), 
  JMeq x y -> x = y.
Proof.
  introv E. apply (@eq_dep_eq Type (fun T => T)).
  apply~ JMeq_to_eq_dep.
Qed.



(* ********************************************************************** *)
(** * Properties of equality *)

(** This section contains a reformulation of the lemmas provided by
    the standard library concerning equality. *)

Implicit Arguments eq [[A]].

(* ---------------------------------------------------------------------- *)
(** ** Equality as an equivalence relation *)

Section EqualityProp.
Variable A : Type.
Implicit Types x y z : A.

(** Reflexivity is captured by the constructor [eq_refl]. *)

(** Symmetry *)

Lemma eq_sym : forall x y,
  x = y -> y = x.
Proof. introv H. destruct~ H. Qed.

(** Transitivity *)

Lemma eq_trans : forall y x z,
  x = y -> y = z -> x = z.
Proof. introv H1 H2. destruct~ H2. Qed.

Lemma eq_trans' : forall y x z,
  y = x -> y = z -> x = z.
Proof. introv H1 H2. destruct~ H2. Qed.

End EqualityProp.

Implicit Arguments eq_trans [A].
Implicit Arguments eq_trans' [A].

(* TODO: two other versions of eq_trans *)

(* ---------------------------------------------------------------------- *)
(** ** Properties of disequality *)

Section DisequalityProp.
Variable A : Type.
Implicit Types x y z : A.

(** Symmetry *)

Lemma neq_sym : forall x y,
  x <> y -> y <> x.
Proof. introv H K. destruct~ K. Qed.

End DisequalityProp.

(* ---------------------------------------------------------------------- *)
(** ** Symmetrized induction principles *)

(* TODO: is this really needed ?*)

Section EqInductionSym.
Variables (A : Type) (x : A).

Definition eq_ind_r : forall (P:A -> Prop), 
  P x -> forall y, y = x -> P y.
Proof. introv Px H. elim (sym_eq H). auto. Qed.

Definition eq_rec_r : forall (P:A -> Set), 
  P x -> forall y, y = x -> P y.
Proof. introv Px H. elim (sym_eq H). auto. Qed.

Definition eq_rect_r : forall (P:A -> Type), 
  P x -> forall y, y = x -> P y.
Proof. introv Px H. elim (sym_eq H). auto. Qed.

End EqInductionSym.



(* ********************************************************************** *)
(** * Equality between function applications *)

(* ---------------------------------------------------------------------- *)
(** ** A same function applied to equal arguments yield equal result *)

Section FuncEq.
Variables (A1 A2 A3 A4 A5 B : Type).

Lemma func_eq_1 : forall (f:A1->B) x1 y1,
  x1 = y1 -> 
  f x1 = f y1.
Proof. intros. subst~. Qed.

Lemma func_eq_2 : forall (f:A1->A2->B) x1 y1 x2 y2,
  x1 = y1 -> x2 = y2 -> 
  f x1 x2 = f y1 y2.
Proof. intros. subst~. Qed.

Lemma func_eq_3 : forall (f:A1->A2->A3->B) x1 y1 x2 y2 x3 y3,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> 
  f x1 x2 x3 = f y1 y2 y3.
Proof. intros. subst~. Qed.

Lemma func_eq_4 : forall (f:A1->A2->A3->A4->B) x1 y1 x2 y2 x3 y3 x4 y4,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> 
  f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof. intros. subst~. Qed.

Lemma func_eq_5 : forall (f:A1->A2->A3->A4->A5->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> 
  f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof. intros. subst~. Qed.

End FuncEq.

(* TODO: generalize to dependent functions *)

(* ---------------------------------------------------------------------- *)
(** ** Equal functions return equal results *)

Section FuncSame.
Variables (A1 A2 A3 A4 A5 B:Type).
Variables (x1:A1) (x2:A2) (x3:A3) (x4:A4) (x5:A5).

Lemma func_same_1 : forall f g,
  f = g -> f x1 = g x1 :> B.
Proof. intros. subst~. Qed.

Lemma func_same_2 : forall f g,
  f = g -> f x1 x2 = g x1 x2 :> B.
Proof. intros. subst~. Qed.

Lemma func_same_3 : forall f g,
  f = g -> f x1 x2 x3 = g x1 x2 x3 :> B.
Proof. intros. subst~. Qed.

Lemma func_same_4 : forall f g,
  f = g -> f x1 x2 x3 x4 = g x1 x2 x3 x4 :> B.
Proof. intros. subst~. Qed.

Lemma func_same_5 : forall f g,
  f = g -> f x1 x2 x3 x4 x5 = g x1 x2 x3 x4 x5 :> B.
Proof. intros. subst~. Qed.

End FuncSame.


(* ********************************************************************** *)
(** * General definition of extensionality *)

(** The property [Extensional A] captures the fact that the type [A]
    features an extensional equality, in the sense that to prove the
    equality between two values of type [A] it suffices to prove that
    those two values are related by some binary relation. *)

Class Extensional (A:Type) := {
  extensional_hyp : A -> A -> Prop;
  extensional : forall x y : A, extensional_hyp x y -> x = y }.


(* ---------------------------------------------------------------------- *)
(** ** Tactic to exploit extensionality *)

(** [extens] is a tactic that can be applied to exploit extensionality
    on any goal of the form [x = y] when [x] and [y] are functions, or
    predicates, or have a type [A] satisfying [Extensional A]. 
    Note: the tactic [extens] automatically calls [intros] if needed. *)

Ltac extens_core :=
  hnf; 
  match goal with 
  | |- _ = _ :> ?T =>
  match T with
  | Prop => apply prop_ext
  | forall _, Prop => apply prop_ext_1
  | forall _ _, Prop => apply prop_ext_2
  | forall _ _ _, Prop => apply prop_ext_3
  | forall _ _ _ _, Prop => apply prop_ext_4
  | forall _ _ _ _ _, Prop => apply prop_ext_5
  | forall _ _ _ _ _ _, Prop => apply prop_ext_6
  | forall _,_ => 
     first [ apply func_ext_dep_4
           | apply func_ext_dep_3
           | apply func_ext_dep_2
           | apply func_ext_dep_1 ]
  | _ => apply extensional; try unfold extensional_hyp; simpl
  end end. 

Ltac extens_base :=
  first [ extens_core | intros; extens_core ].

Tactic Notation "extens" := 
  extens_base.
Tactic Notation "extens" "~" := 
  extens; auto_tilde.
Tactic Notation "extens" "*" := 
  extens; auto_star.





