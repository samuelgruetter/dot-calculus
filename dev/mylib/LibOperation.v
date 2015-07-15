(**************************************************************************
* TLC: A library for Coq                                                  *
* Properties of Unary and Binary Operations                               *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics.

(* ********************************************************************** *)
(** * Types of unary and binary operators and relations *)

Definition oper1 (A : Type) := A -> A.
Definition oper2 (A : Type) := A -> A -> A.
Definition predb (A:Type) := A -> bool. 

(* ********************************************************************** *)
(** * Definition of the properties of operators *)

Section Definitions.

Variable (A : Type).
Implicit Types f g : oper2 A.
Implicit Types i : oper1 A.

(* ---------------------------------------------------------------------- *)
(** ** Commutativity, associativity *)

(** Commutativity *)

Definition comm f := forall x y, 
  f x y = f y x.

(** Associativity *)

Definition assoc f := forall x y z,
  f x (f y z) = f (f x y) z.

(** Combined associativity commutativity *)

Definition comm_assoc f := forall x y z,
  f x (f y z) = f y (f x z).

(* ---------------------------------------------------------------------- *)
(** ** Distributivity *)

(** Distributivity of unary operator *)

Definition distrib i f := forall x y,
  i (f x y) = f (i x) (i y).

(** Commutative distributivity of unary operator *)

Definition distrib_comm i f := forall x y,
  i (f x y) = f (i y) (i x).

(** Left distributivity *)

Definition distrib_l f g := forall x y z,
  f x (g y z) = g (f x y) (f x z).

(** Right distributivity *)

Definition distrib_r f g := forall x y z,
  f (g y z) x = g (f y x) (f z x).

(* ---------------------------------------------------------------------- *)
(** ** Neutral and absorbant *)

(** Left Neutral *)

Definition neutral_l f e:= forall x,
  f e x = x.

(** Right Neutral *)

Definition neutral_r f e := forall x,
  f x e = x.

(** Left Absorbant *)

Definition absorb_l f a := forall x,
  f a x = a.

(** Right Absorbant *)

Definition absorb_r f a := forall x,
  f x a = a.

(** Idempotence *)

Definition idempotent i := forall x, 
  i (i x) = x.

(** Idempotence for binary operators *)

Definition idempotent2 f := forall x, 
  f x x = x.

(** Self Neutral *)

Definition self_neutral f e x := 
  f x x = e.

(* ---------------------------------------------------------------------- *)
(** ** Inverses *)

(** Left Inverse *) 

Definition inverse_for_l f e a b := 
  f a b = e.

(** Right Inverse *)

Definition inverse_for_r f e a b :=
  f b a = e.

(** Left Inverse function -- todo arguments in order f i e ? *)

Definition inverse_l f e i := forall x,
  f (i x) x = e.

(** Right Inverse function *)

Definition inverse_r f e i := forall x,
  f x (i x) = e.

(** Self Inverse *)

Definition self_inverse i x := 
  i x = x.

End Definitions.

(* ---------------------------------------------------------------------- *)
(** ** Morphism and automorphism *)

(** Morphism *)

Definition morphism (A B : Type) (h : A -> B) (f : oper2 A) (g : oper2 B) :=
  forall x y, h (f x y) = g (h x) (h y).

(** Auto-morphism *)

Definition automorphism A := @morphism A A.
Implicit Arguments automorphism [A].

(* ---------------------------------------------------------------------- *)
(** ** Injectivity *)

Definition injective A B (f : A -> B) :=
  forall x y, f x = f y -> x = y.


(* ********************************************************************** *)
(** * Derived properties *)

Section OpProperties.

Variable (A : Type).
Implicit Types f g : oper2 A.
Implicit Types h : oper1 A.

(** For commutative operators, right-properties can be derived from 
    corresponding left-properties *)

Lemma neutral_r_from_comm_neutral_l : forall f e, 
  comm f -> neutral_l f e -> neutral_r f e.
Proof. introv C N. intros_all. rewrite* C. Qed.

Lemma inverse_r_from_comm_inverse_l : forall f e i, 
  comm f -> inverse_l f e i -> inverse_r f e i.
Proof. introv C I. intros_all. rewrite* C. Qed. 

Lemma distrib_r_from_comm_distrib_l : forall f g, 
  comm f -> distrib_l f g -> distrib_r f g.
Proof.
  introv C N. intros_all. unfolds distrib_l.
  do 3 rewrite <- (C x). auto.
Qed.  

(** [comm_assoc] derivable *)

Lemma comm_assoc_prove : forall f,
  comm f -> assoc f -> comm_assoc f.
Proof.
  introv C S. intros_all. rewrite C. 
  rewrite <- S. rewrite~ (C x).
Qed.

End OpProperties.
