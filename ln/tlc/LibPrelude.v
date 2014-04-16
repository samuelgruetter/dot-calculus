(**************************************************************************
* TLC: A library for Coq                                                  *
* Prelude                                                                 *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics.

(** For now on, this file is not used because the standard Prelude of Coq 
    is used instead. *)


(* ********************************************************************** *)
(** * Basic data types 
     -- should be moved to other files, as soon as tactics can be
        implemented without them *)

(** Unit -- move to LibUnit *)

Inductive unit : Type :=
  | tt : unit.

(* TODO: Notation ["()" := tt], as in Program *)

(** Booleans -- move to LibBool *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

Add Printing If bool.
Delimit Scope bool_scope with bool.

(** Natural numbers -- move to LibNat *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

(** Option -- move to LibOption *)

Inductive option A : Type :=
  | Some : A -> option A
  | None : option A.

(** Sum -- move to LibSum *)

Inductive sum A B : Type :=
  | inl : A -> sum A B 
  | inr : B -> sum A B.

Hint Constructors sum : core.

Notation "x + y" := (sum x y) : type_scope.

(** Product -- move to LibProd *)

Inductive prod A B : Type :=
  | pair : A -> B -> prod A B.

Hint Constructors prod : core.

Add Printing Let prod.
Notation "x * y" := (prod x y) : type_scope.
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Definition fst A B (p:A*B) := let '(x,_) := p in x.
Definition snd A B (p:A*B) := let '(_,y) := p in y.


(* ********************************************************************** *)
(** * Logic data types -- move to LibLogic *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of [True], [False] and negation *)

(** Definition of [True] *)

Inductive True : Prop :=
  | True_intro : True. 

Hint Constructors True : core.

(** Definition of [False] *)

Inductive False : Prop := .

(** Definition of negation, [not], written [~ P] *)

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Hint Unfold not : core.

(* ---------------------------------------------------------------------- *)
(** ** Definition of conjunction and disjunction *)

(** Definition of conjonction, [and], written [P /\ Q],
    and associated projections *)

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q. 

Notation "P /\ Q" := (and P Q) : type_scope.

Hint Constructors and : core.

Lemma proj1 : forall (P Q : Prop), P /\ Q -> P.
Proof. auto*. Qed.
Lemma proj2 : forall (P Q : Prop), P /\ Q -> Q.
Proof. auto*. Qed.

(** Definition of disjunction, [or], written [P \/ Q]. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q  (* todo: rename to [or_l] *)
  | or_intror : Q -> or P Q. (* todo: rename to [or_r] *)

Notation "A \/ B" := (or A B) : type_scope.

Hint Constructors or : core.

(* ---------------------------------------------------------------------- *)
(** ** Definition of equivalence and conditional *)

(** Definition of equivalence, [iff], written [P <-> Q] *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) : type_scope.

Hint Unfold iff.

(** [(IF_then_else P Q R)], written [IF P then Q else R] denotes
    either [P] and [Q], or [~P] and [Q] *)

Definition IF_then_else (P Q R : Prop) := (P /\ Q) \/ (~ P /\ R).

Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
  (at level 200, right associativity) : type_scope.


(* ---------------------------------------------------------------------- *)
(** ** Definition of equality and dependent equality *)

(** Definition of equality, [eq], written [x = y] or [x = y :> A] *)

Inductive eq (A : Type) (x : A) : A -> Prop :=
  | eq_refl : eq x x. 

Notation "x = y :> A" := (@eq A x y) : type_scope.
Notation "x = y" := (eq x y) : type_scope.
Notation "x <> y :> A" := (~ @eq A x y) : type_scope.
Notation "x <> y" := (~ eq x y) : type_scope.

Implicit Arguments eq_ind [A].
Implicit Arguments eq_rec [A].
Implicit Arguments eq_rect [A].

Hint Constructors eq : core.

(** Definition of dependent equality *)

Inductive eq_dep (A : Type) (P : A -> Type) (p : A) (x : P p)
  : forall q, P q -> Prop :=
  | eq_dep_refl : eq_dep P p x p x.

Implicit Arguments eq_dep [A P]. 

Hint Constructors eq_dep : core.

(** Definition of John Major's equality *)

Inductive JMeq (A : Type) (x : A) : forall B : Type, B -> Prop :=
   | JMeq_refl : JMeq x x.


(* ---------------------------------------------------------------------- *)
(** ** Definition of existential and unique existential *)

(** Definition of existential, [ex], written [exists x, P] *)

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
  | ex_intro : forall x, P x -> ex P.

Notation "'exists' x , p" := (ex (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : t , p" := (ex (fun x:t => p))
  (at level 200, x ident, right associativity,
    format "'[' 'exists'  '/  ' x  :  t ,  '/  ' p ']'")
  : type_scope.

Hint Constructors ex : core.

(** Definition of unique existential, [unique], written [exists !x, P] *)

Definition unique_st (A : Type) (P : A -> Prop) (x : A) :=
  P x /\ forall y, P y -> x = y.

Hint Unfold unique_st. 

Definition ex_unique (A : Type) (P : A -> Prop) :=
  ex (unique_st P). 

Notation "'exists' ! x , P" := (ex_unique (fun x => P))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x ,  '/  ' P ']'") : type_scope.
Notation "'exists' ! x : A , P" :=
  (ex_unique (fun x:A => P))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x  :  A ,  '/  ' P ']'") : type_scope.


(* ********************************************************************** *)
(** * Peano -- move all the contents to LibNat *)

(* ********************************************************************** *)
(** * Specif -- move to LibLogic *)

(* ---------------------------------------------------------------------- *)
(** ** Subset-type *)

(** Definition *)

Inductive sig (A : Type) (P : A -> Prop) : Type :=
  | exist : forall x, P x -> sig P. 

(* --todo: implicit Arguments exist [A P x]. ?*)

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
Notation "{ x : A | P }" := (sig (fun x:A => P)) : type_scope.
Add Printing Let sig.

(** Projections *)

Section SigProj.
Variables (A : Type) (P : A -> Prop).
Definition sig_1 (e:sig P) : A := 
  let (a,_) := e in a.
Definition sig_2 (e:sig P) : P (sig_1 e) := 
  let (_,b) := e in b.
End SigProj.


(* ---------------------------------------------------------------------- *)
(** ** Sigma-type *)

(** Definition *)

Inductive sigT (A : Type) (P : A -> Type) : Type :=
  | existT : forall x, P x -> sigT P.

Notation "{ x : A & P }" := (sigT (fun x:A => P)) : type_scope.
Add Printing Let sigT.

(* TODO: do we want "Implicit Arguments existT [A P x]." ?*)
(* TODO: do we want "Notation "{ x & P }" := (sigT (fun x:A => P)) : type_scope." ? *)

(** Projections *)

Section SigProj.
Variables (A : Type) (P : A -> Type).
Definition sigT_1 (e:sigT P) : A := 
  let (a,_) := e in a.
Definition sigT_2 (e:sigT P) : P (sigT_1 e) := 
  let (_,b) := e in b.
End SigProj.


(* ---------------------------------------------------------------------- *)
(** ** Connection between subset types and sigma types *)

(* [sigT] is equivalent to [sig] for predicates *)

Coercion sig_of_sigT (A:Type) (P:A->Prop) (E:sigT P) : sig P.
Coercion sigT_of_sig (A:Type) (P:A->Prop) (E:sig P) : sigT P.

Lemma pred_sigT_is_sig : forall (A:Type) (P:A->Prop),
  sigT P = sig P.

(* todo: do we want:
Lemma sig_of_sigT : forall (A:Type) (P:A->Prop), sigT P -> sig P.
Lemma sigT_of_sig : forall (A:Type) (P:A->Prop), sig P -> sigT P.
Coercion sigT_of_sig : sig >-> sigT.
Coercion sig_of_sigT : sigT >-> sig.
*)


(* ********************************************************************** *)
(** * Well-foundedness -- move to LibWf *)

(** An element [x] is accessible with respect to a relation [R] iff any
   finite chain of [R]-related elements starting from [x] is finite *)

Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
  | Acc_intro : (forall y, R y x -> Acc R y) -> Acc R x.

(** A relation is well-founded if all the elements are accessibles *)

Definition wf (A : Type) (R : A -> A -> Prop) := 
  forall a, Acc R a.
