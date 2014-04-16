(**************************************************************************
* TLC: A library for Coq                                                  *
* Axioms                                                                  *
**************************************************************************)

Set Implicit Arguments.


(** This file is used to extend Coq with standard axioms from classical,
    non-constructive higher-order logic. (Such axioms are provided by
    default in other theorem provers like Isabelle/HOL or HOL4.) *)

(** Three axioms taken are: functional extensionality, and propositional
    extensionality and indefinite description.

    All other comomn axioms are derivable, including: the excluded middle,
    the strong excluded middle, propositional degenerency, proof irrelevance, 
    injectivity of equality on dependent pairs, predicate extensionality,
    definite description, and all the versions of the axiom of choice. *)

(* ********************************************************************** *)
(** * Functional extensionality *)

(** Two functions that yield equal results on equal arguments are equal. *)

Axiom func_ext_dep : forall (A:Type) (B:A->Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.


(* ********************************************************************** *)
(** * Propositional extensionality *)

(** Two propositions that are equivalent can be considered to be equal. *)

Axiom prop_ext : forall (P Q : Prop), 
  (P <-> Q) -> P = Q.


(* ********************************************************************** *)
(** * Indefinite description *)

(** Proofs of existence can be reified from [Prop] to [Type]. The lemma
    below is a concise statement for [(exists x, P x) -> { x : A | P x }]. *)

Axiom indefinite_description : forall (A : Type) (P : A->Prop), 
   ex P -> sig P.
