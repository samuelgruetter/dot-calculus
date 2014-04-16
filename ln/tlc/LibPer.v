(**************************************************************************
* TLC: A library for Coq                                                  *
* Partial equivalence relations                                           *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibBool LibLogic LibRelation LibSet.
Module Rel := LibRelation.

(* ********************************************************************** *)
(** * Partial equivalence relations *)

(** [per R] captures the fact that [R] is symmetric and transitive
    relation, that is, a partial equivalence relation *)

Record per A (R:binary A) :=
 { per_sym : sym R;
   per_trans : trans R }.

(** The domain of a PER contains all the points that are related
    to themselves *)

Definition per_dom A (R:binary A) :=
  \set{ x | R x x}.

(** The empty PER *)

Lemma per_empty:
  forall A,
  per (@LibRelation.empty A).
Proof.
  unfold LibRelation.empty.
  constructor.
  unfold sym. eauto.
  unfold trans. eauto.
Qed.

Lemma per_dom_empty:
  forall A,
  per_dom (@LibRelation.empty A) = empty.
Proof.
  reflexivity.
Qed.

(** A singleton PER *)

Definition per_single A (a b:A) :=
  fun x y => x = a /\ y = b.

(** Extension of an per [B] with a node [z] *)

Definition per_add_node A (B:binary A) (z:A) :=
  Rel.union B (per_single z z).

(** Extension of an per [B] with an edge between [x] and [y] *)

Definition per_add_edge A (B:binary A) (x y:A) :=
  stclosure (Rel.union B (per_single x y)).

Lemma per_add_edge_le : forall A (B:binary A) a b,
  Rel.incl B (per_add_edge B a b).
Proof. introv. intros x y H. apply stclosure_step. left~. Qed.

Lemma add_edge_already : forall A (B:binary A) a b,
  per B -> B a b -> per_add_edge B a b = B.
Proof.
  introv P H. extens. intros x y. iff M.
  induction M.
    destruct H0. auto. destruct H0. subst~.
    apply* per_sym.
    apply* per_trans.
  hnf in M.
  apply~ per_add_edge_le.
Qed.

Lemma per_add_edge_per : forall A (R : binary A) a b,
  per R -> per (per_add_edge R a b).
Proof.
  introv [Rs Rt]. unfold per_add_edge. constructor.
  introv H. induction* H.
  introv H1. gen z. induction* H1. 
Qed.

Lemma per_dom_add_edge : forall A (B:binary A) x y,
  per B -> x \in per_dom B -> y \in per_dom B -> 
  per_dom (per_add_edge B x y) = per_dom B \u \{x} \u \{y}.
Proof.
  introv [Sy Tr] Bx By. unfold per_add_edge. apply set_ext. intros z.
  unfold Rel.union. unfold per_dom. unfold per_single.
  do 2 rewrite in_union_eq, in_set. do 2 rewrite in_single_eq.
  iff H.
  set (a:=z) in H at 1. set (b := z) in H.
  asserts~ K: (a = z \/ b = z). clearbody a b. gen K.
  induction H; introv E.
  left. destruct E; subst; destruct H as [M|[? ?]]; subst*.
  intuition.
  intuition.
  destruct H as [E|[Zx|Zy]]; subst*.
Qed.

Lemma per_add_node_per : forall A (B:binary A) r,
  per B -> per (per_add_node B r).
Proof.
  introv [Sy Tr]. unfold per_add_node, per_single, Rel.union.
  constructors.
  intros_all. hnf in Sy. intuition.  
  intros_all. hnf in Tr. intuition; subst*.
Qed.

Lemma per_dom_add_node : forall A (B:binary A) x,
  per_dom (per_add_node B x) = per_dom B \u \{x}.
Proof.
  intros. unfold per_add_node. apply set_ext. intros y.
  unfold Rel.union. unfold per_dom. unfold per_single.
  rewrite in_union_eq. rewrite in_single_eq. do 2 rewrite in_set. 
  intuition. 
Qed.