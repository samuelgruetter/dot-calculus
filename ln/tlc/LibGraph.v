(**************************************************************************
* TLC: A library for Coq                                                  *
* Graphs                                                                  *
**************************************************************************)

(* under construction *)

Set Implicit Arguments.
Require Import LibCore LibArray LibSet.

(*-----------------------------------------------------------*)

Definition value_nonneg A (f:A->int) (P:A->Prop) :=
  forall x, P x -> f x >= 0.  

(*-----------------------------------------------------------*)

Parameter graph : Type -> Type.
Parameter nodes : forall A, graph A -> set int.
Parameter edges : forall A, graph A -> set (int*int*A).
  
Definition has_edge A (g:graph A) x y w :=
  (x,y,w) \in edges g.

Parameter has_edge_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.

Lemma has_edge_in_nodes_l : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g.
Proof. intros. forwards*: has_edge_nodes. Qed.

Lemma has_edge_in_nodes_r : forall A (g : graph A) x y w,
  has_edge g x y w -> y \in nodes g.
Proof. intros. forwards*: has_edge_nodes. Qed.

Definition nonneg_edges (g:graph int) :=
  forall x y w, has_edge g x y w -> w >= 0.
  (* forall x y, value_nonneg id (has_edge g x y) *)

(*-----------------------------------------------------------*)

Definition path A := list (int*int*A).

Inductive is_path A (g:graph A) : int -> int -> path A -> Prop :=
  | is_path_nil : forall x, 
      x \in nodes g ->
      is_path g x x nil
  | is_path_cons : forall x y z w p,
      is_path g x y p ->
      has_edge g y z w ->
      is_path g x z ((y,z,w)::p).

Lemma is_path_in_nodes_l : forall A (g:graph A) x y p,
  is_path g x y p -> x \in nodes g.
Proof. introv H. induction~ H. Qed.

Lemma is_path_in_nodes_r : forall A (g:graph A) x y p,
  is_path g x y p -> y \in nodes g.
Proof. introv H. inverts~ H. apply* has_edge_in_nodes_r. Qed. 

Lemma is_path_cons_has_edge : forall A (g:graph A) x y z w p,
  is_path g x z ((y,z,w)::p) -> has_edge g y z w.
Proof. introv H. inverts~ H. Qed.

(*-----------------------------------------------------------*)

Definition weight (p:path int) :=
  nosimpl (fold_right (fun e acc => let '(_,_,w) := e in w+acc) 0 p).

Lemma weight_nil : 
  weight (nil : path int) = 0.
Proof. auto. Qed.

Lemma weight_cons : forall (p:path int) x y w, 
  weight ((x,y,w)::p) = w + weight p.
Proof. intros. unfold weight. rew_list~. Qed.

(** A graph with nonnegative edges has only paths
    of nonnegative weight *)

Lemma nonneg_edges_to_path : forall g, 
  nonneg_edges g -> forall x y,
  value_nonneg weight (is_path g x y).
Proof.
  introv NG H. induction H. 
  rewrite weight_nil. math. 
  rewrite weight_cons. forwards: NG H0. math.
Qed.

