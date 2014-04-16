(**************************************************************************
* TLC: A library for Coq                                                  *
* Finite arrays                                                           *
**************************************************************************)

(** UNDER CONSTRUCTION *)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibTactics LibLogic LibReflect
  LibRelation LibList LibInt LibOperation LibEpsilon
  LibSet LibMap.
Require Export LibBag.


(* todo: move *)

Parameter range : int -> int -> set int.


(* ********************************************************************** *)
(** * Construction of arrays based on maps *)

(* ---------------------------------------------------------------------- *)
(** ** Basic definitions *)

Record array_raw (A:Type) := {
  array_length : int;
  array_support : map int A }.

Record array_wf A (t:array_raw A) := {
  array_pos : array_length t >= 0;
  array_dom : dom (array_support t) = range 0 (array_length t) }.

Definition array (A:Type) := { t : array_raw A | array_wf t }.

Definition length A (t:array A) :=
  array_length (proj1_sig t).

Definition read_impl `{Inhab A} (t:array A) (i:int) : A :=
  (array_support (proj1_sig t))\(i).

Program Definition update_impl A (t:array A) (i:int) (v:A) : array A :=
  Build_array_raw (length t) ((array_support (proj1_sig t))\(i := v)).
Next Obligation.
  destruct t as [t [Wp Wd]]. constructor; unfold length; simpl.
  auto.
  skip. (* todo: dom udpate *)
Defined.

Definition binds_impl A (t:array A) (i:int) (v:A) := 
  binds (array_support (proj1_sig t)) i v.

Axiom make : forall A (n:int) (v:A), array A.

(* ---------------------------------------------------------------------- *)
(** ** Notation through typeclasses *)

Instance read_inst : forall `{Inhab A}, BagRead int A (array A).
  constructor. rapply (@read_impl A H). Defined.
Instance update_inst : forall A, BagUpdate int A (array A).
  constructor. rapply (@update_impl A). Defined.
Instance binds_inst : forall A, BagBinds int A (array A).
  constructor. rapply (@binds_impl A). Defined.

Global Opaque array read_inst update_inst binds_inst.

(* ---------------------------------------------------------------------- *)
(** ** Index for arrays *)

Instance array_index : forall A, BagIndex (array A) int.
Proof. intros. constructor. exact (fun t i => index (length t) i). Defined.

Lemma array_index_def : forall A (t:array A) i,
  index t i = index (length t) i.
Proof. auto. Qed. 

Lemma array_index_bounds : forall A (t:array A) i,
  index t i = (0 <= i < length t).
Proof. auto. Qed. 

Lemma array_index_prove : forall A (t:array A) i,
  0 <= i < length t -> index t i.
Proof. intros. rewrite~ array_index_def. Qed.

Lemma index_array_length : forall A (t : array A) n i,
  index n i -> n = length t -> index t i.
Proof. intros. subst. rewrite~ array_index_def. Qed.

Global Opaque array_index.



(* ********************************************************************** *)
(** * Properties of arrays *)

(* todo *)
Axiom length_update : forall A (t:array A) i v,
  length (t\(i:=v)) = length t.
(* Axiom length_update_prove : forall A (t:array A) i v n,
  length t = n -> length (t\(i:=v)) = n. *)
Axiom array_update_read_eq : forall `{Inhab A} (t:array A) (i:int) (v:A),
  index t i -> (t\(i:=v))\(i) = v.
Axiom array_update_read_neq : forall `{Inhab A} (t:array A) (i j:int) (v:A),
  index t j -> i<>j -> (t\(i:=v))\(j) = t\(j).
Axiom array_make_read : forall `{Inhab A} (i n:int) (v:A),
  index n i -> (make n v)\(i) = v.

Axiom index_update : forall `{Inhab A} (T:array A) i j (v:A),
  index T i -> index (T\(j:=v)) i.
Axiom index_make : forall `{Inhab A} n i (v:A),
  index n i -> index (make n v) i.
Axiom index_array_length_eq : forall A (t : array A) i,
  index (length t) i -> index t i.
Axiom length_make : forall A n (v:A),
  length (make n v) = n.



Hint Rewrite @array_make_read @length_update @array_update_read_eq @array_update_read_neq : rew_array.

Tactic Notation "rew_array" := 
  autorewrite with rew_array.
Tactic Notation "rew_array" "in" hyp(H) := 
  autorewrite with rew_array in H.
Tactic Notation "rew_array" "in" "*" := 
  autorewrite with rew_array in *.

Tactic Notation "rew_array" "~" :=
  rew_array; auto_tilde.
Tactic Notation "rew_array" "*" :=
  rew_array; auto_star.
Tactic Notation "rew_array" "~" "in" hyp(H) :=
  rew_array in H; auto_tilde.
Tactic Notation "rew_array" "*" "in" hyp(H) :=
  rew_array in H; auto_star.

(* todo : fix bug in rewriting order *)

Hint Rewrite @array_update_read_eq : rew_arr.

Tactic Notation "rew_arr" := 
  autorewrite with rew_arr.
Tactic Notation "rew_arr" "in" hyp(H) := 
  autorewrite with rew_arr in H.
Tactic Notation "rew_arr" "in" "*" := 
  autorewrite with rew_arr in *.

Tactic Notation "rew_arr" "~" :=
  rew_arr; auto_tilde.
Tactic Notation "rew_arr" "*" :=
  rew_arr; auto_star.
Tactic Notation "rew_arr" "~" "in" hyp(H) :=
  rew_arr in H; auto_tilde.
Tactic Notation "rew_arr" "*" "in" hyp(H) :=
  rew_arr in H; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Structural properties

Section Instances.
Variables (A:Type).

Transparent map empty_inst single_bind_inst binds_inst
 union_inst dom_inst disjoint_inst.

Global Instance map_union_empty_l : Union_empty_l (T:=map A B).
Proof. 
  constructor. intros_all. simpl.
  unfold union_impl, empty_impl, map. simpl. extens~.
Qed.

Global Instance map_union_assoc : Union_assoc (T:=map A B).
Proof. 
  constructor. intros M N P. simpl.
  unfold union_impl, map. extens.
  intros k. destruct~ (M k).
Qed.

End Instances.

*)

(* ********************************************************************** *)
(** * Fold *)

Parameter fold_left : 
  forall A B (f:A->B->B) (t:array A) (b:B), B.

(* ********************************************************************** *)
(** * Count *)

Require Import LibWf.

Parameter count : 
  forall A (f:A->Prop) (t:array A), int.

Parameter count_make : forall A (f:A->Prop) n v,
  count f (make n v) = (If f v then n else 0).

Parameter count_update : forall `{Inhab A} (f:A->Prop) (t:array A) i v,
  count f (t\(i:=v)) = count f t
    - (If f (t\(i)) then 1 else 0)
    + (If f v then 1 else 0).

Parameter count_bounds : forall `{Inhab A} (t:array A) (f:A->Prop),
  0 <= count f t <= length t.

Lemma array_count_upto : forall `{Inhab A} (P:A->Prop) (t:array A) n i v,
  ~ P (t\(i)) -> P v -> length t <= n ->
  upto n (count P (t\(i:=v))) (count P t).
Proof.
  introv Ni Pv Le. forwards K: (count_bounds (t\(i:=v)) P). split.
  rewrite length_update in K. math.
  lets M: (@count_update A _). rewrite M. clear M. 
  do 2 (case_if; tryfalse). math.
Qed.

