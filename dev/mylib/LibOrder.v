(**************************************************************************
* TLC: A library for Coq                                                  *
* Order relations                                                         *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect LibOperation LibRelation.
Generalizable Variables A.

(**************************************************************************)
(* * Preorder *)

(** Definition *)

Record preorder (A:Type) (R:binary A) : Prop := {  
   preorder_refl : refl R; 
   preorder_trans : trans R }.

Implicit Arguments preorder_trans [A R p x z].

(** Transformations *)

Lemma preorder_flip : forall A (R:binary A),
  preorder R -> preorder (flip R).
Proof. introv [Re Tr]. constructor; auto~ flip_trans. Qed. 

Lemma preorder_large : forall A (R:binary A),
  preorder R -> preorder (large R).
Proof. introv [Re Tr]. constructor; auto~ large_refl large_trans. Qed.


(**************************************************************************)
(* * Total preorder *)

(** Definition of total preorder relations *)

Record total_preorder (A:Type) (R:binary A) : Prop := { 
   total_preorder_trans : trans R;
   total_preorder_total : total R }.

Implicit Arguments total_preorder_trans [A R x z].

(** Conversion to preorder *)

Lemma total_preorder_refl : forall A (le:binary A),
  total_preorder le -> refl le.
Proof. introv [Tr To]. intros x. destruct~ (To x x). Qed.

Hint Resolve total_preorder_refl.

Coercion total_preorder_to_preorder A (R:binary A)
  (O:total_preorder R) : preorder R.
Proof. lets [M _]: O. constructor~. Qed.

Hint Resolve total_preorder_to_preorder.

(** Transformations *)

Lemma total_preorder_flip : forall A (R:binary A),
  total_preorder R -> total_preorder (flip R).
Proof. introv [Tr To]. constructor; auto~ flip_trans flip_total. Qed.

Lemma total_preorder_large : forall A (R:binary A),
  total_preorder R -> total_preorder (large R).
Proof. introv [Re Tr]. constructor; auto~ large_trans large_total. Qed.

(** Properties *)

Lemma flip_from_not : forall A (R:binary A) x y,
  total R -> ~ R x y -> flip R x y.
Proof. introv T H. destruct (T x y); auto_false~. Qed.

Lemma flip_strict_from_not : forall A (R:binary A) x y,
  total R -> ~ R x y -> flip (strict R) x y.
Proof. 
  introv T H. destruct (T x y). auto_false~. 
  hnf. split~. intro_subst~. 
Qed.


(**************************************************************************)
(* * Order *)

(** Definition *)

Record order (A:Type) (R:binary A) : Prop := { 
   order_refl : refl R; 
   order_trans : trans R;
   order_antisym : antisym R }.

Implicit Arguments order_trans [A R o x z].
Implicit Arguments order_antisym [A R o x y].

(** Conversion to preorder *)

Coercion order_to_preorder (A:Type) (R:binary A) 
  (O:order R) : preorder R.
Proof. destruct* O. Qed.

Hint Resolve order_to_preorder.

(** Transformations *)

Lemma order_flip : forall A (R:binary A),
  order R -> order (flip R).
Proof. 
  introv [Re Tr An]. constructor; 
  auto~ flip_trans flip_antisym. 
Qed.

Lemma order_large : forall A (R:binary A),
  order R -> order (large R).
Proof. 
  introv [Re Tr An]. constructor; 
  auto~ large_refl large_trans large_antisym. 
Qed.

(** Properties *)


(**************************************************************************)
(* * Total Order *)

(** Definition *)

Record total_order (A:Type) (R:binary A) : Prop := { 
   total_order_order :> order R; 
   total_order_total : total R }.

(** Projections *)

Definition total_order_refl := order_refl.
Definition total_order_trans := order_trans.
Definition total_order_antisym := order_antisym.

Implicit Arguments total_order_trans [A R o x z].
Implicit Arguments total_order_antisym [A R o x y].

(** Construction *)

Lemma total_order_intro : forall A (R:binary A),
   trans R -> antisym R -> total R -> total_order R.
Proof.
  introv Tra Ant Tot. constructor~. constructor~.
  intros_all. destruct~ (Tot x x).
Qed.

(** Conversion to order *)

Coercion total_order_to_total_preorder (A:Type) (R:binary A) 
  (O:total_order R) : total_preorder R.
Proof. destruct* O. Qed.

Definition total_order_to_order := total_order_order.

Hint Resolve total_order_to_order total_order_to_total_preorder.

(** Transformations *)

Lemma total_order_flip : forall A (R:binary A),
  total_order R -> total_order (flip R).
Proof. 
  introv [Or To]. constructor; 
  auto~ flip_total order_flip.
Qed.

Lemma total_order_large : forall A (R:binary A),
  total_order R -> total_order (large R).
Proof. 
  introv [Or To]. constructor; 
  auto~ large_total order_large.
Qed.

(** Properties *)

Section TotalOrderProp.
Variables (A:Type) (R:binary A) (To:total_order R).
Notation "'le'" := (R).
Notation "'ge'" := (flip R).
Notation "'lt'" := (strict R).
Notation "'gt'" := (flip lt).

Hint Unfold strict flip.

Lemma total_order_le_is_large_lt : 
  le = large lt. 
Proof.
  extens. intros. unfold large, strict. iff H.
  tests~: (x = y).
  destruct H. auto*. subst*.
Qed. 

Lemma total_order_ge_is_large_gt : 
  ge = large gt. 
Proof.
  extens. intros. unfold large, flip, strict. iff H.
  tests~: (x = y).
  destruct H. auto*. subst*.
Qed. 

Lemma total_order_lt_or_eq_or_gt : forall x y,
  lt x y \/ x = y \/ gt x y.
Proof.
  intros. tests: (x = y). 
    branch~ 2. 
    destruct (total_order_total To x y).
     branch~ 1. 
     branch~ 3. 
Qed.

Lemma total_order_lt_or_ge : forall x y,
  lt x y \/ ge x y. 
Proof. 
  intros. branches (total_order_lt_or_eq_or_gt x y).
  left~.
  right~. subst. hnf. apply~ total_order_refl.
  right~. rewrite total_order_ge_is_large_gt. hnfs~.
Qed.

Lemma total_order_le_or_gt : forall x y,
  le x y \/ gt x y. 
Proof. 
  intros. branches (total_order_lt_or_eq_or_gt x y).
  left~. rewrite total_order_le_is_large_lt. hnfs~.
  left~. subst. apply~ total_order_refl.
  right~. 
Qed.

End TotalOrderProp.


(**************************************************************************)
(* * Strict order *)

(** Definition *)

Record strict_order (A:Type) (R:binary A) : Prop := {  
   strict_order_irrefl : irrefl R; 
   strict_order_asym : asym R;
   strict_order_trans : trans R }.

Implicit Arguments strict_order_trans [A R s x z].

(** Transformations *)

Lemma strict_order_flip : forall A (R:binary A),
  strict_order R -> strict_order (flip R).
Proof. 
  introv [Ir As Tr]. constructor; 
  auto~ flip_antisym flip_trans flip_asym.
Qed.

Lemma strict_order_strict : forall (A:Type) (R:binary A),
  order R -> strict_order (strict R).
Proof.
  introv [Re As Tr]. unfold strict. constructor; intros_all; simpls.
  destruct* H. 
  applys* antisym_elim.
  split. applys* As. intros_all. subst. applys* antisym_elim.
Qed.

Lemma order_from_strict : forall (A:Type) (R:binary A),
  strict_order R -> order (large R).
Proof.
  introv [Re As Tr]. unfold large. constructor; simpl.
  intros_all~.
  introv [H1|E1] [H2|E2]; subst; auto.
    left. apply* trans_elim.
  introv [H1|E1] [H2|E2]; try subst; auto.
    false. apply* As.
Qed.


(**************************************************************************)
(* * Total strict order *)

(** Trichotomy *) 
(* todo: move *)

Inductive trichotomy (A:Type) (R:binary A) : binary A :=
  | trichotomy_left: forall x y, 
      R x y -> x <> y -> ~ R y x -> trichotomy R x y
  | trichotomy_eq : forall x, 
      ~ R x x -> trichotomy R x x
  | trichotomy_right : forall x y, 
      ~ R x y -> x <> y -> R y x -> trichotomy R x y.

Definition trichotomous (A:Type) (R:binary A) :=
  forall x y, trichotomy R x y.

Lemma flip_trichotomous : forall (A:Type) (R:binary A),
  trichotomous R -> trichotomous (flip R).
Proof.
  introv H. intros x y. destruct (H x y).
  apply~ trichotomy_right.
  apply~ trichotomy_eq.
  apply~ trichotomy_left.
Qed. 

(** Definition *)

Record strict_total_order (A:Type) (R:binary A) : Prop := { 
   strict_total_order_trans : trans R;
   strict_total_order_trichotomous : trichotomous R }.

Implicit Arguments strict_total_order_trans [A R s x z].

(** Conversion to strict order and back *)

Lemma strict_total_order_irrefl : forall A (R:binary A),
  strict_total_order R -> irrefl R.
Proof. introv [Tr Tk]. intros x. lets: (Tk x x). inverts~ H. Qed.

Lemma strict_total_order_asym : forall A (R:binary A),
  strict_total_order R -> asym R.
Proof. introv [Tr Tk]. intros x y. lets: (Tk x y). inverts~ H. Qed.

Coercion strict_total_order_to_strict_order A (R:binary A)
  (O:strict_total_order R) : strict_order R.
Proof.
  lets [M _]: O. constructor;
  auto~ strict_total_order_irrefl strict_total_order_asym. 
Qed.

Hint Resolve strict_total_order_to_strict_order.

(** Transformation *)

Lemma strict_total_order_flip : forall A (R:binary A),
  strict_total_order R -> strict_total_order (flip R).
Proof. 
  introv [Tr Tk]. constructor. apply~ flip_trans.
  apply~ flip_trichotomous.
Qed.
(** From total order *)

Lemma strict_total_order_from_total_order : forall (A:Type) (R:binary A),
  total_order R -> strict_total_order (strict R).
Proof.
  introv [[Re Tr As] To]. constructor. 
  apply~ trans_strict.
  intros x y. tests: (x = y).
    subst. apply trichotomy_eq. unfolds* strict.
    unfold strict. destruct (To x y).
      apply* trichotomy_left.
      apply* trichotomy_right.
Qed.


(* ********************************************************************** *)
(** * Definition of order operators *)

(* ---------------------------------------------------------------------- *)
(** ** Classes and notation for comparison operators *)

(** Operators *)

Class Le (A : Type) := { le : binary A }.
Class Ge (A : Type) := { ge : binary A }.
Class Lt (A : Type) := { lt : binary A }.
Class Gt (A : Type) := { gt : binary A }.

Global Opaque le lt ge gt.

(** Structures *)

Class Le_preorder `{Le A} : Prop :=
  { le_preorder : preorder le }.

Class Le_total_preorder `{Le A} : Prop :=
  { le_total_preorder : total_preorder le }.

Class Le_order `{Le A} : Prop :=
  { le_order : order le }.

Class Le_total_order `{Le A} : Prop :=
  { le_total_order : total_order le }.

Class Lt_strict_order `{Lt A} : Prop :=
  { lt_strict_order : strict_order lt }.

Class Lt_strict_total_order `{Lt A} : Prop :=
  { lt_strict_total_order : strict_total_order lt }.

(** Notation *)

Notation "x <= y" := (le x y)
  (at level 70, no associativity) : comp_scope.
Notation "x >= y" := (ge x y)
  (at level 70, no associativity) : comp_scope.
Notation "x < y" := (lt x y)
  (at level 70, no associativity) : comp_scope.
Notation "x > y" := (gt x y)
  (at level 70, no associativity) : comp_scope.

Open Scope comp_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z)
  (at level 70, y at next level) : comp_scope.
Notation "x <= y < z" := (x <= y /\ y < z)
  (at level 70, y at next level) : comp_scope.
Notation "x < y <= z" := (x < y /\ y <= z)
  (at level 70, y at next level) : comp_scope.
Notation "x < y < z" := (x < y /\ y < z)
  (at level 70, y at next level) : comp_scope.


(* ---------------------------------------------------------------------- *)
(** ** The operators [ge], [lt] and [gt] are deduced from [le] *)

Instance ge_from_le : forall `{Le A}, Ge A.
  constructor. apply (flip le). Defined.
Instance lt_from_le : forall `{Le A}, Lt A.
  constructor. apply (strict le). Defined.
Instance gt_from_le : forall `{Le A}, Gt A.
  constructor. apply (flip lt). Defined.

Lemma ge_is_flip_le : forall `{Le A}, ge = flip le.
Proof. intros. apply* prop_ext_2. Qed.
Lemma lt_is_strict_le : forall `{Le A}, lt = strict le.
Proof. intros. apply* prop_ext_2. Qed.
Lemma gt_is_flip_lt : forall `{Le A}, gt = flip lt.
Proof. intros. apply* prop_ext_2. Qed.
Lemma gt_is_flip_strict_le : forall `{Le A}, gt = flip (strict le).
Proof. intros. rewrite gt_is_flip_lt. rewrite~ lt_is_strict_le. Qed.

Global Opaque ge_from_le lt_from_le gt_from_le.
Hint Rewrite @gt_is_flip_strict_le @ge_is_flip_le @lt_is_strict_le : rew_to_le_def.
Tactic Notation "rew_to_le" := 
  autorewrite with rew_to_le_def in *.

Hint Rewrite @ge_is_flip_le @gt_is_flip_lt : rew_to_le_lt_def.
Tactic Notation "rew_to_le_lt" := 
  autorewrite with rew_to_le_lt_def in *.

Lemma gt_is_strict_flip_le : forall `{Le A}, gt = strict (flip le).
Proof. intros. rew_to_le. apply flip_strict. Qed.
Lemma le_is_large_lt : forall `{Le A},
  refl le -> le = large lt.
Proof. intros. rew_to_le. rewrite~ large_strict. Qed.
Lemma le_is_flip_ge : forall `{Le A}, le = flip ge.
Proof. intros. rew_to_le. rewrite~ flip_flip. Qed.
Lemma lt_is_flip_gt : forall `{Le A}, lt = flip gt.
Proof. intros. rew_to_le. rewrite~ flip_flip. Qed.
Lemma gt_is_strict_ge : forall `{Le A}, gt = strict ge.
Proof. intros. rew_to_le. apply flip_strict. Qed.
Lemma ge_is_large_gt : forall `{Le A},  
  refl le -> ge = large gt.
Proof. intros. rewrite gt_is_strict_ge. rewrite~ large_strict. Qed.


(* ********************************************************************** *)
(** * Classes for comparison properties *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of classes *)

(** symmetric structure *)

Class Ge_preorder `{Le A} : Prop :=
  { ge_preorder : preorder ge }.
Class Ge_total_preorder `{Le A} : Prop :=
  { ge_total_preorder : total_preorder ge }.
Class Ge_order `{Le A} : Prop :=
  { ge_order : order ge }.
Class Ge_total_order `{Le A} : Prop :=
  { ge_total_order : total_order le }.
Class Gt_strict_order `{Le A} : Prop :=
  { gt_strict_order : strict_order gt }.
Class Gt_strict_total_order `{Le A} : Prop :=
  { gt_strict_total_order : strict_total_order gt }.

(** properties of le *)

Class Le_refl `{Le A} := 
  { le_refl : refl le }.
Class Le_trans `{Le A} := 
  { le_trans : trans le }.
Class Le_antisym `{Le A} := 
  { le_antisym : antisym le }.
Class Le_total `{Le A} := 
  { le_total : total le }.

(** properties of ge *)

Class Ge_refl `{Ge A} := 
  { ge_refl : refl ge }.
Class Ge_trans `{Ge A} := 
  { ge_trans : trans ge }.
Class Ge_antisym `{Ge A} := 
  { ge_antisym : antisym ge }.
Class Ge_total `{Ge A} := 
  { ge_total : total ge }.

(** properties of lt *)

Class Lt_irrefl `{Lt A} := 
  { lt_irrefl : irrefl lt }.
Class Lt_trans `{Lt A} := 
  { lt_trans : trans lt }.

(** properties of gt *)

Class Gt_irrefl `{Gt A} := 
  { gt_irrefl : irrefl gt }.
Class Gt_trans `{Gt A} := 
  { gt_trans : trans gt }.

(** mixed transitivity results *)

Class Lt_Le_trans `{Le A} := 
  { lt_le_trans : forall y x z, x < y -> y <= z -> x < z }.
Class Le_Lt_trans `{Le A} := 
  { le_lt_trans : forall y x z, x <= y -> y < z -> x < z }.
Class Gt_Ge_trans `{Le A} := 
  { gt_ge_trans : forall y x z, x > y -> y >= z -> x > z }.
Class Ge_Gt_trans `{Le A} := 
  { ge_gt_trans : forall y x z, x >= y -> y > z -> x > z }.

Implicit Arguments lt_irrefl [A H Lt_irrefl]. 
Implicit Arguments le_trans [[A] [H] [Le_trans] x z].
Implicit Arguments ge_trans [[A] [H] [Ge_trans] x z].
Implicit Arguments lt_trans [[A] [H] [Lt_trans] x z].
Implicit Arguments gt_trans [[A] [H] [Gt_trans] x z].

(** conversion between operators *)

Class Ge_As_SLe `{Le A} : Prop :=
  { ge_as_sle : forall x y : A, (x >= y) = (y <= x) }.

Class Gt_As_SLt `{Le A} : Prop :=
  { gt_as_slt : forall x y : A, (x > y) = (y < x) }.

Class NGt_As_SLe `{Le A} : Prop :=
  { ngt_as_sle : forall x y : A, (~ x < y) = (y <= x) }.

Class NLt_As_Ge `{Le A} : Prop :=
  { nlt_as_ge : forall x y : A, (~ x < y) = (x >= y) }.

Class NGt_As_Le `{Le A} : Prop :=
  { ngt_as_le : forall x y : A, (~ x > y) = (x <= y) }.

Class NLe_As_Gt `{Le A} : Prop :=
  { nle_as_gt : forall x y : A, (~ x <= y) = (x > y) }.

Class NGe_As_Lt `{Le A} : Prop :=
  { nge_as_lt : forall x y : A, (~ x >= y) = (x < y) }.

(** inclusion between operators *)

Class Lt_to_Le `{Le A} : Prop :=
  { lt_to_le : forall x y : A, (x < y) -> (x <= y) }.

Class Gt_to_Ge `{Le A} : Prop :=
  { gt_to_ge : forall x y : A, (x > y) -> (x >= y) }.

Class NLe_to_SLe `{Le A} : Prop :=
  { nle_to_sle : forall x y : A, (~ x <= y) -> (y <= x) }.

Class NLe_to_SLt `{Le A} : Prop :=
  { nle_to_slt : forall x y : A, (~ x <= y) -> (y < x) }.

(** case analysis *)

Class Case_Eq_Lt_Gt `{Le A} : Prop :=
  { case_eq_lt_gt : forall x y : A, x = y \/ x < y \/ x > y }.

Class Case_Eq_Lt_SLt `{Le A} : Prop :=
  { case_eq_lt_slt : forall x y : A, x = y \/ x < y \/ y < x }.

Class Case_Le_Gt `{Le A} : Prop :=
  { case_le_gt : forall x y : A, x <= y \/ x > y }.

Class Case_Le_SLt `{Le A} : Prop :=
  { case_le_slt : forall x y : A, x <= y \/ y < x }.

Class Case_Lt_Ge `{Le A} : Prop :=
  { case_lt_ge : forall x y : A, x < y \/ x >= y }.

Class Case_Lt_SLe `{Le A} : Prop :=
  { case_lt_sle : forall x y : A, x < y \/ y <= x }.

(** case analysis under one assumption *)

Class Neq_Case_Lt_Gt `{Le A} : Prop :=
  { neq_case_lt_gt : forall x y : A, x <> y -> x < y \/ x > y }.

Class Neq_Case_Lt_SLt `{Le A} : Prop :=
  { neq_case_lt_slt : forall x y : A, x <> y -> x < y \/ y < x }.

Class Le_Case_Eq_Lt `{Le A} : Prop :=
  { le_case_eq_lt : forall x y : A, x <= y -> x = y \/ x < y }.

Class Ge_Case_Eq_Gt `{Le A} : Prop :=
  { ge_case_eq_gt : forall x y : A, x >= y -> x = y \/ x > y }.

(** case analysis under two assumptions *)

Class Le_NEq_To_Lt `{Le A} : Prop :=
  { le_neq_to_lt : forall x y : A, x <= y -> x <> y -> x < y }.

Class Ge_NEq_To_Gt `{Le A} : Prop :=
  { ge_neq_to_gt : forall x y : A, x >= y -> x <> y -> x > y }.

Class NLt_NSLt_To_Eq `{Le A} : Prop := 
  { nlt_nslt_to_eq : forall x y : A, ~ (lt x y) -> ~ (lt y x) -> x = y }.

(** contradiction from case analysis *)

Class Lt_Ge_false `{Le A} : Prop :=
  { lt_ge_false : forall x y : A, x < y -> x >= y -> False }.

Class Lt_Gt_false `{Le A} : Prop :=
  { lt_gt_false : forall x y : A, x < y -> x > y -> False }.

Class Lt_SLt_false `{Le A} : Prop :=
  { lt_slt_false : forall x y : A, x < y -> y < x -> False }.


(* ********************************************************************** *)
(* * Instances for comparison structures *)

Section Instances.
Context `{Le A}.

(** derived structures *)

Global Instance le_preorder_from_le_order :
  Le_order -> Le_preorder.
Proof. constructor. intros. apply* order_to_preorder. Qed.

Global Instance le_total_preorder_from_le_total_order :
  Le_total_order -> Le_total_preorder.
Proof. constructor. intros. apply* total_order_to_total_preorder. Qed.

Global Instance le_preorder_from_total_preorder :
  Le_total_preorder -> Le_preorder.
Proof. constructor. intros. apply* total_preorder_to_preorder. Qed.

Global Instance le_order_from_le_total_order :
  Le_total_order -> Le_order.
Proof. constructor. intros. apply* total_order_to_order. Qed.

Global Instance lt_strict_order_from_lt_strict_total_order :
  Lt_strict_total_order -> Lt_strict_order.
Proof. constructor. intros. apply* strict_total_order_to_strict_order. Qed.

Global Instance lt_strict_order_from_le_order :
  Le_order -> Lt_strict_order.
Proof. constructor. intros. rew_to_le. apply* strict_order_strict. Qed.

Global Instance lt_strict_total_order_from_le_total_order :
  Le_total_order -> Lt_strict_total_order.
Proof. constructor. intros. rew_to_le. apply* strict_total_order_from_total_order. Qed.

(** symmetric structures *)

Global Instance ge_preorder_from_le_order :
  Le_order -> Ge_preorder.
Proof. constructor. rew_to_le. apply preorder_flip. apply le_preorder. Qed.

Global Instance ge_total_preorder_from_le_total_order :
  Le_total_order -> Ge_total_preorder.
Proof. constructor. rew_to_le. apply total_preorder_flip. apply le_total_preorder. Qed.

Global Instance ge_preorder_from_total_preorder :
  Le_total_preorder -> Ge_preorder.
Proof. constructor. rew_to_le. apply preorder_flip. apply le_preorder. Qed.

Global Instance ge_order_from_le_total_order :
  Le_total_order -> Ge_order.
Proof. constructor. rew_to_le. apply order_flip. apply le_order. Qed.

Global Instance gt_strict_order_from_lt_strict_total_order :
  Lt_strict_total_order -> Gt_strict_order.
Proof. constructor. rewrite gt_is_flip_lt. apply strict_order_flip. apply lt_strict_order. Qed.

Global Instance gt_strict_order_from_le_order :
  Le_order -> Gt_strict_order.
Proof. constructor. rewrite gt_is_flip_lt. apply strict_order_flip. apply lt_strict_order. Qed.

Global Instance gt_strict_total_order_from_le_total_order :
  Le_total_order -> Gt_strict_total_order.
Proof. constructor. rewrite gt_is_flip_lt. apply strict_total_order_flip. apply lt_strict_total_order. Qed.

(** properties of le *)

Global Instance le_refl_from_le_preorder :
  Le_preorder -> Le_refl. 
Proof. intros [[Re Tr]]. constructor~. Qed.

Global Instance le_trans_from_le_preorder :
  Le_preorder -> Le_trans. 
Proof. intros [[Re Tr]]. constructor~. Qed.

Global Instance le_antisym_from_le_order :
  Le_order -> Le_antisym.
Proof. constructor. intros. apply* order_antisym. Qed.

Global Instance le_total_from_le_total_order :
  Le_total_order -> Le_total.
Proof. constructor. intros. apply* total_order_total. Qed.

(** properties of ge *)

Global Instance ge_refl_from_le_preorder :
  Le_preorder -> Ge_refl. 
Proof. constructor. rew_to_le. apply flip_refl. apply le_refl. Qed.

Global Instance ge_trans_from_le_preorder :
  Le_preorder -> Ge_trans. 
Proof. constructor. rew_to_le. apply flip_trans. apply le_trans. Qed.

Global Instance ge_antisym_from_le_order :
  Le_order -> Ge_antisym.
Proof. constructor. rew_to_le. apply flip_antisym. apply le_antisym. Qed.

Global Instance ge_total_from_le_total_order :
  Le_total_order -> Ge_total.
Proof. constructor. rew_to_le. apply flip_total. apply le_total. Qed.

(** properties of lt *)

Global Instance lt_irrefl_from_le_order :
  Le_order -> Lt_irrefl. 
Proof. constructor. apply strict_order_irrefl. apply lt_strict_order. Qed.

Global Instance lt_trans_from_le_order :
  Le_order -> Lt_trans. 
Proof. constructor. apply strict_order_trans. apply lt_strict_order. Qed.

(** properties of gt *)

Global Instance gt_irrefl_from_le_order :
  Le_order -> Gt_irrefl. 
Proof. constructor. apply strict_order_irrefl. apply gt_strict_order. Qed.

Global Instance gt_trans_from_le_order :
  Le_order -> Gt_trans. 
Proof. constructor. apply strict_order_trans. apply gt_strict_order. Qed.

(** mixed transitivity results *)

Global Instance lt_le_trans_from : Le_order -> Lt_Le_trans. 
Proof.
  constructor. introv K L. rew_to_le. destruct K as [U V].
  split~. apply* le_trans. intro_subst. apply V. apply* le_antisym.
Qed.

Global Instance le_le_trans_from : Le_order -> Le_Lt_trans. 
Proof.
  constructor. introv K L. rew_to_le. destruct L as [U V].
  split~. apply* le_trans. intro_subst. apply V. apply* le_antisym.
Qed.

Global Instance gt_ge_trans_from : Le_order -> Gt_Ge_trans. 
Proof.
  constructor. introv K L. rew_to_le_lt. hnf in *. apply* le_lt_trans.
Qed.

Global Instance ge_gt_trans_from : Le_order -> Ge_Gt_trans. 
Proof.
  constructor. introv K L. rew_to_le_lt. hnf in *. apply* lt_le_trans.
Qed.
(** conversion between operators *)

Global Instance ge_as_sle_from : Ge_As_SLe.
Proof. constructor. intros. rew_to_le. auto. Qed.

Global Instance gt_as_slt_from : Gt_As_SLt.
Proof. constructor. intros. rew_to_le. auto. Qed.

Global Instance ngt_as_sle_from : Le_total_order -> NGt_As_SLe. 
Proof.
  constructor. intros. rew_to_le. unfold strict. rew_logic. iff M.
  destruct M.  
    forwards K:(flip_strict_from_not (R:=le)); eauto.
      apply le_total. apply (proj1 K). 
    subst. apply le_refl.
  apply classic_left. intros P Q. apply P. apply* le_antisym. 
Qed.

Global Instance nlt_as_ge_from : Le_total_order -> NLt_As_Ge. 
Proof. constructor. intros. rew_to_le_lt. unfold flip. apply ngt_as_sle. Qed.

Global Instance ngt_as_le_from : Le_total_order -> NGt_As_Le. 
Proof. constructor. intros. rew_to_le_lt. unfold flip. apply ngt_as_sle. Qed.

Global Instance nle_as_gt_from : Le_total_order -> NLe_As_Gt.
Proof.
  constructor. intros. rew_to_le_lt. unfold flip.
  rewrite* <- ngt_as_sle. rewrite~ not_not. 
Qed.

Global Instance nge_as_lt_from : Le_total_order -> NGe_As_Lt. 
Proof.
  constructor. intros. rew_to_le_lt. unfold flip. 
  rewrite nle_as_gt. rewrite~ gt_is_flip_lt. 
Qed.

(** inclusion between operators *)

Global Instance lt_to_le_from : Lt_to_Le.
Proof. constructor. intros. rew_to_le. unfolds* strict. Qed.

Global Instance gt_to_ge_from : Gt_to_Ge. 
Proof. constructor. intros. rew_to_le. unfolds* flip, strict. Qed.

Global Instance nle_to_sle_from : Le_total_order -> NLe_to_SLe.
Proof.
  constructor. introv K. rewrite nle_as_gt in K.
  rew_to_le. unfolds* flip, strict. 
Qed.

Global Instance nle_to_slt_from : Le_total_order -> NLe_to_SLt. 
Proof.
  constructor. introv K. rewrite nle_as_gt in K.
  rew_to_le. unfolds* flip, strict.
Qed.

(** case analysis *)

Global Instance case_eq_lt_gt_from : Le_total_order -> Case_Eq_Lt_Gt. 
Proof.
  constructor. intros.
  branches (total_order_lt_or_eq_or_gt le_total_order x y);
  hnf in *; auto *.
Qed.

Global Instance case_eq_lt_slt_from : Le_total_order -> Case_Eq_Lt_SLt.
Proof.
  constructor. intros. pattern lt at 2. rewrite lt_is_flip_gt.
  apply case_eq_lt_gt. 
Qed.

Global Instance case_le_gt_from : Le_total_order -> Case_Le_Gt. 
Proof.
  constructor. intros.
  branches (total_order_le_or_gt le_total_order x y);
  hnf in *; auto *.
Qed.

Global Instance case_eq_lt_ge_from : Le_total_order -> Case_Lt_Ge. 
Proof. 
  constructor. intros.
  branches (total_order_lt_or_ge le_total_order x y);
  hnf in *; auto *.
Qed.

Global Instance case_le_slt_from : Le_total_order -> Case_Le_SLt. 
Proof. constructor. intros. rewrite lt_is_flip_gt. apply case_le_gt. Qed.

Global Instance case_eq_lt_sle_from : Le_total_order -> Case_Lt_SLe. 
Proof. constructor. intros. rewrite le_is_flip_ge. apply case_lt_ge. Qed.

(** case analysis under one assumption *)

Global Instance neq_case_lt_gt_from : Le_total_order -> Neq_Case_Lt_Gt. 
Proof. constructor. intros. destruct* (case_eq_lt_gt x y). Qed.

Global Instance neq_case_lt_slt_from : Le_total_order -> Neq_Case_Lt_SLt. 
Proof. constructor. intros. destruct* (case_eq_lt_gt x y). Qed.

Global Instance le_case_eq_lt_from : Le_total_order -> Le_Case_Eq_Lt.
Proof. constructor. intros. rew_to_le. unfold strict. tests*: (x = y). Qed.

Global Instance ge_case_eq_gt_from : Le_total_order -> Ge_Case_Eq_Gt.
Proof. constructor. intros. rew_to_le. unfold flip, strict. tests*: (x = y). Qed.

(** case analysis under two assumptions *)

Global Instance le_neq_to_lt_from : Le_total_order -> Le_NEq_To_Lt.
Proof. constructor. intros. rew_to_le. hnfs*. Qed.

Global Instance ge_neq_to_gt_from : Le_total_order -> Ge_NEq_To_Gt. 
Proof. constructor. intros. rew_to_le. hnfs*. Qed.

Global Instance nlt_nslt_to_eq_from : Le_total_order -> NLt_NSLt_To_Eq. 
Proof. constructor. intros. branches* (case_eq_lt_gt x y). Qed.

(** contradiction from case analysis *)

Global Instance lt_ge_false_from : Le_total_order -> Lt_Ge_false.
Proof. constructor. introv H1 H2. rewrite~ <- nlt_as_ge in H2. Qed.

Global Instance lt_gt_false_from : Le_total_order -> Lt_Gt_false. 
Proof.
  constructor. introv H1 H2. rewrite~ <- nle_as_gt in H2. 
  apply H2. apply* lt_to_le.
Qed.

Global Instance lt_slt_false_from_le_order : 
  Le_total_order -> Lt_SLt_false.
Proof.
  constructor. introv H1 H2. rewrite <- gt_as_slt in H2.
  apply* lt_gt_false.
Qed.

End Instances.

Implicit Arguments nle_to_sle [[A] [H] [NLe_to_SLe] x y].



(* ********************************************************************** *)
(* * Order modulo -- todo: move *)

Record order_wrt (A:Type) (E:binary A) (R:binary A) : Prop := { 
   order_wrt_refl : refl R; 
   order_wrt_trans : trans R;
   order_wrt_antisym : antisym_wrt E R }.


(* ********************************************************************** *)
(** * Boolean comparison *)

Open Scope comp_scope.

Notation "x ''<=' y" := (isTrue (@le _ _ x y))
  (at level 70, no associativity) : comp_scope.
Notation "x ''>=' y" := (isTrue (@ge _ _ x y))
  (at level 70, no associativity) : comp_scope.
Notation "x ''<' y" := (isTrue (@lt _ _ x y))
  (at level 70, no associativity) : comp_scope.
Notation "x ''>' y" := (isTrue (@gt _ _ x y))
  (at level 70, no associativity) : comp_scope.


