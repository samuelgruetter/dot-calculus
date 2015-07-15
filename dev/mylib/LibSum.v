(**************************************************************************
* TLC: A library for Coq                                                  *
* Sum of Data Structures                                                  *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibBool.
Generalizable Variables A B.

(* ********************************************************************** *)
(** * Fixing implicit types *)

Implicit Arguments inl [[A] [B]].
Implicit Arguments inr [[A] [B]].


(* ********************************************************************** *)
(** * Inhabited *)

Instance sum_inhab_left : forall `{Inhab A} B, Inhab (A + B).
Proof. intros. apply (prove_Inhab (inl arbitrary)). Qed.
Instance sum_inhab_right : forall `{Inhab B} A, Inhab (A + B).
Proof. intros. apply (prove_Inhab (inr arbitrary)). Qed.

Definition sum_inhab : forall `{Inhab A, Inhab B}, Inhab (A + B).
Proof. typeclass. Qed. 


(* ********************************************************************** *)
(** * Operations *)

Section IsIn.
Variables (A B : Type).
Implicit Type x : A + B.

Definition is_inl x :=
  match x with
  | inl _ => true
  | inr _ => false
  end. 

Definition is_inr x :=
  match x with
  | inl _ => false
  | inr _ => true
  end. 

Lemma is_inl_neg_is_inr : forall x,
  is_inl x = ! (is_inr x).
Proof. intros x. destruct~ x. Qed.

Lemma is_inr_neg_is_inl : forall x,
  is_inr x = ! (is_inl x).
Proof. intros x. destruct~ x. Qed.

End IsIn.


(* ********************************************************************** *)
(** * Projections *)

(*-----------------------------------------------------*)
(** ** Stripping of the branch tag *)

Section Get.
Variables (A1 A2 : Type) (DA1:Inhab A1) (DA2:Inhab A2). 
Implicit Types x : A1+A2.

Definition get21 x :=
  match x with
  | inl x1 => x1
  | inr x2 => arbitrary
  end. 

Definition get22 x :=
  match x with
  | inl x1 => arbitrary
  | inr x2 => x2
  end. 

End Get.

Implicit Arguments get21 [[A1] [A2] [DA1]].
Implicit Arguments get22 [[A1] [A2] [DA2]].


(*-----------------------------------------------------*)
(** ** Lifting functions over sum types *)

Section Fget.
Variables (A1 A2 B1 B2 : Type) 
  (DB1:Inhab B1) (DB2:Inhab B2).
Implicit Types f : A1+A2->B1+B2.

Definition func_get21 f :=
  fun x => get21 (f (inl x)).
Definition func_get22 f :=
  fun x => get22 (f (inr x)).

End Fget.

Implicit Arguments func_get21 [[A1] [A2] [B1] [B2] [DB1]].
Implicit Arguments func_get22 [[A1] [A2] [B1] [B2] [DB2]].

