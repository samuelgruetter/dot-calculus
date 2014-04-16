(**************************************************************************
* Product of Data Structures                                              *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic.


(* ********************************************************************** *)
(** * Inhabited  *)

Instance unit_inhab : Inhab unit.
Proof. intros. apply (prove_Inhab tt). Qed.


(* ********************************************************************** *)
(** * Structure *)

Lemma unit_unique : forall tt1 tt2 : unit,
  tt1 = tt2.
Proof. intros. destruct tt1. destruct~ tt2. Qed.


