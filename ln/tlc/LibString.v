(**************************************************************************
* TLC: A library for Coq                                                  *
* Strings                                                                 *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibReflect.
Require Export String.

(* ********************************************************************** *)
(** * Inhabited and comparable *)

Instance string_inhab : Inhab string.
Proof. apply (prove_Inhab EmptyString). Qed.

Instance string_comparable : Comparable string.
Proof. applys comparable_of_dec string_dec. Qed.