(**************************************************************************
* TLC: A library for Coq                                                  *
* Mathematical structures                                                 *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibOperation.
Generalizable Variables A B.

(* ********************************************************************** *)
(** * Monoids *)

Record monoid_def (A:Type) : Type := monoid_ { 
   monoid_oper : oper2 A;
   monoid_neutral : A }.

Class Monoid (A:Type) (m:monoid_def A) : Prop := {
   monoid_assoc_prop : let (o,n) := m in assoc o;
   monoid_neutral_l_prop : let (o,n) := m in neutral_l o n;
   monoid_neutral_r_prop : let (o,n) := m in neutral_r o n }.

Section MonoidProp.
Context {A:Type} {m:monoid_def A}.
Class Monoid_assoc := {
  monoid_assoc : assoc (monoid_oper m) }.
Class Monoid_neutral_l := {
  monoid_neutral_l : neutral_l (monoid_oper m) (monoid_neutral m) }.
Class Monoid_neutral_r := {
  monoid_neutral_r : neutral_r (monoid_oper m) (monoid_neutral m) }.
End MonoidProp.

Section MonoidInst.
Context {A:Type} {m:monoid_def A} {M:Monoid m}.
Global Instance Monoid_Monoid_assoc : Monoid_assoc (m:=m).
Proof.
  constructor. destruct M as [U ? ?]. destruct m. simpl. apply U.
Qed.
Global Instance Monoid_Monoid_neutral_l : Monoid_neutral_l (m:=m).
Proof.
  constructor. destruct M as [? U ?]. destruct m. simpl. apply U.
Qed.
Global Instance Monoid_Monoid_neutral_r : Monoid_neutral_r (m:=m).
Proof.
  constructor. destruct M as [? ? U]. destruct m. simpl. apply U.
Qed.
End MonoidInst.

