(**************************************************************************
* TLC: A library for Coq                                                  *
* Reflection : Basic Operations on Booleans                               *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibOperation.

(* ********************************************************************** *)
(** * Properties of the boolean type *)

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

Instance bool_inhab : Inhab bool.
Proof. constructor. apply (prove_Inhab true). Qed.

(** For [Extensional bool] and [Comparable bool], see file LibReflect:
    These results are not in [LibBool] because they depend on definition
    from [LibReflect], which itself depends on [LibBool]. *)

(* ********************************************************************** *)
(** * Boolean Operations *)

(* TODO: is it possible to reuse the definition from the library? 
   It might be possible, but it requires to fix several proofs *)

Section Definitions.
Implicit Types x y z : bool.

(** ** Comparison *)

Definition beq_impl x y := 
  match x, y with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

(** Conjunction *)

Definition and x y :=
  match x, y with
  | true, true => true
  | _, _ => false
  end.

(** Disjunction *)

Definition or x y :=
  match x, y with
  | false, false => false
  | _, _ => true
  end.

(** Implication *)

Definition impl x y :=
  match x, y with
  | false, true => false
  | _, _ => true
  end.

(** Negation *)

Definition neg x :=
  match x with 
  | true => false
  | false => true
  end.

(** Exclusive or*)

Definition xor x y := 
  x <> y.

End Definitions.

(** Notations *)

Notation "! x" := (neg x) 
  (at level 35, right associativity) : Bool_scope.
Infix "&&" := and 
  (at level 40, left associativity) : Bool_scope.
Infix "||" := or 
  (at level 50, left associativity) : Bool_scope.

Notation "! x" := (neg x) 
  (at level 35, right associativity) : Bool_scope.
Infix "&&" := and 
  (at level 40, left associativity) : Bool_scope.
Infix "||" := or 
  (at level 50, left associativity) : Bool_scope.

Infix "&&&" := and 
  (at level 40, left associativity, only parsing) : Bool_scope.
Infix "|||" := or 
  (at level 50, left associativity, only parsing) : Bool_scope.
  (* todo: understand why there is a bug on the && *)

Bind Scope Bool_scope with bool.
Open Scope Bool_scope.



(* ********************************************************************** *)
(** * Boolean Decision Procedure : tactic working by exponential case
      analysis on all variables of type bool. *) 

(* ---------------------------------------------------------------------- *)
(** ** A first simple tactic named [tautob]. *)

Tactic Notation "tautob" := 
  let rec go _ :=
    (try intros_all); match goal with
    | b : bool |- _ => destruct b; clear b; go tt
    | _ => simpls; try split; intros; try discriminate
    end in go tt.

Tactic Notation "tautob" "~" := 
   tautob; auto.
Tactic Notation "tautob" "*" := 
   tautob; auto*.


(* ********************************************************************** *)
(** * Properties of booleans *) 

(* ---------------------------------------------------------------------- *)
(** ** Properties of [and], [or] and [neg] *)

(* todo: rename those lemmas according to convention (e.g. and_neutral_l) *)

Lemma or_same : idempotent2 or.
Proof. tautob~. Qed.

Lemma and_same : idempotent2 and.
Proof. tautob~. Qed.

Lemma neutral_l_and : neutral_l and true.
Proof. tautob~. Qed.

Lemma neutral_r_and : neutral_r and true.
Proof. tautob~. Qed.

Lemma absorb_l_and : absorb_l and false.
Proof. tautob~. Qed.

Lemma absorb_r_and : absorb_r and false.
Proof. tautob~. Qed.

Lemma neutral_l_or : neutral_l or false.
Proof. tautob~. Qed.

Lemma neutral_r_or : neutral_r or false.
Proof. tautob~. Qed.

Lemma absorb_l_or : absorb_l or true.
Proof. tautob~. Qed.

Lemma absorb_r_or : absorb_r or true.
Proof. tautob~. Qed.

Lemma comm_or : comm or.
Proof. tautob~. Qed.

Lemma comm_and : comm and.
Proof. tautob~. Qed.

Lemma assoc_and : assoc and. 
Proof. tautob*. Qed.

Lemma assoc_or : assoc or. 
Proof. tautob*. Qed.

Lemma neg_false : ! false = true.
Proof. auto. Qed.

Lemma neg_true : ! true = false.
Proof. auto. Qed. 

Lemma neg_and : @automorphism bool neg and or.
Proof. tautob~. Qed.

Lemma neg_or : @automorphism bool neg or and.
Proof. tautob~. Qed.

Lemma neg_neg : idempotent neg.
Proof. tautob~. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of [if then else] *)

Section PropertiesIf.

Implicit Types x y z : bool. 

Lemma if_t_x_y : forall x y,
  (if true then x else y) = x.
Proof. auto. Qed.

Lemma if_f_x_y : forall x y,
  (if false then x else y) = y.
Proof. auto. Qed.

Lemma if_x_y_y : forall x y,
  (if x then y else y) = y.
Proof. tautob~. Qed.

Lemma if_x_t_f : forall x,
  (if x then true else false) = x.
Proof. tautob~. Qed.

Lemma if_x_f_t : forall x,
  (if x then false else true) = !x.
Proof. tautob~. Qed.

Lemma if_x_t_y : forall x y,
  (if x then true else y) = x || y.
Proof. tautob~. Qed.

Lemma if_x_y_f : forall x y,
  (if x then y else false) = x && y.
Proof. tautob~. Qed.

End PropertiesIf.


(* ********************************************************************** *)
(** * Tactics *) 

(** [fix_neg_neg] is a tactic that simplifies all double negations. *)

Hint Rewrite neg_neg : rew_neg_neg.
Tactic Notation "fix_neg_neg" := 
  autorewrite with rew_neg_neg in *.  
Tactic Notation "fix_neg_neg" "~" := 
  fix_neg_neg; auto_tilde.
Tactic Notation "fix_neg_neg" "*" := 
  fix_neg_neg; auto_star.

(** [rew_bool] simplifies boolean expressions, using rewriting
    lemmas in the database [rew_bool] defined below. *)

Hint Rewrite 
  neg_false neg_true neg_neg neg_and neg_or
  neutral_l_and neutral_r_and absorb_l_and absorb_r_and
  neutral_l_or neutral_r_or absorb_l_or absorb_r_or  
  if_t_x_y if_f_x_y if_x_y_y if_x_t_f if_x_f_t if_x_t_y if_x_y_f       
  : bool_rew.

Tactic Notation "rew_bool" :=
  autorewrite with bool_rew.
Tactic Notation "rew_bool" "in" hyp(H) :=
  autorewrite with bool_rew in H.
Tactic Notation "rew_bool" "in" "*":=
  autorewrite with bool_rew in *.
Tactic Notation "rew_bool" "~" :=
  rew_bool; auto~.
Tactic Notation "rew_bool" "*" :=
  rew_bool; auto*.
Tactic Notation "rew_bool" "~" "in" "*":=
  rew_bool in *; auto~.
Tactic Notation "rew_bool" "*" "in" "*":=
  rew_bool in *; auto*.


(** Making definitions opaque ensures that the [simpl] tactic does
    not break symmetry in proofs. *)

Opaque and or neg. 


