(**************************************************************************
* TLC: A library for Coq                                                  *
* Integers -- TODO: use typeclasses                                       * 
**************************************************************************)

Set Implicit Arguments.  
Require Export ZArith. 
Require Import LibTactics LibLogic LibReflect LibRelation.
Export LibTacticsCompatibility.
Require Export LibNat.

(* ********************************************************************** *)
(** * Notation for integers *)

(* Comparison operators are those of LibOrder, not ZArith *)

Open Scope Z_scope.
Open Scope comp_scope. 

Notation "'int'" := Z : Int_scope.

Infix "+" := Zplus : Int_scope.
Notation "- x" := (Zopp x) : Int_scope.
Infix "-" := Zminus : Int_scope.
Infix "*" := Zmult : Int_scope.

Bind Scope Int_scope with Z.
Delimit Scope Int_scope with I.
Open Scope Int_scope.

(* todo: is all of this really necessary ? *)

(* We can't use 
   Coercion Z_of_nat : nat >-> Z.
   Because
   Opaque Z_of_nat. 
   makes all proofs with omega to fail
*)

Definition my_Z_of_nat := Z_of_nat.

Lemma my_Z_of_nat_def : my_Z_of_nat = Z_of_nat.
Proof. reflexivity. Qed.

Global Opaque my_Z_of_nat.

Coercion my_Z_of_nat : nat >-> Z.


(* ********************************************************************** *)
(** * Conversion to natural numbers, for tactic programming *)

Definition ltac_nat_from_int (x:Z) : nat :=
  match x with
  | Z0 => 0%nat
  | Zpos p => nat_of_P p
  | Zneg p => 0%nat
  end.

Ltac nat_from_number N ::=
  match type of N with
  | nat => constr:(N)
  | int => let N' := constr:(ltac_nat_from_int N) in eval compute in N'
  | Z => let N' := constr:(ltac_nat_from_int N) in eval compute in N'
  (*todo: last case not needed*)
  end.


(* ********************************************************************** *)
(** * Inhabited *)

Instance int_inhab : Inhab int.
Proof. intros. apply (prove_Inhab 0). Qed.


(* ********************************************************************** *)
(** * Order on numbers *)

Instance le_int_inst : Le int := Build_Le Zle.


(* ---------------------------------------------------------------------- *)
(** ** Relation to Peano, for tactic [omega] *)

Lemma le_zarith : le = Zle.
Proof. extens*. Qed.

Global Opaque le_int_inst.

Lemma lt_zarith : lt = Zlt.
Proof.
  extens. rew_to_le. rewrite le_zarith.
  unfold strict. intros. omega.
Qed.

Lemma ge_zarith : ge = Zge.
Proof.
  extens. rew_to_le. rewrite le_zarith. 
  unfold flip. intros. omega.
Qed.

Lemma gt_zarith : gt = Zgt.
Proof.
  extens. rew_to_le. rewrite le_zarith. 
  unfold strict, flip. intros. omega.
Qed.

Hint Rewrite le_zarith lt_zarith ge_zarith gt_zarith : rew_int_comp.
Ltac int_comp_to_zarith := 
  autorewrite with rew_int_comp in *.



(* ********************************************************************** *)
(** * Decision procedure: calling [omega] *)

(** [is_arity_type T] returns a boolean indicating whether
    [T] is equal to [nat] or [int] *)

Ltac is_arith_type T := 
  match T with
  | nat => constr:(true)
  | int => constr:(true)
  | _ => constr:(false)
  end.

(** [is_arity E] returns a boolean indicating whether
    [E] is an arithmetic expression *)

Ltac is_arith E :=
  match E with
  | _ = _ :> ?T => is_arith_type T
  | _ <> _ :> ?T => is_arith_type T
  | ~ ?E' => is_arith E'
  | ?E' -> False => is_arith E'
  | @le ?T _ _ _ => is_arith_type T
  | @ge ?T _ _ _ => is_arith_type T
  | @lt ?T _ _ _ => is_arith_type T
  | @gt ?T _ _ _ => is_arith_type T
  | (_ <= _)%Z => constr:(true)
  | (_ >= _)%Z => constr:(true)
  | (_ < _)%Z => constr:(true)
  | (_ > _)%Z => constr:(true)
  | (_ <= _)%nat => constr:(true)
  | (_ >= _)%nat => constr:(true)
  | (_ < _)%nat => constr:(true)
  | (_ > _)%nat => constr:(true)
  | _ => constr:(false)
  end.

(** [arith_goal_or_false] looks at the current goal and 
    replaces it with [False] if it is not an arithmetic goal*)

Ltac arith_goal_or_false :=
  match goal with |- ?E => 
    match is_arith E with
    | true => idtac
    | false => false
    end
  end.

(** [generalize_arith] generalizes all hypotheses which correspond
    to some arithmetic goal. It destructs conjunctions on the fly. *)

Ltac generalize_arith :=
  repeat match goal with
  | H: istrue (isTrue _) |- _ => generalize (@istrue_isTrue_forw _ H); clear H; intro
  | H:?E1 /\ ?E2 |- _ => destruct H
  | H: ?E -> False |- _ => 
    match is_arith E with
    | true => change (E -> False) with (~ E) in H
    | false => clear H
    end
  | H:?E |- _ =>
    match is_arith E with
    | true => generalize H; clear H (* todo: revert H? *)
    | false => clear H
    end
  end.

(* TODO:
Ltac split_if_eq_bool :=
  let go _ := apply eq_bool_prove; intros in
  match goal with 
  | |- @eq bool _ _ => go tt
  | |- istrue (@eqb bool _ _ _) => apply eq_to_equ; go tt
  end.
*)

(** Two lemmas to help omega out *)

Lemma Z_of_nat_O : 
  Z_of_nat O = 0.
Proof. reflexivity. Qed.

Lemma Z_of_nat_S : forall n, 
  Z_of_nat (S n) = Zsucc (Z_of_nat n).
Proof. intros. rewrite~ <- Zpos_P_of_succ_nat. Qed.

Lemma Z_of_nat_plus1 : forall n, 
  Z_of_nat (1 + n) = Zsucc (Z_of_nat n).
Proof. intros. rewrite <- Z_of_nat_S. fequals~. Qed.

(** [rew_maths] rewrite any lemma in the base [rew_maths].
    The goal should not contain any evar, otherwise tactic might loop. *)

Hint Rewrite my_Z_of_nat_def Z_of_nat_O Z_of_nat_S Z_of_nat_plus1 : rew_maths.

Ltac rew_maths :=  
  autorewrite with rew_maths in *.

(** [math_setup_goal] does introduction, splits, and replace
    the goal by [False] if it is not arithmetic. If the goal
    is of the form [P1 = P2 :> Prop], then the goal is 
    changed to [P1 <-> P2]. *)

Ltac math_setup_goal :=
  intros;
  try match goal with |- _ /\ _ => split end;
  try match goal with |- _ = _ :> Prop => apply prop_ext; iff end;
  arith_goal_or_false. 
  (* try split_if_eq_bool. *)

(* todo; [int_nat_conv] 
Lemma int_nat_plus : forall (n m:nat),
  (n + m)%nat = (n + m)%Z :> int.
Proof. applys inj_plus. Qed.
Hint Rewrite int_nat_plus : int_nat_conv.
*)

(** [math] tactics performs several preprocessing step,
    selects all arithmetic hypotheses, and the call omega. *)
(* todo: autorewrite with int_nat_conv in *. after int_comp_to_zarith *)

(* TODO *)
Ltac check_noevar_goal ::= 
  match goal with |- ?G => first [ has_evar G; fail 1 | idtac ] end.

Ltac math_0 := idtac.
Ltac math_1 := intros; generalize_arith.
Ltac math_2 := instantiate; check_noevar_goal; intros.
Ltac math_3 := rew_maths; nat_comp_to_peano; int_comp_to_zarith.
Ltac math_4 := math_setup_goal.
Ltac math_5 := omega.

Ltac math_debug := math_0; math_1; math_2; math_3; math_4.
Ltac math_base := math_debug; math_5.

Tactic Notation "math" := math_base.

Tactic Notation "math" simple_intropattern(I) ":" constr(E) :=
  asserts I: E; [ math | ].
Tactic Notation "maths" constr(E) :=
  let H := fresh "H" in asserts H: E; [ math | ].
(* todo: parsing conflit *)

(* ---------------------------------------------------------------------- *)
(** ** [math] tactic restricted to arithmetic goals *)

(** [math_only] calls [math] but only on goals which 
    have an arithmetic form. Thus, contracty to [math],
    it does not attempt to look for a contradiction in
    the hypotheses if the conclusion is not an arithmetic
    goal. Useful for efficiency. *)

Ltac math_only :=
  match goal with |- ?T =>
    match is_arith T with true => math end end.

(* ---------------------------------------------------------------------- *)
(** ** Calling [maths] after eliminating boolean reflection *)

(** [maths] is a more powerful version of [math],
    able to deconstruct conjunctions, disjunctions,
    and negations, but as a consequence it might be slower. *)

Hint Rewrite istrue_and istrue_or istrue_neg : rew_reflect_and_or_neg.

Ltac maths := 
  autorewrite with rew_reflect_and_or_neg in *; intuition math.

(* ---------------------------------------------------------------------- *)
(** ** Rewriting equalities provable by the [math] tactic *)

(** [math_rewrite (E = F)] replaces all occurences of [E]
    with the expression [F]. It produces the equality [E = F]
    as subgoal, and tries to solve it using the tactic [math] *)

Tactic Notation "math_rewrite" constr(E) :=
  asserts_rewrite E; [ try math | ].
Tactic Notation "math_rewrite" constr(E) "in" hyp(H) :=
  asserts_rewrite E in H; [ try math | ].
Tactic Notation "math_rewrite" constr(E) "in" "*" :=
  asserts_rewrite E in *; [ try math | ].

Tactic Notation "math_rewrite" "~" constr(E) :=
  math_rewrite E; auto_tilde.
Tactic Notation "math_rewrite" "~" constr(E) "in" hyp(H) :=
  math_rewrite E in H; auto_tilde.
Tactic Notation "math_rewrite" "~" constr(E) "in" "*" :=
  math_rewrite E in *; auto_tilde.

Tactic Notation "math_rewrite" "*" constr(E) :=
  math_rewrite E; auto_star.
Tactic Notation "math_rewrite" "*" constr(E) "in" hyp(H) :=
  math_rewrite E in H; auto_star.
Tactic Notation "math_rewrite" "*" constr(E) "in" "*" :=
  math_rewrite E in *; auto_star.

(* ---------------------------------------------------------------------- *)
(** ** Hint externs for calling math in the hint base [maths] *)
   
Hint Extern 3 (_ = _ :> nat) => math : maths.
Hint Extern 3 (_ = _ :> int) => math : maths.
Hint Extern 3 (_ <> _ :> nat) => math : maths.
Hint Extern 3 (_ <> _ :> int) => math : maths.
Hint Extern 3 (istrue (isTrue (_ = _ :> nat))) => math : maths.
Hint Extern 3 (istrue (isTrue (_ = _ :> int))) => math : maths.
Hint Extern 3 (istrue (isTrue (_ <> _ :> nat))) => math : maths.
Hint Extern 3 (istrue (isTrue (_ <> _ :> int))) => math : maths.
Hint Extern 3 ((_ <= _)%nat) => math : maths.
Hint Extern 3 ((_ >= _)%nat) => math : maths.
Hint Extern 3 ((_ < _)%nat) => math : maths.
Hint Extern 3 ((_ > _)%nat) => math : maths.
Hint Extern 3 ((_ <= _)%Z) => math : maths.
Hint Extern 3 ((_ >= _)%Z) => math : maths.
Hint Extern 3 ((_ < _)%Z) => math : maths.
Hint Extern 3 ((_ > _)%Z) => math : maths.
Hint Extern 3 (@le nat _ _ _) => math : maths.
Hint Extern 3 (@lt nat _ _ _) => math : maths.
Hint Extern 3 (@ge nat _ _ _) => math : maths.
Hint Extern 3 (@gt nat _ _ _) => math : maths.
Hint Extern 3 (@le int _ _ _) => math : maths.
Hint Extern 3 (@lt int _ _ _) => math : maths.
Hint Extern 3 (@ge int _ _ _) => math : maths.
Hint Extern 3 (@gt int _ _ _) => math : maths.


(* ********************************************************************** *)
(** * Simplification lemmas *)

(* ---------------------------------------------------------------------- *)
(** ** Addition and substraction *)

Lemma plus_zero_r : forall n,
  n + 0 = n.
Proof. math. Qed.
Lemma plus_zero_l : forall n,
  0 + n = n.
Proof. math. Qed.
Lemma minus_zero : forall n,
  n - 0 = n.
Proof. math. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Comparison *)

Lemma plus_le_l : forall a b c,
  (a + b <= a + c) = (b <= c).
Proof. math. Qed.
Lemma plus_ge_l : forall a b c,
  (a + b >= a + c) = (b >= c).
Proof. math. Qed.
Lemma plus_lt_l : forall a b c,
  (a + b < a + c) = (b < c).
Proof. math. Qed.
Lemma plus_gt_l : forall a b c,
  (a + b > a + c) = (b > c).
Proof. math. Qed.

Lemma plus_le_r : forall a b c,
  (b + a <= c + a) = (b <= c).
Proof. math. Qed.
Lemma plus_ge_r : forall a b c,
  (b + a >= c + a) = (b >= c).
Proof. math. Qed.
Lemma plus_lt_r : forall a b c,
  (b + a < c + a) = (b < c).
Proof. math. Qed.
Lemma plus_gt_r : forall a b c,
  (b + a > c + a) = (b > c).
Proof. math. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_int] performs some basic simplification on 
    expressions involving integers *)

Hint Rewrite plus_zero_r plus_zero_l minus_zero : rew_int.
Hint Rewrite plus_le_l plus_ge_l plus_lt_l plus_gt_l : rew_int.
Hint Rewrite plus_le_r plus_ge_r plus_lt_r plus_gt_r : rew_int.

Tactic Notation "rew_int" :=
  autorewrite with rew_int.
Tactic Notation "rew_int" "~" :=
  rew_int; auto_tilde.
Tactic Notation "rew_int" "*" :=
  rew_int; auto_star.
Tactic Notation "rew_int" "in" "*" :=
  autorewrite with rew_int in *.
Tactic Notation "rew_int" "~" "in" "*" :=
  rew_int in *; auto_tilde.
Tactic Notation "rew_int" "*" "in" "*" :=
  rew_int in *; auto_star.
Tactic Notation "rew_int" "in" hyp(H) :=
  autorewrite with rew_int in H.
Tactic Notation "rew_int" "~" "in" hyp(H) :=
  rew_int in H; auto_tilde.
Tactic Notation "rew_int" "*" "in" hyp(H) :=
  rew_int in H; auto_star.


(************************************************************)
(* * Relation with Nat *)

Notation "'abs'" := Zabs_nat (at level 0).

Global Opaque Zabs Zabs_nat.

Lemma abs_pos_nat : forall n : nat,
  abs n = n.
Proof. exact Zabs_nat_Z_of_nat. Qed.

Lemma abs_pos : forall n : int,
  n >= 0 -> abs n = n :> int.
Proof. 
  intros. rewrite inj_Zabs_nat.
  rewrite Zabs_eq. math. math.
Qed.

Lemma eq_int_nat : forall n m : nat,
  n = m :> int -> n = m :> nat.
Proof. math. Qed.

Lemma succ_abs : forall n : int,
  n >= 0 -> S (abs n) = abs (1 + n) :> nat.
Proof.
  applys (@measure_induction _ abs). intros n IH Pos.
  rewrite <- Zabs_nat_Zsucc. fequals. math. math. 
Qed.

Lemma abs_spos : forall n : int,
  n > 0 -> abs n = S (abs (n-1)) :> nat.
Proof.
  intros. apply eq_int_nat.
  rewrite abs_pos; try math.
  rewrite succ_abs; try math.
  rewrite abs_pos; math.
Qed. 

Lemma int_nat_eq : forall (x y:nat),
  (x = y :> int) -> (x = y :> nat).
Proof. math. Qed.

Lemma int_nat_le : forall (x y:nat),
  ((x:int) <= (y:int)) -> x <= y.
Proof. math. Qed.

Lemma int_nat_lt : forall (x y:nat),
  x < y -> (x:int) < (y:int).
Proof. math. Qed.

Lemma Zabs_nat_lt : forall n m, 
  (0 <= n) -> (n < m) -> (abs n < abs m).
Proof.
  intros. nat_comp_to_peano. apply Zabs_nat_lt. math.
Qed.

(* begin hide *)

Lemma div_2_parts : forall n n1 n2,
  n >= 4 -> n1 = Zdiv n 2 -> n2 = n - n1 ->
  2 <= n1 /\ n1 < n /\ 2 <= n2 /\ n2 < n.
Proof. skip. Qed. (*TODO: under construction *)

(* TODO: basic lemmas about abs.
   See library file Coq.ZArith.Znat *)
Axiom abs_plus : forall a b : int,
  (a >= 0) -> (b >= 0) -> 
  abs (a+b) = (abs a + abs b)%nat :> nat.
Axiom abs_minus : forall a b : int,
  (a >= b) -> (b >= 0) -> 
  abs (a-b) = (abs a - abs b)%nat :> nat.
Axiom abs_le : forall (a:int) (b:nat),
  (a <= b) -> (abs a <= b).
Axiom abs_ge : forall (a:int) (b:nat),
  (a >= b) -> (abs a >= b).
Axiom abs_gt : forall (a:int) (b:nat),
  (a > b) -> (abs a > b).
Axiom plus_nat_int : forall a b : nat,
  (a+b)%nat = (a:int) + (b:int) :> int.
Axiom abs_pos_le : forall (n:int) (m:nat),
  0 <= n -> n <= m -> abs n <= m.
Axiom nat_int_eq : forall (n:int) (m:nat),
  m = abs n -> m = n :> int.
Implicit Arguments nat_int_eq [n m].

(* end hide *)

Hint Rewrite plus_nat_int : rew_maths.

Lemma abs_1 : abs 1 = 1%nat :> nat.
Proof. reflexivity. Qed.

Hint Rewrite abs_plus abs_1 abs_pos abs_pos_nat : rew_abs_pos.
Tactic Notation "rew_abs_pos" :=
  autorewrite with rew_abs_pos.
Tactic Notation "rew_abs_pos" "~" :=
  autorewrite with rew_abs_pos; try math; auto~.

Lemma mod_eq_prove : forall k a b n,
  a = b + k * n -> a mod n = b mod n.
Proof. intros. subst. rewrite~ Z_mod_plus_full. Qed.

Lemma mod_prove : forall k a b n,
  a = b + k * n -> 0 <= b -> b < n -> a mod n = b.
Proof.
  intros. rewrite <- (@Zmod_small b n).
  apply* mod_eq_prove. math.
Qed.

Lemma mod2_zero : 
  0 mod 2 = 0.
Proof. reflexivity. Qed.
Lemma mod2_odd : forall k,
  (2 * k) mod 2 = 0.
Proof. intros. apply (mod_prove k); math. Qed.
Lemma mod2_even : forall k,
  (2 * k + 1) mod 2 = 1.
Proof. intros. apply (mod_prove k); math. Qed.
Lemma div2_odd : forall k,
  (2 * k) / 2 = k.
Proof.
  intros. math_rewrite (2*k=k*2). 
  apply Z_div_mult_full. math. 
Qed.
Lemma div2_even : forall k,
  k >= 0 -> (2 * k + 1) / 2 = k.
Proof. intros. symmetry. eapply Zdiv_unique with (r:=1); math. Qed.

Lemma mod2_bound : forall n,
  0 <= n mod 2 < 2.
Proof.
  intros. forwards: (Z_mod_remainder n 2). math.
  destruct H as [[? ?]|[? ?]]; math.
Qed.

(* begin hide *)

Lemma div2_bounds : forall m n,
  m = n / 2 -> 2 * m <= n /\ n <= 2 * m + 1.
Proof. 
  intros. forwards K: (Z_div_mod_eq n 2). math.
  destruct (mod2_bound n). subst m. skip. (* TODO math. *)
Qed.

Implicit Arguments div2_bounds [m n].

(* end hide *)

Hint Rewrite mod2_zero mod2_odd mod2_even div2_odd div2_even : rew_parity.

Ltac rew_parity :=
  autorewrite with rew_parity.


(************************************************************)
(* * Elimination of multiplication, to call omega *)

Lemma double : forall x, 2 * x = x + x. 
Proof. intros. ring. Qed.

Lemma triple : forall x, 3 * x = x + x + x. 
Proof. intros. ring. Qed.

Lemma quadruple : forall x, 3 * x = x + x + x. 
Proof. intros. ring. Qed.

(* To use [math] with simple multiplications, add the command:  
   Hint Rewrite double triple : rew_maths.
*)


(************************************************************)
(* * Min function *)

Require Import LibEpsilon.

Instance int_le_total_order : Le_total_order (A:=int).
Proof.
  constructor. constructor. constructor; unfolds.
  math. math. unfolds. math. unfolds. 
  intros. tests: (x <= y). left~. right. math.
Qed. 

(* todo: make polymorphic with classes *)

Section Min.
Implicit Types x y : int.

Definition min x y :=
  If x <= y then x else y.

Lemma min_self : forall x,
  min x x = x.
Proof. intros. unfolds min. case_if~. Qed.
Lemma min_left : forall x y,
  x <= y -> min x y = x.
Proof. intros. unfolds min. case_if~. false*. Qed.
Lemma min_right : forall x y,
  y <= x -> min x y = y.
Proof. intros. unfolds min. case_if~. apply~ le_antisym. Qed.
Lemma min_trans_elim : forall a b x y : int,
  min a b <= x -> y < a -> y < b -> y < x.
Proof. intros. unfolds min. case_if; math. Qed.

End Min.

Require Import Zpow_facts.

Lemma pow2_pos : forall n, n >= 0 -> 2^n >= 1. 
Proof.
  intros. math_rewrite (1 = 2^0). reflexivity. 
  rewrite ge_is_flip_le. unfolds. 
  apply Zpower_le_monotone; math.
Qed.

Lemma pow2_succ : forall n, n >= 0 -> 2^(n+1) = 2*2^n.
Proof.
  intros. math_rewrite (n+1 = Zsucc n).
  rewrite Zpower_Zsucc; math. 
Qed.

(* ********************************************************************** *)
(** * Advanced induction *)

Definition eq_gt_implies (P : (nat->Prop) -> Prop) :=
  forall n, (forall m, n > m -> P (eq m)) -> P (gt n).

Definition eq_lt_implies (P : (nat->Prop) -> Prop) :=
  forall n, (forall m, n < m -> P (eq m)) -> P (gt n).

Hint Unfold eq_lt_implies eq_gt_implies.

Lemma eq_lt_induction : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (lt n)) ->
  (forall n, P (lt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof. intros. induction n using peano_induction. auto. Qed. 

Lemma eq_gt_induction : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (gt n)) ->
  (forall n, P (gt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof. intros. induction n using peano_induction. auto. Qed. 

Lemma eq_gt_induction_2 : forall (P1 P2 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> eq_gt_implies P2 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P1 (eq n) /\ P2 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)).
Proof.
  introv H1 H2 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n)).
    split; intros n; specializes M n; auto*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed.

(* todo: other arities *)

Lemma eq_gt_induction_5 : forall (P1 P2 P3 P4 P5 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> eq_gt_implies P2 -> eq_gt_implies P3 -> 
  eq_gt_implies P4 -> eq_gt_implies P5 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P3 (gt n) -> P4 (gt n) -> P5 (gt n) -> 
    P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)) /\ (forall n, P3 (eq n))
    /\ (forall n, P4 (eq n))  /\ (forall n, P5 (eq n)).
Proof. 
  introv H1 H2 H3 H4 H5 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)).
    splits; intros n; specializes M n; auto*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed. 
