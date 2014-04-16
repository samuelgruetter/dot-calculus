(**************************************************************************
* TLC: A library for Coq                                                  *
* Reflection between booleans and propositions                            *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics.
Require Export LibBool LibLogic.
Generalizable Variable P.

(* ********************************************************************** *)
(** * Reflection between booleans and propositions *)

(** [istrue b] produces a proposition that is [True] if and only if
    the boolean [b] is equal to [true].
    [isTrue P] produces a boolean expression that is [true] if and only
    if the proposition [P] is equal to [True]. *)

(* ---------------------------------------------------------------------- *)
(** ** Translation from booleans into propositions *)

(** Any boolean [b] can be viewed as a proposition through the 
    relation [b = true]. *)

Coercion istrue (b : bool) : Prop := (b = true). 

(** Specification of the coercion [istrue] *)

Lemma istrue_def : forall b, 
  istrue b = (b = true). 
Proof. reflexivity. Qed.

Lemma istrue_true_eq : istrue true = True. 
Proof. rewrite istrue_def. extens*. Qed.

Lemma istrue_false_eq : istrue false = False. 
Proof. rewrite istrue_def. extens. iff; auto_false. Qed.

(** Update of the unfolding tactics to go through the coercion
    [istrue] (see LibTactics). *)

Ltac apply_to_head_of E cont ::=
  let go E := let P := get_head E in cont P in
  match E with
  | istrue ?A => go A
  | istrue (neg ?A) => go A
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A 
  end.

Global Opaque istrue.


(* ---------------------------------------------------------------------- *)
(** ** Tactics for proving boolean goals [true] and [false] *)

(** Proving the goals [true] and [~ false] *) 

Lemma istrue_true : true. 
Proof. reflexivity. Qed.

Hint Resolve istrue_true.

Lemma istrue_not_false : ~ false. 
Proof. rewrite istrue_false_eq. intuition. Qed.

Hint Resolve istrue_not_false.

(** Proving the goal [false] and [False] *)

Lemma False_to_false : False -> false.
Proof. intros K. false. Qed.

Hint Extern 1 (istrue false) => 
  apply False_to_false.

Lemma false_to_False : false -> False.
Proof. intros K. rewrite~ istrue_false_eq in K. Qed.

Hint Extern 1 (False) => match goal with
  | H: istrue false |- _ => apply (istrue_not_false H) end.

(* ---------------------------------------------------------------------- *)
(** ** Translation from propositions into booleans *)

(** The expression [isTrue P] evaluates to [true] if and only if 
    the proposition [P] is [True]. *)

Definition isTrue (P : Prop) : bool := 
  If P then true else false.

(** Simplification lemmas *)

Lemma isTrue_def : forall P,
  isTrue P = If P then true else false.
Proof. reflexivity. Qed.

Lemma isTrue_True : isTrue True = true.
Proof. unfolds. case_if; auto_false~. Qed.

Lemma isTrue_False : isTrue False = false.
Proof. unfolds. case_if; auto_false~. Qed.

(** Notation for comparison in [bool] are [x '= y] and [x '<> y] *)

Notation "x ''=' y :> A" := (isTrue (@eq A x y))
  (at level 70, y at next level, only parsing) : comp_scope.
Notation "x ''<>' y :> A" := (isTrue (~ (@eq A x y)))
  (at level 69, y at next level, only parsing) : comp_scope.
Notation "x ''=' y" := (isTrue (@eq _ x y))
  (at level 70, y at next level, no associativity) : comp_scope.
Notation "x ''<>' y" := (isTrue (~ (@eq _ x y)))
  (at level 69, y at next level, no associativity) : comp_scope.

Global Opaque isTrue.
Open Scope comp_scope.

(* ---------------------------------------------------------------------- *)
(** ** Extensionality for boolean equality *)

Lemma bool_ext : forall b1 b2 : bool,
  (b1 <-> b2) -> b1 = b2.
Proof.
  destruct b1; destruct b2; intros; auto_false.
  destruct H. false H; auto.
  destruct H. false H0; auto.
Qed.

Instance bool_extensional : Extensional bool.
Proof. apply (@Build_Extensional bool iff bool_ext). Defined.


(* ********************************************************************** *)
(** * Lemmas for reflection *)

(* ---------------------------------------------------------------------- *)
(** ** Rewriting rules for distributing [istrue] *)

Section DistribIstrue.
Implicit Types b : bool.
Implicit Types P : Prop.

Lemma istrue_isTrue_iff : forall (P : Prop),
  istrue (isTrue P) <-> P.
Proof. intros. rewrite isTrue_def. case_if; auto_false*. Qed.

Lemma istrue_isTrue : forall P,
  istrue (isTrue P) = P.
Proof. extens. rewrite* istrue_isTrue_iff. Qed.

Lemma istrue_neg : forall b,
  istrue (!b) = ~ (istrue b).
Proof. extens. tautob*. Qed.

Lemma istrue_and : forall b1 b2,
  istrue (b1 && b2) = (istrue b1 /\ istrue b2).
Proof. extens. tautob*. Qed.

Lemma istrue_or : forall b1 b2,
  istrue (b1 || b2) = (istrue b1 \/ istrue b2).
Proof. extens. tautob*. Qed.

End DistribIstrue.

(* ---------------------------------------------------------------------- *)
(** ** Rewriting rules for distributing [isTrue] *)

Section DistribIsTrue.
Implicit Types b : bool.
Implicit Types P : Prop.

Lemma isTrue_istrue : forall b,
  isTrue (istrue b) = b.
Proof. extens. rewrite* istrue_isTrue_iff. Qed.

Lemma isTrue_not : forall P,
  isTrue (~ P) = ! isTrue P.
Proof. extens. do 2 rewrite isTrue_def. do 2 case_if; auto_false*. Qed.

Lemma isTrue_and : forall P1 P2,
  isTrue (P1 /\ P2) = (isTrue P1 && isTrue P2).
Proof. extens. do 3 rewrite isTrue_def. do 3 case_if; auto_false*. Qed.

Lemma isTrue_or : forall P1 P2,
  isTrue (P1 \/ P2) = (isTrue P1 || isTrue P2).
Proof. extens. do 3 rewrite isTrue_def. do 3 case_if; auto_false*. Qed.

End DistribIsTrue.

(* ---------------------------------------------------------------------- *)
(** Corrolaries obtained by composition *)

Lemma istrue_neg_isTrue : forall P,
  istrue (! isTrue P) = ~ P.
Proof. intros. rewrite istrue_neg. rewrite~ istrue_isTrue. Qed.

Lemma isTrue_not_istrue : forall b,
  isTrue (~ istrue b) = !b.
Proof. intros. rewrite isTrue_not. rewrite~ isTrue_istrue. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Tactics for distributing [istrue] and [isTrue] *)

(** [rew_reflect] distributes [istrue]. *)

Hint Rewrite istrue_true_eq istrue_false_eq istrue_isTrue 
  istrue_neg istrue_and istrue_or : rew_reflect.

Tactic Notation "rew_reflect" :=
  autorewrite with rew_reflect.
Tactic Notation "rew_reflect" "in" "*" :=
  autorewrite with rew_reflect in *.
Tactic Notation "rew_reflect" "in" hyp(H) :=
  autorewrite with rew_reflect in H.

Tactic Notation "rew_reflect" "~" :=
  rew_reflect; auto_tilde.
Tactic Notation "rew_reflect" "~" "in" "*" :=
  rew_reflect in *; auto_tilde.
Tactic Notation "rew_reflect" "~" "in" hyp(H) :=
  rew_reflect in H; auto_tilde.

Tactic Notation "rew_reflect" "*" :=
  rew_reflect; auto_star.
Tactic Notation "rew_reflect" "*" "in" "*" :=
  rew_reflect in *; auto_star.
Tactic Notation "rew_reflect" "*" "in" hyp(H) :=
  rew_reflect in H; auto_star.

(** [rew_unreflect] distributes [istrue]. *)

Hint Rewrite isTrue_True isTrue_False isTrue_istrue 
 isTrue_not isTrue_and isTrue_or : rew_unreflect.

Tactic Notation "rew_unreflect" :=
  autorewrite with rew_unreflect.
Tactic Notation "rew_unreflect" "in" "*" :=
  autorewrite with rew_unreflect in *.
Tactic Notation "rew_unreflect" "in" hyp(H) :=
  autorewrite with rew_unreflect in H.

Tactic Notation "rew_unreflect" "~" :=
  rew_unreflect; auto_tilde.
Tactic Notation "rew_unreflect" "~" "in" "*" :=
  rew_unreflect in *; auto_tilde.
Tactic Notation "rew_unreflect" "~" "in" hyp(H) :=
  rew_unreflect in H; auto_tilde.

Tactic Notation "rew_unreflect" "*" :=
  rew_unreflect; auto_star.
Tactic Notation "rew_unreflect" "*" "in" "*" :=
  rew_unreflect in *; auto_star.
Tactic Notation "rew_unreflect" "*" "in" hyp(H) :=
  rew_unreflect in H; auto_star.

(** [rew_refl] distributes [istrue] and [isTrue]
    and replaces [decide] with [isTrue]. *)

Hint Rewrite isTrue_True isTrue_False isTrue_istrue 
 isTrue_not isTrue_and isTrue_or 
 istrue_true_eq istrue_false_eq istrue_isTrue 
 istrue_neg istrue_and istrue_or : rew_refl.

Tactic Notation "rew_refl" :=
  autorewrite with rew_refl.
Tactic Notation "rew_refl" "in" "*" :=
  autorewrite with rew_refl in *.
Tactic Notation "rew_refl" "in" hyp(H) :=
  autorewrite with rew_refl in H.

Tactic Notation "rew_refl" "~" :=
  rew_refl; auto_tilde.
Tactic Notation "rew_refl" "~" "in" "*" :=
  rew_refl in *; auto_tilde.
Tactic Notation "rew_refl" "~" "in" hyp(H) :=
  rew_refl in H; auto_tilde.

Tactic Notation "rew_refl" "*" :=
  rew_refl; auto_star.
Tactic Notation "rew_refl" "*" "in" "*" :=
  rew_refl in *; auto_star.
Tactic Notation "rew_refl" "*" "in" hyp(H) :=
  rew_refl in H; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Properties of boolean comparison *)

Lemma isTrue_true : forall (P:Prop),
  P -> isTrue P = true.
Proof. intros. rewrite isTrue_def. case_if*. Qed.

Lemma isTrue_false : forall (P:Prop),
  ~ P -> isTrue P = false.
Proof. intros. rewrite isTrue_def. case_if*. Qed.

Lemma eqb_eq : forall A (x y:A),
  x = y -> (x '= y) = true.
Proof. intros. subst. apply~ isTrue_true. Qed.

Lemma eqb_self : forall A (x:A),
  (x '= x) = true.
Proof. intros. apply~ eqb_eq. Qed.

Lemma eqb_neq : forall A (x y:A),
  x <> y -> (x '= y) = false.
Proof. intros. subst. apply~ isTrue_false. Qed.

Lemma neqb_eq : forall A (x y:A),
  x = y -> (x '<> y) = false.
Proof. intros. subst. rewrite~ isTrue_false. Qed.

Lemma neqb_neq : forall A (x y:A),
  x <> y -> (x '<> y) = true.
Proof. intros. subst. rewrite~ isTrue_true. Qed.

Lemma neqb_self : forall A (x:A),
  (x '<> x) = false.
Proof. intros. apply~ neqb_eq. Qed.


(* ********************************************************************** *)
(** * Tactics for reflection *)

(* ---------------------------------------------------------------------- *)
(** ** Tactic [fold_bool] *)

(** Tactic [fold_bool] simplifies goal and hypotheses of the form
    [b = true] and [b = false], as well as their symmetric *)

Section FoldingBool.
Variables (b : bool).

Lemma bool_eq_true :
  b -> b = true.
Proof. auto. Qed.

Lemma eq_true_l : 
  true = b -> b.
Proof. tautob~. Qed.

Lemma eq_true_r :
  b = true -> b.
Proof. tautob~. Qed.

Lemma eq_false_l :
  false = b -> !b.
Proof. tautob~. Qed.

Lemma eq_false_r : 
  b = false -> !b.
Proof. tautob~. Qed.

Lemma eq_true_l_back : 
  b -> true = b.
Proof. tautob~. Qed.

Lemma eq_true_r_back :
  b -> b = true.
Proof. tautob~. Qed.

Lemma eq_false_l_back :
  !b -> false = b.
Proof. tautob~. Qed.

Lemma eq_false_r_back : 
  !b -> b = false.
Proof. tautob~. Qed.

Lemma eq_false_r_back_not : 
  (~b) -> b = false.
Proof. destruct b; auto_false. Qed. (*todo:tautob~.*)

Lemma neg_neg_back : 
  b -> !!b.
Proof. tautob~. Qed.

Lemma neg_neg_forward : 
  !!b -> b.
Proof. tautob~. Qed.

Lemma eq_bool_prove : forall b' : bool,
  (b -> b') -> (b' -> b) -> b = b'.
Proof. lets: false_to_False. tautob~; tryfalse~. Qed.
  (* todo: simplify *)

Lemma eq_bool_iff : forall b' : bool,
  b = b' -> (b <-> b').
Proof. tautob*. Qed.

End FoldingBool.

Ltac fold_bool := 
  repeat match goal with 
  | H: true = ?b |- _ => applys_to H eq_true_l
  | H: ?b = true |- _ => applys_to H eq_true_r
  | H: false = ?b |- _ => applys_to H eq_false_l
  | H: ?b = false |- _ => applys_to H eq_false_r
  | H: istrue (!! ?b) |- _ => applys_to H neg_neg_forward 
  | |- true = ?b => apply eq_true_l_back
  | |- ?b = true => apply eq_true_r_back
  | |- false = ?b => apply eq_false_l_back
  | |- ?b = false => apply eq_false_r_back
  | |- istrue (!! ?b) => apply neg_neg_back
  end.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [fold_prop] *)

(** Tactic [fold_prop] simplifies goal and hypotheses of the form 
    [istrue b] or [~ istrue b], or [P = True] or [P = False]
    as well as their symmetric *)

Section FoldingProp.
Variables (P : Prop) (b : bool).

Lemma istrue_isTrue_back :
  P -> istrue (isTrue P).
Proof. rewrite~ istrue_isTrue. Qed.

Lemma istrue_isTrue_forw :
  istrue (isTrue P) -> P.
Proof. rewrite~ istrue_isTrue. Qed.

Lemma istrue_not_isTrue_back :
  ~ P -> istrue (! isTrue P).
Proof. rewrite~ istrue_neg_isTrue. Qed.

Lemma istrue_not_isTrue_forw :
  istrue (! isTrue P) -> ~ P.
Proof. rewrite~ istrue_neg_isTrue. Qed.

Lemma prop_eq_True_forw :
  (P = True) -> P.
Proof. intros. subst~. Qed.

Lemma prop_eq_True_back :
  P -> (P = True).
Proof. intros. extens*. Qed.

Lemma prop_eq_False_forw :
  (P = False) -> ~ P.
Proof. intro. subst*. Qed.

Lemma prop_eq_False_back :
  ~ P -> (P = False).
Proof. intros. extens*. Qed.

Lemma prop_neq_True_forw :
  (P <> True) -> ~ P.
Proof. intros_all. apply H. extens*. Qed.

Lemma prop_neq_True_back :
  ~ P -> (P <> True).
Proof. intros_all. subst~. Qed.

Lemma prop_neq_False_forw :
  (P <> False) -> P.
Proof.
  intros_all. apply not_not_elim.
  intros_all. apply H. extens*.
Qed.

Lemma prop_neq_False_back :
  P -> (P <> False).
Proof. introv M K. rewrite~ <- K. Qed.

Lemma not_istrue_isTrue_forw : 
  ~ istrue (isTrue P) -> ~ P.
Proof. apply contrapose_intro. rewrite~ istrue_isTrue. Qed.

Lemma not_istrue_not_isTrue_forw : 
  ~ istrue (! isTrue P) -> P.
Proof.
  rewrite <- (@not_not P). apply contrapose_intro.
  rewrite~ istrue_neg_isTrue. 
Qed. (* todo: missing lemma from lib logic about ~A->B *)

Lemma not_istrue_isTrue_back : 
  ~ P -> ~ istrue (isTrue P).
Proof. apply contrapose_intro. rewrite~ istrue_isTrue. Qed.

Lemma not_istrue_not_isTrue_back : 
  P -> ~ istrue (! isTrue P).
Proof. 
  rewrite <- (@not_not P). apply contrapose_intro.
  rewrite~ istrue_neg_isTrue. 
Qed.

End FoldingProp.

Ltac fold_prop := 
  repeat match goal with 
  | H: istrue (isTrue ?P) |- _ => applys_to H istrue_isTrue_forw
  | H: istrue (! isTrue ?P) |- _ => applys_to H istrue_not_isTrue_forw
  | H: ~ istrue (isTrue ?P) |- _ => applys_to H not_istrue_isTrue_forw
  | H: ~ istrue (! isTrue ?P) |- _ => applys_to H not_istrue_not_isTrue_forw
  | H: (?P = True) |- _ => applys_to H prop_eq_True_forw
  | H: (?P = False) |- _ => applys_to H prop_eq_False_forw
  | H: (True = ?P) |- _ => symmetry in H; applys_to H prop_eq_True_forw
  | H: (False = ?P) |- _ => symmetry in H; applys_to H prop_eq_False_forw
  | H: ~ (~ ?P) |- _ => applys_to H not_not_elim 
  | |- istrue (isTrue ?P) => apply istrue_isTrue_back
  | |- istrue (! isTrue ?P) => apply istrue_not_isTrue_back
  | |- ~ istrue (isTrue ?P) => apply not_istrue_isTrue_back
  | |- ~ istrue (! isTrue ?P) => apply not_istrue_not_isTrue_back
  | |- (?P = True) => apply prop_eq_True_back
  | |- (?P = False) => apply prop_eq_False_back
  | |- (True = ?P) => symmetry; apply prop_eq_True_back
  | |- (False = ?P) => symmetry; apply prop_eq_False_back
  | |- ~ (~ ?P) => apply not_not_intro
  end.

Ltac case_if_post ::= fold_prop; tryfalse.

  (* todo: improve case_if so that there is no need for that *)


(* ---------------------------------------------------------------------- *)
(** ** Tactics for case analysis on booleans *)

(** Extends the tactic [test_dispatch] from LibLogic.v, so as to
    be able to call the tactic [tests] directly on boolean expressions *)

Ltac tests_bool_base E H1 H2 :=
  tests_prop_base (istrue E) H1 H2.

Ltac tests_dispatch E H1 H2 ::=
  match type of E with
  | bool => tests_bool_base E H1 H2
  | Prop => tests_prop_base E H1 H2
  | {_}+{_} => tests_ssum_base E H1 H2
  end.


(* ---------------------------------------------------------------------- *)
(** ** Lemmas for testing booleans *)

Lemma bool_cases : forall (b : bool), 
  b \/ !b.
Proof. tautob*. Qed.

Lemma bool_cases_eq : forall (b : bool), 
  b = true \/ b = false.
Proof. tautob*. Qed.

Lemma xor_cases : forall (b1 b2 : bool), 
  xor b1 b2 -> (b1 = true /\ b2 = false)
            \/ (b1 = false /\ b2 = true).
Proof. tautob; auto_false*. Qed.

Implicit Arguments xor_cases [b1 b2].




(* ********************************************************************** *)
(** * Decidable predicates *)

(** [Decidable P] asserts that there exists a boolean
    value indicating whether [P] is true. The definition
    is interesting when this boolean is computable and
    can lead to code extraction. *)

Class Decidable (P:Prop) := decidable_make {
  decide : bool;
  decide_spec : decide = isTrue P }.

Hint Rewrite @decide_spec : rew_refl.
Implicit Arguments decide [[Decidable]].
Extraction Inline decide.

(** Notation [ifb P then x else y] can be used for 
    testing a proposition [P] for which there exists an
    instance of [Decidable P]. *)

Notation "'ifb' P 'then' v1 'else' v2" := 
  (if decide P then v1 else v2)
  (at level 200, right associativity) : type_scope.

(** In classical logic, any proposition is decidable; of course,
    we do not want to use this lemma as an instance because 
    it cannot be extracted to executable code. *)

Lemma prop_decidable : forall (P:Prop), Decidable P.
Proof. intros. applys~ decidable_make (isTrue P). Qed.

(** Extending the [case_if] tactic to support [if decide] *)

Lemma Decidable_dec : forall (P:Prop) {H: Decidable P} (A:Type) (x y:A),  
  exists (Q : {P}+{~P}),
  (if decide P then x else y) = (if Q then x else y).
Proof.
  intros. exists (classicT P). 
  rewrite decide_spec.
  tautotest P; case_if as C; case_if as C';
  first [ rewrite isTrue_True in C
        | rewrite isTrue_False in C
        | idtac ]; auto*; false*.
Qed.

Ltac case_if_on_tactic_core E Eq ::=
  match E with
  | decide ?P => 
      let Q := fresh in let E := fresh in
      forwards (Q&E): (@Decidable_dec P); 
      rewrite E in *; clear E; destruct Q 
  | _ =>
    match type of E with
    | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
    | _ => let X := fresh in 
           sets_eq <- X Eq: E;
           destruct X
    end
  end.

(** Rewriting lemma *)

Lemma istrue_decide : forall `{Decidable P},
  istrue (decide P) = P.
Proof. intros. rew_refl~. Qed.

Lemma decide_prove : forall `{Decidable P},
  P -> istrue (decide P).
Proof. intros. rewrite~ istrue_decide. Qed.



(* ********************************************************************** *)
(** * Comparable types *)

(** [Comparable A] asserts that there exists a decidable
    equality over values of type [A] *)

Class Comparable (A:Type) := make_comparable {
  comparable : forall (x y:A), Decidable (x = y) }.

Hint Resolve @comparable : typeclass_instances.
Extraction Inline comparable.

(** In classical logic, any type is comparable; of course,
    we do not want to use this lemma as an instance because 
    it cannot be extracted to executable code. *)

Lemma type_comparable : forall (A:Type), Comparable A.
Proof. constructor. intros. applys~ prop_decidable. Qed.

(** [Comparable] can be proved by exhibiting a boolean
    comparison function *)

Lemma comparable_beq : forall A (f:A->A->bool),
  (forall x y, (istrue (f x y)) <-> (x = y)) ->
  Comparable A.
Proof.
  introv H. constructors. intros. 
  applys decidable_make (f x y). 
  rewrite isTrue_def. extens.
  rewrite H. case_if; auto_false*.
Qed.

Extraction Inline comparable_beq.

(** [Comparable] can be proved by exhibiting a decidability
    result in the form of a strong sum *)

Lemma comparable_of_dec : forall (A:Type),
  (forall x y : A, {x = y} + {x <> y}) ->
  Comparable A.
Proof.
  introv H. constructors. intros.
  applys decidable_make (if H x y then true else false).
  rewrite isTrue_def. destruct (H x y); case_if*.
Qed.

(** Comparison for booleans *)

Instance bool_comparable : Comparable bool.
Proof.
  applys (comparable_beq Bool.eqb).
  destruct x; destruct y; simpl; rew_refl; auto_false*.
Qed.
