(**************************************************************************
* TLC: A library for Coq                                                  *
* Properties of logical connectives and functions                         *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics.
Require Export LibAxioms LibEqual.
Generalizable Variables A B P.


(* ********************************************************************** *)
(** * Inhabited types *)

(* ---------------------------------------------------------------------- *)
(** ** Typeclass for describing inhabited types *)

(** The proposition [Inhab A] captures the fact that the type [A] is 
    inhabited (i.e., there exists at least one value of type [A]). *)

Class Inhab (A:Type) : Prop := 
  { inhabited : (exists (x:A), True) }.

(* ---------------------------------------------------------------------- *)
(** ** Arbitrary values for inhabited types *)

(** The value [arbitrary] can be used as a dummy value at any place
    where a value of an inhabited type is expected. *)

Definition arbitrary `{Inhab A} : A :=
  proj1_sig (@indefinite_description A _ inhabited).

Extract Constant arbitrary => "(raise Not_found)".

(* ---------------------------------------------------------------------- *)
(** ** Inhabited types *)

(** Proving a type to be inhabited *)

Lemma prove_Inhab : forall (A:Type), A -> Inhab A.
Proof. intros A x. constructor. exists x. auto. Qed. 

(** Arrows are inhabited if their codomain is inhabited. *)

Instance arrow_inhab : forall A B {I:Inhab B},
  Inhab (A -> B).
Proof. intros. apply (prove_Inhab (fun _ => arbitrary)). Qed.



(* ********************************************************************** *)
(** * Non-constructive conditionals *)

(* ---------------------------------------------------------------------- *)
(** ** Excluded middle *)

(** Every proposition is either [True] or [False]. *)

Lemma classic : forall (P : Prop), P \/ ~ P.
Proof.
  intros.
  set (B1 := fun b => b = true \/ P).
  set (B2 := fun b => b = false \/ P).
  asserts H1: (ex B1). exists true. left~.
  asserts H2: (ex B2). exists false. left~.
  sets i1: (indefinite_description H1).
  sets i2: (indefinite_description H2).
  destruct (proj2_sig i1) as [HA|]; [|auto].  
  destruct (proj2_sig i2) as [HB|]; [|auto].
  right. intros HP. asserts EB: (B1 = B2).
    apply prop_ext_1. intros b. split; intros _; right; auto.
  subst i1 i2. destruct EB.
  rewrite (proof_irrelevance H2 H1) in HB. congruence.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Strong excluded middle *)

(** From classical logic and indefinite description, we can prove
    the strong (or informative) excluded middle, which allows Coq
    definitions to make a case analysis on the truth value of any
    proposition. *)

Lemma classicT : forall (P : Prop), {P} + {~ P}.
Proof.
  intros. pose (select := fun (b:bool) => if b then P else ~P).
  cuts (M,HP): { b:bool | select b }.
    destruct M. left~. right~.
  apply indefinite_description. 
  destruct (classic P). exists~ true. exists~ false.
Qed.

(** Simplification lemmas *)

Lemma classicT_left : forall (P : Prop) (H:P),
   classicT P = left _ H.
Proof. intros. destruct (classicT P). fequals. false~. Qed.

Lemma classicT_right : forall (P : Prop) (H:~P),
   classicT P = right _ H.
Proof. intros. destruct (classicT P). false~. fequals. Qed.

(* ---------------------------------------------------------------------- *)
(** ** If-then-else on propositions *)

(** The expression [If P then v1 else v2] can be used to build
    a conditional that depends on a proposition [P]. *)

Notation "'If' P 'then' v1 'else' v2" := 
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) : type_scope.

(** Lemmas to simplify If-then-else statement *)

Lemma If_l : forall (A:Type) (P:Prop) (x y : A), 
  P -> (If P then x else y) = x.
Proof. intros. case_if*. Qed.

Lemma If_r : forall (A:Type) (P:Prop) (x y : A), 
  ~ P -> (If P then x else y) = y.
Proof. intros. case_if*. Qed.

(** A lemma to prove an equality between two If-then-else *)

Lemma If_eq : forall (A : Type) (P P' : Prop) (x x' y y' : A),
  (P <-> P') -> (P -> x = x') -> (~P -> y = y') ->
  (If P then x else y) = (If P' then x' else y').
Proof. intros. do 2 case_if; auto*. Qed.

(** A simpler version of the above lemma *)

Lemma If_eq_simple : forall (A:Type) (P P':Prop) (x x' y y' : A), 
  (P <-> P') -> (x = x') -> (y = y') ->
  (If P then x else y) = (If P' then x' else y').
Proof. intros. subst. asserts_rewrite (P = P'). apply~ prop_ext. auto. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Consequences of clasical logic *)

(** Propositional completeness (degeneracy) *)

Lemma prop_degeneracy : forall (P : Prop),
   P = True \/ P = False.
Proof.
  intros. destruct (classic P).
    left. apply* prop_ext.
    right. apply* prop_ext.
Qed.

(** Independence of general premises *)

Lemma indep_general_premises : 
  forall `{Inhab A} (P : A -> Prop) (Q : Prop),
  (Q -> exists x, P x) -> (exists x, Q -> P x).
Proof.
  introv I M. destruct (classic Q).
  destruct* (M H). 
  exists arbitrary. auto_false.
Qed.

(** Small drinker's paradox *)

Lemma small_drinker_paradox : forall `{Inhab A} (P : A -> Prop), 
  exists x, (exists x, P x) -> P x.
Proof.
  intros A I P. destruct (classic (exists x, P x)).
  destruct H. exists x. auto.
  exists arbitrary. auto_false.
Qed.

(** The tactic [tautotest] helps performing case analysis on
    the propositions that are given to it as parameters. *)

Ltac tautotest_case P :=
  match type of P with
  | Prop => destruct (prop_degeneracy P)
  | bool => destruct P
  end.

Ltac tautotest_post :=
  subst; try solve [ intuition auto_false ].

Tactic Notation "tautotest" constr(P1) :=
  tautotest_case P1; tautotest_post.
Tactic Notation "tautotest" constr(P1) constr(P2) :=
  tautotest_case P1; tautotest_case P2; tautotest_post.
Tactic Notation "tautotest" constr(P1) constr(P2) constr(P3) :=
  tautotest_case P1; tautotest_case P2; tautotest_case P3; tautotest_post.


(* ********************************************************************** *)
(** * Additional logic connectives *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of Xor on propositions *)

(* TODO: should be defined simply as P <> Q *)

Definition Xor (P Q : Prop) :=
  (P /\ ~ Q) \/ (~ P /\ Q).

Hint Unfold Xor.

Notation "P '\+/' Q" := (Xor P Q)
  (at level 76, right associativity) : Logic_scope.

Open Scope Logic_scope.


(* ********************************************************************** *)
(** * Properties of logical combinators *)

Section CombinatorsProp.
Implicit Types P Q : Prop.

(* TODO: simplify the proofs using tautotest or rew_classic *)

(* ---------------------------------------------------------------------- *)
(** ** Properties of true and false propositions *)

(** Recall that the axiom [prop_ext] asserts that two equivalent 
    propositions are equal, i.e. [(P <-> Q) -> (P = Q)]. *)

(** Provable propositions are equal to [True], and contradictory
    propositions are equal to [False] *)

Lemma is_True : forall P, P -> P = True.
Proof. intros. extens*. Qed.

Lemma is_False : forall P, ~ P -> P = False.
Proof. intros. extens*. Qed.

Lemma is_True_inv : forall P, P = True -> P.
Proof. introv H. rewrite~ H. Qed.

Lemma is_False_inv : forall P, P = False -> ~P.
Proof. introv H. rewrite~ H. Qed.

(** True is not False *)

Lemma True_neq_False : True <> False.
Proof. intros K. rewrite~ <- K. Qed.

(** Proving two propositions not equal *)

Lemma prop_neq_l : forall P Q,
  (P <-> ~ Q) -> P <> Q.
Proof. intros. tautotest P Q. Qed.

Lemma prop_neq_r : forall P Q,
  (~ P <-> Q) -> P <> Q.
Proof. intros. tautotest P Q. Qed.

Lemma prop_neq_l_inv : forall P Q, 
  P <> Q -> (P <-> ~ Q).
Proof. intros. tautotest P Q. Qed.

Lemma prop_neq_r_inv : forall P Q,
  P <> Q -> (~ P <-> Q).
Proof. intros. tautotest P Q. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Double negation and contrapose *)

(** Double negation *)

Lemma not_not_elim : forall P, 
  ~ ~ P -> P.
Proof. intros. tautotest P. Qed.

Lemma not_not_intro : forall P, 
  P -> ~ ~ P.
Proof. auto. Qed.

(** Contrapose *)

Lemma contrapose_elim : forall P Q, 
  (~ Q -> ~ P) -> (P -> Q).
Proof. intros. tautotest P Q. Qed.

Lemma contrapose_intro : forall P Q,
  (Q -> P) -> (~ P -> ~ Q).
Proof. intros. tautotest P Q. Qed.

(** Negation cancel *)

Lemma not_cancel : forall P Q,  
  ((~P) = (~Q)) -> (P = Q).
Proof. introv H. extens. iff; apply not_not_elim. rewrite~ <- H. rewrite~ H. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Peirce rule and similar *)

(** Peirce's result: proving a fact by assuming its negation *)

Lemma assume_not : forall P, 
  (~ P -> P) -> P.
Proof. intros. tautotest P. Qed.

(** Proving a disjunction, assuming the negation of the other branch *)

Lemma classic_left : forall P Q, 
  (~ Q -> P) -> P \/ Q.
Proof. intros. tautotest P Q. Qed.

Lemma classic_right : forall P Q,
  (~ P -> Q) -> P \/ Q.
Proof. intros. tautotest P Q. Qed.

(** Same, but in forward style *)

Lemma case_classic_l : forall P Q, 
  P \/ Q -> (P \/ (~ P /\ Q)).
Proof. intros. tautotest P Q. Qed.

Lemma case_classic_r : forall P Q, 
  P \/ Q -> (Q \/ (P /\ ~ Q)).
Proof. intros. tautotest P Q. Qed.

End CombinatorsProp.

Hint Resolve is_True is_False True_neq_False.

(* ---------------------------------------------------------------------- *)
(** ** Properties of logical equivalence *)

Section EquivalenceProp.
Implicit Types P Q R : Prop.

(** Introduction *)

Lemma iff_intro : forall P Q : Prop,
  (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof. intros. tautotest P Q. Qed.

(** Reflexivity *)

Lemma iff_refl : forall P, 
  P <-> P.
Proof. intros. tautotest P. Qed.

(** Symmetry *)

Lemma iff_sym : forall P Q,
  (P <-> Q) -> (Q <-> P).
Proof. intros. tautotest P Q. Qed.

(** Transitivity *)

Lemma iff_trans : forall P Q R,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. intros. tautotest P Q R. Qed.

(** First projection *)

Lemma iff_1 : forall P Q,
  (P <-> Q) -> P -> Q.
Proof. intros. tautotest P Q. Qed.

(** Second projection *)

Lemma iff_2 : forall P Q,
  (P <-> Q) -> Q -> P.
Proof. intros. tautotest P Q. Qed.

(** Contrapose of the first projection *)

Lemma iff_neg_1 : forall P Q,
  (P <-> Q) -> ~ P -> ~ Q.
Proof. intros. tautotest P Q. Qed.

(** Contrapose of the second projection *)

Lemma iff_neg_2 : forall P Q,
  (P <-> Q) -> ~ Q -> ~ P.
Proof. intros. tautotest P Q. Qed.

(** Negation can change side of an equivalence *)

Lemma iff_not_swap : forall P Q, 
  ((~ P) <-> Q) = (P <-> (~ Q)).
Proof. intros. extens. tautotest P Q. Qed.

(** Negation can be cancelled on both sides *)

Lemma iff_not_cancel : forall P Q, 
  ((~ P) <-> (~Q)) = (P <-> Q).
Proof. intros. extens. tautotest P Q. Qed.

End EquivalenceProp.

(* ********************************************************************** *)
(** * Simplification of logical expressions by rewriting *)

Section Simpl.
Implicit Types P Q : Prop.
 
(* ---------------------------------------------------------------------- *)
(** ** Simplification of equality *)

Lemma prop_eq_True : forall P, (P = True) = P.
Proof. intros. apply* prop_ext. iff H. rewrite~ H. auto. Qed.

Lemma prop_eq_False : forall P, (P = False) = (~ P).
Proof. intros. apply* prop_ext. iff H. rewrite~ H. auto. Qed.

Lemma prop_eq_to_iff : forall P Q, (P = Q) = (P <-> Q).
Proof. intros. extens. iff. subst*. apply~ prop_ext. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Simplification of conjunction and disjunction *)

Lemma and_True_l : forall P, (True /\ P) = P.
Proof. intros. apply* prop_ext. Qed.

Lemma and_True_r : forall P, (P /\ True) = P.
Proof. intros. apply* prop_ext. Qed.

Lemma and_False_l : forall P, (False /\ P) = False.
Proof. intros. apply* prop_ext. Qed.

Lemma and_False_r : forall P, (P /\ False) = False.
Proof. intros. apply* prop_ext. Qed.

Lemma or_True_l : forall P, (True \/ P) = True.
Proof. intros. apply* prop_ext. Qed.

Lemma or_True_r : forall P, (P \/ True) = True.
Proof. intros. apply* prop_ext. Qed.

Lemma or_False_l : forall P, (False \/ P) = P.
Proof. intros. apply* prop_ext. Qed.

Lemma or_False_r : forall P, (P \/ False) = P.
Proof. intros. apply* prop_ext. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Distribution of negation *)

Lemma not_True : (~ True) = False.
Proof. intros. apply* prop_ext. Qed.

Lemma not_False : (~ False) = True.
Proof. intros. apply* prop_ext. Qed.

Lemma not_not : forall P, (~ ~ P) = P.
Proof. intros. apply prop_ext. tautotest P. Qed.

Lemma not_and : forall P Q, (~ (P /\ Q)) = (~ P \/ ~ Q).
Proof. intros. apply prop_ext. tautotest P Q. Qed.

Lemma not_or : forall P Q, (~ (P \/ Q)) = (~ P /\ ~ Q).
Proof. intros. apply prop_ext. tautotest P Q. Qed.

Lemma not_impl : forall P Q, (~ (P -> Q)) = (P /\ ~ Q).
Proof. intros. apply prop_ext. tautotest P Q. Qed.

Lemma not_or_nots : forall P Q, (~ (~ P \/ ~ Q)) = (P /\ Q).
Proof. intros. apply prop_ext. tautotest P Q. Qed.

Lemma not_and_nots : forall P Q, (~ (~ P /\ ~ Q)) = (P \/ Q).
Proof. intros. apply prop_ext. tautotest P Q. Qed.

End Simpl.

Section ClassicQuantifiers.
Variables (A : Type).
Implicit Types P : A -> Prop.

(** Three auxiliary facts *)

Lemma exists_from_not : forall P,
  ~ (forall x, ~ P x) -> (exists x, P x).
Proof. intros. apply* not_not_elim. Qed.

Lemma forall_from_not : forall P,
  ~ (exists x, ~ P x) -> (forall x, P x).
Proof. intros. apply* not_not_elim. Qed.

Lemma not_not_pred_1 : forall A (P:A->Prop), 
  P = (fun x => ~ ~ (P x)).
Proof. intros. extens. intros. rewrite* not_not. Qed.

(** Rewriting rules for quantifiers *)

Lemma not_forall : forall P,
  (~ (forall x, P x)) = (exists x, ~ P x).
Proof.
  extens. iff.
  apply exists_from_not. rewrite~ (not_not_pred_1 P) in H.
  intros M. destruct H as [x Cx]. eauto.  
Qed. 

Lemma not_exists : forall P,
  (~ (exists x, P x)) = (forall x, ~ P x).
Proof.
  intros. apply not_cancel. rewrite not_forall.
  rewrite not_not. set (P':=P) at 1. rewrite~ (not_not_pred_1 P').
Qed.

Lemma not_forall_not : forall P,
  (~ (forall x, ~ P x)) = (exists x, P x).
Proof.
  intros. rewrite not_forall. 
   set (P':=P) at 2. rewrite~ (not_not_pred_1 P').
Qed.

Lemma not_exists_not : forall P,
  (~ (exists x, ~ P x)) = (forall x, P x).
Proof.
  intros. rewrite not_exists. 
   set (P':=P) at 2. rewrite~ (not_not_pred_1 P').
Qed.

End ClassicQuantifiers.

(* ---------------------------------------------------------------------- *)
(** ** Tactic for simplifying expressions *)

(** The tactic [rew_logic] can be used to automatically
    simplify logical expressions. Syntax [rew_logic in H]
    and [rew_logic in *] are also available. *)

Hint Rewrite not_not not_and not_or not_impl not_True not_False 
  not_forall_not not_exists_not not_forall not_exists
  prop_eq_True prop_eq_False prop_eq_to_iff
  and_True_l and_True_r and_False_l and_False_r
  or_True_l or_True_r or_False_l or_False_r not_False not_True
  : rew_logic.

Tactic Notation "rew_logic" := 
  autorewrite with rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) := 
  autorewrite with rew_logic in H.
Tactic Notation "rew_logic" "in" "*" := 
  autorewrite with rew_logic in *.

Tactic Notation "rew_logic" "~" := 
  rew_logic; auto_tilde.
Tactic Notation "rew_logic" "~" "in" hyp(H) := 
  rew_logic in H; auto_tilde.
Tactic Notation "rew_logic" "~" "in" "*" := 
  rew_logic in *; auto_tilde.

Tactic Notation "rew_logic" "*" := 
  rew_logic; auto_star.
Tactic Notation "rew_logic" "*" "in" hyp(H) := 
  rew_logic in H; auto_star.
Tactic Notation "rew_logic" "*" "in" "*" := 
  rew_logic in *; auto_star.

(** The tactic [rew_logic'] is similar except that it only
    tries to apply the most frequently useful rules, in order
    to run faster. *)

Hint Rewrite not_not not_and not_or not_True not_False : rew_logic'.

Tactic Notation "rew_logic'" := 
  autorewrite with rew_logic'.
Tactic Notation "rew_logic'" "in" hyp(H) := 
  autorewrite with rew_logic' in H.
Tactic Notation "rew_logic'" "in" "*" := 
  autorewrite with rew_logic' in *.

Tactic Notation "rew_logic'" "~" := 
  rew_logic'; auto_tilde.
Tactic Notation "rew_logic'" "~" "in" hyp(H) := 
  rew_logic' in H; auto_tilde.
Tactic Notation "rew_logic'" "~" "in" "*" := 
  rew_logic' in *; auto_tilde.

Tactic Notation "rew_logic'" "*" := 
  rew_logic'; auto_star.
Tactic Notation "rew_logic'" "*" "in" hyp(H) := 
  rew_logic' in H; auto_star.
Tactic Notation "rew_logic'" "*" "in" "*" := 
  rew_logic' in *; auto_star.

(** The tactic [tests: P] can be used to tests whether the proposition [P]
    is true or not. If [P] is an equality, it is substituted. Use the
    tactic [tests_nosubst: P] to disable the automated substitution.
    Use the tactic [tests_basic: P] to moreover disable simplification
    of logical expressions.
    To name the resulting hypotheses use [tests I: P], or [tests I1 I2: P]
    to assign different names to both sides.
    (In LibReflect, the tactic is extended so that [P] can be a boolean.) *)

Ltac tests_ssum_base E H1 H2 :=
  destruct E as [H1|H2].

Ltac tests_prop_base E H1 H2 :=
  tests_ssum_base (classicT E) H1 H2.

Ltac tests_dispatch E H1 H2 :=
  match type of E with
  | Prop => tests_prop_base E H1 H2
  | {_}+{_} => tests_ssum_base E H1 H2
  end.

Ltac tests_post H introstac :=
  tryfalse; rew_logic in H; revert H; 
  introstac tt; tryfalse.

Ltac tests_post_subst H I :=
  tests_post H ltac:(fun _ => first [ intro_subst_hyp | intros I ]).

Ltac tests_post_nosubst H I :=
  tests_post H ltac:(fun _ => intros I).

Ltac tests_base E I1 I2 tests_post :=
  let H1 := fresh "TEMP" in
  let H2 := fresh "TEMP" in
  tests_dispatch E H1 H2;  
    [ tests_post H1 I1
    | tests_post H2 I2 ].

Tactic Notation "tests" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E) := 
  tests_base E I1 I2 ltac:(tests_post_subst).
Tactic Notation "tests" simple_intropattern(I) ":" constr(E) :=
  tests I I: E.
Tactic Notation "tests" ":" constr(E) :=
  let I := fresh "C" in tests I: E.
Tactic Notation "tests" "~" ":" constr(E) :=
  tests: E; auto_tilde.
Tactic Notation "tests" "*" ":" constr(E) :=
  tests: E; auto_star.

Tactic Notation "tests_nosubst" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E) := 
  tests_base E I1 I2 ltac:(tests_post_nosubst).
Tactic Notation "tests_nosubst" simple_intropattern(I) ":" constr(E) :=
  tests I I: E.
Tactic Notation "tests_nosubst" ":" constr(E) :=
  let I := fresh "C" in tests I: E.
Tactic Notation "tests_nosubst" "~" ":" constr(E) :=
  tests: E; auto_tilde.
Tactic Notation "tests_nosubst" "*" ":" constr(E) :=
  tests: E; auto_star.

Tactic Notation "tests_basic" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E) :=
  tests_dispatch E I1 I2.
Tactic Notation "tests_basic" simple_intropattern(I1) ":" constr(E) :=
  tests_basic I1 I1: E.
Tactic Notation "tests_basic" ":" constr(E) :=
  let C := fresh "C" in tests_basic C: E.


(* ********************************************************************** *)
(** * Predicate combinators, comparison and compatibility *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of predicate combinators *)

Definition pred_true {A : Type} := 
  fun _:A => True.

Definition pred_false {A : Type} := 
  fun _:A => False.

Definition pred_not (A : Type) (P : A -> Prop) :=
  fun x => ~ (P x).

Definition pred_and (A : Type) (P Q : A -> Prop) :=
  fun x => P x /\ Q x.

Definition pred_or (A : Type) (P Q : A -> Prop) :=
  fun x => P x \/ Q x.

Definition pred_impl (A : Type) (P Q : A -> Prop) :=
  fun x => P x -> Q x.

Hint Unfold pred_true pred_false.

(* ---------------------------------------------------------------------- *)
(** ** Properties of combinators *)

(* Todo: reformulate using [pred_all] and [pred_and] *)

Lemma pred_conj_forall_distrib : forall A (P Q: A->Prop), 
  ((forall x, P x) /\ (forall x, Q x)) = (forall x, P x /\ Q x).
Proof. intros. apply prop_ext. iff H. auto*. split; intros x; apply* (H x). Qed.

(* ---------------------------------------------------------------------- *)
(** ** Order on predicates *)

Definition pred_le (A : Type) (P Q : A -> Prop) :=
  forall x, P x -> Q x.

Lemma pred_le_refl : forall A (P : A -> Prop),
  pred_le P P.
Proof. unfolds~ pred_le. Qed.

Lemma pred_le_trans : forall A (Q P R : A -> Prop), 
  pred_le P Q -> pred_le Q R -> pred_le P R.
Proof. unfolds~ pred_le. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Compatibility of a predicate with an equivalence relation *)

(** A predicate is compatible with an equivalence relation [E]
    iff it is either true or false on each equivalence class. *)

Definition pred_compatible A (E:A->A->Prop) (Q:A->Prop) :=
  forall x y, Q x -> E y x -> Q y.



(* ********************************************************************** *)
(** * Existentials *)

(* ---------------------------------------------------------------------- *)
(** ** A shorthand for [ex_intro] with more implicit arguments *)

Definition ex_intro' A (x:A) (P:A->Prop) (H:P x) := 
  @ex_intro A P x H.

Implicit Arguments ex_intro' [A [P] [H]].

(* ---------------------------------------------------------------------- *)
(** * Properties of unique existentials *)

(** Alternative definition of uniqueness (copied from LibPrelude) *)
(* TODO: add comments *)

Definition unique_st (A : Type) (P : A -> Prop) (x : A) :=
  P x /\ forall y, P y -> y = x.

Hint Unfold unique_st. 

Definition ex_unique (A : Type) (P : A -> Prop) :=
  ex (unique_st P). 

Notation "'exists' ! x , P" := (ex_unique (fun x => P))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x ,  '/  ' P ']'") : type_scope.
Notation "'exists' ! x : A , P" :=
  (ex_unique (fun x:A => P))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x  :  A ,  '/  ' P ']'") : type_scope.

Definition at_most_one (A : Type) (P : A -> Prop) :=
  forall x y, P x -> P y -> x = y.

Section UniqueProp.
Variables (A : Type) (P : A -> Prop).

Lemma ex_unique_to_ex : ex_unique P -> ex P.
Proof. introv [x [H U]]. eauto. Qed.

Lemma ex_unique_to_at_most_one : 
  ex_unique P -> at_most_one P.
Proof.
  introv [a [H U]] Px Py. apply (eq_trans a).
  auto. rewrite~ <- (U y).
Qed.

Lemma ex_unique_from_ex_at_most_one : 
  ex P -> at_most_one P -> ex_unique P.
Proof. introv [x Px] H. exists x. split~. Qed.

End UniqueProp.

Definition at_most_one_upto (A : Type) (E : A -> A -> Prop) (P : A -> Prop) :=
  forall x y, P x -> P y -> E x y.



(* ********************************************************************** *)
(** * Conjunctions *)

(* ---------------------------------------------------------------------- *)
(** ** Changing the order of branches *)

Lemma conj_swap: forall (P Q: Prop), P -> Q -> Q /\ P.
Proof. auto*. Qed.

Lemma conj_dup_r : forall P Q : Prop,
  Q -> (Q -> P) -> P /\ Q.
Proof. auto*. Qed.

Lemma conj_dup_l : forall P Q : Prop,
  P -> (P -> Q) -> P /\ Q.
Proof. auto*. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Parallel strengthening of a conjunction *)

Lemma conj_strengthen_2 : forall (Q1 Q2 P1 P2 : Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> 
  (Q1 /\ Q2) -> (P1 /\ P2).
Proof. auto*. Qed.

Lemma conj_strengthen_3 : forall (Q1 Q2 Q3 P1 P2 P3 : Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> (Q3 -> P3) -> 
  (Q1 /\ Q2 /\ Q3) -> (P1 /\ P2 /\ P3).
Proof. auto*. Qed.

Lemma conj_strengthen_4 : forall (Q1 Q2 Q3 Q4 P1 P2 P3 P4 : Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> (Q3 -> P3) -> (Q4 -> P4) -> 
  (Q1 /\ Q2 /\ Q3 /\ Q4) -> (P1 /\ P2 /\ P3 /\ P4).
Proof. auto*. Qed.

Lemma conj_strengthen_5 : forall (Q1 Q2 Q3 Q4 Q5 P1 P2 P3 P4 P5 : Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> (Q3 -> P3) -> (Q4 -> P4) -> (Q5 -> P5) ->
  (Q1 /\ Q2 /\ Q3 /\ Q4 /\ Q5) -> (P1 /\ P2 /\ P3 /\ P4 /\ P5).
Proof. auto*. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Projections of lemmas concluding on a conjunction *)

Section ProjLemma.
Variables
  (A1 : Type) 
  (A2 : forall (x1 : A1), Type) 
  (A3 : forall (x1 : A1) (x2 : A2 x1), Type)
  (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type)
  (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type)
  (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type)
  (A7 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5), Type)
  (A8 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6), Type)
  (A9 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6) (x8 : A8 x7), Type)
  (A10 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6) (x8 : A8 x7) (x9 : A9 x8), Type)
  (A11 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6) (x8 : A8 x7) (x9 : A9 x8) (x10 : A10 x9), Type).

Lemma proj_lemma_1 : forall (P Q : forall (x1:A1), Prop),
  (forall x1, P x1 /\ Q x1) -> 
  (forall x1, P x1) /\
  (forall x1, Q x1).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_2 : forall (P Q : forall (x1:A1) (x2:A2 x1), Prop),
  (forall x1 x2, P x1 x2 /\ Q x1 x2) -> 
  (forall x1 x2, P x1 x2) /\
  (forall x1 x2, Q x1 x2).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_3 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), Prop),
  (forall x1 x2 x3, P x1 x2 x3 /\ Q x1 x2 x3) -> 
  (forall x1 x2 x3, P x1 x2 x3) /\
  (forall x1 x2 x3, Q x1 x2 x3).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_4 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3), Prop),
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 /\ Q x1 x2 x3 x4) -> 
  (forall x1 x2 x3 x4, P x1 x2 x3 x4) /\
  (forall x1 x2 x3 x4, Q x1 x2 x3 x4).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_5 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4), Prop),
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 /\ Q x1 x2 x3 x4 x5) -> 
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5) /\
  (forall x1 x2 x3 x4 x5, Q x1 x2 x3 x4 x5).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_6 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5), Prop),
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 /\ Q x1 x2 x3 x4 x5 x6) -> 
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6) /\
  (forall x1 x2 x3 x4 x5 x6, Q x1 x2 x3 x4 x5 x6).
Proof. introv H. split; intros; forwards*: H. Qed.

(* Commented out for efficiency of compilation

Lemma proj_lemma_7 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 /\ Q x1 x2 x3 x4 x5 x6 x7) -> 
  (forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7) /\
  (forall x1 x2 x3 x4 x5 x6 x7, Q x1 x2 x3 x4 x5 x6 x7).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_8 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 /\ Q x1 x2 x3 x4 x5 x6 x7 x8) -> 
  (forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8, Q x1 x2 x3 x4 x5 x6 x7 x8).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_9 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7) (x9:A9 x8), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9) -> 
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, Q x1 x2 x3 x4 x5 x6 x7 x8 x9).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_10 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7) (x9:A9 x8) (x10:A10 x9), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) -> 
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10).
Proof. introv H. split; intros; forwards*: H. Qed.

Lemma proj_lemma_11 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7) (x9:A9 x8) (x10:A10 x9) (x11:A11 x10), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) -> 
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).
Proof. introv H. split; intros; forwards*: H. Qed.

*)

End ProjLemma.

Implicit Arguments proj_lemma_1 [A1 P Q].
Implicit Arguments proj_lemma_2 [A1 A2 P Q].
Implicit Arguments proj_lemma_3 [A1 A2 A3 P Q].
Implicit Arguments proj_lemma_4 [A1 A2 A3 A4 P Q].
Implicit Arguments proj_lemma_5 [A1 A2 A3 A4 A5 P Q].
Implicit Arguments proj_lemma_6 [A1 A2 A3 A4 A5 A6 P Q].
(* Commented out for efficiency of compilation
Implicit Arguments proj_lemma_7 [A1 A2 A3 A4 A5 A6 A7 P Q].
Implicit Arguments proj_lemma_8 [A1 A2 A3 A4 A5 A6 A7 A8 P Q].
Implicit Arguments proj_lemma_9 [A1 A2 A3 A4 A5 A6 A7 A8 A9 P Q].
Implicit Arguments proj_lemma_10 [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 P Q].
Implicit Arguments proj_lemma_11 [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 P Q].
*)


