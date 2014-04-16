(**************************************************************************
* TLC: A library for Coq                                                  *
* Binary relations                                                        *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibBool LibLogic LibProd LibSum.
Require Export LibOperation.


(* ********************************************************************** *)
(** * Generalities on binary relations *)

Definition binary (A : Type) := A -> A -> Prop.

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

Instance binary_inhab : forall A, Inhab (binary A).
Proof. intros. apply (prove_Inhab (fun _ _ => True)). Qed.

(* ---------------------------------------------------------------------- *)
(** ** Extensionality *)

Lemma binary_extensional : forall A (R1 R2:binary A),
  (forall x y, R1 x y <-> R2 x y) -> R1 = R2.
Proof. intros_all. apply~ prop_ext_2. Qed.

Instance binary_extensional_inst : forall A, Extensional (binary A).
Proof. intros. apply (Build_Extensional _ (@binary_extensional A)). Defined.


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section Properties.
Variables (A:Type).
Implicit Types x y z : A.
Implicit Types R : binary A.

(** Reflexivity, irreflexivity, transitivity, symmetry, totality *)

Definition refl R := 
  forall x, R x x.
Definition irrefl R := 
  forall x, ~ (R x x).
Definition trans R := 
  forall y x z, R x y -> R y z -> R x z.
Definition sym R := 
  forall x y, R x y -> R y x.
Definition asym R := 
  forall x y, R x y -> ~ R y x.
Definition total R :=
  forall x y, R x y \/ R y x.

(** Antisymmetry with respect to an equivalence relation, 
    antisymmetry with respect to Leibnitz equality,
     i.e. [forall x y, R x y -> R y x -> x = y] *)

Definition antisym_wrt (E:binary A) R :=
  forall x y, R x y -> R y x -> E x y.
Definition antisym := 
  antisym_wrt (@eq A).

(** Inclusion between relations *)

Definition incl R1 R2 :=
  forall x y, R1 x y -> R2 x y.

(** Equality between relations *)

Lemma rel_eq_intro : forall R1 R2,
  (forall x y, R1 x y <-> R2 x y) -> R1 = R2.
Proof. intros. extens*. Qed.

Lemma rel_eq_elim : forall R1 R2,
  R1 = R2 -> (forall x y, R1 x y <-> R2 x y).
Proof. intros. subst*. Qed.

End Properties.

(* ---------------------------------------------------------------------- *)
(** ** Constructions *)

Section Constructions.
Variable (A : Type).
Implicit Types R : binary A.
Implicit Types x y z : A.

(** The empty relation *)

Definition empty : binary A :=
  fun x y => False.

(** Swap (i.e. symmetric, converse, or transpose) of a relation *)
 
Definition flip R : binary A := 
  fun x y => R y x.

(** Complement of a relation *)
 
Definition compl R : binary A := 
  fun x y => ~ R y x.

(** Union of two relations *)

Definition union R1 R2 : binary A :=
  fun x y => R1 x y \/ R2 x y.

(** Strict order associated with an order, wrt Leibnitz' equality *)

Definition strict R : binary A :=
  fun x y => R x y /\ x <> y.

(** Large order associated with an order, wrt Leibnitz' equality *)

Definition large R : binary A :=
  fun x y => R x y \/ x = y.

End Constructions.

(** Inverse image *)

Definition inverse_image (A B:Type) (R:binary B) (f:A->B) : binary A :=
  fun x y => R (f x) (f y).

(** Pointwise product *)

Definition prod2 (A1 A2:Type) 
 (R1:binary A1) (R2:binary A2) : binary (A1*A2) :=
  fun p1 p2 : A1*A2 => match p1,p2 with (x1,x2),(y1,y2) => 
    R1 x1 y1 /\ R2 x2 y2 end.

Definition prod3 (A1 A2 A3:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) 
 : binary (A1*A2*A3) := 
  prod2 (prod2 R1 R2) R3.

Definition prod4 (A1 A2 A3 A4:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4) 
 : binary (A1*A2*A3*A4) := 
  prod2 (prod3 R1 R2 R3) R4.

Tactic Notation "unfold_prod" :=
  unfold prod4, prod3, prod2.

Tactic Notation "unfolds_prod" :=
  unfold prod4, prod3, prod2 in *.

(** Lexicographical order *)

Definition lexico2 {A1 A2} (R1:binary A1) (R2:binary A2)
  : binary (A1*A2) :=
  fun p1 p2 : A1*A2 => let (x1,x2) := p1 in let (y1,y2) := p2 in
  (R1 x1 y1) \/ (x1 = y1) /\ (R2 x2 y2).

Definition lexico3 {A1 A2 A3} 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) : binary (A1*A2*A3) :=
  lexico2 (lexico2 R1 R2) R3.

Definition lexico4 {A1 A2 A3 A4}
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4) 
 : binary (A1*A2*A3*A4) :=
  lexico2 (lexico3 R1 R2 R3) R4.

Tactic Notation "unfold_lexico" :=
  unfold lexico4, lexico3, lexico2.

Tactic Notation "unfolds_lexico" :=
  unfold lexico4, lexico3, lexico2 in *.


(* ---------------------------------------------------------------------- *)
(** ** Properties of constructions *)

Section ConstructionsProp.
Variable (A : Type).
Implicit Types R : binary A.
Implicit Types x y z : A.

Lemma refl_elim : forall x y R,
  refl R -> x = y -> R x y.
Proof. intros_all. subst~. Qed.

Lemma sym_elim : forall x y R,
  sym R -> R x y -> R y x.
Proof. introv Sy R1. apply* Sy. Qed.

Lemma antisym_elim : forall x y R,
  antisym R -> R x y -> R y x -> x <> y -> False.
Proof. intros_all*. Qed.

Lemma irrefl_neq : forall R,
  irrefl R -> 
  forall x y, R x y -> x <> y. 
Proof. introv H P E. subst. apply* H. Qed.

Lemma irrefl_elim : forall R,
  irrefl R -> 
  forall x, R x x -> False. 
Proof. introv H P. apply* H. Qed.

Lemma sym_to_eq : forall R,
  sym R -> 
  forall x y, R x y = R y x.
Proof. introv H. intros. apply prop_ext. split; apply H. Qed.

Lemma sym_flip : forall R,
  sym R -> flip R = R.
Proof. intros. unfold flip. apply* prop_ext_2. Qed.

Lemma trans_strict : forall R,
  trans R -> antisym R -> trans (strict R).
Proof. 
  introv T S. unfold strict. introv [H1 H2] [H3 H4]. split. 
    apply* T.
    intros K. subst. apply H2. apply~ S.
Qed.

Lemma flip_flip : forall R, 
  flip (flip R) = R.
Proof. intros. apply* prop_ext_2. Qed.

Lemma flip_refl : forall R,
  refl R -> refl (flip R).
Proof. intros_all. unfolds flip. auto. Qed.

Lemma flip_trans : forall R,
  trans R -> trans (flip R).
Proof. intros_all. unfolds flip. eauto. Qed.

Lemma flip_antisym : forall R,
  antisym R -> antisym (flip R).
Proof. intros_all. unfolds flip. auto. Qed.

Lemma flip_asym : forall R,
  asym R -> asym (flip R).
Proof. intros_all. unfolds flip. apply* H. Qed.

Lemma flip_total : forall R,
  total R -> total (flip R).
Proof. intros_all. unfolds flip. auto. Qed.

Lemma flip_strict : forall R,
  flip (strict R) = strict (flip R).
Proof. intros. unfold flip, strict. apply* prop_ext_2. Qed.

Lemma flip_large : forall R,
  flip (large R) = large (flip R).
Proof. intros. unfold flip, large. apply* prop_ext_2. Qed.

Lemma large_refl : forall R,
  refl (large R).
Proof. unfold large. intros_all~. Qed.

Lemma large_trans : forall R,
  trans R -> trans (large R).
Proof. unfold large. introv Tr [H1|E1] [H2|E2]; subst*. Qed.

Lemma large_antisym : forall R,
  antisym R -> antisym (large R).
Proof. introv T. introv H1 H2. (* todo: bug introv *)
  unfolds large. destruct H1; destruct H2; auto. Qed.

Lemma large_total : forall R,
  total R -> total (large R).
Proof. unfold large. intros_all~. destruct* (H x y). Qed.

Lemma strict_large : forall R,
  irrefl R -> strict (large R) = R.
Proof.
  intros. unfold large, strict. apply prop_ext_2.
  intros_all. split; intros K.
  auto*.
  split. left*. apply* irrefl_neq. 
Qed.

Lemma large_strict : forall R,
  refl R -> large (strict R) = R.
Proof. 
  intros. unfold large, strict. apply prop_ext_2. 
  intros_all. split; intros K.
  destruct K. auto*. subst*.
  destruct (classic (x1 = x2)). subst. right*. left*.
  (* todo: cases *)
Qed.

Lemma double_incl : forall R1 R2,
  incl R1 R2 -> incl R2 R1 -> R1 = R2.
Proof. unfolds incl. intros. apply* prop_ext_2. Qed. 

Lemma flip_injective : injective (@flip A).
Proof.
  intros R1 R2 E. apply prop_ext_2. intros x y.
  unfolds flip. rewrite* (func_same_2 y x E).
Qed.

Lemma eq_by_flip_l : forall R1 R2,
  R1 = flip R2 -> flip R1 = R2.
Proof. intros. apply flip_injective. rewrite~ flip_flip. Qed.

Lemma eq_by_flip_r : forall R1 R2,
  flip R1 = R2 -> R1 = flip R2.
Proof. intros. apply flip_injective. rewrite~ flip_flip. Qed.

(* TODO: do we really need this extensional version? *)

Lemma flip_flip_applied : forall R x y, 
  (flip (flip R)) x y = R x y.
Proof. auto. Qed.

End ConstructionsProp.

Lemma trans_elim : forall A (y x z : A) R,
  trans R -> R x y -> R y z -> R x z.
Proof. introv Tr R1 R2. apply* Tr. Qed.

Lemma trans_sym : forall A (y x z : A) R,
  trans R -> sym R -> R z y -> R y x -> R x z.
Proof. introv Tr Sy R1 R2. apply* Tr. Qed.

Lemma trans_sym_1 : forall A (y x z : A) R,
  trans R -> sym R -> R y x -> R y z -> R x z.
Proof. introv Tr Sy R1 R2. apply* Tr. Qed.

Lemma trans_sym_2 : forall A (y x z : A) R,
  trans R -> sym R -> R x y -> R z y -> R x z.
Proof. introv Tr Sy R1 R2. apply* Tr. Qed.

Implicit Arguments trans_elim [A x z R].
Implicit Arguments trans_sym [A x z R].
Implicit Arguments trans_sym_1 [A x z R].
Implicit Arguments trans_sym_2 [A x z R].

(** Other forms of transitivity *)

Lemma large_strict_trans : forall A y x z (R:binary A),
  trans R -> large R x y -> R y z -> R x z.
Proof. introv T [E|H] H'; subst*. Qed.

Lemma strict_large_trans : forall A y x z (R:binary A),
  trans R -> R x y -> large R y z -> R x z.
Proof. introv T H [E|H']; subst*. Qed.



(* ---------------------------------------------------------------------- *)
(** ** Properties of inclusion *)

Lemma incl_refl : forall A (R:binary A), incl R R.
Proof. unfolds incl. auto. Qed.

Hint Resolve incl_refl. 

Lemma lexico2_incl : forall A1 A2
 (R1 R1':binary A1) (R2 R2':binary A2),
  incl R1 R1' -> incl R2 R2' -> incl (lexico2 R1 R2) (lexico2 R1' R2').
Proof. 
  introv I1 I2. intros [x1 x2] [y1 y2] [H1|[H1 H2]].
  left~. subst. right~.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of lexicographical composition *)

Section LexicoApp.
Variables (A1 A2 A3 A4:Type). 
Variables (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4). 

Lemma lexico2_app_1 : forall x1 x2 y1 y2,
  R1 x1 y1 -> 
  lexico2 R1 R2 (x1,x2) (y1,y2).
Proof. intros. left~. Qed.

Lemma lexico2_app_2 : forall x1 x2 y1 y2,
  x1 = y1 -> R2 x2 y2 -> 
  lexico2 R1 R2 (x1,x2) (y1,y2).
Proof. intros. right~. Qed.

Lemma lexico3_app_1 : forall x1 x2 x3 y1 y2 y3,
  R1 x1 y1 -> 
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof. intros. left. left~. Qed.

Lemma lexico3_app_2 : forall x1 x2 x3 y1 y2 y3,
  x1 = y1 -> R2 x2 y2 -> 
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof. intro. left. right~. Qed.

Lemma lexico3_app_3 : forall x1 x2 x3 y1 y2 y3,
  x1 = y1 -> x2 = y2 -> R3 x3 y3 -> 
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof. intros. right~. Qed.

Lemma lexico4_app_1 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  R1 x1 y1 -> 
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof. intros. left. left. left~. Qed.

Lemma lexico4_app_2 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> R2 x2 y2 -> 
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof. intros. left. left. right~. Qed.

Lemma lexico4_app_3 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> x2 = y2 -> R3 x3 y3 -> 
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof. intros. left. right~. Qed.

Lemma lexico4_app_4 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> R4 x4 y4 -> 
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof. intros. right~. Qed.

End LexicoApp.

(** Transitivity *)

Lemma lexico2_trans : forall A1 A2 
 (R1:binary A1) (R2:binary A2),
  trans R1 -> trans R2 -> trans (lexico2 R1 R2).
Proof.
  introv Tr1 Tr2. intros [x1 x2] [y1 y2] [z1 z2] Rxy Ryz.
  simpls. destruct Rxy as [L1|[Eq1 L1]]; 
   destruct Ryz as [M2|[Eq2 M2]]; subst*.
Qed.

Lemma lexico3_trans : forall A1 A2 A3 
 (R1:binary A1) (R2:binary A2) (R3:binary A3),
  trans R1 -> trans R2 -> trans R3 -> trans (lexico3 R1 R2 R3).
Proof.
  introv Tr1 Tr2 Tr3. applys~ lexico2_trans. applys~ lexico2_trans.
Qed.

Lemma lexico4_trans : forall A1 A2 A3 A4 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  trans R1 -> trans R2 -> trans R3 -> trans R4 -> trans (lexico4 R1 R2 R3 R4).
Proof.
  introv Tr1 Tr2 Tr3. applys~ lexico3_trans. applys~ lexico2_trans.
Qed.



(* ********************************************************************** *)
(** * Equivalence relations *)

Record equiv A (R:binary A) :=
 { equiv_refl : refl R;
   equiv_sym : sym R;
   equiv_trans : trans R }. 

(** Equality is an equivalence *)

Lemma eq_equiv : forall A, equiv (@eq A).
Proof. intros. constructor; intros_all; subst~. Qed.

Hint Resolve eq_equiv.

(** Symmetric of an equivalence is an equivalence *)

Lemma flip_equiv : forall A (E:binary A),
  equiv E -> equiv (flip E).
Proof.
  introv Equi. unfold flip. constructor; intros_all*.
Qed.

(** Product of two equivalences is an equivalence *)

Lemma prod2_equiv : forall A1 A2 (E1:binary A1) (E2:binary A2),
  equiv E1 -> equiv E2 -> equiv (prod2 E1 E2).
Proof.
  introv Equi1 Equi2. constructor.
  intros [x1 x2]. simple*.
  intros [x1 x2] [y1 y2]. simple*.
  intros [x1 x2] [y1 y2] [z1 z2]. simple*.
Qed.

(* todo: other arities of Prod *)


(**************************************************************************)
(* * Closures *)

Section Closures.
Variables (A : Type) (R : binary A).

(* ---------------------------------------------------------------------- *)
(** ** Constructions *)

(** Reflexive-transitive closure ( R* ) *)

Inductive rtclosure : binary A :=
  | rtclosure_refl : forall x,
      rtclosure x x
  | rtclosure_step : forall y x z,
      R x y -> rtclosure y z -> rtclosure x z.

(** Transitive closure ( R+ ) *)

Inductive tclosure : binary A :=
  | tclosure_intro : forall x y z,
     R x y -> rtclosure y z -> tclosure x z.

(** Another definition of transitive closure ( R+ ) *)

Inductive tclosure' : binary A :=
  | tclosure'_step : forall x y,  
     R x y -> tclosure' x y
  | tclosure'_trans : forall y x z,
     tclosure' x y -> tclosure' y z -> tclosure' x z.

(** Symmetric-transitive closure *)

Inductive stclosure (A:Type) (R:binary A) : binary A :=
  | stclosure_step : forall x y,
      R x y -> stclosure R x y
  | stclosure_sym : forall x y, 
      stclosure R x y -> stclosure R y x
  | stclosure_trans : forall y x z,
      stclosure R x y -> stclosure R y z -> stclosure R x z.

(* TODO Reflexive-symmetric-transitive closure ( R== ) 

Inductive equiv : binary A :=
  | equiv_step : forall x y,
      R x y -> equiv x y
  | equiv_refl : forall x,
      equiv x x
  | equiv_sym : forall x y, 
      equiv x y -> equiv y x
  | equiv_trans : forall y x z,
      equiv x y -> equiv y z -> equiv x z.
*)


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Hint Constructors tclosure rtclosure equiv.

Lemma rtclosure_once : forall x y,
  R x y -> rtclosure x y.
Proof. auto*. Qed.

Hint Resolve rtclosure_once.

Lemma rtclosure_trans : trans rtclosure.  
Proof. introv R1 R2. induction* R1. Qed.

Lemma rtclosure_last : forall y x z,
  rtclosure x y -> R y z -> rtclosure x z.
Proof. introv R1 R2. induction* R1. Qed.

Hint Resolve rtclosure_trans.

Lemma tclosure_once : forall x y,
  R x y -> tclosure x y.  
Proof. eauto. Qed.

Lemma tclosure_rtclosure : forall x y,
  tclosure x y -> rtclosure x y.  
Proof. intros. destruct* H. Qed.

Hint Resolve tclosure_once tclosure_rtclosure.

Lemma tclosure_rtclosure_step : forall x y z,
  rtclosure x y -> R y z -> tclosure x z.
Proof. intros. induction* H. Qed.

Lemma tclosure_step_rtclosure : forall x y z,
  R x y -> rtclosure y z -> tclosure x z.
Proof. intros. gen x. induction* H0. Qed.

Lemma tclosure_step_tclosure : forall x y z,
  R x y -> tclosure y z -> tclosure x z.
Proof. intros. inverts* H0. Qed.

Hint Resolve tclosure_rtclosure_step tclosure_step_rtclosure.

Lemma tclosure_rtclosure_tclosure : forall y x z,
  rtclosure x y -> tclosure y z -> tclosure x z.  
Proof. intros. gen z. induction* H. Qed.

Lemma tclosure_tclosure_rtclosure : forall y x z,
  tclosure x y -> rtclosure y z -> tclosure x z.  
Proof. intros. induction* H. Qed. 

Lemma tclosure_trans : trans tclosure.
Proof. intros_all. auto* tclosure_tclosure_rtclosure. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Induction *)

(** Star induction principle with transitivity hypothesis *)

Lemma rtclosure_ind_trans : forall (P : A -> A -> Prop),
  (forall x : A, P x x) ->
  (forall x y : A, R x y -> P x y) ->
  (forall y x z : A, rtclosure x y -> P x y -> rtclosure y z -> P y z -> P x z) ->
  forall x y : A, rtclosure x y -> P x y.
Proof.
  introv Hrefl Hstep Htrans S. induction S.
  auto. apply~ (@Htrans y).
Qed.

(** Star induction principle with steps at the end *)

Lemma rtclosure_ind_right : forall (P : A -> A -> Prop),
  (forall x : A, P x x) ->
  (forall y x z : A, rtclosure x y -> P x y -> R y z -> P x z) ->
  forall x y : A, rtclosure x y -> P x y.
Proof.
  introv Hrefl Hlast. apply rtclosure_ind_trans. 
  auto.
  intros. apply~ (Hlast x).
  introv S1 P1 S2 _. gen x. induction S2; introv S1 P1.
     auto.
     apply IHS2. eauto. apply~ (Hlast x). 
Qed.

End Closures.

Hint Resolve rtclosure_refl rtclosure_step rtclosure_once : rtclosure.
(* TODO: should rename and complete the [closure] database *)
(* TODO: should not need to re-export the following version *)

Lemma incl_tclosure_self : forall A (R:binary A), 
   incl R (tclosure R).
Proof. unfolds incl. intros. apply~ tclosure_once. Qed.
Hint Resolve incl_tclosure_self. 

(* TODO: sort and complete the following *)

Hint Resolve stclosure_step stclosure_sym stclosure_trans.

Lemma stclosure_le : forall A (R1 R2 : binary A),
  incl R1 R2 -> incl (stclosure R1) (stclosure R2).
Proof. unfolds incl. introv Le H. induction* H. Qed.
