(**************************************************************************
* TLC: A library for Coq                                                  *
* Well-founded relations                                                  *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic
 LibProd LibSum LibRelation LibNat.

(* ********************************************************************** *)
(** * Compatibility *)

Definition wf := well_founded.

Hint Extern 1 (wf ?R) => unfold R : wf.

(** New tactic [splits_all] that does not loop on well-founded goals *)

Ltac splits_all_base ::= 
  match goal with
  | |- wf _ => idtac
  | |- well_founded => idtac
  | _ => try (split; splits_all_base)
  end.


(* ********************************************************************** *)
(** * Properties of well-foundedness *)

(* ---------------------------------------------------------------------- *)
(** ** Inclusion and equivalence *)

(** Well-foundedness preserved by inclusion *)

Lemma incl_wf : forall A (R1 R2 : binary A),
  wf R1 -> incl R2 R1 -> wf R2.
Proof.
  introv W1 Inc. intros x.
  pattern x. apply (well_founded_ind W1). clear x.
  intros x IH. constructor. intros. apply IH. apply~ Inc.
Qed.

(** Well-foundedness modulo extensional equality *)

Lemma wf_iff : forall A (R1 R2:binary A),
  wf R1 -> (forall x y, R1 x y <-> R2 x y) -> wf R2.
Proof. introv W1 Ext. apply* incl_wf. introv H. rewrite~ Ext. Qed.



(************************************************************)
(* * Measures *)

(*-----------------------------------------------------*)
(** ** Measures as well-founded relations *)

Section Measure.
Variables (A : Type).

Definition measure (f : A -> nat) : binary A :=
  fun x1 x2 => f x1 < f x2.

Lemma measure_wf : forall f, wf (measure f).
Proof.
  intros f a. gen_eq n: (f a). gen a. pattern n. 
  apply peano_induction. clear n. introv IH Eq.
  apply Acc_intro. introv H. unfolds in H.
  rewrite <- Eq in H. apply* IH.
Qed.

(* todo: measure_order *)
Lemma measure_trans : forall (f : A -> nat), trans (measure f).
Proof. intros. unfold measure, trans. intros. nat_math. Qed.

End Measure.

(* todo: should be next to measure_induction *)
Lemma measure_2_induction : forall A B (mu : A -> B -> nat) (P : A -> B -> Prop),
  (forall x1 x2, (forall y1 y2, mu y1 y2 < mu x1 x2 -> P y1 y2) -> P x1 x2) ->
  (forall x1 x2, P x1 x2).
Proof.
  introv H. intros x1 x2. gen_eq p: (x1,x2). gen x1 x2.
  induction_wf IH: (measure_wf (fun p => mu (fst p) (snd p))) p.
  introv E. destruct p. inverts E. apply H.
  introv L. apply* IH. simpl. auto.
Qed.


Hint Resolve measure_wf : wf.

(** The relation "less than" on natural numbers is well_founded. *)

Lemma lt_wf : wf lt.
Proof.
  intros x.
  induction x using peano_induction. apply~ Acc_intro.
Qed.

Hint Resolve lt_wf : wf.


(** Measures at arity 2 *)

Definition measure2 A1 A2 (f : A1 -> A2 -> nat) : binary (A1*A2) :=
  fun p1 p2 => let (x1,y1) := p1 in let (x2,y2) := p2 in f x1 y1 < f x2 y2.

Lemma measure2_wf : forall A1 A2 (f:A1->A2->nat), wf (measure2 f).
Proof.
  intros A1 A2 f [x1 x2]. apply (@measure_induction _ (uncurry2 f)). clear x1 x2.
  intros [x1 x2] H. apply Acc_intro. intros [y1 y2] Lt. apply~ H.
Qed.

Hint Resolve measure2_wf : wf.

(*-----------------------------------------------------*)
(** ** The relation "less than" on the set of 
       integers greater than a fixed lower bound. *)

Require Import LibInt.

Definition downto (b : int) := 
  fun n m : int => (b <= n) /\ (n < m). 

Lemma downto_def : forall b n m,
  downto b n m = (b <= n /\ n < m).
Proof. auto. Qed.

Lemma downto_intro : forall b n m,
  b <= n -> n < m -> downto b n m.
Proof. split~. Qed.
  
Lemma int_downto_wf : forall n, wf (downto n).
Proof.
  intros b n.
  induction_wf: (measure_wf (fun n => Zabs_nat (n-b))) n.
  apply Acc_intro. introv [H1 H2]. apply IH.
  unfolds. applys Zabs_nat_lt; math.
Qed. 

Hint Resolve int_downto_wf : wf.

Hint Unfold downto.
Hint Extern 1 (downto _ _ _) => math : maths.
  (* todo:bin  apply downto_intro; math : maths. *)


(*-----------------------------------------------------*)
(** ** The relation "greater than" on the set of 
       integers lower than a fixed upper bound. *)

Definition upto (b : int) := 
  fun n m : int => (n <= b) /\ (m < n). 

Lemma upto_def : forall b n m,
  upto b n m = ((n <= b) /\ (m < n)).
Proof. auto. Qed.

Lemma upto_intro : forall b n m,
  n <= b -> m < n -> upto b n m.
Proof. split~. Qed.
 
Lemma int_upto_wf : forall n, wf (upto n).
Proof.
  intros b n. 
  induction_wf: (measure_wf (fun n => Zabs_nat (b-n))) n.
  apply Acc_intro. introv [H1 H2]. apply IH.
  applys Zabs_nat_lt; math.
Qed.

Hint Resolve int_upto_wf : wf.

Hint Unfold upto.
Hint Extern 1 (upto _ _ _) => math : maths.


(* ********************************************************************** *)
(** * Empty relation *)

Lemma empty_wf : forall A, wf (@empty A).
Proof. intros_all. constructor. introv H. false. Qed. 

Hint Resolve empty_wf : wf.


(* ********************************************************************** *)
(** * Inverse projections *)

Section UnprojWf.
Variables (A1 A2 A3 A4 : Type).

Lemma unproj21_wf : forall (f : binary A1),
  wf f ->
  wf (unproj21 A2 f).
Proof.
  intros f H [x1 x2]. gen x2.
  induction_wf IH: H x1. constructor. intros [y1 y2]. auto.
Qed.

Lemma unproj22_wf : forall (f : binary A2),
  wf f ->
  wf (unproj22 A1 f).
Proof.
  intros f H [x1 x2]. gen x1.
  induction_wf IH: H x2. constructor. intros [y1 y2]. auto.
Qed.

Lemma unproj31_wf : forall (f : binary A1),
  wf f ->
  wf (unproj31 A2 A3 f).
Proof.
  intros f H [[x1 x2] x3]. gen x2 x3.
  induction_wf IH: H x1. constructor. intros [[y1 y2] y3]. auto.
Qed.

Lemma unproj32_wf : forall (f : binary A2),
  wf f ->
  wf (unproj32 A1 A3 f).
Proof.
  intros f H [[x1 x2] x3]. gen x1 x3.
  induction_wf IH: H x2. constructor. intros [[y1 y2] y3]. auto.
Qed.

Lemma unproj33_wf : forall (f : binary A3),
  wf f ->
  wf (unproj33 A1 A2 f).
Proof.
  intros f H [[x1 x2] x3]. gen x1 x2.
  induction_wf IH: H x3. constructor. intros [[y1 y2] y3]. auto.
Qed.

Lemma unproj41_wf : forall (f : binary A1),
  wf f ->
  wf (unproj41 A2 A3 A4 f).
Proof.
  intros f H [[[x1 x2] x3] x4]. gen x2 x3 x4.
  induction_wf IH: H x1. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

Lemma unproj42_wf : forall (f : binary A2),
  wf f ->
  wf (unproj42 A1 A3 A4 f).
Proof.
  intros f H [[[x1 x2] x3] x4]. gen x1 x3 x4.
  induction_wf IH: H x2. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

Lemma unproj43_wf : forall (f : binary A3),
  wf f ->
  wf (unproj43 A1 A2 A4 f).
Proof.
  intros f H [[[x1 x2] x3] x4]. gen x1 x2 x4.
  induction_wf IH: H x3. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

Lemma unproj44_wf : forall (f : binary A4),
  wf f ->
  wf (unproj44 A1 A2 A3 f).
Proof.
  intros f H [[[x1 x2] x3] x4]. gen x1 x2 x3.
  induction_wf IH: H x4. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

End UnprojWf.

Hint Resolve 
  unproj21_wf unproj22_wf 
  unproj31_wf unproj32_wf unproj33_wf
  unproj41_wf unproj42_wf unproj43_wf unproj44_wf : wf.


(* ********************************************************************** *)
(** * Lexicographical product *)

Lemma lexico2_wf : forall {A1 A2} 
 (R1:binary A1) (R2:binary A2),
  wf R1 -> wf R2 -> wf (lexico2 R1 R2).
Proof. 
  introv W1 W2. intros [x1 x2]. gen x2. 
  induction_wf IH1: W1 x1. intros.
  induction_wf IH2: W2 x2. constructor. intros [y1 y2] H.
  simpls. destruct H as [H1|[H1 H2]].
  apply~ IH1. rewrite H1. apply~ IH2.
Qed.

Lemma lexico3_wf : forall {A1 A2 A3} 
 (R1:binary A1) (R2:binary A2) (R3:binary A3),
  wf R1 -> wf R2 -> wf R3 -> 
  wf (lexico3 R1 R2 R3).
Proof. 
  intros. apply~ @lexico2_wf. apply~ @lexico2_wf.
Qed.

Lemma lexico4_wf : forall {A1 A2 A3 A4} 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  wf R1 -> wf R2 -> wf R3 -> wf R4 -> 
  wf (lexico4 R1 R2 R3 R4).
Proof. 
  intros. apply~ @lexico3_wf. apply~ @lexico2_wf.
Qed.

Implicit Arguments lexico2_wf [[A1] [A2] R1 R2].
Implicit Arguments lexico3_wf [[A1] [A2] [A3] R1 R2 R3].
Implicit Arguments lexico4_wf [[A1] [A2] [A3] [A4] R1 R2 R3 R4].

Hint Resolve @lexico2_wf @lexico3_wf @lexico4_wf : wf.


(* ********************************************************************** *)
(** * Symmetric product *)

Lemma prod2_wf_1 : forall (A1 A2:Type) 
 (R1:binary A1) (R2:binary A2), 
  wf R1 -> wf (prod2 R1 R2).
Proof.
  introv W1. intros [x1 x2]. 
  gen x2. induction_wf IH: W1 x1. intros.
  constructor. intros [y1 y2] [E1 E2]. apply~ IH.
Qed.

Lemma prod2_wf_2 : forall (A1 A2:Type) 
 (R1:binary A1) (R2:binary A2), 
  wf R2 -> wf (prod2 R1 R2).
Proof.
  introv W2. intros [x1 x2]. 
  gen x1. induction_wf IH: W2 x2. intros.
  constructor. intros [y1 y2] [E1 E2]. apply~ IH.
Qed.

Lemma prod3_wf_1 : forall (A1 A2 A3:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3), 
  wf R1 -> wf (prod3 R1 R2 R3).
Proof. intros. apply prod2_wf_1. apply~ prod2_wf_1. Qed.

Lemma prod3_wf_2 : forall (A1 A2 A3:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3), 
  wf R2 -> wf (prod3 R1 R2 R3).
Proof. intros. apply prod2_wf_1. apply~ prod2_wf_2. Qed.

Lemma prod3_wf_3 : forall (A1 A2 A3:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3), 
  wf R3 -> wf (prod3 R1 R2 R3).
Proof. intros. apply~ prod2_wf_2. Qed.

Lemma prod4_wf_1 : forall (A1 A2 A3 A4:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4), 
  wf R1 -> wf (prod4 R1 R2 R3 R4).
Proof. intros. apply prod2_wf_1. apply~ prod3_wf_1. Qed.

Lemma prod4_wf_2 : forall (A1 A2 A3 A4:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4), 
  wf R2 -> wf (prod4 R1 R2 R3 R4).
Proof. intros. apply prod2_wf_1. apply~ prod3_wf_2. Qed.

Lemma prod4_wf_3 : forall (A1 A2 A3 A4:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4), 
  wf R3 -> wf (prod4 R1 R2 R3 R4).
Proof. intros. apply prod2_wf_1. apply~ prod3_wf_3. Qed.

Lemma prod4_wf_4 : forall (A1 A2 A3 A4:Type) 
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4), 
  wf R4 -> wf (prod4 R1 R2 R3 R4).
Proof. intros. apply~ prod2_wf_2. Qed.

Hint Resolve
  prod2_wf_1 prod2_wf_2
  prod3_wf_1 prod3_wf_2 prod3_wf_3
  prod4_wf_1 prod4_wf_2 prod4_wf_3 prod4_wf_4 : wf.

(* todo: swapproduct? *)

(* ********************************************************************** *)
(** * Well-foundedness of a function image *)

Definition binary_map A B (f:A->B) (R:binary B) : binary A :=
  fun x y => R (f x) (f y).

Lemma binary_map_wf : forall A B (f:A->B) (R:binary B),
  wf R -> wf (binary_map f R).
Proof.
  introv W. intros x. gen_eq a: (f x). gen x.
  induction_wf: W a. introv E. constructors.
  intros y Hy. subst a. hnf in Hy. applys* IH.
Qed.

Hint Resolve binary_map_wf : wf.


(* ********************************************************************** *)
(** * Inverse image *)
 
Lemma inverse_image_wf : forall (A B : Type) (R : binary B) (f : A -> B),
  wf R -> wf (inverse_image R f).
Proof.
  introv W. intros x. gen_eq y: (f x). gen x.
  induction_wf IH: W y. intros u E. subst y.
  constructor. intros v I. applys~ IH (f v).
Qed.

(* todo: inverse image of relation ? *)

(* begin hide *)

(* ********************************************************************** *)
(** * Union *)

(* TODO..

Section WfUnion.
  Variable A : Type.
  Variables R1 R2 : binary A.
  
  Notation Union := (union A R1 R2).
  
  Remark strip_commut :
    commut A R1 R2 ->
    forall x y:A,
      clos_trans A R1 y x ->
      forall z:A, R2 z y ->  exists2 y' : A, R2 y' x & clos_trans A R1 z y'.
  Proof.
    induction 2 as [x y| x y z H0 IH1 H1 IH2]; intros.
    elim H with y x z; auto with sets; intros x0 H2 H3.
    exists x0; auto with sets.
    
    elim IH1 with z0; auto with sets; intros.
    elim IH2 with x0; auto with sets; intros.
    exists x1; auto with sets.
    apply t_trans with x0; auto with sets.
  Qed.


  Lemma Acc_union :
    commut A R1 R2 ->
    (forall x:A, Acc R2 x -> Acc R1 x) -> forall a:A, Acc R2 a -> Acc Union a.
  Proof.
    induction 3 as [x H1 H2].
    apply Acc_intro; intros.
    elim H3; intros; auto with sets.
    cut (clos_trans A R1 y x); auto with sets.
    elimtype (Acc (clos_trans A R1) y); intros.
    apply Acc_intro; intros.
    elim H8; intros.
    apply H6; auto with sets.
    apply t_trans with x0; auto with sets.
    
    elim strip_commut with x x0 y0; auto with sets; intros.
    apply Acc_inv_trans with x1; auto with sets.
    unfold union in |- *.
    elim H11; auto with sets; intros.
    apply t_trans with y1; auto with sets.

    apply (Acc_clos_trans A).
    apply Acc_inv with x; auto with sets.
    apply H0.
    apply Acc_intro; auto with sets.
  Qed.

  
  Theorem wf_union :
    commut A R1 R2 -> well_founded R1 -> well_founded R2 -> well_founded Union.
  Proof.
    unfold well_founded in |- *.
    intros.
    apply Acc_union; auto with sets.
  Qed.

End WfUnion.

*)

(* TODO: Disjoint union, useful? *)


(* ********************************************************************** *)
(** * Transitive closure *)

(* TODO

Section Wf_Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.

  Notation trans_clos := (clos_trans A R).
 
  Lemma incl_clos_trans : inclusion A R trans_clos.
    red in |- *; auto with sets.
  Qed.

  Lemma Acc_clos_trans : forall x:A, Acc R x -> Acc trans_clos x.
    induction 1 as [x0 _ H1].
    apply Acc_intro.
    intros y H2.
    induction H2; auto with sets.
    apply Acc_inv with y; auto with sets.
  Qed.

  Hint Resolve Acc_clos_trans.

  Lemma Acc_inv_trans : forall x y:A, trans_clos y x -> Acc R x -> Acc R y.
  Proof.
    induction 1 as [| x y]; auto with sets.
    intro; apply Acc_inv with y; assumption.
  Qed.

  Theorem wf_clos_trans : well_founded R -> well_founded trans_clos.
  Proof.
    unfold well_founded in |- *; auto with sets.
  Qed.

End Wf_Transitive_Closure.

*)

Axiom tclosure_wf : forall A (R:binary A),
  wf R -> wf (tclosure R).
(* need to copy proof from the standard library *)

(* end hide *)

(* ********************************************************************** *)
(** * Tactics *)

(** [prove_wf] is a tactic that tries and prove a goal of the
    form [wf R]. It is implemented using [auto]. *)

Tactic Notation "prove_wf" :=
  solve [ auto with wf ].

(** [unfold_wf] and [unfolds_wf] are shorthands for unfolding  
    definitions related to well-foundedness. *)

Ltac unfold_wf_base := 
  unfold_unproj; unfold_uncurryp; unfold_lexico.

Ltac unfolds_wf_base := 
  unfolds_unproj; unfolds_uncurryp; unfolds_lexico.

Tactic Notation "unfold_wf" :=
  unfold_wf_base.
Tactic Notation "unfold_wf" "~" :=
  unfold_wf; auto_tilde.
Tactic Notation "unfold_wf" "*" :=
  unfold_wf; auto_star.

Tactic Notation "unfolds_wf" :=
  unfolds_wf_base.
Tactic Notation "unfolds_wf" "~" :=
  unfolds_wf; auto_tilde.
Tactic Notation "unfolds_wf" "*" :=
  unfolds_wf; auto_star.


