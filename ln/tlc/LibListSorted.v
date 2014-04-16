(**************************************************************************
* TLC: A library for Coq                                                  *
* Sorted lists                                                            *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibTactics LibLogic LibRelation LibWf LibList
 LibOrder LibNat.


(* ********************************************************************** *)
(** * Permutations of lists *)

Section Permutation.
Variable A : Type.

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** We could define permutation in terms of multisets, 
    but this would impose additional constraints on the
    type of elements. So instead, we use a definition
    in terms of permutation of two inner segment of lists,
    taking the reflexive-transitive closure. *)

Inductive permut_one : list A -> list A -> Prop :=
  | permut_one_intro : forall l1 l2 l3 l4, 
      permut_one (l1++l2++l3++l4) (l1++l3++l2++l4).

Hint Constructors permut_one.

Definition permut := rtclosure permut_one.


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

(** Permutation is an equivalence *)

Lemma permut_refl : forall l,
  permut l l.
Proof. intros. apply rtclosure_refl. Qed.

Lemma permut_sym : forall l1 l2,
  permut l1 l2 -> permut l2 l1.
Proof. 
  intros. induction H.
  apply permut_refl.
  applys rtclosure_last. apply IHrtclosure. inverts~ H.
Qed.

Lemma permut_trans : forall l2 l1 l3,
  permut l1 l2 -> permut l2 l3 -> permut l1 l3.
Proof. intros. apply* rtclosure_trans. Qed.

(** Permutation is a congruence with respect to [++] and [::] *)

Lemma permut_flip : forall l1 l2,
  permut (l1++l2) (l2++l1).
Proof.
  intros. lets: (permut_one_intro nil l1 l2 nil).
  rew_app in *. apply~ rtclosure_once.
Qed.

Lemma permut_app_l : forall l1 l1' l2,
  permut l1 l1' ->
  permut (l1 ++ l2) (l1' ++ l2).
Proof.
  introv H. gen l2. induction H; intros.
  apply permut_refl.
  specializes IHrtclosure l2. inverts H.
   rew_app in *. eapply permut_trans.
   applys* rtclosure_step. apply permut_refl.
Qed.

Lemma permut_app_r : forall l1 l2 l2',
  permut l2 l2' ->
  permut (l1 ++ l2) (l1 ++ l2').
Proof.
  introv H. gen l1. induction H; intros.
  apply permut_refl.
  specializes IHrtclosure l1. inverts H.
   rewrite <- app_assoc in *. eapply permut_trans. 
   applys* rtclosure_step. apply permut_refl.
Qed.

Lemma permut_app_lr : forall l1 l1' l2 l2',
  permut l1 l1' -> permut l2 l2' ->
  permut (l1 ++ l2) (l1' ++ l2').
Proof.
  intros. applys rtclosure_trans.
  sapply* permut_app_l.
  apply* permut_app_r.  
Qed.

Lemma permut_cons : forall x l1 l1',
  permut l1 l1' ->
  permut (x::l1) (x::l1').
Proof.
  intros. lets: (@permut_app_r (x::nil) _ _ H).
  rew_app in *. auto.
Qed.

(** Permutation are stable through list reversal *)

Lemma permut_rev : forall l,
  permut l (rev l).
Proof.
  induction l. apply permut_refl. rew_rev.
  lets: (@permut_flip (a::nil) (rev l)). rew_app in *.
  apply~ (@permut_trans (a::rev l)). apply~ permut_cons. 
Qed.

(** Properties of elements are preserved by permutation *)

Lemma Forall_permut_one : forall (P:A->Prop) l1 l2, 
  Forall P l1 -> permut_one l1 l2 -> Forall P l2.
Proof.
  introv F Per. inverts Per.
  lets F0 F345: (Forall_app_inv _ _ F).
  lets F3 F45: (Forall_app_inv _ _ F345).  
  lets F4 F5: (Forall_app_inv _ _ F45).
  apply~ Forall_app. apply~ Forall_app. apply~ Forall_app.
Qed. 

Lemma Forall_permut : forall (P:A->Prop) l1 l2, 
  Forall P l1 -> permut l1 l2 -> Forall P l2.
Proof.
  introv F1 Per. gen F1. induction Per.
  auto. 
  auto* Forall_permut_one.
Qed. 

End Permutation.

Hint Resolve permut_refl permut_flip
             permut_app_lr permut_cons.


(* ---------------------------------------------------------------------- *)
(** ** Permutation tactic *)

Section PermutationTactic.
Variable A : Type.
Implicit Types l : list A.

Lemma permut_get_1 : forall l1 l2,
  permut (l1 ++ l2) (l1 ++ l2).
Proof. intros. apply permut_refl. Qed.
Lemma permut_get_2 : forall l1 l2 l3,
  permut (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof. 
  intros. apply rtclosure_once. 
  applys (@permut_one_intro _ nil l1 l2 l3). 
Qed.
Lemma permut_get_3 : forall l1 l2 l3 l4,
  permut (l1 ++ l2 ++ l3 ++ l4) (l2 ++ l3 ++ l1 ++ l4).
Proof.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_2.
Qed.
Lemma permut_get_4 : forall l1 l2 l3 l4 l5,
  permut (l1 ++ l2 ++ l3 ++ l4 ++ l5) 
         (l2 ++ l3 ++ l4 ++ l1 ++ l5).
Proof.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_3.
Qed.
Lemma permut_get_5 : forall l1 l2 l3 l4 l5 l6,
  permut (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6) 
         (l2 ++ l3 ++ l4 ++ l5 ++ l1 ++ l6).
Proof.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_4.
Qed.
Lemma permut_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
  permut (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7) 
         (l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l1 ++ l7).
Proof.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_5.
Qed.

Lemma permut_tactic_setup : forall l1 l2,
  permut (nil ++ l1 ++ nil) (l2 ++ nil) -> permut l1 l2.
Proof. intros. rew_list~ in H. Qed.

Lemma permut_tactic_keep : forall l1 l2 l3 l4,
  permut ((l1 ++ l2) ++ l3) l4 ->
  permut (l1 ++ (l2 ++ l3)) l4.
Proof. intros. rew_list~ in H. Qed.

Lemma permut_tactic_simpl : forall l1 l2 l3 l4,
  permut (l1 ++ l3) l4 ->
  permut (l1 ++ (l2 ++ l3)) (l2 ++ l4).
Proof.
  intros. eapply permut_trans.
  apply permut_get_2. apply~ permut_app_r.
Qed.

Lemma permut_tactic_trans : forall l1 l2 l3,
  permut l3 l2 -> permut l1 l3 -> permut l1 l2.
Proof. introv P1 P2. apply~ (permut_trans P2 P1). Qed.

End PermutationTactic.


(** [permut_prepare] applies to a goal of the form [permut l l']
    and sets [l] and [l'] in the form [l1 ++ l2 ++ .. ++ nil],
    (some of the lists [li] are put in the form [x::nil]). *)
(* todo: improve so as to ensure no rewrite inside elements *)

Hint Rewrite app_assoc app_nil_l app_nil_r : permut_rew.

Ltac permut_lemma_get n :=
  match nat_from_number n with
  | 1 => constr:(permut_get_1)
  | 2 => constr:(permut_get_2)
  | 3 => constr:(permut_get_3)
  | 4 => constr:(permut_get_4)
  | 5 => constr:(permut_get_5) 
  end.

Ltac permut_isolate_cons :=
  do 20 try (* todo : repeat *)
    match goal with |- context [?x::?l] =>
      match l with 
      | nil => fail 1
      | _ => rewrite <- (@app_cons_one _ x l)
      end 
    end.

Ltac permut_simpl_prepare :=
   autorewrite with permut_rew;
   permut_isolate_cons;
   autorewrite with permut_rew;
   apply permut_tactic_setup;
   repeat rewrite app_assoc.


(** [permut_simplify] simplifies a goal of the form 
    [permut l l'] where [l] and [l'] are lists built with 
    concatenation and consing, by cancelling syntactically 
    equal elements *)

Ltac permut_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l ++ _ => constr:(1)
  | _ ++ l ++ _ => constr:(2)
  | _ ++ _ ++ l ++ _ => constr:(3)
  | _ ++ _ ++ _ ++ l ++ _ => constr:(4)
  | _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(5)
  | _ ++ _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(6)
  | _ => constr:(0) (* not found *)
  end.

Ltac permut_simpl_once := 
  match goal with
  | |- permut (_ ++ nil) _ => fail 1
  | |- permut (_ ++ (?l ++ _)) ?l' => 
     match permut_index_of l l' with
     | 0 => apply permut_tactic_keep
     | ?n => let F := permut_lemma_get n in
            eapply permut_tactic_trans; 
            [ apply F
            | apply permut_tactic_simpl ]
     end
  end.

Ltac permut_simpl :=
  permut_simpl_prepare;
  repeat permut_simpl_once;
  autorewrite with permut_rew;
  try apply permut_refl.

(* todo: permut rewrite *)


(* ********************************************************************** *)
(** * Sorted lists *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

Section Sorted.
Variable A : Type.
Implicit Types le : binary A.

Inductive sorted le : list A -> Prop :=
  | sorted_nil : sorted le nil
  | sorted_one : forall x, sorted le (x::nil)
  | sorted_two : forall x y l, 
     sorted le (y::l) -> le x y ->
     sorted le (x::y::l).

Definition rsorted le := sorted (flip le).

Definition head_of_le le x l :=
  match l with
  | nil => True
  | h::_ => le x h
  end.

Definition head_le le l1 l2 :=
  match l1,l2 with
  | _,nil => True
  | nil,_ => True
  | h1::_,h2::_ => le h1 h2
  end.

End Sorted.

(* ---------------------------------------------------------------------- *)
(** ** Properties about sorted *)

Implicit Arguments sorted [A].
Hint Unfold rsorted.

Section SortedProperties.
Hint Constructors sorted.

Variables (A : Type).
Variable le : binary A.
Hint Resolve sorted_nil sorted_one.

Lemma sorted_inv : forall x l,
  sorted le (x::l) -> head_of_le le x l /\ sorted le l.
Proof. introv H. inverts H; simpls~. Qed. 

Lemma sorted_sub : forall x l,
  sorted le (x::l) -> sorted le l.
Proof. introv H. inverts~ H. Qed.

Lemma sorted_cons : forall l,
  sorted le l -> forall x,
  head_of_le le x l -> sorted le (x::l).
Proof. introv S Hd. inverts~ S. Qed.

Lemma head_le_from_sorted : forall x l1 l2,
  sorted le (x::l2) ->
  head_le le l1 (x::l2) ->
  head_le le (x::l1) l2.
Proof.
  intros. destruct l2; simpl. auto. inverts~ H.
Qed.

Lemma sorted_cons_head_of : forall x l,
  sorted le (x::l) -> head_of_le le x l.
Proof. introv H. inverts H; simpls~. Qed.

Lemma head_le_nil_l : forall l,
  head_le le nil l.
Proof. intros. unfolds. destruct~ l. Qed.

Lemma head_le_nil_r : forall l,
  head_le le l nil.
Proof. intros. unfolds. destruct~ l. Qed.

Lemma sorted_cons_head : forall l1 l2 x,
  head_le le (x::l1) l2 -> 
  sorted le l2 ->
  sorted le (x::l2).
Proof. introv H S2. destruct l2. auto. apply~ sorted_cons. Qed.

Lemma head_le_flip : forall l1 l2,
  head_le (flip le) l1 l2 = head_le le l2 l1.
Proof. destruct l1; destruct l2; auto. Qed.

Lemma head_le_flip_1 : forall l1 l2,
  head_le (flip le) l1 l2 -> head_le le l2 l1.
Proof. intros. rewrite~ <- head_le_flip. Qed.

Lemma head_le_flip_2 : forall l1 l2,
  head_le le l2 l1 -> head_le (flip le) l1 l2.
Proof. intros. rewrite~ head_le_flip. Qed.

Lemma sorted_Forall_le : forall x l,
  total_preorder le ->
  head_of_le le x l -> sorted le l -> Forall (le x) l.
Proof.
  induction l; simpl; introv Tot LeH Sl. auto. constructor~.
  lets: (sorted_sub Sl). constructor~. apply~ IHl.
  destruct~ l; simpls~. inverts Sl. sapply* total_preorder_trans.
Qed.

Lemma head_of_le_Forall_le : forall x l,
  Forall (le x) l -> head_of_le le x l.
Proof. introv H. destruct l; simpls. auto. inverts~ H. Qed.

Lemma sorted_flip_flip : forall l,
  sorted le l ->
  sorted (flip (flip le)) l.
Proof.
  introv H. rewrite flip_flip. induction H.
   constructor. constructor. apply~ sorted_cons.
Qed.

End SortedProperties.

(* ---------------------------------------------------------------------- *)
(** ** Properties about rsorted *)

Section RSortedProperties.
Variables (A : Type).
Variable le : binary A.
Hint Resolve sorted_nil sorted_one.
Hint Constructors sorted.

Lemma rsorted_inv : forall x l,
  rsorted le (x::l) -> head_of_le (flip le) x l /\ rsorted le l.
Proof. introv H. inverts H; simpls~. Qed. 

Lemma head_le_from_rsorted : forall x l1 l2,
  rsorted le (x::l2) ->
  head_le (flip le) l1 (x::l2) ->
  head_le (flip le) (x::l1) l2.
Proof.
  intros. destruct l2; simpl. auto. inverts~ H.
Qed.

Lemma rsorted_cons_head : forall l1 l2 x,
  head_le (flip le) (x::l1) l2 -> 
  rsorted le l2 ->
  rsorted le (x::l2).
Proof. introv H S2. destruct~ l2. Qed.

Lemma sorted_app : forall l1 l2,
  head_le le l1 l2 -> rsorted le l1 -> sorted le l2 -> 
  sorted le ((rev l1) ++ l2).
Proof.
  introv. gen l2. induction l1; introv Hd S1 S2; rew_rev. auto.
  lets Hd1 S1': (rsorted_inv S1). clear S1.
  apply IHl1. destruct~ l1. auto.
  apply sorted_cons. auto. destruct~ l2.
Qed.

End RSortedProperties.

Lemma rsorted_app : forall (A : Type) (le : binary A) l1 l2,
  head_le le l2 l1 -> sorted le l1 -> rsorted le l2 -> 
  rsorted le ((rev l1) ++ l2).
Proof.
  unfold rsorted. intros. apply sorted_app.
    rewrite~ head_le_flip.
    unfolds. apply~ sorted_flip_flip.
    auto.
Qed.


(* ********************************************************************** *)
(** * Sorting of a list *)

Section Sorts.
Variables (A : Type).
Implicit Types le : binary A.
Hint Resolve sorted_nil sorted_one.

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

Definition sorts le l l' :=
  permut l l' /\ sorted le l'.

Definition rsorts le := sorts (flip le).


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Lemma sorts_refl : forall le l,
  sorted le l -> sorts le l l.
Proof. split. apply permut_refl. auto. Qed.

Lemma rsorts_refl : forall le l,
  rsorted le l -> rsorts le l l.
Proof. intros. apply~ sorts_refl. Qed.

Lemma sorts_app_rev : forall le l1 l2,
 head_le le l1 l2 -> rsorted le l1 -> sorted le l2 ->
 sorts le (l1 ++ l2) (rev l1 ++ l2).
Proof.
  introv H S1 S2. split.
  apply permut_app_l. apply permut_rev.
  apply~ sorted_app. 
Qed.

Lemma rsorts_app_rev : forall le l1 l2,
 head_le le l2 l1 -> sorted le l1 -> rsorted le l2 ->
 rsorts le (l1 ++ l2) (rev l1 ++ l2).
Proof.
  introv H S1 S2. split.
  apply permut_app_l. apply permut_rev.
  apply~ rsorted_app. 
Qed.

Lemma sorts_permut : forall l1 l2 l' le,
  sorts le l1 l' -> permut l2 l1 ->
  sorts le l2 l'.
Proof.
  introv [P1 S1] Per. split~. 
  apply* (@permut_trans _ l1). 
Qed.

Lemma rsorts_permut : forall l1 l2 l' le,
  rsorts le l1 l' -> permut l2 l1 ->
  rsorts le l2 l'.
Proof. intros. apply~ (@sorts_permut l1). Qed.

Lemma sorts_cons : forall le l l' x,
  sorts le l l' -> head_of_le le x l' ->
  sorts le (x::l) (x::l').
Proof.
  introv [P S] Hd. split. 
  apply~ permut_cons. apply~ sorted_cons.
Qed.

Lemma sorts_2 : forall le l x1 x2,
  permut l (x1::x2::nil) ->
  le x1 x2 ->
  sorts le l (x1::x2::nil).
Proof.
  intros. apply~ (@sorts_permut (x1::x2::nil)).
  apply sorts_refl. apply sorted_cons.
  apply sorted_one. simpls~.
Qed.

Lemma sorts_3 : forall le l x1 x2 x3,
  permut l (x1::x2::x3::nil) ->
  le x1 x2 -> le x2 x3 ->
  sorts le l (x1::x2::x3::nil).
Proof.
  intros.
   apply~ (@sorts_permut (x1::x2::x3::nil)).
   apply sorts_refl. apply sorted_cons.
   apply sorted_cons. apply sorted_one.
   simpls~. simpls~.
Qed.

Lemma rsorts_2 : forall le l x1 x2,
  permut l (x1::x2::nil) ->
  le x2 x1 ->
  rsorts le l (x1::x2::nil).
Proof.
  intros.
   apply~ (@rsorts_permut (x1::x2::nil)).
   apply rsorts_refl. applys sorted_cons.
   apply sorted_one. unfold flip. simpls~.
Qed.

Lemma rsorts_3 : forall le l x1 x2 x3,
  permut l (x1::x2::x3::nil) ->
  le x2 x1 -> le x3 x2 ->
  rsorts le l (x1::x2::x3::nil).
Proof.
  intros.
   apply~ (@rsorts_permut (x1::x2::x3::nil)).
   apply rsorts_refl. applys sorted_cons.
   apply sorted_cons. apply sorted_one.
   simpls~. simpls~.
Qed.

Lemma sorts_length_lt_2 : forall le l,
  length l < 2 -> sorts le l l.
Proof.
  intros. apply sorts_refl. destruct~ l. 
  destruct~ l. rew_length in *. false. nat_math.
Qed.

End Sorts.



