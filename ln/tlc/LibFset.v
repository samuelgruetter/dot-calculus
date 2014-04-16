(**************************************************************************
* TLC: A library for Coq                                                  *
* Finite sets                                                             *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibList.
Require Import LibSet LibLogic LibEqual LibReflect.

(** DISCLAIMER: for the time being, this file only contains the
    operations for type fset, but not yet all the typeclasses 
    associated with it. A module signature is currently used to
    hide the implentation. *)

(* ********************************************************************** *)
(** * Abstract interface for finite sets *)

Module Type FsetSig.

(** Definitions and operations on finite sets *)

Section Operations.
Variables (A:Type).

Parameter fset : Type -> Type.
Parameter mem : A -> fset A -> Prop.
Parameter empty : fset A.
Parameter singleton : A -> fset A.
Parameter union : fset A -> fset A -> fset A.
Parameter inter : fset A -> fset A -> fset A.
Parameter remove : fset A -> fset A -> fset A.

(** Equality on these sets is extensional *)

Definition subset E F :=
  forall x, mem x E -> mem x F.

Definition notin x E :=
  ~ mem x E.

Definition disjoint E F :=
  inter E F = empty.

Definition from_list L :=
  fold_right (fun x acc => union (singleton x) acc) empty L.

End Operations.

Implicit Arguments empty [[A]].

(** Notations *)

Notation "\{}" := (empty) : fset_scope.

Notation "\{ x }" := (singleton x) : fset_scope.

Notation "E \u F" := (union E F)
  (at level 37, right associativity) : fset_scope.

Notation "E \n F" := (inter E F)
  (at level 36, right associativity) : fset_scope.

Notation "E \- F" := (remove E F)
  (at level 35) : fset_scope.

Notation "x \in E" := (mem x E) (at level 39) : fset_scope.

Notation "x \notin E" := (notin x E) (at level 39) : fset_scope.

Notation "E \c F" := (subset E F)
  (at level 38) : fset_scope.

Delimit Scope fset_scope with fset.
Bind Scope fset_scope with fset.
Open Scope fset_scope.

Section Properties.
Variables A : Type.
Implicit Types x : A.
Implicit Types E : fset A.

(** Extensionality *)

Parameter fset_extens : forall E F, 
  subset E F -> subset F E -> E = F.

(** Finiteness *)

Parameter fset_finite : forall E,
  exists L, E = from_list L.

(** Semantics of basic operations *)

Parameter in_empty : forall x,
  x \in \{} = False. 

Parameter in_singleton : forall x y,
  x \in \{y} = (x = y).

Parameter in_union : forall x E F,
  x \in (E \u F) = ((x \in E) \/ (x \in F)).

Parameter in_inter : forall x E F,
  x \in (E \n F) = ((x \in E) /\ (x \in F)).

Parameter in_remove : forall x E F,
  x \in (E \- F) = ((x \in E) /\ (x \notin F)).

End Properties.

End FsetSig.


(* ********************************************************************** *)
(** * Implementation of finite sets *)

Module Export FsetImpl : FsetSig.

(** Note: most of the material contained in this module will ultimately
    be moved into the TLC library in a file called LibFset. *)

Close Scope container_scope.

Definition finite A (U:set A) := 
  exists L, forall x, is_in x U -> Mem x L.

Definition fset A := sig (@finite A).

Definition build_fset A (U:set A) (F:finite U) :=
  exist (@finite A) U F.

Section Operations.
Variables (A:Type).
 
Definition mem (x:A) (E:fset A) :=
  is_in x (proj1_sig E).

Lemma finite_empty : @finite A LibBag.empty.
Proof. exists (@nil A). intros x. rewrite in_empty_eq. auto_false. Qed.

Definition empty : fset A := 
  build_fset finite_empty.

Lemma singleton_finite : forall (x:A),
  finite (LibBag.single x).
Proof.
  intros. exists (x::nil). intros y. 
  rewrite in_single_eq. intro_subst. constructor.
Qed.

Definition singleton (x : A) :=
  build_fset (singleton_finite x).

Lemma union_finite : forall U V : set A,
  finite U -> finite V -> finite (union U V).
Proof.
  introv [L1 E1] [L2 E2]. exists (L1 ++ L2). intros x.
  rewrite in_union_eq. rewrite Mem_app_or_eq. introv [H|H]; auto. 
Qed.

Definition union (E F : fset A) :=
  build_fset (union_finite (proj2_sig E) (proj2_sig F)).

Lemma inter_finite : forall U V : set A,
  finite U -> finite V -> finite (inter U V).
Proof.
  introv [L1 E1] [L2 E2]. exists (L1 ++ L2). intros x.
  rewrite in_inter_eq. rewrite Mem_app_or_eq. auto*.
Qed.

Definition inter (E F : fset A) :=
  build_fset (inter_finite (proj2_sig E) (proj2_sig F)).

Lemma remove_finite : forall U V : set A,
  finite U -> finite V -> finite (remove U V).
Proof.
  introv [L1 E1] [L2 E2]. exists L1. intros x.
  rewrite in_remove_eq. introv [H1 H2]; auto. 
Qed.

Definition remove (E F : fset A) :=
  build_fset (remove_finite (proj2_sig E) (proj2_sig F)).

Definition subset E F :=
  forall x, mem x E -> mem x F.

Definition notin x E :=
  ~ mem x E.

Definition disjoint E F :=
  inter E F = empty.

Definition from_list L :=
  fold_right (fun x acc => union (singleton x) acc) empty L.

End Operations.

Implicit Arguments empty [[A]].

(** Notations *)

Notation "\{}" := (empty) : fset_scope.

Notation "\{ x }" := (singleton x) : fset_scope.

Notation "E \u F" := (union E F)
  (at level 37, right associativity) : fset_scope.

Notation "E \n F" := (inter E F)
  (at level 36, right associativity) : fset_scope.

Notation "E \- F" := (remove E F)
  (at level 35) : fset_scope.

Notation "x \in E" := (mem x E) (at level 39) : fset_scope.

Notation "x \notin E" := (notin x E) (at level 39) : fset_scope.

Notation "E \c F" := (subset E F)
  (at level 38) : fset_scope.

Delimit Scope fset_scope with fset.
Bind Scope fset_scope with fset.
Open Scope fset_scope.

Section Properties.
Variables A : Type.
Implicit Types x : A.
Implicit Types E : fset A.

Lemma fset_extens_eq : forall E F,
  (forall x, x \in E = x \in F) -> E = F.
Proof.
  unfold mem. intros [U FU] [V FV] H. simpls.
  apply exist_eq. apply in_double_eq. auto.
Qed. 

Lemma fset_extens : forall E F, 
  subset E F -> subset F E -> E = F.
Proof. intros. apply fset_extens_eq. extens*. Qed.

Lemma in_empty : forall x,
  x \in \{} = False.
Proof. unfold mem, empty. simpl. intros. rewrite in_empty_eq. auto*. Qed.

Lemma in_singleton : forall x y,
  x \in \{y} = (x = y).
Proof. unfold mem, singleton. simpl. intros. rewrite in_single_eq. auto*. Qed.

Lemma in_union : forall x E F,
  x \in (E \u F) = ((x \in E) \/ (x \in F)).
Proof. unfold mem, union. simpl. intros. rewrite in_union_eq. auto*. Qed.

Lemma in_inter : forall x E F,
  x \in (E \n F) = ((x \in E) /\ (x \in F)).
Proof. unfold mem, inter. simpl. intros. rewrite in_inter_eq. auto*. Qed.

Lemma in_remove : forall x E F,
  x \in (E \- F) = ((x \in E) /\ (x \notin F)).
Proof. unfold mem, remove. simpl. intros. rewrite in_remove_eq. auto*. Qed.

Lemma from_list_spec : forall x L,
  x \in from_list L = Mem x L.
Proof.
  unfold from_list. induction L; rew_list.
  rewrite in_empty. rewrite~ Mem_nil_eq. 
  rewrite in_union, in_singleton. rewrite~ Mem_cons_eq. congruence.
Qed.

Hint Constructors Mem.

Lemma fset_finite : forall E,
  exists L, E = from_list L.
Proof.
  intros [U [L' H]]. exists (filter (fun x => isTrue (is_in x U)) L').
  apply fset_extens_eq. intros x. rewrite from_list_spec.
  unfold mem at 1. simpl. extens. iff M.
    specializes H M. induction L'.
      inverts H.
      rewrite filter_cons. inverts H.
        rewrite (is_True M). rewrite~ isTrue_True. 
        case_if; fold_bool; fold_prop; auto.
    clear H. induction L'.
      rewrite filter_nil in M. inverts M.
      rewrite filter_cons in M. cases_if; fold_bool; fold_prop. 
        inverts~ M.
        apply~ IHL'.
Qed.

End Properties.

End FsetImpl.



(* ********************************************************************** *)
(** * Derivable properties about finite sets *)

Section Properties.
Variables A : Type.
Implicit Types x : A.
Implicit Types E : fset A.

(** Properties of [in] *)

Lemma in_empty_elim : forall x,
  x \in \{} -> False.
Proof. introv H. rewrite~ in_empty in H. Qed.

Lemma in_singleton_self : forall x,
  x \in \{x}.
Proof. intros. rewrite~ in_singleton. Qed.

(** Properties of [union] *)

Lemma union_same : forall E,
  E \u E = E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_union.
Qed.

Lemma union_comm : forall E F,
  E \u F = F \u E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_union.
Qed.

Lemma union_assoc : forall E F G,
  E \u (F \u G) = (E \u F) \u G.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_union.
Qed.

Lemma union_empty_l : forall E,
  \{} \u E = E.
Proof.
  intros. apply fset_extens; 
   intros x; rewrite_all in_union.
    intros [ H | H ]. false. rewrite~ in_empty in H. auto.
    auto*.
Qed.

Lemma union_empty_r : forall E,
  E \u \{} = E.
Proof. intros. rewrite union_comm. apply union_empty_l. Qed.

Lemma union_comm_assoc : forall E F G,
  E \u (F \u G) = F \u (E \u G).
Proof.
  intros. rewrite union_assoc.
  rewrite (union_comm E F).
  rewrite~ <- union_assoc.
Qed.

(** Properties of [inter] *)

Lemma inter_same : forall E,
  E \n E = E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_inter.
Qed.

Lemma inter_comm : forall E F,
  E \n F = F \n E.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_inter.
Qed.

Lemma inter_assoc : forall E F G,
  E \n (F \n G) = (E \n F) \n G.
Proof.
  intros. apply fset_extens;
   intros x; rewrite_all* in_inter.
Qed.

Lemma inter_empty_l : forall E,
  \{} \n E = \{}.
Proof.
  intros. apply fset_extens; 
   intros x; rewrite_all in_inter.
    intros. false* in_empty_elim.
    intros. false* in_empty_elim. 
Qed.

Lemma inter_empty_r : forall E,
  E \n \{} = \{}.
Proof. intros. rewrite inter_comm. apply inter_empty_l. Qed.

Lemma inter_comm_assoc : forall E F G,
  E \n (F \n G) = F \n (E \n G).
Proof.
  intros. rewrite inter_assoc.
  rewrite (inter_comm E F).
  rewrite~ <- inter_assoc.
Qed.

(* Properties of [from_list] *)

Lemma from_list_nil : 
  from_list (@nil A) = \{}.
Proof. auto. Qed.

Lemma from_list_cons : forall x l,
  from_list (x::l) = \{x} \u (from_list l).
Proof. auto. Qed.

(* Properties of [disjoint] *)

Lemma disjoint_comm : forall E F,
  disjoint E F -> disjoint F E.
Proof. unfold disjoint. intros. rewrite~ inter_comm. Qed.

Lemma disjoint_in_notin : forall E F x,
  disjoint E F -> x \in E -> x \notin F.
Proof.
  unfold disjoint. introv H InE InF. applys in_empty_elim x.
  rewrite <- H. rewrite in_inter. auto.
Qed.

(** Properties of [notin] *)

Lemma notin_empty : forall x,
  x \notin \{}.
Proof. intros_all. rewrite~ in_empty in H. Qed.

Lemma notin_singleton : forall x y,
  x \notin \{y} <-> x <> y.
Proof. unfold notin. intros. rewrite* <- in_singleton. Qed.

Lemma notin_same : forall x,
  x \notin \{x} -> False.
Proof. intros. apply H. apply* in_singleton_self. Qed.

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof. unfold notin. intros. rewrite* in_union. Qed.

(** Properties of [subset] *)

Lemma subset_refl : forall E,
  E \c E.
Proof. intros_all. auto. Qed.

Lemma subset_empty_l : forall E,
  \{} \c E.
Proof. intros_all. rewrite* in_empty in H. Qed.

Lemma subset_union_weak_l : forall E F,
  E \c (E \u F).
Proof. intros_all. rewrite* in_union. Qed.

Lemma subset_union_weak_r : forall E F,
  F \c (E \u F).
Proof. intros_all. rewrite* in_union. Qed.

Lemma subset_union_2 : forall E1 E2 F1 F2,
  E1 \c F1 -> E2 \c F2 -> (E1 \u E2) \c (F1 \u F2).
Proof. introv H1 H2. intros x. do 2 rewrite* in_union. Qed.

(** Properties of [remove] *)

Lemma union_remove : forall E F G,
  (E \u F) \- G = (E \- G) \u (F \- G).
Proof.
  intros. apply fset_extens; intros x;
  repeat (first [ rewrite in_remove | rewrite in_union ]); auto*.
Qed.

End Properties.








