(**************************************************************************
* TLC: A library for Coq                                                  *
* MultiSets -- PROTOTYPE                                                  *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibTactics LibLogic LibReflect
  LibRelation LibList LibInt LibNat LibOperation 
  LibEpsilon LibSet LibStruct.
Require Export LibBag.


(* ********************************************************************** *)
(** * Construction of sets as predicates *)

(* ---------------------------------------------------------------------- *)
(** ** Basic definitions *)

Definition multiset (A : Type) := A -> nat.

Section Operations.
Variables (A B : Type).
Implicit Types x : A.
Implicit Types E F G : multiset A.

Definition empty_impl : multiset A := fun _ => 0.
Definition single_impl x := fun y => If x = y then 1 else 0.
Definition in_impl x E := E x > 0.
Definition union_impl E F := fun x => (E x + F x)%nat.
Definition incl_impl E F := forall x, E x <= F x.
Definition dom_impl E := \set{ x | E x > 0 }.
Definition list_repr_impl (E:multiset A) (l:list (A*nat)) :=
     no_duplicate (LibList.map (@fst _ _) l) 
  /\ forall n x, In (x,n) l <-> (n = E x /\ n > 0).
Definition to_list_impl (E:multiset A) := epsilon (list_repr_impl E).
Definition fold_impl (m:monoid_def B) (f:A->nat->B) (E:multiset A) := 
  LibList.fold_right (fun p acc => let (x,n) := p : A*nat in monoid_oper m (f x n) acc)
    (monoid_neutral m) (to_list_impl E).
End Operations.
Definition card_impl A (E:multiset A) := 
  fold_impl (monoid_ plus 0) (fun _ n => n) E.


(* ---------------------------------------------------------------------- *)
(** ** Notation through typeclasses *)

Lemma in_inst : forall A, BagIn A (multiset A).
Proof. constructor. exact (@in_impl A). Defined.
Hint Extern 1 (BagIn _ (multiset _)) => apply in_inst
  : typeclass_instances.

Instance empty_inst : forall A, BagEmpty (multiset A).
  constructor. rapply (@empty_impl A). Defined.
Instance single_inst : forall A, BagSingle A (multiset A) .
  constructor. rapply (@single_impl A). Defined.
Instance union_inst : forall A, BagUnion (multiset A).
  constructor. rapply (@union_impl A). Defined.
Instance incl_inst : forall A, BagIncl (multiset A).
  constructor. rapply (@incl_impl A). Defined.
Instance fold_inst : forall A B, BagFold B (A->nat->B) (multiset A).
  constructor. rapply (@fold_impl A B). Defined.
Instance card_inst : forall A, BagCard (multiset A).
  constructor. rapply (@card_impl A). Defined.

Global Opaque multiset empty_inst single_inst in_inst 
 union_inst incl_inst fold_inst card_inst.

Instance multiset_inhab : forall A, Inhab (multiset A).
Proof. intros. apply (prove_Inhab (@empty_impl A)). Qed.


(* ********************************************************************** *)
(** * Properties of multisets *)

(* ---------------------------------------------------------------------- *)
(** ** Structural properties *)

Section Instances.
Variables (A:Type).
Hint Extern 1 False => math.
Hint Extern 1 (_ > _) => solve [ math | false ].
Hint Extern 1 (_ = _) => math.

Transparent multiset empty_inst single_inst in_inst 
 union_inst incl_inst fold_inst card_inst.

Global Instance multiset_in_empty_inst : In_empty_eq (A:=A) (T:=multiset A).
Proof. 
  constructor. intros. extens. simpl.
  unfold empty_impl, in_impl. auto*.
Qed.

Global Instance multiset_in_single_inst : In_single_eq (A:=A) (T:=multiset A).
Proof.
  constructor. intros. extens. simpl.
  unfold single_impl, in_impl. case_if*. 
Qed.

Global Instance multiset_in_union_inst : In_union_eq (A:=A) (T:=multiset A).
Proof.
  constructor. intros. extens. simpl.
  unfold single_impl, union_impl, in_impl. 
  iff. tests: (E x = 0). right~. left~. destruct H; math.
Qed.

Global Instance multiset_union_empty_l : Union_empty_l (T:=multiset A).
Proof. 
  constructor. intros_all. simpl.
  unfold union_impl, empty_impl, multiset. simpl. extens~.
Qed.

Global Instance multiset_union_comm : Union_comm (T:=multiset A).
Proof. 
  constructor. intros_all. simpl.
  unfold union_impl, multiset. simpl. extens~.
Qed.

Global Instance multiset_union_assoc : Union_assoc (T:=multiset A).
Proof. 
  constructor. intros_all. simpl.
  unfold union_impl, multiset. simpl. extens~.
Qed.

Global Instance multiset_card_empty : Card_empty (T:=multiset A).
Proof. skip. (*TODO: under construction *) Qed.

Global Instance multiset_card_single : Card_single (A:=A) (T:=multiset A).
Proof. skip. (*TODO: under construction *) Qed.

Global Instance multiset_card_union : Card_union (T:=multiset A).
Proof. skip. (*TODO: under construction *) Qed.

Global Instance multiset_empty_incl : Empty_incl (T:=multiset A).
Proof. 
  constructor. intros_all. simpl.
  unfold incl_impl, empty_impl, multiset. simpl. math.
Qed.

Global Instance multiset_union_empty_inv : Union_empty_inv (T:=multiset A).
Proof. 
  constructor. simpl. unfolds union_impl, empty_impl, multiset.
  intros_all. split; extens; intros x; lets: (func_same_1 x H); math.
Qed.

End Instances.

Ltac auto_tilde ::= auto_tilde_default.



(* ********************************************************************** *)
(** * Additional predicates *)

(* ---------------------------------------------------------------------- *)
(** ** Foreach *)

Section ForeachProp.
Variables (A : Type).
Implicit Types P Q : A -> Prop.
Implicit Types E F : multiset A.

Lemma foreach_empty : forall P,
  @foreach A (multiset A) _ P \{}. 
Proof. intros_all. Admitted.
(* TODO: false* @in_empty. typeclass. *)

Lemma foreach_single : forall P X,
  P X -> @foreach A (multiset A) _ P (\{ X }). 
Proof. intros_all. rewrite~ (in_single H0). Qed.

Lemma foreach_union : forall P E F,
  foreach P E -> foreach P F -> foreach P (E \u F).
Proof. intros_all. destruct~ (in_union_inv H1). Qed.

Hint Resolve foreach_empty foreach_single foreach_union.

Lemma foreach_union_inv : forall P E F,
  foreach P (E \u F) -> foreach P E /\ foreach P F.
Proof.
  introv H. split; introv K.
  apply H. rewrite~ @in_union_eq. typeclass.
  apply H. rewrite~ @in_union_eq. typeclass.
Qed.

Lemma foreach_union_eq : forall P E F,
  foreach P (E \u F) = (foreach P E /\ foreach P F).
Proof.
  intros. extens. iff.
  apply~ foreach_union_inv. apply* foreach_union.
Qed.

Lemma foreach_single_eq : forall P X,
  foreach P (\{X}:multiset A) = P X.
Proof.
  intros. extens. iff.
  apply H. apply in_single_self.
  apply~ foreach_single.
Qed. 

Lemma foreach_weaken : forall P Q E,
  foreach P E -> pred_le P Q -> foreach Q E.
Proof. introv H L K. apply~ L. Qed.

End ForeachProp.

Hint Resolve foreach_empty foreach_single foreach_union.

Hint Rewrite foreach_union_eq : rew_foreach.
Tactic Notation "rew_foreach" hyp(H) := autorewrite with rew_foreach in H.
Tactic Notation "rew_foreach" := autorewrite with rew_foreach.

Tactic Notation "rew_foreach" "~" constr(H) :=
  rew_foreach H; auto~.
Tactic Notation "rew_foreach" "*" constr(H) :=
  rew_foreach H; auto*.



(* ********************************************************************** *)
(** * Tactics *)

(* ---------------------------------------------------------------------- *)
(** ** Tactics to prove equalities on unions *)

(* todo: doc *)

Lemma for_multiset_union_assoc : forall A, assoc (union (T:=multiset A)).
Proof. intros. apply union_assoc. Qed.

Lemma for_multiset_union_comm : forall A, comm (union (T:=multiset A)).
Proof. intros. apply union_comm. Qed.

Lemma for_multiset_union_empty_l : forall A (E:multiset A), \{} \u E = E.
Proof. intros. apply union_empty_l. Qed.

Lemma for_multiset_union_empty_r : forall A (E:multiset A), E \u \{} = E.
Proof. intros. apply union_empty_r. Qed.

Lemma for_multiset_empty_incl : forall A (E:multiset A), \{} \c E.
Proof. intros. apply empty_incl. Qed.

Hint Rewrite <- for_multiset_union_assoc : rew_permut_simpl.
Hint Rewrite for_multiset_union_empty_l for_multiset_union_empty_r : rew_permut_simpl.
Ltac rew_permut_simpl :=
  autorewrite with rew_permut_simpl.
Ltac rews_permut_simpl :=
  autorewrite with rew_permut_simpl in *.

Section PermutationTactic.
Context (A:Type).
Implicit Types l : multiset A.

Lemma permut_get_1 : forall l1 l2,
  (l1 \u l2) = (l1 \u l2).
Proof. intros. auto. Qed.

Lemma permut_get_2 : forall l1 l2 l3,
  (l1 \u l2 \u l3) = (l2 \u l1 \u l3).
Proof. intros. apply union_comm_assoc. Qed.
(* rewrite (union_comm _ l1). auto. Qed. *)

Lemma permut_get_3 : forall l1 l2 l3 l4,
  (l1 \u l2 \u l3 \u l4) = (l2 \u l3 \u l1 \u l4).
Proof.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_2.
Qed.

Lemma permut_get_4 : forall l1 l2 l3 l4 l5,
    (l1 \u l2 \u l3 \u l4 \u l5)
  = (l2 \u l3 \u l4 \u l1 \u l5).
Proof.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_3.
Qed.

Lemma permut_get_5 : forall l1 l2 l3 l4 l5 l6,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6) 
  = (l2 \u l3 \u l4 \u l5 \u l1 \u l6).
Proof.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_4.
Qed.

Lemma permut_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7) 
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l1 \u l7).
Proof.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_5.
Qed.

Lemma permut_get_7 : forall l1 l2 l3 l4 l5 l6 l7 l8,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8) 
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l1 \u l8).
Proof.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_6.
Qed.

Lemma permut_get_8 : forall l1 l2 l3 l4 l5 l6 l7 l8 l9,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8 \u l9) 
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8 \u l1 \u l9).
Proof.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_7.
Qed.


Lemma permut_tactic_setup : forall C l1 l2,
   C (\{} \u l1 \u \{}) (l2 \u \{}) -> C l1 l2.
Proof. intros. rews_permut_simpl. eauto. Qed.

Lemma permut_tactic_keep : forall C l1 l2 l3 l4,
  C ((l1 \u l2) \u l3) l4 ->
  C (l1 \u (l2 \u l3)) l4.
Proof. intros. rews_permut_simpl. eauto. Qed.


Lemma permut_tactic_trans : forall C l1 l2 l3,
  l3 = l2 -> C l1 l3 -> C l1 l2.
Proof. intros. subst~. Qed.

End PermutationTactic.

(** [permut_lemma_get n] returns the lemma [permut_get_n]
    for the given value of [n] *)

Ltac permut_lemma_get n :=
  match nat_from_number n with
  | 1%nat => constr:(permut_get_1)
  | 2%nat => constr:(permut_get_2)
  | 3%nat => constr:(permut_get_3)
  | 4%nat => constr:(permut_get_4)
  | 5%nat => constr:(permut_get_5) 
  | 6%nat => constr:(permut_get_6) 
  | 7%nat => constr:(permut_get_7) 
  | 8%nat => constr:(permut_get_8) 
  end.

(** [permut_prepare] applies to a goal of the form [permut l l']
    and sets [l] and [l'] in the form [l1 \u l2 \u .. \u \{}],
    (some of the lists [li] are put in the form [x::\{}]). *)

Ltac permut_simpl_prepare :=
   rew_permut_simpl;
   apply permut_tactic_setup;
   repeat rewrite <- union_assoc.

(* todo : doc *)

Ltac permut_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l \u _ => constr:(1)
  | _ \u l \u _ => constr:(2)
  | _ \u _ \u l \u _ => constr:(3)
  | _ \u _ \u _ \u l \u _ => constr:(4)
  | _ \u _ \u _ \u _ \u l \u _ => constr:(5)
  | _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(6)
  | _ \u _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(7)
  | _ \u _ \u _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(8)
  | _ => constr:(0) (* not found *)
  end.

(** [permut_simplify] simplifies a goal of the form 
    [permut l l'] where [l] and [l'] are lists built with 
    concatenation and consing *)

Ltac permut_simpl_once_for permut_tactic_simpl := 
  let go l0 l' := 
    match l0 with
    | _ \u \{} => fail 1
    | _ \u (?l \u ?lr) => 
      match permut_index_of l l' with
      | 0 => apply permut_tactic_keep
      | ?n => let F := permut_lemma_get n in
             eapply permut_tactic_trans; 
             [ eapply F; try typeclass
             | apply permut_tactic_simpl ]
      end 
     end in
   match goal with
   | |- _ ?x ?y => go x y
   | |- _ _ ?x ?y => go x y
   | |- _ _ _ ?x ?y => go x y
   | |- _ _ _ _ ?x ?y => go x y
   end.

Ltac permut_conclude :=
  first [ apply refl_equal
        | apply for_multiset_empty_incl ].

Ltac permut_simpl_for permut_tactic_simpl :=
  permut_simpl_prepare;
  repeat permut_simpl_once_for permut_tactic_simpl;
  rew_permut_simpl;
  try permut_conclude.

Lemma permut_tactic_simpl_eq : forall A (l1 l2 l3 l4:multiset A),
  (l1 \u l3) = l4 ->
  (l1 \u (l2 \u l3)) = (l2 \u l4).
Proof. intros. subst. apply permut_get_2. Qed.

Lemma permut_tactic_simpl_incl : forall A (l1 l2 l3 l4:multiset A),
  (l1 \u l3) \c l4 ->
  (l1 \u (l2 \u l3)) \c (l2 \u l4).
(* todo: reason on inclusion *)
Admitted.

Ltac get_premut_tactic_simpl tt :=
  match goal with
  | |- ?x = ?y => constr:(permut_tactic_simpl_eq)
  | |- ?x \c ?y => constr:(permut_tactic_simpl_incl)
  end.

Ltac permut_simpl_once :=
  let L := get_premut_tactic_simpl tt in permut_simpl_once_for L.

Ltac permut_simpl :=
  let L := get_premut_tactic_simpl tt in permut_simpl_for L.

Tactic Notation "multiset_eq" := 
  permut_simpl.

Section DemoSetUnion.
Variables (A:Type).
Implicit Types l : multiset A.

Lemma demo_multiset_union_permut_simpl_1 : 
  forall l1 l2 l3 : multiset A,
  (l1 \u l2 \u l3) = (l3 \u l2 \u l1).
Proof.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  rew_permut_simpl.
  permut_conclude.
Qed.

Lemma demo_multiset_union_permut_simpl_2 : 
  forall 
  (x:A) l1 l2 l3 l4,
  (l1 \u \{x} \u l3 \u l2) \c (l1 \u l2 \u l4 \u (\{x} \u l3)).
Proof.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  rew_permut_simpl.
  permut_conclude.
Qed.

Lemma demo_multiset_union_permut_simpl_3 : forall (x y:A) l1 l1' l2 l3 l4,
  l1 \c l4 \u l1' ->
  (l1 \u (\{x} \u l2) \u \{x} \u (\{y} \u l3)) \c
  (\{y} \u \{x} \u (l1' \u l2 \u l4) \u (\{x} \u l3)).
Proof.
  intros. dup.
  (* details *)
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  try permut_simpl_once.
  rew_permut_simpl.
  equates 1. apply H. 
  permut_simpl_prepare.
  permut_simpl_once.
  rew_permut_simpl.
  permut_conclude.
  (* short *)
  permut_simpl. applys_eq H 1. permut_simpl.
Qed.

End DemoSetUnion.


(* ---------------------------------------------------------------------- *)
(** ** Tactics to prove membership *)

Section InUnionGet.
Variables (A:Type).
Implicit Types l : multiset A.

Lemma in_union_get_1 : forall x l1 l2,
  x \in l1 -> x \in (l1 \u l2).
Proof. intros. apply in_union_l. auto. Qed.

Lemma in_union_get_2 : forall x l1 l2 l3,
  x \in l2 -> x \in (l1 \u l2 \u l3).
Proof. intros. apply in_union_r. apply~ in_union_get_1. Qed.

Lemma in_union_get_3 : forall x l1 l2 l3 l4,
  x \in l3 -> x \in (l1 \u l2 \u l3 \u l4).
Proof. intros. apply in_union_r. apply~ in_union_get_2. Qed.

Lemma in_union_get_4 : forall x l1 l2 l3 l4 l5,
  x \in l4 -> x \in (l1 \u l2 \u l3 \u l4 \u l5).
Proof. intros. apply in_union_r. apply~ in_union_get_3. Qed.

Lemma in_union_get_5 : forall x l1 l2 l3 l4 l5 l6,
  x \in l5 -> x \in (l1 \u l2 \u l3 \u l4 \u l5 \u l6).
Proof. intros. apply in_union_r. apply~ in_union_get_4. Qed.

End InUnionGet.

Implicit Arguments in_union_get_1 [A x l1 l2].
Implicit Arguments in_union_get_2 [A x l1 l2 l3].
Implicit Arguments in_union_get_3 [A x l1 l2 l3 l4].
Implicit Arguments in_union_get_4 [A x l1 l2 l3 l4 l5].
Implicit Arguments in_union_get_5 [A x l1 l2 l3 l4 l5 l6].

(** [in_union_get] solves a goal of the form
    [x \in F1 \u ... \u FN] when there exists an 
    hypothesis of the form [x \in Fi] for some [i]. *)

Ltac in_union_get :=
  match goal with H: ?x \in ?A |- ?x \in ?B =>
  match B with context [A] =>
  let go tt := first       
        [ apply (in_union_get_1 H)
        | apply (in_union_get_2 H)
        | apply (in_union_get_3 H)
        | apply (in_union_get_4 H)
        | apply (in_union_get_5 H) ] in
  first [ go tt 
        | rewrite <- (for_multiset_union_empty_r B);
          repeat rewrite <- for_multiset_union_assoc;
          go tt ]
  end end. 

 
(* todo: remove hint 
Hint Extern 3 (_ \in _ \u _) => in_union_get.
*)

Section InUnionExtract.
Variables (A:Type).
Implicit Types l : multiset A.

Lemma in_union_extract_1 : forall x l1,
  x \in (\{x} \u l1).
Proof. intros. apply in_union_get_1. apply in_single_self. Qed.

Lemma in_union_extract_2 : forall x l1 l2,
  x \in (l1 \u \{x} \u l2).
Proof. intros. apply in_union_get_2. apply in_single_self. Qed.

Lemma in_union_extract_3 : forall x l1 l2 l3,
  x \in (l1 \u l2 \u \{x} \u l3).
Proof. intros. apply in_union_get_3. apply in_single_self. Qed.

Lemma in_union_extract_4 : forall x l1 l2 l3 l4,
  x \in (l1 \u l2 \u l3 \u \{x} \u l4).
Proof. intros. apply in_union_get_4. apply in_single_self. Qed.

Lemma in_union_extract_5 : forall x l1 l2 l3 l4 l5,
  x \in (l1 \u l2 \u l3 \u l4 \u \{x} \u l5).
Proof. intros. apply in_union_get_5. apply in_single_self. Qed.

End InUnionExtract.

(** [in_union_extract] solves a goal of the form
    [x \in F1 \u ... \u \{x} \u ... \u FN]. *)

Ltac in_union_extract :=
  match goal with |- ?x \in ?A =>
  match A with context [\{x}] =>
  let go tt := first       
        [ apply (in_union_extract_1)
        | apply (in_union_extract_2)
        | apply (in_union_extract_3)
        | apply (in_union_extract_4)
        | apply (in_union_extract_5) ] in
  first [ go tt 
        | rewrite <- (for_multiset_union_empty_r A);
          repeat rewrite <- for_multiset_union_assoc;
          go tt ]
  end end. 

Tactic Notation "multiset_in" := 
   first [ in_union_extract | in_union_get ].


(* ---------------------------------------------------------------------- *)
(** ** Tactics to invert a membership hypothesis *)

Section InversionsTactic.
Context (A:Type).
Implicit Types l : multiset A.
Implicit Types x : A.
Lemma empty_eq_single_inv_1 : forall x l1 l2,
  l1 = l2 -> x \notin l1 -> x \in l2 -> False.
Proof. intros. subst*. Qed.
Lemma empty_eq_single_inv_2 : forall x l1 l2,
  l1 = l2 -> x \notin l2 -> x \in l1 -> False.
Proof. intros. subst*. Qed.
Lemma notin_empty : forall x,
  x \notin (\{}:multiset A).
Proof. intros. unfold notin. rewrite in_empty_eq. auto. Qed. 
End InversionsTactic.
Hint Resolve notin_empty.

Ltac in_union_meta :=
  match goal with 
  | |- _ \in \{_} => apply in_single_self
  | |- _ \in \{_} \u _ => apply in_union_l; apply in_single_self
  | |- _ \in _ \u _ => apply in_union_r; in_union_meta
  end.

Ltac fseq_inv_core H :=
  let go L := 
     false L; [ apply H
              | try apply notin_empty 
              | instantiate; try in_union_meta ] in
  match type of H with
  | \{} = _ => go empty_eq_single_inv_1
  | _ = \{} => go empty_eq_single_inv_2
  | _ = _ => go empty_eq_single_inv_1
  end.

(** [multiset_inv H] solves a goal by contraction if
    there exists an hypothesis of the form 
    [\{} = E1 \u ... \u \{x} \u ... \u EN]
    (or its symmetric).
    [multiset_inv] speculates on the hypothesis [H] to 
    be used. *)

Tactic Notation "multiset_inv" constr(H) := 
  fseq_inv_core H.

Tactic Notation "multiset_inv" := 
  match goal with
  | |- \{} <> _ => let H := fresh in intro H; multiset_inv H
  | |- _ <> \{} => let H := fresh in intro H; multiset_inv H
  | H: \{} = _ |- _ => multiset_inv H
  | H: _ = \{} |- _ => multiset_inv H
  end.

Section InUnionInv.
Variables (A:Type).
Implicit Types l : multiset A.

Lemma in_empty_inv : forall x,
  x \in (\{}:multiset A) -> False.
Proof. introv. apply notin_empty. Qed.

Lemma in_single_inv : forall x y : A,
  x \in (\{y}:multiset A) -> x = y.
Proof. intros. rewrite @in_single_eq in H. auto. typeclass. Qed.

Lemma in_union_inv : forall x l1 l2,
  x \in (l1 \u l2) -> x \in l1 \/ x \in l2.
Proof. introv H. rewrite @in_union_eq in H. auto. typeclass. Qed.

End InUnionInv.

Implicit Arguments in_single_inv [A x y].
Implicit Arguments in_union_inv [A x l1 l2].

Ltac multiset_in_inv_base H M :=
  match type of H with
  | _ \in \{} => false; apply (@in_empty_inv _ _ H)  
  | _ \in \{_} => 
    generalize (in_single_inv H); try clear H; try intro_subst_hyp
  | _ \in _ \u _ => 
    let H' := fresh "TEMP" in
    destruct (in_union_inv H) as [H'|H']; 
    try clear H; multiset_in_inv_base H' M
  | _ => rename H into M
  end.

Tactic Notation "multiset_in" constr(H) "as" ident(M) :=
  multiset_in_inv_base H M.
Tactic Notation "multiset_in" constr(H) :=
  let M := fresh "H" in multiset_in H as M.

Lemma union_empty_inv_multiset : forall A (l1 l2:multiset A),
  l1 \u l2 = \{} -> l1 = \{} /\ l2 = \{}.
Proof. intros. apply union_empty_inv. auto. Qed.

Implicit Arguments union_empty_inv_multiset [A l1 l2].

Ltac multiset_empty_core H :=
  match type of H with
  | _ \u _ = \{} => 
     let H1 := fresh "M" in let H2 := fresh "M" in  
     destruct (union_empty_inv_multiset H) as [H1 H2]; clear H;
     multiset_empty_core H1; multiset_empty_core H2
  | ?E = \{} => try subst E; try solve [ false ]
  | \{} = _ \u _ => symmetry in H; multiset_empty_core H
  | \{} = ?E => symmetry in H; multiset_empty_core H
  end.

Tactic Notation "multiset_empty" "in" hyp(H) :=
  multiset_empty_core H.
Tactic Notation "multiset_empty" :=
  let H := fresh "M" in intro H; multiset_empty in H.
Tactic Notation "multiset_empty" constr(E) :=
  let H := fresh "M" in lets H:E; multiset_empty in H.

