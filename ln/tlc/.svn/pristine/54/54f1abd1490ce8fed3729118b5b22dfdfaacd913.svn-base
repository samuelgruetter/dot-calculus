(**************************************************************************
* TLC: A library for Coq                                                  *
* Heaps: finite maps from keys to values                                  *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibReflect LibList LibSet.
Generalizable Variable K V.

(***********************************************************)
(***********************************************************)
(***********************************************************)
(* Abstract interface of a heap *)

Module Type HeapSpec.

Parameter heap : Type -> Type -> Type.


(***********************************************************)
(** Operations *)

Section HeapDef.
Variables K V : Type. 

Parameter empty : heap K V.
Parameter dom : heap K V -> set K. (* LATER: should be a finite set *)
Parameter binds : heap K V -> K -> V -> Prop.
Parameter write : heap K V -> K -> V -> heap K V.
Parameter to_list : heap K V -> list (K * V).
Definition indom h r :=	(r \in dom h).

End HeapDef.

Parameter read : forall `{Comparable K} `{Inhab V}, heap K V -> K -> V.
Parameter read_option : forall `{Comparable K} V, heap K V -> K -> option V.
Parameter rem : forall `{Comparable K} V, heap K V -> K -> heap K V.

Implicit Arguments empty [[K] [V]].


(***********************************************************)
(** Properties *)

Section HeapAxioms.
Context `{Comparable K} `{Inhab V}.
Implicit Types h : heap K V.

Parameter indom_equiv_binds : forall h k,
  indom h k = (exists v, binds h k v).

Parameter dom_empty :
  dom (@empty K V) = \{}.

Parameter binds_equiv_read : forall h k,
  indom h k -> (forall v, (binds h k v) = (read h k = v)).

Parameter dom_write : forall h r v,
  dom (write h r v) = dom h \u \{r}.

Parameter binds_write_eq : forall h k v,
  binds (write h k v) k v.

Parameter binds_write_neq : forall h k v k' v',
  binds h k v -> k <> k' -> 
  binds (write h k' v') k v.

Parameter binds_write_inv : forall h k v k' v',
  binds (write h k' v') k v -> 
  (k = k' /\ v = v') \/ (k <> k' /\ binds h k v). 

Parameter binds_rem : forall h k k' v,
  binds h k v -> k <> k' -> binds (rem h k') k v.

Parameter binds_rem_inv : forall h k v k',
  binds (rem h k') k v -> k <> k' /\ binds h k v.

(* TODO: need to add the instance BagRemove to LibSet
Parameter dom_rem : forall h k,
  dom (rem h k) = (dom h) \- k.
For now, we used this derived form:
*)

Parameter not_indom_rem : forall h k,
  ~ indom (rem h k) k.

Parameter binds_equiv_read_option : forall h k v,
  (binds h k v) = (read_option h k = Some v).

Parameter not_indom_equiv_read_option : forall h k,
  (~ indom h k) = (read_option h k = None).

Parameter read_option_def : forall h k,
  read_option h k = (If indom h k then Some (read h k) else None).

End HeapAxioms.

Parameter indom_decidable : forall `{Comparable K} V (h:heap K V) k,
  Decidable (indom h k).
Existing Instance indom_decidable.

End HeapSpec.


(***********************************************************)
(***********************************************************)
(***********************************************************)
(** Implementation of heaps as lists *)

Module HeapList : HeapSpec.

Definition heap K V := list (K*V).

Section HeapDefs.
(*Variables K V : Type.*)
Context `{Comparable K} `{Inhab V}.
Definition empty : heap K V := nil.
Definition dom (l : heap K V) : set K :=
  fold_right (fun p acc => acc \u \{fst p}) \{} l.
Definition binds (l : heap K V) k v :=
  Assoc k v l.
Definition to_list (l : heap K V) := l.

(* TODO: move *)
Generalizable Variable A B.
Fixpoint assoc `{Comparable A} `{Inhab B} k (l:list (A*B)) : B :=
  match l with
  | nil => arbitrary
  | (x, v) :: l' => ifb x = k then v else assoc k l'
  end.
Definition read (l : heap K V) k :=
  assoc k l.
Definition write (l : heap K V) k v :=
  (k, v) :: l.
Definition rem K `{Comparable K} V (l : heap K V) k :=
  LibList.filter (fun p => ifb (fst p) = k then true else false) l.
Definition indom h r := (r \in dom h).
Fixpoint read_option (l : heap K V) k :=
  match l with
  | nil => None
  | (x, v) :: l' => ifb x = k then Some v else read_option l' k
  end.

End HeapDefs.

Implicit Arguments empty [[K] [V]].


Section HeapAxioms.
Context `{Comparable K} `{Inhab V}.
Implicit Types h : heap K V.

Lemma indom_equiv_binds : forall h k,
  indom h k = (exists v, binds h k v).
Admitted.

Lemma dom_empty :
  dom (@empty K V) = \{}.
Proof. auto. Qed.

Lemma binds_equiv_read : forall h k,
  indom h k -> (forall v, (binds h k v) = (read h k = v)).
Admitted.

Lemma dom_write : forall h r v,
  dom (write h r v) = dom h \u \{r}.
Proof. intros. unfold dom, write. rew_list. auto. Qed.

Lemma binds_write_eq : forall h k v,
  binds (write h k v) k v.
Proof. unfolds binds, write. intros. constructors. Qed.

Lemma binds_write_neq : forall h k v k' v',
  binds h k v -> k <> k' -> 
  binds (write h k' v') k v.
Proof. unfolds binds, write. intros. constructors~. Qed.

Lemma binds_write_inv : forall h k v k' v',
  binds (write h k' v') k v -> 
  (k = k' /\ v = v') \/ (k <> k' /\ binds h k v). 
Proof. unfolds binds, write. introv M. inverts* M. Qed.

Lemma binds_rem : forall h k k' v,
  binds h k v -> k <> k' -> binds (rem h k') k v.
Admitted.

Lemma binds_rem_inv : forall h k v k',
  binds (rem h k') k v -> k <> k' /\ binds h k v.
Admitted.

(* TODO: need to add the instance BagRemove to LibSet
Lemma dom_rem : forall h k,
  dom (rem h k) = (dom h) \- k.
For now, we used this derived form:
*)

Lemma not_indom_rem : forall h k,
  ~ indom (rem h k) k.
Admitted. (* TODO: prove *)

Lemma binds_equiv_read_option : forall h k v,
  (binds h k v) = (read_option h k = Some v).
Proof.
  unfolds binds. introv. extens.
  induction h as [|(x&v0)].
   splits ; intro N ; invert* N.
   simpl. cases_if.
     subst. splits ; intro N ; inverts* N. constructors.
     splits ; intro N.
      inverts* N.
      constructors*.
Qed.

Lemma not_indom_equiv_read_option : forall h k,
  (~ indom h k) = (read_option h k = None).
Proof.
  introv. apply* not_cancel. rew_logic. rewrite indom_equiv_binds.
  splits ; intro N.
   lets (v & B): rm N.
    rewrite binds_equiv_read_option in B. rewrite* B. discriminate.
   asserts (v & E): (exists v, read_option h k = Some v).
     destruct* @read_option.
    rewrite* <- binds_equiv_read_option in E.    
Qed.

Lemma read_option_def : forall h k,
  read_option h k = (If indom h k then Some (read h k) else None).
Proof.
  introv. cases_if.
   rewrite* <- binds_equiv_read_option. rewrite* binds_equiv_read.
   rewrite* <- not_indom_equiv_read_option.
Qed.

(* TODO: move *)
Generalizable Variable A.
Fixpoint mem_assoc B `{Comparable A} k (l : list (A * B)) : bool :=
  match l with
  | nil => false
  | (x, _) :: l' => decide (x = k) || mem_assoc k l'
  end.

Definition indom_dec `{Comparable K} V (h:heap K V) (k:K) : bool :=
  mem_assoc k h.

Lemma indom_dec_spec : forall `{Comparable K} V (h:heap K V) k, 
  indom_dec h k = isTrue (indom h k).
Proof.
  intros. unfold indom, dom, indom_dec.
  induction h as [|[k' v'] h]; simpl.
  rewrite in_empty_eq. rew_refl~. 
  rewrite in_union_eq. rewrite in_single_eq. rewrite IHh.
   extens. rew_refl*.
Qed.

End HeapAxioms.

Lemma indom_decidable : forall `{Comparable K} V (h:heap K V) k,
  Decidable (indom h k).
Proof.
  intros. applys decidable_make (indom_dec h k).
  applys indom_dec_spec.
Qed.

End HeapList.

Export HeapList.


(***********************************************************)
(** Facts *)

Section HeapFacts.
Context `{HK:Comparable K} `{HV:Inhab V}.
Implicit Types h : heap K V.

(** indom *)

Lemma indom_binds : forall h k, 
  indom h k -> exists v, binds h k v.
Proof. introv H. rewrite~ @indom_equiv_binds in H. Qed.

Lemma binds_indom : forall h k v, 
  binds h k v -> indom h k.
Proof. introv H. rewrite* @indom_equiv_binds. Qed.

(** binds-func *)

Lemma binds_func : forall h k v v',
  binds h k v -> binds h k v' -> v = v'.
Proof.
  introv B1 B2. forwards: binds_indom B1. forwards: binds_indom B2.
  rewrite binds_equiv_read in B1,B2; congruence.
Qed.

(** read--binds *)

Lemma binds_read : forall h k v,
  binds h k v -> read h k = v.
Proof. introv H. rewrite~ <- binds_equiv_read. apply* binds_indom. Qed.

Lemma read_binds : forall h k v,
  read h k = v -> indom h k -> binds h k v.
Proof. introv H D. rewrite~ binds_equiv_read. Qed.

(** read-write *)

Lemma read_write_eq : forall h k v, 
  read (write h k v) k = v.
Proof. introv. apply binds_read. apply binds_write_eq. Qed.

Lemma read_write_neq : forall h k k' v', 
  indom h k -> k <> k' -> read (write h k' v') k = read h k.
Proof.
  introv. rewrite indom_equiv_binds. introv [v B] N.
  rewrite (binds_read B).
  forwards B': @binds_write_neq B N. rewrite~ (binds_read B'). 
Qed.

(** indom-write *)

Lemma indom_write_eq : forall h k v,
  indom (write h k v) k.
Proof. 
  intros. rewrite indom_equiv_binds. exists v.
  apply* @binds_write_eq.
Qed.

Lemma indom_write : forall h k k' v',
  indom h k -> indom (write h k' v') k.
Proof.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B]. tests: (k = k').
    subst. exists v'. apply* @binds_write_eq.
    exists v. apply* @binds_write_neq.
Qed.

Lemma indom_write_inv : forall h k k' v',
  indom (write h k' v') k -> k <> k' -> indom h k.
Proof.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B] N. lets [[? ?]|[? ?]]: @binds_write_inv B.
  false. eauto.
Qed.  

(** binds-write *)

Lemma binds_write_eq_inv : forall h k v v',
  binds (write h k v') k v -> v = v'.
Proof.
  introv B. lets [[? ?]|[? ?]]: @binds_write_inv B; auto_false.
Qed.

Lemma binds_write_neq_inv : forall h k v k' v',
  binds (write h k' v') k v -> k <> k' -> binds h k v. 
Proof.
  introv B. lets [[? ?]|[? ?]]: @binds_write_inv B; auto_false.
Qed.

(** indom-rem *)

Lemma indom_rem : forall h k k',
  indom h k -> k <> k' -> indom (rem h k') k.
Proof.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B] N. exists v. apply* @binds_rem.
Qed.

Lemma indom_rem_inv : forall h k k',
  indom (rem h k) k' -> k <> k' /\ indom h k'.
Proof.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B]. lets [? ?]: @binds_rem_inv B. eauto.
Qed.

(** read-rem *)

Lemma read_rem_neq : forall h k k',
  indom h k -> k <> k' -> read (rem h k') k = read h k.
Proof.
  introv. rewrite indom_equiv_binds. introv [v B] N.
  rewrite (binds_read B).
  forwards B': @binds_rem B N. rewrite~ (binds_read B'). 
Qed.

(** indom-empty, binds-empty *)

Lemma not_indom_empty : forall k,
  ~ indom (@empty K V) k.
Proof. introv H. unfold indom in H. rewrite dom_empty in H. 
  skip. (* TODO: add an instance for in_empty_eq in LibSet.
  apply* in_empty_eq. *) Qed.

Lemma not_binds_empty : forall k v,
  ~ binds (@empty K V) k v.
Proof. introv H. eapply not_indom_empty. apply* binds_indom. Qed.


(** binds--read_option **)

Lemma binds_read_option : forall h k v,
  binds h k v -> read_option h k = Some v.
Proof. introv. rewrite* <- @binds_equiv_read_option. Qed.

Lemma read_option_binds : forall h k v,
  read_option h k = Some v -> binds h k v.
Proof. introv R. rewrite* <- @binds_equiv_read_option in R. Qed.


(** indom--read_option **)

Lemma not_indom_read_option : forall h k,
  ~ indom h k -> read_option h k = None.
Proof. introv. rewrite not_indom_equiv_read_option. auto*. Qed.

Lemma read_option_not_indom : forall h k,
  read_option h k = None -> ~ indom h k.
Proof. introv. rewrite not_indom_equiv_read_option. auto*. Qed.

End HeapFacts.

