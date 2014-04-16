(***************************************************************************
* Safety for STLC with Patterns - Definitions                             *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import List LibLN.

Require Import Max LibLN_Set OrderedType OrderedTypeEx.

Module NatSet := FinSet Nat_as_OT.

Section Range.
Import NatSet.
Parameter range_from : nat -> nat -> NatSet.fset.

Parameter range_from_spec : forall k n,
  forall i, 
 ((k <= i < k+n) <-> i \in (range_from k n)).

End Range.

Section LogicList.
Variables A : Type.
Inductive Nth : nat -> list A -> A -> Prop :=
  | Nth_here : forall l x,
      Nth 0 (x::l) x
  | Nth_next : forall y n l x, 
      Nth n l x ->
      Nth (S n) (y::l) x.
End LogicList.



(* todo in libtactics : destructs sur \/ fait unfold *)
(* et unfolds in *)


(***************************************************************************)

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_var   : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_prod  : typ -> typ -> typ.

(** Grammar of patterns. *)

Inductive pat : Set :=
  | pat_var : nat -> pat
  | pat_wild : pat
  | pat_pair : pat -> pat -> pat
  | pat_alias : nat -> pat -> pat.

(** Grammar of pre-terms. *)

Inductive trm : Set :=
  | trm_bvar : nat -> nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_let  : pat -> trm -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_pair : trm -> trm -> trm.

(** Arity of a pattern. *)

Fixpoint pat_arity (p : pat) : nat :=
  match p with
  | pat_var n      => n+1
  | pat_wild       => 0
  | pat_pair p1 p2 => max (pat_arity p1) (pat_arity p2)
  | pat_alias n p1 => max (n+1) (pat_arity p1)
  end.

(** Default term and nth function on term lists *)

Definition trm_def := trm_bvar 0 0.

Definition trm_nth n ts := List.nth n ts trm_def.

(** Opening up abstractions *)

Fixpoint opens_rec (k : nat) (us : list trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i j  => If k = i then (trm_nth j us) else (trm_bvar i j)
  | trm_fvar x    => trm_fvar x
  | trm_abs t1    => trm_abs (opens_rec (S k) us t1)
  | trm_let p1 t1 t2 => trm_let p1 (opens_rec k us t1) 
                                   (opens_rec (S k) us t2)
  | trm_app t1 t2 => trm_app (opens_rec k us t1) (opens_rec k us t2)
  | trm_pair t1 t2 => trm_pair (opens_rec k us t1) (opens_rec k us t2)
  end.

Definition opens t us := opens_rec 0 us t.
Definition open t u := opens t (u::nil).
Definition trm_fvars := List.map trm_fvar.

Notation "{ k ~> u } t" := (opens_rec k u t) (at level 67).
Notation "t ^^ us" := (opens t us) (at level 67).
Notation "t ^ xs" := (opens t (trm_fvars xs)).

(** Well-formed patterns *)

Section Binds.
Import NatSet.
Inductive pat_binds : pat -> NatSet.fset -> Prop :=
  | pat_binds_var : forall n,
      pat_binds (pat_var n) \{n}
  | pat_binds_wild :
      pat_binds (pat_wild) \{}
  | pat_binds_pair : forall p1 p2 s1 s2,
      pat_binds p1 s1 ->
      pat_binds p2 s2 ->
      disjoint s1 s2 ->
      pat_binds (pat_pair p1 p2) (s1 \u s2)
  | pat_binds_alias : forall n p s1,
      pat_binds p s1 ->
      disjoint \{n} s1 ->
      pat_binds (pat_alias n p) (\{n} \u s1).
End Binds.

Definition pattern p :=
  pat_binds p (range_from 0 (pat_arity p)).

(** Terms are locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, fresh L 1 (x::nil) -> 
        term (t1 ^ (x::nil))) ->
      term (trm_abs t1)
  | term_let : forall L p1 t1 t2,
      pattern p1 ->
      term t1 ->
      (forall xs, fresh L (pat_arity p1) xs -> term (t2 ^ xs)) ->
      term (trm_let p1 t1 t2)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_pair : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_pair t1 t2).

(** Predicate caraterizing lists of a given number of terms *)

Definition terms := list_for_n term.

(** Definition of [bodys n t] as [t ^ xs] is a term when [|xs|=n] *)
  
Definition bodys n t :=
  exists L : vars, forall xs,
  fresh L n xs -> term (t ^ xs).

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env typ.


(** Typing relation for patterns: if Ts are the types of the
    bound variables in the pattern p, then the pattern p matches
    values of type T. *)

Reserved Notation "Ts \= p ~: T" (at level 69).

Inductive pat_typing : list typ -> pat -> typ -> Prop :=
  | pat_typing_var : forall n T Ts,
      Nth n Ts T ->
      Ts \= (pat_var n) ~: T
  | pat_typing_wild : forall T Ts,
      Ts \= (pat_wild) ~: T
  | pat_typing_pair : forall p1 p2 T1 T2 Ts,
      Ts \= p1 ~: T1 ->
      Ts \= p2 ~: T2 ->
      Ts \= (pat_pair p1 p2) ~: (typ_prod T1 T2)
  | pat_typing_alias : forall n p T Ts,
      Nth n Ts T ->
      Ts \= p ~: T ->
      Ts \= (pat_alias n p) ~: T

where "Ts \= p ~: T" := (pat_typing Ts p T).

Definition Pat_typing Ts p T :=
  pattern p /\ pat_typing Ts p T.

(* TODO:

Inductive pat_typing : 
  fmap nat typ -> pat -> typ -> Prop :=
   (n ~ T) \= (pat_var n) ~: T

Definition Pat_typing Ts p T :=
  pattern p /\ pat_typing (map (range 0 n) Ts) p T.


*)

(** Typing relation for terms *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      E |= (trm_fvar x) ~: T
  | typing_abs : forall L E U T t1,
       (forall x, fresh L 1 (x::nil) -> 
       (E & x ~ U) |= t1 ^ (x::nil) ~: T) ->
      E |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_let : forall L E Us R T p1 t1 t2,
      E |= t1 ~: T ->
      Pat_typing Us p1 T ->
      (forall xs, fresh L (pat_arity p1) xs -> 
        (E & xs ~* Us) |= (t2 ^ xs) ~: R) ->
      E |= (trm_let p1 t1 t2) ~: R
  | typing_app : forall S T E t1 t2,
      E |= t1 ~: (typ_arrow S T) -> 
      E |= t2 ~: S ->
      E |= (trm_app t1 t2) ~: T
  | typing_pair : forall E t1 t2 T1 T2,
      E |= t1 ~: T1 -> 
      E |= t2 ~: T2 ->
      E |= (trm_pair t1 t2) ~: (typ_prod T1 T2)

where "E |= t ~: T" := (typing E t T).

(** Definition of values (only abstractions are values) *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1,
      bodys 1 t1 -> 
      value (trm_abs t1)
  | value_pair : forall v1 v2,
     value v1 ->
     value v2 ->
     value (trm_pair v1 v2).

(** Pattern matching. *)

Definition inst := LibEnv.env trm.

Inductive pat_match : list trm -> pat -> trm -> Prop :=
  | pat_match_var : forall n v vs,
      Nth n vs v ->
      pat_match vs (pat_var n) v 
  | pat_match_wild : forall v vs,
      pat_match vs pat_wild v
  | pat_match_pair : forall p1 p2 v1 v2 vs,
      pat_match vs p1 v1 ->
      pat_match vs p2 v2 ->
      pat_match vs (pat_pair p1 p2) (trm_pair v1 v2)
  | pat_match_alias : forall n p v vs,
      Nth n vs v ->
      pat_match vs p v ->
      pat_match vs (pat_alias n p) v.

Definition Pat_match vs p v :=
  pattern p /\ terms (pat_arity p) vs /\ term v /\ 
  pat_match vs p v.

(** Reduction relation - one step in call-by-value *)

Inductive red : trm -> trm -> Prop :=
  | red_beta : forall t1 t2,
      term (trm_abs t1) -> 
      value t2 ->
      red (trm_app (trm_abs t1) t2) (t1 ^^ (t2::nil))
  | red_let : forall p1 t1 t2 ts,
      value t1 ->
      bodys (pat_arity p1) t2 ->
      Pat_match ts p1 t1 ->
      red (trm_let p1 t1 t2) (t2 ^^ ts)
  | red_app_1 : forall t1 t1' t2,
      red t1 t1' ->
      term t2 ->
      red (trm_app t1 t2) (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2',
      value t1 ->
      red t2 t2' ->
      red (trm_app t1 t2) (trm_app t1 t2')
  | red_let_1 : forall p1 t1 t1' t2,
      red t1 t1' ->
      pattern p1 ->
      bodys (pat_arity p1) t2 ->
      red (trm_let p1 t1 t2) (trm_let p1 t1' t2)
  | red_pair_1 : forall t1 t1' t2,
      red t1 t1' ->
      term t2 ->
      red (trm_pair t1 t2) (trm_pair t1' t2)
  | red_pair_2 : forall t1 t2 t2',
      value t1 ->
      red t2 t2' ->
      red (trm_pair t1 t2) (trm_pair t1 t2').

Notation "t ---> t'" := (red t t') (at level 68).

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  E |= t ~: T ->
  t ---> t' ->
  E |= t' ~: T.

Definition progress := forall t T, 
  empty |= t ~: T ->
     value t 
  \/ exists t', t ---> t'.

