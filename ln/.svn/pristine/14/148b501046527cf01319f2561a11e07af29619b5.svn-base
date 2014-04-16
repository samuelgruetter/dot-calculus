(***************************************************************************
* Church-Rosser Property in Pure Lambda-Calculus - Definitions             *
* Arthur Charguéraud, March 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Description of the Task (only part which has to be trusted) *)

(* ********************************************************************** *)
(** Grammar of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_app  : trm -> trm -> trm
  | trm_abs  : trm -> trm.

(* ********************************************************************** *)
(** Operation to open up abstractions. *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x 
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1    => trm_abs (open_rec (S k) u t1) 
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(* ********************************************************************** *)
(** Definition of well-formedness of a term *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1). 

(* ********************************************************************** *)
(** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

(* ********************************************************************** *)
(** Definition of the beta relation *)

Definition relation := trm -> trm -> Prop.

Inductive beta : relation :=
  | beta_red : forall t1 t2,
      body t1 -> 
      term t2 ->
      beta (trm_app (trm_abs t1) t2) (t1 ^^ t2) 
  | beta_app1 : forall t1 t1' t2, 
      term t2 ->
      beta t1 t1' -> 
      beta (trm_app t1 t2) (trm_app t1' t2) 
  | beta_app2 : forall t1 t2 t2',
      term t1 ->
      beta t2 t2' ->
      beta (trm_app t1 t2) (trm_app t1 t2') 
  | beta_abs : forall L t1 t1', 
     (forall x, x \notin L -> beta (t1 ^ x) (t1' ^ x)) ->
     beta (trm_abs t1) (trm_abs t1').

(* ********************************************************************** *)
(** Definition of the reflexive-transitive closure of a relation *)

Inductive star_ (R : relation) : relation :=
  | star_refl : forall t,
      term t ->
      star_ R t t
  | star_trans : forall t2 t1 t3,
      star_ R t1 t2 -> star_ R t2 t3 -> star_ R t1 t3
  | star_step : forall t t',
      R t t' -> star_ R t t'.

Notation "R 'star'" := (star_ R) (at level 69).

(* ********************************************************************** *)
(** Definition of the reflexive-symmetric-transitive closure of a relation *)

Inductive equiv_ (R : relation) : relation :=
  | equiv_refl : forall t,
      term t ->
      equiv_ R t t
  | equiv_sym: forall t t',
      equiv_ R t t' ->
      equiv_ R t' t
  | equiv_trans : forall t2 t1 t3, 
      equiv_ R t1 t2 -> equiv_ R t2 t3 -> equiv_ R t1 t3
  | equiv_step : forall t t',
      R t t' -> equiv_ R t t'.

Notation "R 'equiv'" := (equiv_ R) (at level 69).

(* ********************************************************************** *)
(** Definition of confluence and of the Church-Rosser property
 (Our goal is to prove the Church-Rosser Property for beta relation) *)

Definition confluence (R : relation) := 
  forall M S T, R M S -> R M T -> 
  exists P, R S P /\ R T P. 

Definition church_rosser (R : relation) :=
  forall t1 t2, (R equiv) t1 t2 -> 
  exists t, (R star) t1 t /\ (R star) t2 t.
