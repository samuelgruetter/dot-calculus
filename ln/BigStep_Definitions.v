(***************************************************************************
* Equivalence of big-step and small-step in call-by-value - Definitions    *
* Arthur Charguéraud, March 2009                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.

(* ********************************************************************** *)
(** ** Grammar of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_app  : trm -> trm -> trm.


(* ********************************************************************** *)
(** ** Operation to open up abstractions. *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x 
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1    => trm_abs (open_rec (S k) u t1) 
  end.

Definition open t u := open_rec 0 u t.

Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).


(* ********************************************************************** *)
(** ** Definition of well-formedness of a term *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1). 


(* ********************************************************************** *)
(** ** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).


(* ********************************************************************** *)
(** ** Definition of the small-step semantics *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1, 
      term (trm_abs t1) -> value (trm_abs t1).

Inductive beta : trm -> trm -> Prop :=
  | beta_red : forall t1 t2,
      body t1 -> 
      value t2 ->
      beta (trm_app (trm_abs t1) t2) (t1 ^^ t2) 
  | beta_app1 : forall t1 t1' t2, 
      term t2 ->
      beta t1 t1' -> 
      beta (trm_app t1 t2) (trm_app t1' t2) 
  | beta_app2 : forall t1 t2 t2',
      value t1 ->
      beta t2 t2' ->
      beta (trm_app t1 t2) (trm_app t1 t2').

Inductive beta_star : trm -> trm -> Prop :=
  | beta_star_refl : forall t,
      term t ->
      beta_star t t
  | beta_star_step : forall t2 t1 t3,
      beta t1 t2 -> 
      beta_star t2 t3 -> 
      beta_star t1 t3.


(* ********************************************************************** *)
(** ** Definition of the big-step semantics *)

Inductive reds : trm -> trm -> Prop :=
  | reds_val : forall t1, 
      value t1 ->
      reds t1 t1
  | reds_red : forall t3 v2 v3 t1 t2,
      reds t1 (trm_abs t3) ->
      reds t2 v2 -> 
      reds (t3 ^^ v2) v3 ->
      reds (trm_app t1 t2) v3.


(* ********************************************************************** *)
(** ** Definition of the big-step semantics *)

Definition equivalence := forall t v,
  reds t v <-> beta_star t v /\ value v.








