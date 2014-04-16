(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Definitions              *
* Arthur Charguéraud, January 2009                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_var   : var -> typ
  | typ_arrow : typ -> typ -> typ.

(** Grammar of pre-terms. *)

Inductive val : Set :=
  | val_bvar : nat -> val
  | val_fvar : var -> val
  | val_abs  : trm -> val

with trm : Set :=
  | trm_val  : val -> trm
  | trm_app  : val -> trm -> trm.

Notation "'\' v" := (trm_val v) (at level 69).
Coercion trm_val : val >-> trm.
Implicit Types v : val.

(** Opening up abstractions *)

Fixpoint trm_open_rec (k : nat) (u : val) (t : trm) {struct t} : trm :=
  match t with
  | trm_val v1    => trm_val (val_open_rec k u v1)
  | trm_app v1 t2 => trm_app (val_open_rec k u v1) (trm_open_rec k u t2)
  end 
with val_open_rec (k : nat) (u : val) (v : val) {struct v} : val :=
  match v with
  | val_bvar i  => If k = i then u else v
  | val_fvar x  => v
  | val_abs t1  => val_abs (trm_open_rec (S k) u t1)
  end.

Definition open t u := trm_open_rec 0 u t.

Notation "{ k ~> u } t" := (trm_open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (val_fvar x)).

(** Terms are locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_val : forall v,
      value v ->
      term (trm_val v)
  | term_app : forall v1 t2,
      value v1 -> 
      term t2 -> 
      term (trm_app v1 t2)
with value : val -> Prop :=
  | value_var : forall x,
      value (val_fvar x)
  | value_abs : forall L t1,
      (forall x, x \notin L -> term (t1^x)) ->
      value (val_abs t1).

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env typ.

(** Typing relation *)

Reserved Notation "E |= t ~: T" (at level 69).
Reserved Notation "E \= v ~: T" (at level 69).

Inductive typing_trm : env -> trm -> typ -> Prop :=
  | typing_trm_val : forall E v T,
      E \= v ~: T -> 
      E |= (trm_val v) ~: T
  | typing_trm_app : forall S T E v1 t2,
      E \= v1 ~: (typ_arrow S T) -> 
      E |= t2 ~: S ->
      E |= (trm_app v1 t2) ~: T

where "E |= t ~: T" := (typing_trm E t T)

with typing_val : env -> val -> typ -> Prop :=
  | typing_val_var : forall E x T,
      ok E ->
      binds x T E ->
      E \= (val_fvar x) ~: T
  | typing_val_abs : forall L E U T t1,
      (forall x, x \notin L -> 
        (E & x ~ U) |= t1 ^ x ~: T) ->
      E \= (val_abs t1) ~: (typ_arrow U T)

where "E \= t ~: T" := (typing_val E t T).

(** Reduction relation - one step in call-by-value *)

Inductive red : trm -> trm -> Prop :=
  | red_beta : forall t1 v2,
      value (val_abs t1) ->
      value v2 ->
      red (trm_app (val_abs t1) v2) (t1 ^^ v2)
  | red_app_2 : forall v1 t2 t2',
      red t2 t2' ->
      red (trm_app v1 t2) (trm_app v1 t2').

Notation "t --> t'" := (red t t') (at level 68).

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  E |= t ~: T ->
  t --> t' ->
  E |= t' ~: T.

Definition progress := forall t T, 
  empty |= t ~: T ->
     exists v, t = trm_val v
  \/ exists t', t --> t'.

