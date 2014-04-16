(***************************************************************************
* Safety for STLC with Exceptions - Definitions                            *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.

(** Grammar of types. *)

Parameter atm : Set.

Inductive typ : Set :=
  | typ_exn : typ
  | typ_var : atm -> typ
  | typ_arrow  : typ -> typ -> typ.

(** Grammar of pre-terms. *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_raise : trm -> trm
  | trm_catch : trm -> trm -> trm.

(** Opening up abstractions *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs t1    => trm_abs (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_raise t1  => trm_raise (open_rec k u t1)
  | trm_catch t1 t2 => trm_catch (open_rec k u t1) (open_rec k u t2) 
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(** Terms are locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (trm_abs t1)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_raise : forall t1,
      term t1 ->
      term (trm_raise t1)
  | term_catch : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_catch t1 t2).

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env typ.

(** Typing relation *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      E |= (trm_fvar x) ~: T
  | typing_abs : forall L E U T t1,
      (forall x, x \notin L -> (E & x ~ U) |= t1 ^ x ~: T) ->
      E |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_app : forall S T E t1 t2,
      E |= t1 ~: (typ_arrow S T) -> E |= t2 ~: S ->
      E |= (trm_app t1 t2) ~: T
  | typing_raise : forall E t1 T,
      E |= t1 ~: typ_exn ->
      E |= (trm_raise t1) ~: T
  | typing_catch : forall E t1 t2 T,
      E |= t1 ~: (typ_arrow typ_exn T) ->
      E |= t2 ~: T ->
      E |= (trm_catch t1 t2) ~: T

where "E |= t ~: T" := (typing E t T).

(** Definition of values (only abstractions are values) *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1,
      term (trm_abs t1) -> value (trm_abs t1).

(** Exception generation *)

Inductive fails : trm -> trm -> Prop :=
  | fails_raise_val : forall t1,
      value t1 ->
      fails (trm_raise t1) t1
  | fails_raise_1 : forall t1 e,
      fails t1 e ->
      fails (trm_raise t1) e
  | fails_app_1 : forall t1 t2 e,
      term t2 ->
      fails t1 e ->
      fails (trm_app t1 t2) e
  | fails_app_2 : forall t1 t2 e,
      value t1 ->
      fails t2 e ->
      fails (trm_app t1 t2) e.

(** Reduction relation - one step in call-by-value *)

Inductive red : trm -> trm -> Prop :=
  | red_beta : forall t1 t2,
      term (trm_abs t1) -> 
      value t2 ->
      red (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | red_app_1 : forall t1 t1' t2,
      term t2 ->
      red t1 t1' ->
      red (trm_app t1 t2) (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2',
      value t1 ->
      red t2 t2' ->
      red (trm_app t1 t2) (trm_app t1 t2')
  | red_catch_2 : forall t1 t2 t2',
      term t1 ->
      red t2 t2' ->
      red (trm_catch t1 t2) (trm_catch t1 t2')
  | red_catch_val : forall t1 t2,
      term t1 ->
      value t2 ->
      red (trm_catch t1 t2) t2
  | red_catch_exn : forall t1 t2 e,
      term t1 ->
      fails t2 e ->
      red (trm_catch t1 t2) (trm_app t1 e)
  | red_raise_1 : forall t1 t1',
      red t1 t1' ->
      red (trm_raise t1) (trm_raise t1').

Notation "t --> t'" := (red t t') (at level 68).

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  E |= t ~: T ->
  t --> t' ->
  E |= t' ~: T.

Definition progress := forall t T, 
  empty |= t ~: T ->
     value t 
  \/ (exists e, fails t e)
  \/ (exists t', t --> t').

