(***************************************************************************
* Safety for STLC with References - Definitions                            *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.


(* ********************************************************************** *)

(** Grammar of types. *)

Parameter atm : Set.

Inductive typ : Set :=
  | typ_var   : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_ref   : typ -> typ
  | typ_unit  : typ.

(** Grammar of pre-terms. *)

Definition loc := var.

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_unit : trm
  | trm_loc : loc -> trm
  | trm_ref : trm -> trm
  | trm_get : trm -> trm
  | trm_set : trm -> trm -> trm.

(** Opening up abstractions *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs t1    => trm_abs (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_unit          => trm_unit
  | trm_loc l     => trm_loc l
  | trm_ref t1    => trm_ref (open_rec k u t1)
  | trm_get t1    => trm_get (open_rec k u t1)
  | trm_set t1 t2 => trm_set (open_rec k u t1) (open_rec k u t2)
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
  | term_trm_unit :
      term trm_unit
  | term_loc : forall l,
      term (trm_loc l)
  | term_new : forall t1,
      term t1 ->
      term (trm_ref t1)
  | term_get : forall t1,
      term t1 ->
      term (trm_get t1)
  | term_set : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_set t1 t2).

(** Store maps (sto) locations to values, and
    Store typing (phi) maps locations to type. *)

Definition sto := LibEnv.env trm.
Definition phi := LibEnv.env typ.

Inductive sto_ok : sto -> Prop :=
  | sto_ok_empty : sto_ok empty
  | sto_ok_push : forall mu l t,
      sto_ok mu -> term t -> 
      sto_ok (mu & l ~ t).

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env typ.


(* ********************************************************************** *)

(** Typing relation *)

Reserved Notation "E ! P |= t ~: T" (at level 69).

Inductive typing : env -> phi -> trm -> typ -> Prop :=
  | typing_var : forall E P x T,
      ok E ->
      binds x T E ->
      E ! P |= (trm_fvar x) ~: T
  | typing_abs : forall L E P U T t1,
      (forall x, x \notin L -> (E & x ~ U) ! P  |= t1 ^ x ~: T) ->
      E ! P |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_app : forall S T E P t1 t2,
      E ! P |= t1 ~: (typ_arrow S T) -> E ! P  |= t2 ~: S ->
      E ! P  |= (trm_app t1 t2) ~: T
  | typing_trm_unit : forall E P,
      ok E ->
      E ! P |= trm_unit ~: typ_unit
  | typing_loc : forall E P l T,
      ok E ->
      binds l T P ->
      E ! P |= (trm_loc l) ~: (typ_ref T)
  | typing_new : forall E P t1 T,
      E ! P |= t1 ~: T ->
      E ! P |= (trm_ref t1) ~: (typ_ref T)
  | typing_get : forall E P t1 T,
      E ! P |= t1 ~: (typ_ref T) ->
      E ! P |= (trm_get t1) ~: T
  | typing_set : forall E P t1 t2 T,
      E ! P |= t1 ~: (typ_ref T) ->
      E ! P |= t2 ~: T ->
      E ! P |= (trm_set t1 t2) ~: typ_unit

where "E ! P |= t ~: T" := (typing E P t T).

(** Typing store *)

Definition sto_typing P mu :=
     sto_ok mu 
  /\ (forall l, l # mu -> l # P)
  /\ (forall l T, binds l T P -> 
        exists t, binds l t mu
               /\ empty ! P |= t ~: T).

Notation "P |== mu" := (sto_typing P mu) (at level 68).


(** Definition of values *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1,
      term (trm_abs t1) -> 
      value (trm_abs t1)
  | value_trm_unit : 
      value trm_unit
  | value_loc : forall l,
      value (trm_loc l).

(** Reduction relation - one step in call-by-value *)

Definition conf := (trm * sto)%type.

Inductive red : conf -> conf -> Prop :=

  | red_beta : forall mu t1 t2,
      sto_ok mu ->
      term (trm_abs t1) -> 
      value t2 ->
      red (trm_app (trm_abs t1) t2, mu) (t1 ^^ t2, mu)
  | red_new : forall mu t1 l,
      sto_ok mu ->
      value t1 ->
      l # mu ->
      red (trm_ref t1, mu) (trm_loc l, (mu & l ~ t1))
  | red_get : forall mu l t,
      sto_ok mu ->
      binds l t mu ->
      red (trm_get (trm_loc l), mu) (t, mu)
  | red_set : forall mu l t2,
      sto_ok mu ->
      value t2 ->
      red (trm_set (trm_loc l) t2, mu) (trm_unit, mu & l ~ t2)  

  | red_app_1 : forall mu mu' t1 t1' t2,
      term t2 ->
      red (t1, mu) (t1', mu') ->
      red (trm_app t1 t2, mu) (trm_app t1' t2, mu')
  | red_app_2 : forall mu mu' t1 t2 t2',
      value t1 ->
      red (t2, mu) (t2', mu') ->
      red (trm_app t1 t2, mu) (trm_app t1 t2', mu')
  | red_new_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_ref t1, mu) (trm_ref t1', mu')
  | red_get_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_get t1, mu) (trm_get t1', mu')
  | red_set_1 : forall mu mu' t1 t1' t2,
      red (t1, mu) (t1', mu') ->
      term t2 ->
      red (trm_set t1 t2, mu) (trm_set t1' t2, mu')
  | red_set_2 : forall mu mu' t1 t2 t2',
      value t1 ->
      red (t2, mu) (t2', mu') ->
      red (trm_set t1 t2, mu) (trm_set t1 t2', mu').

Notation "c --> c'" := (red c c') (at level 68).

(** Goal is to prove preservation and progress *)

Definition preservation := forall P t t' mu mu' T,
  empty ! P |= t ~: T ->
  (t,mu) --> (t',mu') ->
  P |== mu ->
  exists P', 
     extends P P'
  /\ empty ! P' |= t' ~: T
  /\ P' |== mu'.

Definition progress := forall P t mu T, 
  empty ! P |= t ~: T ->
  P |== mu ->
     value t 
  \/ exists t', exists mu', (t,mu) --> (t',mu').

