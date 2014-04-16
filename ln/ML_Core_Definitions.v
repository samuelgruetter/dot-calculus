(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Definitions                *
* Arthur Charguéraud, March 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN List.

(* ********************************************************************** *)
(** ** Description of types *)

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  | typ_arrow : typ -> typ -> typ.

(** Types are inhabited, giving us a default value. *)

Definition typ_def := typ_bvar 0.

(** Type schemes. *)

Record sch : Set := Sch { 
  sch_arity : nat ; 
  sch_type  : typ }.

(** Opening body of type schemes. *)

Fixpoint typ_open (T : typ) (Vs : list typ) {struct T} : typ :=
  match T with
  | typ_bvar i      => nth i Vs typ_def
  | typ_fvar x      => typ_fvar x 
  | typ_arrow T1 T2 => typ_arrow (typ_open T1 Vs) (typ_open T2 Vs)
  end.

(** Opening body of type schemes with variables *)

Definition typ_fvars := 
  List.map typ_fvar.

Definition typ_open_vars T Xs := 
  typ_open T (typ_fvars Xs).

(** Instanciation of a type scheme *)

Definition sch_open M := 
  typ_open (sch_type M).

Definition sch_open_vars M := 
  typ_open_vars (sch_type M).
  
Notation "M ^^ Vs" := (sch_open M Vs) 
  (at level 67, only parsing) : typ_scope.
Notation "M ^ Xs" := 
  (sch_open_vars M Xs) (only parsing) : typ_scope.

Bind Scope typ_scope with typ.
Open Scope typ_scope.

(** Locally closed types *)

Inductive type : typ -> Prop :=
  | type_fvar : forall X, 
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2).

(** List of n locally closed types *)

Definition types := list_for_n type.

(** Body of a scheme *)

Definition typ_body n T :=
  exists L, forall Xs, 
  fresh L n Xs ->
  type (typ_open_vars T Xs).

(** Definition of a well-formed scheme *)

Definition scheme M :=
   typ_body (sch_arity M) (sch_type M).


(* ********************************************************************** *)
(** ** Description of terms *)

(** Grammar of terms. *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_let  : trm -> trm -> trm
  | trm_app  : trm -> trm -> trm.

(** Opening term binders. *)

Fixpoint trm_open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x 
  | trm_abs t1    => trm_abs (trm_open_rec (S k) u t1) 
  | trm_let t1 t2 => trm_let (trm_open_rec k u t1) (trm_open_rec (S k) u t2) 
  | trm_app t1 t2 => trm_app (trm_open_rec k u t1) (trm_open_rec k u t2)
  end.

Definition trm_open t u := trm_open_rec 0 u t.

Notation "{ k ~> u } t" := (trm_open_rec k u t) (at level 67).
Notation "t ^^ u" := (trm_open t u) (at level 67).
Notation "t ^ x" := (trm_open t (trm_fvar x)).

(** Locally closed termessions *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1)
  | term_let : forall L t1 t2,
      term t1 -> 
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_let t1 t2)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2).

(** Definition of the body of an abstraction *)

Definition term_body t :=
  exists L, forall x, x \notin L -> term (t ^ x).


(* ********************************************************************** *)
(** ** Description of typing *)

(** Definition of typing environments *)

Definition env := env sch.

(** The typing judgment *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x M Us, 
      ok E -> 
      binds x M E -> 
      types (sch_arity M) Us ->
      scheme M ->
      E |= (trm_fvar x) ~: (M ^^ Us)
  | typing_abs : forall L E U T t1, 
      type U ->
      (forall x, x \notin L -> 
        (E & x ~ Sch 0 U) |= (t1 ^ x) ~: T) -> 
      E |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_let : forall M L1 L2 E T2 t1 t2, 
      (forall Xs, fresh L1 (sch_arity M) Xs ->
         E |= t1 ~: (M ^ Xs)) ->
      (forall x, x \notin L2 -> (E & x ~ M) |= (t2 ^ x) ~: T2) -> 
      E |= (trm_let t1 t2) ~: T2
  | typing_app : forall E S T t1 t2, 
      E |= t1 ~: (typ_arrow S T) ->
      E |= t2 ~: S ->   
      E |= (trm_app t1 t2) ~: T

where "E |= t ~: T" := (typing E t T).


(* ********************************************************************** *)
(** ** Description of the semantics *)

(** Grammar of values *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1, term (trm_abs t1) -> value (trm_abs t1).

(** Reduction rules *)

Inductive red : trm -> trm -> Prop :=
  | red_abs : forall t1 t2, 
      term (trm_abs t1) -> 
      value t2 ->  
      red (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | red_let : forall t1 t2, 
      term (trm_let t1 t2) ->
      value t1 -> 
      red (trm_let t1 t2) (t2 ^^ t1)
  | red_let_1 : forall t1 t1' t2, 
      term_body t2 ->
      red t1 t1' -> 
      red (trm_let t1 t2) (trm_let t1' t2)
  | red_app_1 : forall t1 t1' t2,
      term t2 ->
      red t1 t1' -> 
      red (trm_app t1 t2) (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2', 
      value t1 ->
      red t2 t2' ->
      red (trm_app t1 t2) (trm_app t1 t2').
                  
Notation "t --> t'" := (red t t') (at level 68).


(* ********************************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  E |= t ~: T ->
  t --> t' ->
  E |= t' ~: T.

Definition progress := forall t T, 
  empty |= t ~: T ->
     value t 
  \/ exists t', t --> t'.
