(***************************************************************************
* Calculus of Constructions - Definitions                                  *
* Arthur Charguéraud, April 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Description of the Language *)

(* ********************************************************************** *)
(** Grammar of pre-terms of the calculus of constructions *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_type : nat -> trm
  | trm_app  : trm -> trm -> trm
  | trm_abs  : trm -> trm -> trm
  | trm_prod : trm -> trm -> trm.

(* ********************************************************************** *)
(** Open operation *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i     => If k = i then u else (trm_bvar i)
  | trm_fvar x     => trm_fvar x 
  | trm_type n     => trm_type n
  | trm_app t1 t2  => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1 t2  => trm_abs (open_rec k u t1) (open_rec (S k) u t2) 
  | trm_prod t1 t2 => trm_prod (open_rec k u t1) (open_rec (S k) u t2) 
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(* ********************************************************************** *)
(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_type : forall n,
      term (trm_type n)
  | term_abs : forall L t1 t2,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_abs t1 t2)
  | term_prod : forall L t1 t2,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_prod t1 t2). 

(* ********************************************************************** *)
(** Closedness of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x). 

(* ********************************************************************** *)
(** Definition of a relation on terms *)

Definition relation := trm -> trm -> Prop.

(* ********************************************************************** *)
(** Definition of the beta relation *)

Inductive beta : relation :=
  | beta_red : forall t1 t2 u,
      term (trm_abs t1 t2) -> term u ->
      beta (trm_app (trm_abs t1 t2) u) (t2 ^^ u) 
  | beta_app1 : forall t1 t1' t2, 
      term t2 ->
      beta t1 t1' -> 
      beta (trm_app t1 t2) (trm_app t1' t2) 
  | beta_app2 : forall t1 t2 t2',
      term t1 ->
      beta t2 t2' ->
      beta (trm_app t1 t2) (trm_app t1 t2') 
  | beta_abs1 : forall t1 t1' t2, 
     body t2 ->
     beta t1 t1' ->
     beta (trm_abs t1 t2) (trm_abs t1' t2)
  | beta_abs2 : forall L t1 t2 t2', 
     term t1 ->
     (forall x, x \notin L -> beta (t2 ^ x) (t2' ^ x)) ->
     beta (trm_abs t1 t2) (trm_abs t1 t2')
  | beta_prod1 : forall t1 t1' t2, 
     body t2 ->
     beta t1 t1' ->
     beta (trm_prod t1 t2) (trm_prod t1' t2)
  | beta_prod2 : forall L t1 t2 t2', 
     term t1 ->
     (forall x, x \notin L -> beta (t2 ^ x) (t2' ^ x)) ->
     beta (trm_prod t1 t2) (trm_prod t1 t2').

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
(** Conversion relation *)

Definition conv := beta equiv.

(* ********************************************************************** *)
(** Subtyping relation *)

Inductive less : relation :=
  | less_conv : forall t1 t2,
      conv t1 t2 -> less t1 t2
  | less_univ : forall i j, 
      i <= j -> 
      less (trm_type i) (trm_type j)
  | less_prod : forall L U U' T T',
     conv U U' -> 
     (forall x, x \notin L -> less (T ^ x) (T' ^ x) ) ->
     less (trm_prod U T) (trm_prod U' T')
  | less_refl : forall T,
     term T ->
     less T T
  | less_trans : forall U T V,
     less T U ->
     less U V ->
     less T V.

(* ********************************************************************** *)
(** Environment for typing *)

Definition env := LibEnv.env trm.

(* ********************************************************************** *)
(** Typing relation for terms and contexts *)

Section Typing.
Implicit Types E : env.

Inductive typing : env -> relation :=
  | typing_type : forall E i,
      wf E ->
      typing E (trm_type i) (trm_type (i+1))
  | typing_var : forall E x U,
      wf E ->
      binds x U E ->
      typing E (trm_fvar x) U
 | typing_prod : forall k L i E U T,
      typing E U (trm_type k) ->
      (forall x, x \notin L ->
        typing (E & x ~ U) (T ^ x) (trm_type i)) -> 
      (i = k \/ i = 0) ->
      typing E (trm_prod U T) (trm_type i)
  | typing_abs : forall i L E U t T,
      typing E (trm_prod U T) (trm_type i) ->
      (forall x, x \notin L ->
        typing (E & x ~ U) (t ^ x) (T ^ x)) ->
      typing E (trm_abs U t) (trm_prod U T)
  | typing_app : forall E t u T U,
      typing E t (trm_prod U T) ->
      typing E u U ->
      typing E (trm_app t u) (T ^^ u)
  | typing_sub : forall T i E t U,
      less T U ->
      typing E t T ->
      typing E U (trm_type i) ->
      typing E t U
 
with wf : env -> Prop :=
  | wf_nil : wf empty
  | wf_cons : forall i E x U,
     x # E -> 
     typing E U (trm_type i) -> 
     wf (E & x ~ U).

End Typing.

(* ********************************************************************** *)
(** ** Description of our Goals *)

(** Confluence property (proved for beta star) *)

Definition confluence (R : relation) := 
  forall M S T, R M S -> R M T -> 
  exists P, R S P /\ R T P. 

(** Church-Rosser property (proved for beta) *)

Definition church_rosser (R : relation) :=
  forall t1 t2, (R equiv) t1 t2 -> 
  exists t, (R star) t1 t /\ (R star) t2 t.

(** Subject relation (proved for beta and beta star) *)

Definition subject_reduction (R : relation) :=
  forall E t t' T,
  R t t' -> 
  typing E t T -> 
  typing E t' T.
