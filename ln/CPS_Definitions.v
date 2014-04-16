(***************************************************************************
* Correctness of the CPS-transformation - Definitions                      *
* Arthur Charguéraud, January 2009                                         *
***************************************************************************)

Set Implicit Arguments.
Require Export LibLN LibLogic LibFix.
Implicit Types x y z : var.

(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Syntax of lambda-terms with constants *)

(* ********************************************************************** *)
(** Grammar of terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_cst  : nat -> trm
  | trm_app  : trm -> trm -> trm
  | trm_abs  : trm -> trm.

Instance trm_inhab : Inhab trm.
Proof. intros. apply (prove_Inhab (trm_bvar 0)). Qed.


(* ********************************************************************** *)
(** Opening of terms *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => t
  | trm_cst k     => t
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1    => trm_abs (open_rec (S k) u t1) 
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).


(* ********************************************************************** *)
(** Closing of term *)

Fixpoint close_var_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => If x = z then (trm_bvar k) else t
  | trm_cst k     => t
  | trm_app t1 t2 => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_abs t1    => trm_abs (close_var_rec (S k) z t1) 
  end.

Definition close_var z t := close_var_rec 0 z t.


(* ********************************************************************** *)
(** Local closure of terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_cst : forall k, 
      term (trm_cst k)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1). 


(* ********************************************************************** *)
(** Body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).


(* ********************************************************************** *)
(** Free variables of a term *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_cst k     => \{}
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  | trm_abs t1    => (fv t1)
  end.


(* ********************************************************************** *)
(** Substitution for a name *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => t
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_cst k     => t 
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_abs t1    => trm_abs (subst z u t1) 
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).


(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Semantics *)

(* ********************************************************************** *)
(** Values *)

Inductive value : trm -> Prop :=
  | value_cst : forall k,
      value (trm_cst k)
  | value_abs : forall t1, 
      term (trm_abs t1) -> 
      value (trm_abs t1).


(* ********************************************************************** *)
(** Big-step reduction relation *)

Inductive eval : trm -> trm -> Prop := 
  | eval_val : forall t1, 
      value t1 ->
      eval t1 t1
  | eval_red : forall v2 t3 v3 t1 t2,
      eval t1 (trm_abs t3) ->
      eval t2 v2 -> 
      eval (t3 ^^ v2) v3 ->
      eval (trm_app t1 t2) v3.


(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Transformation *)

(* ********************************************************************** *)
(** CPS transformation of terms *)

Definition Cps (cps : trm -> trm) (t : trm) : trm :=
  match t with 
  | trm_bvar i => 
      arbitrary
  | trm_fvar x => 
      trm_abs (trm_app (trm_bvar 0) t)
  | trm_cst k  => 
      trm_abs (trm_app (trm_bvar 0) t)
  | trm_abs t1 => 
      let x := var_gen (fv t1) in
      let t1' := close_var x (cps (t1 ^ x)) in
      trm_abs (trm_app (trm_bvar 0) (trm_abs t1'))
  | trm_app t1 t2 => 
      let k := trm_abs (trm_app (trm_app (trm_bvar 1) (trm_bvar 0)) (trm_bvar 2)) in
      trm_abs (trm_app (cps t1) (trm_abs (trm_app (cps t2) k)))
  end.

Definition cps := FixFun Cps.


(* ********************************************************************** *)
(** CPS transformation of values *)

Definition cps_abs_body t1 :=
  let x := var_gen (fv t1) in
  close_var x (cps (t1 ^ x)).

Definition cpsval (t:trm) : trm :=
  match t with
  | trm_cst k  => t
  | trm_abs t1 => trm_abs (cps_abs_body t1)
  | _          => arbitrary
  end.


(* ********************************************************************** *)
(** Correctness of the CPS translation *)

Definition trm_id := trm_abs (trm_bvar 0).

Definition cps_correctness_statement := forall v t,
   eval t v -> value v ->
   eval (trm_app (cps t) trm_id) (cpsval v).



