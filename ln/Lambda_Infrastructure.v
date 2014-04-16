(***************************************************************************
* Church-Rosser Property in Pure Lambda-Calculus - Infrastructure          *
* Arthur Charguéraud, March 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN Lambda_Definitions.

(* ********************************************************************** *)
(** ** Additional Definitions Used in the Proofs *)

(* ********************************************************************** *)
(** Computing free variables of a term *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  | trm_abs t1    => (fv t1)
  end.

(* ********************************************************************** *)
(** Abstracting a name out of a term *)

Fixpoint close_var_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => If x = z then (trm_bvar k) else (trm_fvar x)
  | trm_app t1 t2 => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_abs t1    => trm_abs (close_var_rec (S k) z t1) 
  end.

Definition close_var z t := close_var_rec 0 z t.

(* ********************************************************************** *)
(** Substitution for a name *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_abs t1    => trm_abs (subst z u t1) 
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

(* ********************************************************************** *)
(** Definition of parallel relation *)

Inductive para : relation :=
  | para_red : forall L t1 t1' t2 t2',
      (forall x, x \notin L -> para (t1 ^ x) (t1' ^ x) ) ->
      para t2 t2' ->
      para (trm_app (trm_abs t1) t2) (t1' ^^ t2') 
  | para_var : forall x, 
      para (trm_fvar x) (trm_fvar x)
  | para_app : forall t1 t1' t2 t2',
      para t1 t1' -> para t2 t2' ->
      para (trm_app t1 t2) (trm_app t1' t2')
  | para_abs : forall L t1 t1',
     (forall x, x \notin L -> para (t1 ^ x) (t1' ^ x) ) ->
     para (trm_abs t1) (trm_abs t1').

(* ********************************************************************** *)
(** Definition of the transitive closure of a relation *)

Inductive iter_ (R : relation) : relation :=
  | iter_trans : forall t2 t1 t3,
      iter_ R t1 t2 -> iter_ R t2 t3 -> iter_ R t1 t3
  | iter_step : forall t t',
      R t t' -> iter_ R t t'.

Notation "R 'iter'" := (iter_ R) (at level 69).

(* ********************************************************************** *)
(** Inclusion between relations (simulation or a relation by another) *)

Definition simulated (R1 R2 : relation) := 
  forall (t t' : trm), R1 t t' -> R2 t t'.
 
Infix "simulated_by" := simulated (at level 69).

(* ********************************************************************** *)
(** Properties of relations *)

Definition red_regular (R : relation) :=
  forall t t', R t t' -> term t /\ term t'.

Definition red_refl (R : relation) :=
  forall t, term t -> R t t.

Definition red_in (R : relation) :=
  forall t x u u', term t -> R u u' ->
  R ([x ~> u]t) ([x ~> u']t).
  
Definition red_all (R : relation) :=
  forall x t t', R t t' -> 
  forall u u', R u u' -> 
  R ([x~>u]t) ([x~>u']t').

Definition red_out (R : relation) :=
  forall x u t t', term u -> R t t' -> 
  R ([x~>u]t) ([x~>u]t').

Definition red_rename (R : relation) :=
  forall x t t' y,
  x \notin (fv t) -> x \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Definition red_through (R : relation) :=
  forall x t1 t2 u1 u2, 
  x \notin (fv t1) -> x \notin (fv u1) ->
  R (t1 ^ x) (u1 ^ x) -> R t2 u2 ->
  R (t1 ^^ t2) (u1 ^^ u2).


(* ********************************************************************** *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv x) in
  constr:(A \u B \u C).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

Hint Constructors term.

(* ********************************************************************** *)
(** ** Lemmas *)

(* ********************************************************************** *)
(** Properties of substitutions *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term_core :forall e j v i u, i <> j ->
  {j ~> v}e = {i ~> u}({j ~> v}e) -> e = {i ~> u}e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*. unfolds open.
  pick_fresh x. apply* (@open_rec_term_core t1 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; f_equal*. case_var*. 
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u e, y <> x -> term u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.

(** Tactic to permute subst and open var *)

Ltac cross := 
  rewrite subst_open_var; try cross.

Tactic Notation "cross" "*" := 
  cross; auto*.


(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh term_abs as y. rewrite* subst_open_var.
Qed.

Lemma subst_body : forall z u t,
  body t -> term u -> body ([z ~> u]t).
  unfold body. introv [L H]. exists (L \u \{z}).
  intros. rewrite~ subst_open_var. apply* subst_term.
Qed.

Hint Resolve subst_term subst_body.


(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> body t1.
Proof.
  intros. unfold body. inversion* H.
Qed.

Lemma body_to_term_abs : forall t1, 
  body t1 -> term (trm_abs t1).
Proof.
  intros. inversion* H.
Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

(** ** Opening a body with a term gives a term *)

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_term.


(* ********************************************************************** *)
(** ** Additional results on primitive operations *)

(** Open_var with fresh names is an injective operation *)

Lemma open_var_inj : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_var_body] and [close_var_open] *)

Lemma close_var_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (fv t1) ->
    {i ~> trm_fvar y} ({j ~> trm_fvar z} (close_var_rec j x t1) )
  = {j ~> trm_fvar z} (close_var_rec j x ({i ~> trm_fvar y}t1) ).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ]. 
  case_var*. simpl. case_nat*. 
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_fresh : forall x t,
  x \notin fv (close_var x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simpls*.
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_body : forall x t,
  term t -> body (close_var x t).
Proof.
  introv W. exists \{x}. intros y Fr.
  unfold open, close_var. generalize 0. gen y.
  induction W; intros y Fr k; simpls.
  case_var; simpls*. case_nat*.
  auto*.
  apply_fresh* term_abs as z.
   unfolds open. rewrite* close_var_rec_open.
Qed.

(** Close var is the right inverse of open_var *)

Lemma close_var_open : forall x t,
  term t -> t = (close_var x t) ^ x.
Proof.
  introv W. unfold close_var, open. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
Qed.
 
(** An abstract specification of close_var, which packages the
  result of the operation and all the properties about it. *)

Lemma close_var_spec : forall t x, term t -> 
  exists u, t = u ^ x /\ body u /\ x \notin (fv u).
Proof.
  intros. exists (close_var x t). splits 3.
  apply* close_var_open.
  apply* close_var_body.
  apply* close_var_fresh.
Qed. 

(* ********************************************************************** *)
(** Tactics *)

(** [inst_notin H y as H'] expects [H] to be of the form
  [forall x, x \notin L, P x] and creates an hypothesis [H']
  of type [P y]. It tries to prove the subgoal [y \notin L]
  by [auto]. This tactic is very useful to apply induction
  hypotheses given in the cases with binders. *)

Tactic Notation "inst_notin" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  let go L := let Fr := fresh in assert (Fr : var \notin L);
     [ notin_solve | lets hyp_name: (@lemma var Fr); clear Fr ] in
  match type of lemma with
    forall _, _ \notin ?L -> _ => go L end.

Tactic Notation "inst_notin" "~" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  inst_notin lemma var as hyp_name; auto_tilde.

Tactic Notation "inst_notin" "*" constr(lemma) constr(var)
                "as" ident(hyp_name) :=
  inst_notin lemma var as hyp_name; auto_star.

(* TODO: re-implement inst_notin using forwards *)

(* ********************************************************************** *)
(** Regularity: relations only hold on well-formed terms *)

Section TermRelations.

Hint Extern 1 (term (trm_abs ?t)) => 
  match goal with H: context [term (t ^ _) ] |- _ =>
   let y := fresh in let K := fresh in 
   apply_fresh term_abs as y;
   inst_notin H y as K; destruct K; auto end.

Lemma red_regular_beta : red_regular beta.
Proof.
  intros_all. induction* H.
Qed.

Lemma red_regular_beta_star : red_regular (beta star).
Proof.
  intros_all. induction* H. apply* red_regular_beta.
Qed.

Lemma red_regular_para : red_regular para.
Proof.
  intros_all. induction* H.
Qed.

Lemma red_regular_para_iter : red_regular (para iter).
Proof.
  intros_all. induction* H. apply* red_regular_para.
Qed.

End TermRelations.

Hint Resolve red_regular_beta red_regular_beta_star red_regular_para red_regular_para_iter.

Hint Extern 1 (term ?t) => match goal with
  | H: beta t _ |- _ => apply (proj1 (red_regular_beta H))
  | H: beta _ t |- _ => apply (proj2 (red_regular_beta H))
  | H: para t _ |- _ => apply (proj1 (red_regular_para H))
  | H: para _ t |- _ => apply (proj2 (red_regular_para H))
  | H: (beta star) t _ |- _ => apply (proj1 (red_regular_beta_star H))
  | H: (beta star) _ t |- _ => apply (proj2 (red_regular_beta_star H))
  | H: (para iter) t _ |- _ => apply (proj1 (red_regular_para_iter))
  | H: (para iter) _ t |- _ => apply (proj2 (red_regular_para_iter))
  end.

(* A last helper to solve the case where we have to prove
   [body t] and that we only know that [t ^ x] is a term
   because it appears as an argument to some reduction R. *)

Hint Extern 1 (body ?t) => 
   match goal with H: context [?R (t ^ _) _ ] |- _ => 
     let y := fresh in apply term_abs_to_body;
     apply_fresh term_abs as y; 
     inst_notin H y as K; clear H end.

