(***************************************************************************
* Safety for STLC in Wright & Felleisen style                              *
* Arthur Charguéraud, July 2007                                            *
*                                                                          *
* Made more verbose by Sam                                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_var   : var -> typ
  | typ_arrow : typ -> typ -> typ.

(** Grammar of pre-terms. *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_app  : trm -> trm -> trm.

(** Opening up abstractions *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs t1    => trm_abs (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  end.

Definition open u t := open_rec 0 u t.

(** Terms are locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (open (trm_fvar x) t1)) ->
      term (trm_abs t1)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2).

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env typ.

(** Typing relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      typing E (trm_fvar x) T
  | typing_abs : forall L E U T t1,
      (forall x, x \notin L -> 
        typing (E & x ~ U) (open (trm_fvar x) t1)  T) ->
      typing E (trm_abs t1)  (typ_arrow U T)
  | typing_app : forall S T E t1 t2,
      typing E t1  (typ_arrow S T) -> 
      typing E t2  S ->
      typing E (trm_app t1 t2)  T.

(** Definition of values (only abstractions are values) *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1,
      term (trm_abs t1) -> value (trm_abs t1).

(** Reduction contexts *)

Inductive ctx : Set :=
  | ctx_hole : ctx
  | ctx_app_1 : forall (C : ctx) t2,
      term t2 -> ctx
  | ctx_app_2 : forall t1 (C : ctx),
      value t1 -> ctx.

Fixpoint ctx_of (C : ctx) (t : trm) {struct C} : trm :=
  match C with
  | ctx_hole         => t
  | ctx_app_1 C t2 _ => trm_app (ctx_of C t) t2
  | ctx_app_2 t1 C _ => trm_app t1 (ctx_of C t)
  end.

(** Reduction relation - one step in call-by-value *)

Inductive red : trm -> trm -> Prop :=
  | red_beta : forall t1 t2,
      term (trm_abs t1) -> 
      value t2 ->
      red (trm_app (trm_abs t1) t2) (open t2 t1)
  | red_ctx : forall C t t',
      red t t' ->
      red (ctx_of C t) (ctx_of C t').

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  typing E t T ->
  red t t' ->
  typing E t' T.

Definition progress := forall t T, 
  typing empty t T ->
     value t 
  \/ exists t', red t t'.


(* ###################################################################### *)
(* ** Infrastructure *)

(* ********************************************************************** *)
(** ** Additional Definitions used in the Proofs *)

(** Computing free variables of a term. *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs t1    => (fv t1)
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  end.

(** Substitution for names *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs (subst z u t1)
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  end.

(* Substitution should have lower precedence than application (which is 10), so
   we take 9. *)
Notation "[ z ~> u ] t" := (subst z u t) (at level 9).

(** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (open (trm_fvar x) t).


(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : trm => fv x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

Hint Constructors term value red.


(* ********************************************************************** *)
(** ** Properties of var-by-var substitution (simpler) *)

Module VarByVarSubst.

Lemma subst_fresh : forall x t u, 
  x \notin fv t ->  [x ~> (trm_fvar u)] t = t.
Proof.
  intros. induction t; simpls; f_equal*. case_var*. 
Qed.

Lemma subst_open: forall x u1 u2 t,
   [x ~> (trm_fvar u1)] (open (trm_fvar u2) t)
 = open ([x ~> (trm_fvar u1)](trm_fvar u2)) ([x ~> (trm_fvar u1)]t).
Proof.
  intros. unfold open. generalize 0.
  induction t; intros; simpl; f_equal*.
  case_nat*. case_var*.
Qed.

(* If we only substitute vars for vars (and not terms for vars), we don't 
   need the "term" judgment, because there's no risk of variable capture. *)
Lemma subst_intro : forall x t u,
  x \notin (fv t) ->
  open (trm_fvar u) t = [x ~> (trm_fvar u)](open (trm_fvar x) t).
Proof.
  introv Fr. rewrite* subst_open.
  rewrite* (@subst_fresh x t u). simpl. case_var*.
Qed.

End VarByVarSubst.


(* ********************************************************************** *)
(** ** Properties of substitution *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  open_rec j v t = open_rec i u (open_rec j v t) ->
  t = open_rec i u t.
Proof.
  induction t; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  term t -> forall k, t = open_rec k u t.
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
  [x ~> u] (open t2 t1) = open ([x ~> u]t2) ([x ~> u]t1).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u t, y <> x -> term u ->
  open (trm_fvar y) ([x ~> u]t) = [x ~> u] (open (trm_fvar y) t).
Proof.
  introv Neq Wu. rewrite* subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> term u ->
  open u t = [x ~> u](open (trm_fvar x) t).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* (@subst_fresh x t u). simpl. case_var*.
Qed.


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

Hint Resolve subst_term.


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

Lemma open_term_orig : forall t u,
  body t -> term u -> term (open u t).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Lemma open_term : forall t u,
  body t -> term u -> term (open u t).
Proof.
  introv Wt Wu. destruct Wt as [L Wt]. pick_fresh x. rewrite (@subst_intro x).
  + apply (subst_term _ Wu). apply Wt. auto.
  + auto.
  + apply Wu.
Qed.

Hint Resolve open_term.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)

Lemma typing_regular : forall E e T,
  typing E e T -> ok E /\ term e.
Proof.
  split; induction H; auto*.
  pick_fresh y. forwards~ K: (H0 y). 
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  induction 1; auto*.
Qed.

(** Reduction contexts preserve local closure. *)

Lemma ctx_regular : forall C t,
  term t -> term (ctx_of C t).
Proof.
  lets: value_regular. intros. induction C; simpl; jauto.
Qed.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  lets: value_regular. lets: ctx_regular. induction 1; jauto.
Qed.

(** Automation for reasoning on well-formedness. *)

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: typing E _ _ |- _ => apply (proj1 (typing_regular H))
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ t _ |- _ => apply (proj2 (typing_regular H))
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  | H: value t |- _ => apply (value_regular H)
  end.


(* ###################################################################### *)
(* ** Soundness *)

(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   typing (E & G) t  T -> 
   ok (E & F & G) ->
   typing (E & F & G) t  T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply* typing_app.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F E t T z u U,
  typing (E & z ~ U & F) t  T ->
  typing E u  U ->
  typing (E & F) [z ~> u]t T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; intros G Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  apply* typing_app.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ Red. gen T.
  induction Red; intros T Typ.
  (* case: beta *)
  inversions Typ. inversions H4.
  pick_fresh x. rewrite* (@subst_intro x).
  apply_empty* typing_subst.
  (* case: ctx *)
  gen t' T. induction C; simpls; intros t' Red SR T Typ.
  auto*.
  inversions Typ. apply* typing_app.
  inversions Typ. apply* typing_app.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ.
  cuts K: (value t \/ exists c, exists t0, exists t0', 
                     red t0 t0' /\ t = ctx_of c t0).
  destruct K as [Val | [C [t1a [t1'a [Red Ctx]]]]]; subst*.
  gen_eq E: (empty : env). lets Typ': Typ.
  induction Typ; intros; subst.
  false* binds_empty_inv.
  left*.
  right. destruct~ IHTyp1 as [Val1 | [C [t1a [t1'a [Red1 Ctx1]]]]].
    destruct~ IHTyp2 as [Val2 | [C [t2a [t2a' [Red2 Ctx2]]]]].
      inversions Typ1; inversions Val1.
        exists ctx_hole (trm_app (trm_abs t0) t2) (open t2 t0). split*.
        subst. exists (ctx_app_2 C Val1). eauto.
      subst. asserts* W: (term t2). exists (ctx_app_1 C W). eauto.
Qed.
