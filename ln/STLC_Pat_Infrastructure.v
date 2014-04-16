(***************************************************************************
* Safety for STLC with Patterns - Infrastructure                          *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import List LibLN STLC_Pat_Definitions.

(* ********************************************************************** *)
(** ** Additional Definitions used in the Proofs *)

(** Computing free variables of a term. *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i j  => \{}
  | trm_fvar x    => {{x}
  | trm_abs t1    => (fv t1)
  | trm_let p1 t1 t2 => (fv t1) \u (fv t2)
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  | trm_pair t1 t2 => (fv t1) \u (fv t2)
  end.

(** Computing free variables of a list of terms. *)

Definition fv_list :=
  List.fold_right (fun t acc => fv t \u acc) \{}.

(** Free variables of the default term. *)

Lemma trm_def_fresh : fv trm_def = \{}.
Proof.
  auto.
Qed.

(** Substitution for names *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i j  => trm_bvar i j
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs (subst z u t1)
  | trm_let p1 t1 t2 => trm_let p1 (subst z u t1) (subst z u t2)
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_pair t1 t2 => trm_pair (subst z u t1) (subst z u t2)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

(** Iterated substitution *)

Fixpoint substs (zs : list var) (us : list trm) (t : trm)
   {struct zs} : trm :=
  match zs, us with
  | z::zs', u::us' => substs zs' us' ([z ~> u]t)
  | _, _ => t
  end.    

(** Iterated typing *)

Inductive typings (E : env) : list trm -> list typ -> Prop :=
  | typings_nil : typings E nil nil 
  | typings_cons : forall ts Us t U,
      typings E ts Us ->
      typing E t U ->
      typings E (t::ts) (U::Us).


(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : trm => fv x) in
  let E := gather_vars_with (fun x : list trm => fv_list x) in
  constr:(A \u B \u C \u D \u E).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Ltac pick_freshes n Y :=
  let L := gather_vars in (pick_freshes_gen L n Y).

Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.

Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto*.

Tactic Notation "apply_fresh" constr(T) "as" ident(X) :=
  apply_fresh_base T gather_vars X.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(X) :=
  apply_fresh T as X; auto*.

Hint Constructors term value red typing typings.

Hint Extern 1 (_ \notin fv trm_def) =>
  rewrite trm_def_fresh.

Hint Extern 1 (terms _ _) => split; auto.

Hint Extern 1 (fresh (dom (_ & _)) _ _) => simpl_env.
(* todo: move *)


(* ********************************************************************** *)
(** ** Properties of iterated operators *)

Lemma fv_list_map : forall ts1 ts2,
  fv_list (ts1 ++ ts2) = fv_list ts1 \u fv_list ts2.
Proof.
  induction ts1; simpl; intros. 
  rewrite* union_empty_l.
  rewrite IHts1. rewrite* union_assoc.
Qed.

Lemma typings_concat : forall E ts1 Us1 ts2 Us2,
  typings E ts1 Us1 ->
  typings E ts2 Us2 ->
  typings E (ts1++ts2) (Us1++Us2).
Proof.
  induction ts1; introv Typ1 Typ2; inversions Typ1; simpls*.
Qed.


(* ********************************************************************** *)
(** ** Properties of substitution *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) -> t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*.
  pick_fresh x. forwards~ K: (H0 x).
   apply* (@open_rec_term_core t1 0 (trm_fvars (x::nil))).
  pick_freshes (pat_arity p1) xs. forwards~ K: (H1 xs).
   apply* (@open_rec_term_core t2 0 (trm_fvars xs)).
  unfolds~ opens. (* todo : was not needed *)
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> 
  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; f_equal*.
  case_var*. notin_false.
Qed.

Lemma subst_fresh_list : forall z u ts,
  z \notin fv_list ts ->
  ts = List.map (subst z u) ts.
Proof.
  induction ts; simpl; intros Fr.
  auto. f_equal. rewrite~ subst_fresh. auto.
Qed.

Lemma subst_fresh_trm_fvars : forall z u xs,
  fresh ({{z}) (length xs) xs ->
  trm_fvars xs = List.map (subst z u) (trm_fvars xs).
Proof.
  intros. apply subst_fresh_list.
  induction xs; simpls. auto.
    destruct H. notin_solve. auto. 
Qed.

Lemma substs_fresh : forall xs us t, 
  fresh (fv t) (length xs) xs -> 
  substs xs us t = t.
Proof.
  induction xs; simpl; intros us t Fr.
  auto. destruct us. auto.
  inversions Fr. rewrite* subst_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ (List.map (subst x u) t2).
Proof.
  intros. unfold open, opens. simpl. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. unfold trm_nth.
   apply list_map_nth. apply* subst_fresh. 
  case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_vars : forall x ys u t, 
  fresh {{x} (length ys) ys -> 
  term u ->
  ([x ~> u]t) ^ ys = [x ~> u] (t ^ ys).
Proof.
  introv Fr Tu. rewrite* subst_open. 
  unfold trm_fvars. fequals.
  induction ys; simpls. auto.
  destruct Fr. case_var. 
    notin_false. fequals~.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma substs_intro_ind : forall t xs us vs, 
  fresh (fv t \u fv_list vs \u fv_list us) (length xs) xs -> 
  terms (length xs) us ->
  terms (length vs) vs ->
  t ^^ (vs ++ us) = substs xs us (t ^^ (vs ++ (trm_fvars xs))).
Proof.
  induction xs; simpl; introv Fr Tu Tv; 
   destruct Tu; destruct us; tryfalse.
  auto.
  inversions H0. destruct Fr as [Fra Frb]. simpls.
  rewrite app_last.
  forwards K: (IHxs us (vs++t0::nil)); clear IHxs.
    rewrite* fv_list_map.
    auto. 
    split~. inversions Tv. apply* Forall_app.
  rewrite K. clear K. 
  f_equal. rewrite~ subst_open. rewrite~ subst_fresh. 
  f_equal. rewrite map_app.
  simpl. case_var; tryfalse*.
  rewrite <- app_last. 
  fequals. apply~ subst_fresh_list.
  fequals. apply* subst_fresh_trm_fvars.
Qed.

Lemma substs_intro : forall xs t us, 
  fresh (fv t \u fv_list us) (length xs) xs -> 
  terms (length xs) us ->
  t ^^ us = substs xs us (t ^ xs).
Proof.
  intros. apply* (@substs_intro_ind t xs us nil).
Qed.


(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh term_abs. rewrite* subst_open_vars.
  apply_fresh* term_let. rewrite* subst_open_vars.
Qed.

Hint Resolve subst_term.

(** Terms are stable by iterated substitution *)

Lemma substs_terms : forall xs us t,
  terms (length xs) us ->
  term t ->
  term (substs xs us t).
Proof.
  induction xs; destruct us; introv TU TT; simpl; auto.
  inversions TU. simpls. inversions H. inversions* H0.
Qed.

(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> bodys 1 t1.
Proof.
  intros. unfold bodys. inversions* H.
  exists L. intros.
  destruct xs; simpl in H; destruct H.
  destruct xs; simpl in H0; destruct H0. auto.
Qed.

Lemma body_to_term_abs : forall t1,
  bodys 1 t1 -> term (trm_abs t1).
Proof. 
  destruct 1. apply_fresh* term_abs.
Qed.
Lemma term_let_to_body : forall p1 t1 t2, 
  term (trm_let p1 t1 t2) -> bodys (pat_arity p1) t2.
Proof.
  intros. unfold bodys. inversions* H. 
Qed.

Lemma body_to_term_let : forall p1 t1 t2,
  pattern p1 -> term t1 -> bodys (pat_arity p1) t2 -> 
  term (trm_let p1 t1 t2).
Proof. 
  destruct 3. apply_fresh* term_let.
Qed.
 
Hint Resolve body_to_term_abs term_abs_to_body
             body_to_term_let.

Hint Extern 1 (bodys (pat_arity ?p1) ?t2) =>
  match goal with H: context [trm_let p1 ?t1 t2] |- _ =>
    apply (@term_let_to_body p1 t1 t2) end.

(** ** Opening a body with a term gives a term *)

Lemma open_terms : forall t us,
  bodys (length us) t ->
  terms (length us) us -> 
  term (t ^^ us).
Proof. 
  introv [L K] WT. pick_freshes (length us) xs. lets Fr': Fr.
  rewrite (fresh_length _ _ _  Fr) in WT, Fr'.
  rewrite* (@substs_intro xs). apply* substs_terms.
Qed.

Hint Resolve open_terms.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** Pattern typing is regular. *)

Lemma Pat_typing_regular : forall Ts p T,
  Pat_typing Ts p T -> pattern p.
Proof. unfolds* Pat_typing. Qed.

(* The typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)

Lemma typing_regular : forall E e T,
  typing E e T -> ok E /\ term e.
Proof.
  split; induction* H.
  pick_fresh x. forwards~ K: (H0 x). inversions* K.
  auto* Pat_typing_regular.
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  induction 1; auto*. 
Qed.

(** Pattern-matching regular. *)

Lemma Pat_match_regular : forall vs p v,
  Pat_match vs p v -> 
  pattern p /\ terms (pat_arity p) vs /\ term v.
Proof. unfolds* Pat_match. Qed.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  induction 1; auto* value_regular.
  destruct H1 as [? [[Eq ?] [? ?]]]. split~.
   apply~ open_terms. rewrite~ <- Eq.
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

Hint Extern 1 (pattern ?p) =>
  match goal with
  | H: Pat_match _ p _ |- _ => apply (proj31 (Pat_match_regular H))
  | H: Pat_typing _ p _ |- _ => apply (Pat_typing_regular H)
  end.

