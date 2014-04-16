(***************************************************************************
* Calculus of Constructions - Infrastructure                               *
* Arthur Charguéraud, April 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoC_Definitions.


(* ********************************************************************** *)
(** ** Additional Definitions Used in the Proofs *)

(* ********************************************************************** *)
(** Computing free variables of a term *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i     => \{}
  | trm_fvar x     => \{x}
  | trm_type n     => \{}
  | trm_app t1 t2  => (fv t1) \u (fv t2)
  | trm_abs t1 t2  => (fv t1) \u (fv t2)
  | trm_prod t1 t2 => (fv t1) \u (fv t2)
  end.

(* ********************************************************************** *)
(** Substitution for a name *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i     => trm_bvar i 
  | trm_fvar x     => If x = z then u else (trm_fvar x)
  | trm_type n     => trm_type n
  | trm_app t1 t2  => trm_app (subst z u t1) (subst z u t2)
  | trm_abs t1 t2  => trm_abs (subst z u t1) (subst z u t2)
  | trm_prod t1 t2 => trm_prod (subst z u t1) (subst z u t2)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

(* ********************************************************************** *)
(** Abstracting a name out of a term *)

Fixpoint close_var_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i     => trm_bvar i 
  | trm_fvar x     => If x = z then (trm_bvar k) else (trm_fvar x)
  | trm_type n     => trm_type n
  | trm_app t1 t2  => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_abs t1 t2  => trm_abs (close_var_rec k z t1) (close_var_rec (S k) z t2) 
  | trm_prod t1 t2 => trm_prod (close_var_rec k z t1) (close_var_rec (S k) z t2) 
  end.

Definition close_var z t := close_var_rec 0 z t.

(* ********************************************************************** *)
(** An environment contains only terms *)

Definition contains_terms E :=
  forall x U, binds x U E -> term U.

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
  R (t ^ x) (t' ^ x) -> 
  x \notin (fv t) -> x \notin (fv t') ->
  R (t ^ y) (t' ^ y).

Definition red_through (R : relation) :=
  forall x t1 t2 u1 u2, 
  x \notin (fv t1) -> x \notin (fv u1) ->
  R (t1 ^ x) (u1 ^ x) -> R t2 u2 ->
  R (t1 ^^ t2) (u1 ^^ u2).


(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv x) in
  let D := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

Ltac exists_fresh := 
  let L := gather_vars_with (fun x : vars => x) in exists L.

Scheme typing_induct := Induction for typing Sort Prop
  with wf_induct := Induction for wf Sort Prop.

Hint Constructors beta star_ equiv_ less typing wf.
Hint Unfold conv.


(* ********************************************************************** *)
(** ** Lemmas *)

(* ********************************************************************** *)
(** Properties of substitutions *)

Section SubstProperties.

Hint Constructors term.

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
  induction 1; intros; simpl; f_equal*.
  unfolds open. pick_fresh x.
   apply* (@open_rec_term_core t2 0 (trm_fvar x)).
  unfolds open. pick_fresh x. 
   apply* (@open_rec_term_core t2 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> [x ~> u] t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. 
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

End SubstProperties.

(** Tactic to permute subst and open var *)

Ltac cross := 
  rewrite subst_open_var; try cross.

Tactic Notation "cross" "*" := 
  cross; auto*.


(* ********************************************************************** *)
(** Lifting operations to terms *)

Hint Constructors term.

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_open_var.
  apply_fresh* term_prod as y. rewrite* subst_open_var.
Qed.

(** Terms are stable by open *)

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@subst_intro y). apply* subst_term.
Qed.

Hint Resolve subst_term open_term.


(* ********************************************************************** *)
(** Properties of Body *)

Lemma term_abs1 : forall t2 t1,
  term (trm_abs t1 t2) -> term t1.
Proof.
  intros. inversion* H.
Qed.

Lemma body_abs2 : forall t1 t2,  
  term (trm_abs t1 t2) -> body t2.
Proof.
  intros. unfold body. inversion* H.
Qed.

Lemma body_prod2 : forall t1 t2,  
  term (trm_prod t1 t2) -> body t2.
Proof.
  intros. unfold body. inversion* H.
Qed.

Hint Extern 1 (term ?t) =>
  match goal with H: term (trm_abs t ?t2) |- _ => 
    apply (@term_abs1 t2) end.

Hint Extern 3 (body ?t) =>
  match goal with 
  | H: context [trm_abs ?t1 t] |- _ => apply (@body_abs2 t1)
  | H: context [trm_prod ?t1 t] |- _ => apply (@body_prod2 t1)
  end.

Hint Extern 1 (body ?t) =>
  match goal with 
  | H: context [t ^ _] |- _ =>
      let x := fresh in let Fr := fresh in
      let P := fresh in
      let L := gather_vars in exists L; intros x Fr; 
      lets P: H x __; [ notin_solve 
                      | try destructs P ]
  end.

Lemma term_abs_prove : forall t1 t2,
  term t1 -> body t2 -> term (trm_abs t1 t2).
Proof.
  intros. apply_fresh* term_abs as x.
Qed.

Lemma term_prod_prove : forall t1 t2,
  term t1 -> body t2 -> term (trm_prod t1 t2).
Proof.
  intros. apply_fresh* term_prod as x.
Qed.

Hint Resolve term_abs_prove term_prod_prove.

Lemma body_prove : forall L t,
  (forall x, x \notin L -> term (t ^ x)) -> body t.
Proof.
  intros. exists* L.
Qed.

Hint Extern 1 (body ?t) =>
  match goal with 
  | H: forall _, _ \notin ?L -> term (t ^ _)  |- _ =>
    apply (@body_prove L)
  end. 

Lemma body_subst : forall x t u,
  term u -> body t -> body ([x ~> u]t).
Proof.
  introv. intros Wu [L Bt].
  exists (\{x} \u L). intros y Fr. cross*.
Qed.

Hint Resolve body_subst.


(* ********************************************************************** *)
(** ** Additional results on primitive operations *)

Section PrimProperties.

Hint Constructors term.

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
  case_var; simple*.
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_body : forall x t,
  term t -> body (close_var x t).
Proof.
  introv W. exists \{x}. intros y Fr.
  unfold open, close_var. generalize 0. gen y.
  induction W; intros y Fr k; simpls.
  case_var; simple*. case_nat*.
  auto*.
  auto*.
  apply_fresh* term_abs as z.
   unfolds open. rewrite* close_var_rec_open.
  apply_fresh* term_prod as z.
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

End PrimProperties.


(* ********************************************************************** *)
(** ** Regularity: relations are restricted to terms *)

Lemma red_regular_beta : red_regular beta.
Proof.
  intros_all. induction* H.

Qed.

Lemma red_regular_beta_star : red_regular (beta star).
Proof.
  intros_all. induction* H. apply* red_regular_beta.
Qed.

Lemma red_regular_conv : red_regular conv.
Proof.
  intros_all. induction* H. apply* red_regular_beta.
Qed.

Hint Extern 1 (term ?t) => match goal with
  | H: beta t _ |- _ => apply (proj1 (red_regular_beta H))
  | H: beta _ t |- _ => apply (proj2 (red_regular_beta H))
  | H: (beta star) t _ |- _ => apply (proj1 (red_regular_beta_star H))
  | H: (beta star) _ t |- _ => apply (proj2 (red_regular_beta_star H))
  | H: conv t _ |- _ => apply (proj1 (red_regular_conv H))
  | H: conv _ t |- _ => apply (proj2 (red_regular_conv H))
  end.

Hint Extern 1 (term (trm_abs ([?x ~> ?u]?t1) ([?x ~> ?u]?t2))) =>
  match goal with H: term (trm_abs t1 t2) |- _ => 
  unsimpl ([x ~> u](trm_abs t1 t2)) end.

Lemma red_regular_less : red_regular less.
Proof.
  intros_all. induction* H.
Qed.

Hint Extern 1 (term ?t) => match goal with
  | H: less t _ |- _ => apply (proj1 (red_regular_less H))
  | H: less _ t |- _ => apply (proj2 (red_regular_less H))
  end.

Lemma regular_typing : forall E t T, typing E t T ->
  (wf E /\ ok E /\ contains_terms E /\ term t /\ term T). 
Proof.
  apply typing_induct with
   (P0 := fun E (_ : wf E) => ok E /\ contains_terms E); 
   unfolds contains_terms; intros; splits*.
  destructs H. inversions~ H3.
  intros. false* binds_empty_inv.
  intros. destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst*.
Qed.

Hint Extern 1 (term ?t) => match goal with
  | H: typing _ t _ |- _ => apply (proj32 (proj33 (regular_typing H)))
  | H: typing _ _ t |- _ => apply (proj33 (proj33 (regular_typing H)))
  end.

Lemma ok_from_wf : forall E, wf E -> ok E.
Proof.
  induction 1. auto. auto* (regular_typing H0).
Qed.

Hint Extern 1 (ok ?E) => match goal with
  | H: wf E |- _ => apply (ok_from_wf H)
  end.

Hint Extern 1 (wf ?E) => match goal with
  | H: typing E _ _ |- _ => apply (proj1 (regular_typing H))
  end.

Lemma wf_push_inv : forall E x U,
  wf (E & x ~ U) -> wf E /\ term U.
Proof.
  introv W. inversions W. 
  false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. subst~.
Qed.
(*todo: as hints ?*)

Lemma term_from_binds_in_wf : forall x E U,
  wf E -> binds x U E -> term U.
Proof.
  introv W Has. gen E. induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct (wf_push_inv W). binds_push~ Has.
Qed.

Hint Extern 1 (term ?t) => match goal with
  H: binds ?x t ?E |- _ => apply (@term_from_binds_in_wf x E)
  end.

Lemma wf_left : forall E F : env,
  wf (E & F) -> wf E.
Proof.
  intros. induction F using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   inversions H. false (empty_push_inv H1).
   destruct (eq_push_inv H0) as [? [? ?]]. subst~. 
Qed.

Implicit Arguments wf_left [E F].


(* ********************************************************************** *)
(** ** Some freshness results *)

Lemma fv_open_var : forall y x t,
  x <> y -> x \notin fv (t ^ y) -> x \notin fv t.
Proof.
  introv Neq. unfold open. generalize 0. 
  induction t; simpl; intros; try notin_solve.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
Qed.

Lemma typing_fresh : forall E T i x,
  typing E T (trm_type i) -> x # E -> x \notin fv T.
Proof.
  introv Typ.
  induction Typ; simpls; intros.
  auto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1.
  pick_fresh y. notin_simpl. auto. apply* (@fv_open_var y).
  pick_fresh y. lets: (IHTyp H1). notin_simpl. auto. apply* (@fv_open_var y).
  lets: (IHTyp1 H). lets: (IHTyp2 H). auto.
  auto.
Qed.

Lemma notin_fv_from_wf : forall E F x V,
  wf (E & x ~ V & F) -> x \notin fv V.
Proof.
  intros.
  lets W: (wf_left H). inversions W.
  false (empty_push_inv H1). 
  destruct (eq_push_inv H0) as [? [? ?]]. subst~.
    (*todo: factorize the above pattern *) 
  apply* typing_fresh.
Qed.

Lemma notin_fv_from_binds : forall x y U E,
  wf E -> binds y U E -> x # E -> x \notin fv U.
Proof.
  induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct (wf_push_inv H). binds_push H0.
    inversions H. false* (empty_push_inv H5).
     destruct (eq_push_inv H4) as [? [? ?]]. subst~. 
     apply* typing_fresh.
    auto*.
Qed.

Lemma notin_fv_from_binds' : forall E F x V y U,
  wf (E & x ~ V & F) -> binds y U E -> x \notin fv U.
Proof.
  intros. lets W: (wf_left H). inversions keep W.
  false (empty_push_inv H2). 
  destruct (eq_push_inv H1) as [? [? ?]]. subst~. 
  lets W': (wf_left W). apply* notin_fv_from_binds.
Qed.

Hint Extern 1 (?x \notin fv ?V) => 
  match goal with H: wf (?E & x ~ V & ?F) |- _ =>
    apply (@notin_fv_from_wf E F) end.

Hint Extern 1 (?x \notin fv ?U) => 
  match goal with H: wf (?E & x ~ ?V & ?F), B: binds ?y U ?E |- _ =>
    apply (@notin_fv_from_binds' E F x V y) end.


