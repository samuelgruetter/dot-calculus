(***************************************************************************
* Correctness of the CPS-transformation - Infrastructure                   *
* Arthur Charguéraud, January 2009                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import CPS_Definitions LibNat.
Implicit Types x y z : var.

Tactic Notation "math" := nat_math.


(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv x) in
  constr:(A \u B \u C).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in pick_fresh_gen L x.
Tactic Notation "pick_fresh" ident(x) "from" constr(E) :=
  let L := gather_vars in pick_fresh_gen (L \u E) x.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

Tactic Notation "exists_fresh" :=
  let y := fresh "y" in let Fry := fresh "Fr" y in
  exists_fresh_gen gather_vars y Fry.

Hint Constructors term.



(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Properties of the syntax *)

(* ********************************************************************** *)
(** ** Extra definitions *)

Notation "'[[' x '~>' y ']]' t" := (subst x (trm_fvar y) t) (at level 69).


(* ********************************************************************** *)
(** ** Properties of local closure *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> body t1.
Proof. intros. unfold body. inversion* H. Qed.

Lemma body_to_term_abs : forall t1, 
  body t1 -> term (trm_abs t1).
Proof. intros. inversion* H. Qed.

Hint Resolve term_abs_to_body body_to_term_abs.


(* ********************************************************************** *)
(** ** Properties of open and subst *)

(** Substitution for a fresh name is the identity *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> [x ~> u]t = t.
Proof.
  intros. induction t; simpls; fequals~. case_var~.
Qed.

(** Opening of a locally-closed term is the identity *)

Lemma open_rec_term_ind :forall t j v i u, i <> j ->
  {i ~> u}({j ~> v}t) = {j ~> v}t -> {i ~> u}t = t.
Proof.
  induction t; introv Neq Equ; simpls; inversions~ Equ; fequals*.
  case_nat~. case_nat~.
Qed.

Lemma open_rec_term : forall t u k,
  term t -> {k ~> u}t = t.
Proof.
  introv H. gen k. induction H; intros; simpl; fequals~. 
  unfolds open. pick_fresh x. 
   apply~ (@open_rec_term_ind t1 0 (trm_fvar x)).
Qed.

(** Open_var with fresh names  *)

(* todo: fv (t^x) << fv t \u {x} *)

Lemma open_fresh : forall x y t,
  x \notin fv t -> x <> y -> x \notin fv (t^y).
Proof.
  introv. unfold open. generalize 0. 
  induction t; simpl; intros i Fr Neq; auto.
  case_nat; simple~.
Qed.

Hint Resolve open_fresh.

(** Open_var with fresh names is injective *)

Lemma open_var_inj : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ fequals*
            | do 2 try case_nat; inversions~ H1; try notin_false ].
Qed.

(** Substitution distributes on open *)

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; fequals~.
  case_nat~. case_var~. rewrite~ open_rec_term.
Qed.

(** Substitution commutes with open_var for distinct names *)

Lemma subst_open_var : forall x y u t, y <> x -> term u ->
  ([x ~> u]t) ^ y = [x ~> u](t ^ y).
Proof.
  introv Neq Wu. rewrite~ subst_open. simpl. case_var~.
Qed.

(** Open can be decomposed as open_var followed with substitution *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite~ subst_open.
  rewrite~ subst_fresh. simpl. case_var~.
Qed.

(** Substitution perserves local closure *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simple~.
  case_var~.
  apply_fresh term_abs. rewrite~ subst_open_var.
Qed.

Hint Resolve subst_term.

(** Open preserves local closure *)

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite~ (@subst_intro y).
Qed.

Hint Resolve open_term.

(** Substitution preserves bodies -- todo: remove ? *)

Lemma body_subst : forall t u x,
  body t -> term u -> body ([x~>u]t).
Proof.
  introv T U. invert T. intros L B.
  exists_fresh. rewrite~ subst_open_var.
Qed.


(* ********************************************************************** *)
(** ** Properties of close_var *)

(* Closing on a fresh name is the identity *)

Lemma close_var_fresh : forall x t i,
  x \notin fv t -> close_var_rec i x t = t.
Proof.
  induction t; simpl; intros i Fr; fequals~. case_var~. 
Qed.

(** Close_var on x returns a term with no occurence of x *)

(* todo: prove and use in the next two lemmas 
Lemma close_var_fresh_ind : forall t,
  fv (close_var x t) = (fv t) \rem x.
*)

Lemma close_var_notin : forall x t,
  x \notin fv (close_var x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple~.
Qed.

Hint Resolve close_var_notin.

Lemma close_var_notin_keep : forall x y t,
  x \notin fv t ->
  x \notin fv (close_var y t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; simpl; intros i Fr; auto. case_var; simple~.
Qed.

(** Close_var is the reciprocal of open_var *)

Lemma close_var_open_ind : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (fv t1) ->
    {i ~> trm_fvar y} ({j ~> trm_fvar z} (close_var_rec j x t1) )
  = {j ~> trm_fvar z} (close_var_rec j x ({i ~> trm_fvar y}t1) ).
Proof.
  induction t1; simpl; intros; try solve [ fequals~ ].
  do 2 (case_nat; simpl); try solve [ case_var~ | case_nat~ ]. 
  case_var~. simpl. case_nat~. 
Qed.

Lemma close_var_open : forall x t,
  term t -> t = (close_var x t) ^ x.
Proof.
  introv W. unfold close_var, open. generalize 0.
  induction W; intros j; simpls; fequals~.
  case_var~. simpl. case_nat~.
  match goal with |- _ = ?t => pick_fresh y from (fv t) end.
  apply~ (@open_var_inj y).
  unfolds open. rewrite~ close_var_open_ind.
Qed.

(** Close_var returns a body *)

Lemma close_var_body : forall x t,
  term t -> body (close_var x t).
Proof.
  introv W. exists \{x}. intros y Fr.
  unfold open, close_var. generalize 0. gen y.
  induction W; intros y Fr j; simpls.
  case_var; simple~. case_nat~.
  auto.
  auto.
  apply_fresh term_abs as z.
   unfolds open. rewrite~ close_var_open_ind.
Qed.
 
Hint Resolve close_var_body.

(** Abstract specification of close_var *)

Lemma close_var_spec : forall t x, 
  term t -> exists u, t = u ^ x /\ body u /\ x \notin (fv u).
Proof.
  intros. exists (close_var x t). splits 3.
  apply* close_var_open.
  apply* close_var_body.
  apply* close_var_notin.
Qed. 

(* Close_var commutes with substitution for fresh names *)

Lemma close_var_subst : forall x t z u, 
  x \notin fv u -> x <> z -> 
  close_var x ([z~>u]t) = [z~>u](close_var x t).
Proof.
  introv Fr Neq. unfold close_var. generalize 0.
  induction t; intros i; simpl; fequals~. 
  case_var; case_var; simpl.
    case_var. rewrite~ close_var_fresh.
    case_var~.
    do 2 case_var~.
Qed.
(* Close_var and renaming *)

Lemma close_var_rename : forall y x t,
  y \notin fv t ->
  close_var y ([[x ~> y]]t) = close_var x t.
Proof.
  introv Fr. unfold close_var. generalize 0. gen Fr.
  induction t; simpl; intros Fr i; fequals~.
  case_var; simpl; case_var~.
Qed.


(* ********************************************************************** *)
(** Size of a term *)

Fixpoint trm_size (t : trm) {struct t} : nat :=
  match t with
  | trm_bvar i    => 1
  | trm_fvar x    => 1
  | trm_cst k     => 1
  | trm_abs t1    => 1 + (trm_size t1)
  | trm_app t1 t2 => 1 + (trm_size t1) + (trm_size t2)
  end.

Lemma trm_size_rename : forall x y t,
  trm_size ([x ~> trm_fvar y]t) = trm_size t.
Proof.
  induction t; simpl; fequals. case_var~.
Qed.

Lemma trm_size_open : forall x t,
  trm_size (t^x) = trm_size t.
Proof.
  intros. unfold open. generalize 0.
  induction t; intros; simpl; fequals.
  case_nat~.
Qed.

Lemma term_size : 
  forall P : trm -> Prop,
  (forall x, P (trm_fvar x)) ->
  (forall k, P (trm_cst k)) ->
  (forall t1 t2,
     term t1 -> P t1 -> term t2 -> P t2 -> P (trm_app t1 t2)) ->
  (forall t1,
     body t1 ->
     (forall t2 x, x \notin fv t2 -> trm_size t2 = trm_size t1 ->
       term (t2 ^ x) -> P (t2 ^ x)) -> 
     P (trm_abs t1)) ->
  (forall t, term t -> P t).
Proof.
  intros P Ha Hb Hc Hd t. gen_eq n: (trm_size t). gen t.
  induction n using peano_induction. introv Eq T. subst. inverts T.
  apply Ha.
  apply Hb.
  apply~ Hc. apply~ H. simpl; nat_math. apply~ H. simpl; nat_math.
  apply~ Hd. exists_fresh; auto. introv Fr Eq T.
   apply~ H. rewrite trm_size_open. simpl. math.
Qed.

(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Tactics *)


(* ********************************************************************** *)
(** Computation of beta-reductions *)

Tactic Notation "calc_open" := 
  unfold open; simpl; repeat (case_nat); rewrite_all open_rec_term.
Tactic Notation "calc_open" "~" := 
  calc_open; auto_tilde.
Tactic Notation "calc_open" "*" := 
  calc_open; auto_star.


(* ********************************************************************** *)
(** Proving local closure *)

Hint Extern 1 (body _) => 
  exists_fresh; calc_open.
Hint Extern 1 (term (trm_abs _)) =>
  apply_fresh term_abs; calc_open; auto.
Hint Extern 1 (term ?x) =>
  match goal with H: x = _ |- _ => subst x end.


(* ********************************************************************** *)
(** Shortand for naming [var_gen] variables *)

Tactic Notation "name_var_gen" ident(x) :=
  match goal with
  | |- context [var_gen ?L] => sets x: (var_gen L)
  | H: context [var_gen ?L] |- _ => sets x: (var_gen L)
  end.


(* ********************************************************************** *)
(** Proving freshness of [var_gen] variables *)

Hint Extern 5 (?x \notin _) =>
  progress (unfold x); apply notin_var_gen; intros.

Hint Resolve open_fresh. 


(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Properties of definitions *)




(* ********************************************************************** *)
(** Fixpoint equation for the CPS transformation *)

Require Import LibWf. 

Lemma cps_fix : forall t, 
  cps t = Cps cps t.
Proof.
  applys~ (FixFun_fix (measure trm_size)). applys measure_wf.
  intros f1 f2 t IH. unfolds measure.
  unfolds. destruct t; simpl in IH; fequals.
  do 2 (rewrite IH; try math). auto.
  rewrite~ IH. rewrite trm_size_open. math.
Qed.

Hint Resolve cps_fix.


(* ********************************************************************** *)
(** Regularity lemmas *)

Lemma cps_term : forall t,
  term t -> term (cps t).
Proof.
  introv T. induction T using term_size; rewrite cps_fix; unfold Cps.
  auto.
  auto.
  auto.
  name_var_gen x.
   protects (trm_abs (close_var x (cps (t1^x)))) do auto 8.
Qed.

(* details for the third auto in the proof above:
     apply_fresh term_abs. unfold open. simpl. case_if. case_if. case_if. rewrite_all~ open_rec_term.
     constructors~. apply_fresh term_abs. unfold open. simpl. case_if. case_if. 
     rewrite_all~ open_rec_term. constructors~. 
     apply_fresh term_abs. unfold open. simpl. case_if.
     constructors~. *)

Lemma cps_term_abs : forall t1,
  term (trm_abs t1) ->
  term (trm_abs (cps_abs_body t1)).
Proof.
  intros. unfold cps_abs_body. name_var_gen x.
  lets: cps_term. auto 8.
Qed.

Hint Resolve cps_term cps_term_abs.

Lemma cpsval_term : forall v,
  value v -> term (cpsval v).
Proof.
  introv V. inverts V; simple~.
Qed.

Hint Resolve cpsval_term.

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; auto.
Qed.

Lemma eval_regular : forall t v,
  eval t v -> term t /\ term v.
Proof.
  induction 1; auto* value_regular.
Qed.


(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Automation *)

(* todo: move les hint resolve vers les hints extern si besoin *)

Hint Extern 1 (term ?t) => 
  match goal with
  | H: value t |- _ => apply (value_regular H)
  | H: eval t _ |- _ => apply (proj1 (eval_regular H))
  | H: eval _ t |- _ => apply (proj2 (eval_regular H))
  end.



