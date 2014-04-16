(***************************************************************************
* Correctness of the CPS-transformation - Correctness                      *
* Arthur Charguéraud, January 2009                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import CPS_Definitions CPS_Infrastructure Omega.
Implicit Types x y z : var.

Opaque cps.
Hint Constructors value.

(* ********************************************************************** *)
(** ** Properties of the big-step evaluation relation *)

(** If a term [t] evaluates to [v], then [v] is a value *)

Lemma eval_to_value : forall t v,
  eval t v -> value v.
Proof.
  introv H. induction~ H. 
Qed.

Hint Extern 1 (value ?v) => 
  match goal with H: eval _ v |- _ =>
    apply (eval_to_value H) end.

(** If a value [v] evaluates to something, then it must be to [v] *)

Lemma eval_value : forall v v', 
  eval v v' -> value v -> v' = v.
Proof.
  introv E V. inverts V; inverts~ E. 
Qed.

Hint Resolve eval_val.

(** Specialization of the reduction rule for the application of
    an abstraction to a value. *)

Lemma eval_red_values : forall t1 v2 r,
  body t1 -> value v2 ->
  eval (t1 ^^ v2) r ->
  eval (trm_app (trm_abs t1) v2) r.
Proof.
  intros. applys~ eval_red. 
Qed.

(** Specialization of the reduction rule for the application of
    an abstraction to two values. *)

Lemma eval_red_values_bis : forall t1 v2 v3 r,
  body t1 -> value v2 -> value v3 ->
  eval (trm_app (t1 ^^ v2) v3) r ->
  eval (trm_app (trm_app (trm_abs t1) v2) v3) r.
Proof.
  introv T1 V2 V3 E. inverts E. inverts H.
  apply~ eval_red.
  apply* eval_red_values.
  rewrite~ <- (eval_value H2). 
Qed.

Hint Resolve eval_red_values.


(* ********************************************************************** *)
(** Properties of the CPS transformation *)

(** Relationship between [cps] and [cpsval] on values *)

Lemma cps_of_value : forall v, 
  value v -> 
  cps v = trm_abs (trm_app (trm_bvar 0) (cpsval v)).
Proof.
  introv V. inverts V; rewrite~ cps_fix.
Qed.

(** [cpsval] of a value is a value *)

Lemma cpsval_value : forall v,
  value v ->
  value (cpsval v).
Proof.
  introv V. inverts V; simple~.
Qed.

Hint Resolve cpsval_value.

(** [cps] does not introduce any free variables *)

Lemma cps_fv : forall t x,
  term t ->
  x \notin fv t -> 
  x \notin fv (cps t).
Proof. 
  introv T. induction T using term_size; introv Fr;
  rewrite cps_fix; unfold Cps; simpls; notin_simpl; auto.
  name_var_gen y. tests: (x = y).
    subst. apply close_var_notin.
    apply~ close_var_notin_keep.
Qed.

(** (TODO) useful hack to work around a bug of "rewrite cps_fix at 2"  *)

Ltac protect_left := 
  let x := fresh "left" in
  match goal with |- ?X = _ => sets x: X end.

Ltac simpl_cps :=
  rewrite cps_fix; unfold Cps.

(** [cps] commutes with renaming on fresh names *)

Lemma cps_rename : forall x y t, 
  term t -> y \notin fv t ->
  cps ([[x~>y]]t) = [[x~>y]](cps t).
Proof.
  introv T. gen x y. induction T using term_size; introv Fr; simpls.
  (* var *)
  protect_left. simpl_cps. subst left. simpl_cps. simpl. case_var~.
  (* cst *)
  simpl_cps. auto.
  (* app *)
  protect_left. simpl_cps. subst left. simpl_cps.
  simpl. fequals. rewrite~ IHT1. rewrite~ IHT2. 
  (* abs *)
  simpl_cps. name_var_gen z.
   protect_left. simpl_cps. subst left. name_var_gen z'.
   simpl. fequals_rec. 
   sets ta: ([[x~>y]]t1).
   pick_fresh a from (fv ta).
   rewrite~ (@subst_intro a).
   lets IH1: H0 ta a a z ___. 
     auto.
     subst ta. rewrite~ trm_size_rename.
     subst ta. rewrite~ subst_open_var.
     auto.
   rewrite IH1; clear IH1.
   rewrite~ close_var_rename; [|
     apply~ cps_fv; subst ta; rewrite~ subst_open_var].
   rewrite~ (@subst_intro a t1).
   subst ta. rewrite~ subst_open_var.
   do 2 rewrite~ H0.
   rewrite~ close_var_subst; [|simple~].
   fequals. rewrite~ close_var_rename. apply~ cps_fv.
Qed.

(** [cps] does not depend on the named used to open a body *)

Lemma cps_rename_body : forall y x t,
  y \notin fv t -> x \notin fv t -> body t ->
  close_var x (cps (t^x)) = close_var y (cps (t^y)).
Proof.
  intros. tests: (x = y). subst~.
  rewrite~ (@subst_intro y).
  rewrite~ cps_rename. 
  rewrite~ close_var_rename.
  apply~ cps_fv.
Qed. 

(** [cps] commutes with substitution *)

Lemma cps_subst : forall z v t, 
  term t -> value v ->
  cps (subst z v t) = subst z (cpsval v) (cps t). 
Proof.
  introv T V. induction T; (protect_left; simpl_cps; subst left); simpl.
  case_var.
    apply~ cps_of_value.
    simpl_cps. auto.
  simpl_cps. auto.
  simpl_cps. rewrite IHT1. rewrite~ IHT2.
  simpl_cps. fequals_rec. 
  name_var_gen y. name_var_gen y'.
   pick_fresh a from (fv ([z ~> v]t1) \u fv (cpsval v)).
   rewrite~ (@cps_rename_body a); [|apply* body_subst].
   rewrite~ subst_open_var. rewrite~ (H0 a).
   rewrite* (@cps_rename_body a).
   rewrite~ close_var_subst.
Qed.

(** [cps] commutes with open *)

Lemma cps_open : forall t1 v, 
  value v -> body t1 ->
  cps (t1 ^^ v) = (cps_abs_body t1) ^^ cpsval v.
Proof.
  introv V B. unfold cps_abs_body. name_var_gen y.
  rewrite~ (@subst_intro y).
  rewrite~ cps_subst. 
  rewrite~ (@subst_intro y (close_var y (cps (t1^y)))).
  rewrite~ <- close_var_open.
Qed.


(* ********************************************************************** *)
(** Prove of the semantic preservation of CPS *)

Lemma cps_correct_ind : forall v t k r,
  eval t v -> 
  eval (trm_app k (cpsval v)) r -> 
  value k -> 
  eval (trm_app (cps t) k) r.
Proof.
  introv E. gen k r. induction E; introv EV VK.
  (* case: val *)
  rewrite~ cps_of_value.
  applys~ eval_red_values. calc_open~.
  (* case: red *)
  simpl_cps.
  apply~ eval_red_values. calc_open~.
  applys~ IHE1. clear IHE1.
  apply eval_red_values; auto. calc_open~.
  sets_eq t3': (trm_abs (cps_abs_body t3)).
  applys~ IHE2. clear IHE2.
  apply~ eval_red_values. calc_open~.
  subst t3'. applys~ eval_red_values_bis.
  forwards H: IHE3; clear IHE3. eauto. auto.
  inverts H as F1 F2 F3. inverts F1.
  rewrite~ (eval_value F2) in F3. 
  rewrite~ <- cps_open.
  apply* eval_red.
Qed.

Lemma cps_correctness : cps_correctness_statement.
Proof.
  introv E V. unfold trm_id. apply* cps_correct_ind.
  constructors~. calc_open~.
Qed.

