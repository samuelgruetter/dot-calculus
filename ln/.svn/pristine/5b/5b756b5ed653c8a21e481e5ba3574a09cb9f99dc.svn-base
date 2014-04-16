(***************************************************************************
* The pure lambda-calculus in locally nameless style - Formalization       *
* Arthur Charguéraud, January 2009                                         *
***************************************************************************)

(** This file is the appendix to the paper:
       The Locally Nameless Representation
       Arthur Charguéraud
       Journal of Automated Reasoning (JAR), May 2011 *)
    

Set Implicit Arguments.
Require Import LibLN LibNat.



(* ====================================================================== *)
(** ** Definitions *)

Implicit Types x y z : var.


(* ********************************************************************** *)
(** Grammar of terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_app  : trm -> trm -> trm
  | trm_abs  : trm -> trm.


(* ********************************************************************** *)
(** Opening *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else t
  | trm_fvar x    => t
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1    => trm_abs (open_rec (S k) u t1) 
  end.

Definition open t u := open_rec 0 u t.


(* ********************************************************************** *)
(** Variable opening, defined in terms of opening *)

Definition open_var t x := open t (trm_fvar x).

Definition open_var_rec k x t := open_rec k (trm_fvar x) t.

(* ********************************************************************** *)
(** Variable closing *)

Fixpoint close_var_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => If x = z then (trm_bvar k) else t
  | trm_app t1 t2 => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_abs t1    => trm_abs (close_var_rec (S k) z t1) 
  end.

Definition close_var x t := close_var_rec 0 x t.


(* ********************************************************************** *)
(** Local closure, inductively defined *)

Inductive lc : trm -> Prop :=
  | lc_var : forall x, 
      lc (trm_fvar x)
  | lc_app : forall t1 t2,
      lc t1 -> lc t2 -> lc (trm_app t1 t2)
  | lc_abs : forall L t1,
      (forall x, x \notin L -> lc (open_var t1 x)) -> 
      lc (trm_abs t1). 

Definition body t :=
  exists L, forall x, x \notin L -> lc (open_var t x).


(* ********************************************************************** *)
(** Computation of the set of free variables *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  | trm_abs t1    => (fv t1)
  end.


(* ********************************************************************** *)
(** Closed terms *)

Definition closed t := 
  fv t = \{}.


(* ********************************************************************** *)
(** Substitution *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => t
  | trm_fvar x    => If x = z then u else t
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_abs t1    => trm_abs (subst z u t1) 
  end.


(* ********************************************************************** *)
(** Size of a term *)

Fixpoint size (t : trm) {struct t} : nat :=
  match t with
  | trm_bvar i    => 1
  | trm_fvar x    => 1
  | trm_abs t1    => 1 + (size t1)
  | trm_app t1 t2 => 1 + (size t1) + (size t2)
  end.


(* ====================================================================== *)
(** ** Tactics *)

Hint Constructors lc.

(** Tactics for freshness *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{ x }) in
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

(** Tactics for comparison of indices *)

Hint Extern 1 (_ < _) => nat_math.
Hint Extern 1 (_ <= _) => nat_math.

(** Tactics for equalities between sets *)

Lemma subset_union_2p : forall E1 E2 F1 F2 G : vars,
  E1 \c (F1 \u G) -> E2 \c (F2 \u G) -> (E1 \u E2) \c ((F1 \u F2) \u G).
Proof.
  introv H1 H2. intros x. specializes H1 x. specializes H2 x.
  repeat rewrite in_union in *. auto*.
Qed.

Lemma subset_remove_11 : forall x y : var, 
  x <> y -> \{x} \c (\{x} \- \{y}).
Proof.
  introv H. intros z M. rewrite in_singleton in M. subst.
  rewrite in_remove. split. rewrite~ in_singleton. auto.
Qed.

Lemma subset_remove_2p : forall E1 E2 F1 F2 G : vars,
  E1 \c (F1 \- G) -> E2 \c (F2 \- G) -> (E1 \u E2) \c ((F1 \u F2) \- G).
Proof. introv H1 H2. forwards: subset_union_2 H1 H2. rewrite~ union_remove. Qed.

Hint Resolve subset_union_weak_l subset_union_weak_r subset_refl
  subset_union_2 subset_union_2p subset_empty_l 
  subset_remove_2p subset_remove_11 : fset.

Ltac fset := first [ auto with fset ].


(* ====================================================================== *)
(** ** Proofs *)

(* ********************************************************************** *)
(** Variable closing and variable opening are reciprocal of one another *)

(** Showing that [close_var] after [open_var] is the identity is easy *)

Lemma close_open_var : forall x t, 
  x \notin fv t -> 
  close_var x (open_var t x) = t.
Proof.
  introv. unfold open_var, open, close_var. generalize 0.
  induction t; simpl; introv Fr; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

(** The other direction is much harder; First, we first need
    to establish the injectivity of [open_var] *)

Lemma open_var_inj : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (open_var t1 x = open_var t2 x) -> (t1 = t2).
Proof.
  introv Fr1 Fr2 Eq.
  rewrite~ <- (@close_open_var x t1).
  rewrite~ <- (@close_open_var x t2).
  fequals~.
Qed.

(** Another proof of the same injectivity result *)

Lemma open_var_inj_alternative : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (open_var t1 x = open_var t2 x) -> (t1 = t2).
Proof.
  intros x t1. unfold open_var, open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ fequals*
            | do 2 try case_nat; inversions~ H1; try notin_false ].
Qed.

(** We also need one (tricky) auxiliary lemma to handle the binder case *)

Lemma open_close_var_on_open_var : forall x y z t i j,
  i <> j -> y <> x -> y \notin (fv t) ->
    open_var_rec i y (open_var_rec j z (close_var_rec j x t))
  = open_var_rec j z (close_var_rec j x (open_var_rec i y t)).
Proof.
  unfold open_var_rec.
  induction t; simpl; intros; try solve [ fequals~ ].
  do 2 (case_nat; simpl); try solve [ case_var~ | case_nat~ ]. 
  case_var~. simpl. case_nat~. 
Qed.

(** Now we can prove that [open_var] after [close_var] is the identity *)

Lemma open_close_var : forall x t, 
  lc t -> 
  open_var (close_var x t) x = t.
Proof.
  introv T. unfold open_var, open, close_var. generalize 0.
  induction T; simpl; introv; fequals~.
  case_var~. simpl. case_nat~.
  match goal with |- ?t = _ => pick_fresh y from (fv t) end.
   apply~ (@open_var_inj y).
   lets M: open_close_var_on_open_var. unfold open_var_rec in M.
   unfold open_var, open. rewrite~ M. apply~ H0.
Qed.

(** As a bonus, we get the injectivity of [close_var] *)

Lemma close_var_inj : forall x t1 t2, 
  lc t1 -> lc t2 ->
  (close_var x t1 = close_var x t2) -> (t1 = t2).
Proof.
  introv T1 T2 Eq.
  rewrite~ <- (@open_close_var x t1).
  rewrite~ <- (@open_close_var x t2).
  fequals~.
Qed.


(* ********************************************************************** *)
(** Properties of [body] *)

(** An abstraction is locally closed iff it satifies the predicate [body] *) 

Lemma lc_abs_iff_body : forall t1, 
  lc (trm_abs t1) <-> body t1.
Proof. intros. unfold body. iff H; inversions* H. Qed.


(* ********************************************************************** *)
(** Interaction of [fv] with [open_var] and [close_var] *)

(** Opening with [u] adds [fv u] to the set of free variables *)

Lemma fv_open : forall t u,
  fv (open t u) \c fv t \u fv u.
Proof.
  introv. unfold open. generalize 0.
  induction t; intros k; simpl; try fset.
  case_nat; simpl; fset. 
Qed.

(** In particular, opening with variable [x] adds [x] to the set 
    of free variables *)

Lemma open_var_fv : forall x t,
  fv (open_var t x) \c (fv t \u \{x}).
Proof. intros. apply fv_open. Qed.

(** Closing w.r.t variable [x] removes [x] from the set of free variables *)

Lemma close_var_fv : forall x t,
  fv (close_var x t) \c (fv t \- \{x}).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpl; try fset.
  case_var; simpl; fset. 
Qed.


(* ********************************************************************** *)
(** Properties of substitution *)

(** Distributivity of [subst] on [open].
    Two (tricky) intermediate lemmas are required *)

Lemma open_rec_lc_ind : forall t j v i u, i <> j ->
  open_rec i u (open_rec j v t) = open_rec j v t ->
  open_rec i u t = t.
Proof.
  induction t; introv Nq Eq;
   simpls; inversions~ Eq; fequals*.
  case_nat~. case_nat~.
Qed.

Lemma open_rec_lc : forall u t k,
  lc t -> open_rec k u t = t.
Proof.
  unfold open_var_rec. introv T. gen k.
  induction T; intros; simpl; fequals~. 
  pick_fresh y. apply~ (@open_rec_lc_ind t1 0 (trm_fvar y)).
  apply~ H0.
Qed.

Lemma subst_open : forall x u t v, lc u -> 
  subst x u (open t v) = open (subst x u t) (subst x u v).
Proof.
  intros. unfold open. generalize 0.
  induction t; intros; simpl; fequals~.
  case_nat~.
  case_var~. rewrite~ open_rec_lc.
Qed.

(** In particular, we can distribute [subst] on [open_var] *)

Lemma subst_open_var : forall x y u t, 
  y <> x -> lc u -> 
  subst x u (open_var t y) = open_var (subst x u t) y.
Proof.
  introv N U. unfold open_var. rewrite~ subst_open.
  fequals. simpl. case_if~.
Qed.

(** For the distributivity of [subst] on [close_var],
    one simple intermediate lemmas is required to 
    say that closing on a fresh name is the identity *)

Lemma close_var_rec_fresh : forall k x t,
  x \notin fv t -> close_var_rec k x t = t.
Proof.
  introv. gen k. induction t; simpl; intros; fequals*. 
  case_var~. 
Qed.

(** Distributivity of [subst] on [close_var] *)

Lemma subst_close_var : forall x y u t, 
  y <> x -> y \notin fv u -> 
  subst x u (close_var y t) = close_var y (subst x u t).
Proof.
  introv N F. unfold close_var. generalize 0.
  induction t; intros k; simpl; fequals~.
  case_var~; simpl.
    case_var~; simpl. case_var~.
    case_var~; simpl.
      rewrite~ close_var_rec_fresh.
      case_var~.
Qed.

(** Substitution for a fresh name is the identity *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> subst x u t = t.
Proof. intros. induction t; simpls; fequals~. case_var~. Qed.

(** Substitution can be introduced to decompose an opening *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> lc u ->
  open t u = subst x u (open_var t x).
Proof.
  introv F U. unfold open_var. rewrite~ subst_open.
  fequals. rewrite~ subst_fresh. simpl. case_var~.
Qed.

(** An alternative, longer proof, but with fewer hypotheses *)

Lemma subst_intro_alternative : forall x t u, 
  x \notin (fv t) -> 
  open t u = subst x u (open_var t x).
Proof.
  introv H. unfold open_var, open. generalize 0. gen H.
  induction t; simpl; intros; fequals*.
  case_nat*.
  simpl. case_var*.
  case_var*.
Qed.

(** Substitution can be introduced to decompose a variable
    closing in terms of another one using a different name *)

Lemma close_var_rename : forall x y t,
  x \notin fv t ->
  close_var y t = close_var x (subst y (trm_fvar x) t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; simpl; intros k F; fequals~.
  case_var; simpl; case_var~.
Qed.


(* ********************************************************************** *)
(** Preservation of local closure through substitution and opening *)

(** Substitution of a locally closed terms into another one produces
    a locally closed term *)

Lemma subst_lc : forall z u t,
  lc u -> lc t -> lc (subst z u t).
Proof.
  introv U T. induction T; simple~.
  case_var~.
  apply_fresh lc_abs. rewrite~ <- subst_open_var.
Qed.

(** Substitution of a locally closed terms into a body one produces
    another body *)

Lemma subst_body : forall z t u,
  lc u -> body t -> body (subst z u t).
Proof.
  introv U [L H]. exists_fresh. 
  rewrite~ <- subst_open_var. apply~ subst_lc.
Qed.

(** Opening of a body with a locally closed terms produces a 
    locally closed term *)

Lemma open_lc : forall t u,
  body t -> lc u -> lc (open t u).
Proof.
  introv [L H] U. pick_fresh y. rewrite~ (@subst_intro y).
  apply~ subst_lc. 
Qed.


(* ********************************************************************** *)
(** Two additional lemmas (not used in practical developments) *)

(** A body becomes a locally closed term when [open_var] is applied *)

Lemma open_var_lc : forall t1 x, 
  body t1 -> lc (open_var t1 x).
Proof.
  introv [L M]. pick_fresh y. unfold open_var. 
  rewrite~ (@subst_intro y). applys~ subst_lc.
Qed. 

(** A locally closed term becomes a body when [closed_var] is applied *)

Lemma close_var_lc : forall t x, 
  lc t -> body (close_var x t).
Proof.
  introv T. exists_fresh.
  rewrite~ (@close_var_rename y).
  rewrite~ open_close_var; apply~ subst_lc.
Qed.



(* ====================================================================== *)
(** ** An induction principle for locally closed terms *)

(** Interaction of [size] with [open_var] *)

Lemma size_open_var : forall x t,
  size (open_var t x) = size t.
Proof.
  intros. unfold open_var, open. generalize 0.
  induction t; intros; simple~. case_nat~.
Qed.

(** Interaction of [size] with [close_var] *)

Lemma size_close_var : forall x t,
  size (close_var x t) = size t.
Proof.
  intros. unfold close_var. generalize 0.
  induction t; intros; simple~. case_var~.
Qed.

(** The induction principle *)

Lemma lc_induct_size : forall P : trm -> Prop,
  (forall x, P (trm_fvar x)) ->
  (forall t1 t2,
     lc t1 -> P t1 -> lc t2 -> P t2 -> P (trm_app t1 t2)) ->
  (forall t1,
     body t1 ->
     (forall t2 x, x \notin fv t2 -> size t2 = size t1 ->
       lc (open_var t2 x) -> P (open_var t2 x)) -> 
     P (trm_abs t1)) ->
  (forall t, lc t -> P t).
Proof.
  intros P Hvar Happ Habs t. 
  induction t using (@measure_induction _ size).
  introv T. inverts T; simpl in H; auto.
  apply~ Habs. exists_fresh; auto. introv Fr Eq T.
   apply~ H. rewrite~ size_open_var.
Qed.



(* ====================================================================== *)
(** ** Alternative definition for local closure *)


(* ********************************************************************** *)
(** Local closure, recursively defined *)

Fixpoint lc_at (k:nat) (t:trm) {struct t} : Prop :=
  match t with 
  | trm_bvar i    => i < k
  | trm_fvar x    => True
  | trm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | trm_abs t1    => lc_at (S k) t1
  end.

Definition lc' t := lc_at 0 t.

Definition body' t := lc_at 1 t.


(* ********************************************************************** *)
(** Equivalence of [lc] and [lc'] *)

Lemma lc_rec_open_var_rec : forall x t k,
  lc_at k (open_var_rec k x t) -> lc_at (S k) t.
Proof.
  unfold open_var_rec.
  induction t; simpl; introv H; auto*.
  case_nat; simpls~.
Qed.

Lemma lc_to_lc' : forall t,
  lc t -> lc' t.
Proof.
  introv T. induction T; unfold lc'; simple~.
  pick_fresh x. apply~ (@lc_rec_open_var_rec x). apply~ H0.
Qed.

Lemma lc_at_open_var_rec : forall x t k,
  lc_at (S k) t -> lc_at k (open_var_rec k x t).
Proof.
  unfold open_var_rec.
  induction t; simpl; introv H; auto*. case_nat; simple~.
Qed.

Lemma lc'_to_lc : forall t,
  lc' t -> lc t.
Proof.
  introv. unfold lc'.
  induction t using (@measure_induction _ size).
  destruct t; simpl; introv T'; simpl in H; auto*.
  apply_fresh lc_abs. apply H. rewrite~ size_open_var.
   apply~ lc_at_open_var_rec.
Qed.

Lemma lc_eq_lc' : lc = lc'.
Proof. extens. split. applys lc_to_lc'. applys lc'_to_lc. Qed.


(* ********************************************************************** *)
(** Equivalence of [body] and [body'] *)

Lemma body_to_body' : forall t,
  body t -> body' t.
Proof.
  introv [L H]. pick_fresh x. 
  applys (@lc_rec_open_var_rec x).
  apply lc_to_lc'. apply~ H.
Qed.

Lemma body'_to_body : forall t,
  body' t -> body t.
Proof.
  introv B. exists (\{}:vars). introv F.
  apply lc'_to_lc. apply~ lc_at_open_var_rec.
Qed.

Lemma body_eq_body' : body = body'.
Proof. extens. split. applys body_to_body'. applys body'_to_body. Qed.


(* ********************************************************************** *)
(** Weakening property of [lc_at] *)

Lemma lc_at_weaken_ind : forall k1 k2 t,
  lc_at k1 t -> k1 <= k2 -> lc_at k2 t.
Proof. introv. gen k1 k2. induction t; simpl; introv T Lt; auto*. Qed.

Lemma lc_at_weaken : forall k t,
  lc' t -> lc_at k t.
Proof. introv H. apply~ (@lc_at_weaken_ind 0). Qed.


(* ********************************************************************** *)
(** Proofs revisited with [lc_at] *)

(** The inductions are now simpler because they are structural *)

Lemma lc'_abs_to_body' : forall t1, 
  lc' (trm_abs t1) -> body' t1.
Proof. auto. Qed.

Lemma body'_to_lc'_abs : forall t1, 
  body' t1 -> lc' (trm_abs t1).
Proof. auto. Qed.

Lemma open_var_lc' : forall x t,
  body' t -> lc' (open_var t x).
Proof.
  introv B. applys~ lc_at_open_var_rec.
Qed.

Lemma close_var_body' : forall x t,
  lc' t -> body' (close_var x t).
Proof.
  introv. unfold lc', body', close_var.
  generalize 0. induction t; simpl; intros k T; auto*.
  case_var~. simpl. nat_math.
Qed.

Lemma subst_lc' : forall z u t,
  lc' u -> lc' t -> lc' (subst z u t).
Proof.
  introv U. unfold lc'. generalize 0.
  induction t; simpl; introv T; auto*.
  case_var~. apply~ lc_at_weaken.
Qed.

Lemma subst_body' : forall z u t,
  lc' u -> body' t -> body' (subst z u t).
Proof.
  introv U. unfold body'. generalize 1.
  induction t; simpl; introv T; auto*.
  case_var~. apply~ lc_at_weaken.
Qed.

Lemma open_rec_lc'_ind : forall u t k,
  lc_at k t -> open_rec k u t = t.
Proof.
  introv. gen k. induction t; simpl; introv F; fequals*.
  case_nat~. false. nat_math.
Qed.

Lemma open_rec_lc' : forall u t k,
  lc' t -> open_rec k u t = t.
Proof.
  unfold lc'. introv T.
  apply open_rec_lc'_ind. apply* lc_at_weaken.
Qed.

Lemma subst_open' : forall x u t v, lc' u -> 
  subst x u (open t v) = open (subst x u t) (subst x u v).
Proof.
  intros. unfold open. generalize 0.
  induction t; intros; simpl; fequals~.
  case_nat~.
  case_var~. rewrite~ open_rec_lc'.
Qed.

Lemma subst_intro' : forall x t u, 
  x \notin (fv t) -> lc' u ->
  open t u = subst x u (open_var t x).
Proof.
  introv F U. unfold open_var. rewrite~ subst_open'.
  fequals. rewrite~ subst_fresh. simpl. case_var~.
Qed.

Lemma open_lc' : forall t u,
  body' t -> lc' u -> lc' (open t u).
Proof.
  introv B U. pick_fresh y. rewrite~ (@subst_intro' y).
  apply~ subst_lc'. apply~ open_var_lc'.
Qed.

Lemma open_close_var' : forall x t, 
  lc' t -> 
  open_var (close_var x t) x = t.
Proof.
  introv. unfold lc', open_var, open, close_var. generalize 0.
  induction t; simpl; introv Lt; fequals*.
  case_nat~. false. nat_math.
  case_var~. simpl. case_nat~.
Qed.

Lemma close_var_inj' : forall x t1 t2, 
  lc' t1 -> lc' t2 ->
  (close_var x t1 = close_var x t2) -> (t1 = t2).
Proof.
  introv T1 T2 Eq.
  rewrite~ <- (@open_close_var' x t1).
  rewrite~ <- (@open_close_var' x t2).
  fequals~.
Qed.



