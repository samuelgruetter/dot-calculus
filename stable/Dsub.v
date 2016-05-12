(*
 DSub (D<:)
 T ::= Top | p.Type | { Type = T } | { Type <: T } | (z: T) -> T^z
 t ::= p | t t
 p ::= x | v
 v ::= { Type = T } | lambda x:T.t
*)

(* based on *)
(***************************************************************************
* Preservation and Progress for System-F with Subtyping - Definitions      *
* Brian Aydemir & Arthur Charguéraud, March 2007                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ : Set :=
  | typ_top   : typ
  | typ_sel  : trm -> typ
  | typ_mem   : bool -> typ -> typ
  | typ_all   : typ -> typ -> typ

(** Representation of pre-terms *)

with trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_mem  : typ -> trm
  | trm_app  : trm -> trm -> trm.

Fixpoint open_t_rec (k : nat) (f : trm) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_sel t       => typ_sel (open_e_rec k f t)
  | typ_mem b T     => typ_mem b (open_t_rec k f T)
  | typ_all T1 T2   => typ_all (open_t_rec k f T1) (open_t_rec (S k) f T2)
  end

(** Opening up a term binder occuring in a term *)

with open_e_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs (open_t_rec k f V) (open_e_rec (S k) f e1)
  | trm_mem T     => trm_mem (open_t_rec k f T)
  | trm_app e1 e2 => trm_app (open_e_rec k f e1) (open_e_rec k f e2)
  end.

Definition open_t T f := open_t_rec 0 f T.
Definition open_e t u := open_e_rec 0 u t.

(** Notation for opening up binders with variables *)

Notation "t 'open_t_var' x" := (open_t t (trm_fvar x)) (at level 67).
Notation "t 'open_e_var' x" := (open_e t (trm_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_sel : forall e1,
      term e1 ->
      type (typ_sel e1)
  | type_mem : forall b T1,
      type T1 ->
      type (typ_mem b T1)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall x, x \notin L -> type (T2 open_t_var x)) ->
      type (typ_all T1 T2)

(** Terms as locally closed pre-terms *)

with term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1,
      type V ->
      (forall x, x \notin L -> term (e1 open_e_var x)) ->
      term (trm_abs V e1)
  | term_mem : forall T1,
      type T1 ->
      term (trm_mem T1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2).

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1)
  | value_mem : forall V, term (trm_mem V) ->
                 value (trm_mem V).

(** Environment is an associative list of bindings. *)

Definition env := LibEnv.env typ.

(** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  subtyping relation in E. This predicates implies
  that T is a type *)

Inductive wft : env -> typ -> Prop :=
  | wft_top : forall E,
      wft E typ_top
  | wft_sel : forall E e,
      value e \/ (exists x, trm_fvar x = e) ->
      wfe E e ->
      wft E (typ_sel e)
  | wft_mem : forall E b T1,
      wft E T1 ->
      wft E (typ_mem b T1)
  | wft_all : forall L E T1 T2,
      wft E T1 ->
      (forall x, x \notin L ->
        wft (E & x ~ T1) (T2 open_t_var x)) ->
      wft E (typ_all T1 T2)
with wfe : env -> trm -> Prop :=
  | wfe_var : forall U E x,
      binds x U E ->
      wfe E (trm_fvar x)
   | wfe_abs : forall L E V e,
      wft E V ->
      (forall x, x \notin L -> wfe (E & x ~ V) (e open_e_var x)) ->
      wfe E (trm_abs V e)
  | wfe_mem : forall E T,
      wft E T ->
      wfe E (trm_mem T)
  | wfe_app : forall E e1 e2,
      wfe E e1 ->
      wfe E e2 ->
      wfe E (trm_app e1 e2)
.

(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_push : forall E x T,
      okt E -> wft E T -> x # E -> okt (E & x ~ T).

(** Subtyping relation *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      okt E ->
      wft E S ->
      sub E S typ_top
  | sub_refl_sel : forall E t,
      okt E ->
      wft E (typ_sel t) ->
      sub E (typ_sel t) (typ_sel t)
  | sub_sel1 : forall E U t,
      has E t (typ_mem false U) ->
      sub E (typ_sel t) U
  | sub_sel2 : forall E S t,
      has E t (typ_mem true S) ->
      sub E S (typ_sel t)
  | sub_mem_false : forall E b1 T1 T2,
      sub E T1 T2 ->
      sub E (typ_mem b1 T1) (typ_mem false T2)
  | sub_mem_true : forall E T1 T2,
      sub E T1 T2 -> sub E T2 T1 ->
      sub E (typ_mem true T1) (typ_mem true T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall x, x \notin L ->
          sub (E & x ~ T1) (S2 open_t_var x) (T2 open_t_var x)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
  | sub_trans : forall E S T U,
      sub E S T ->
      sub E T U ->
      sub E S U

with has : env -> trm -> typ -> Prop :=
  | has_var : forall E x TX b T,
      okt E ->
      binds x TX E ->
      sub E TX (typ_mem b T) ->
      has E (trm_fvar x) T
  | has_mem : forall E b T,
      okt E -> wft E T ->
      has E (trm_mem T) (typ_mem b T)
.

(** Typing relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x T E ->
      typing E (trm_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~ V) (e1 open_e_var x) (T1 open_t_var x)) ->
      typing E (trm_abs V e1) (typ_all V T1)
  | typing_mem : forall E T1,
      okt E ->
      wft E T1 ->
      typing E (trm_mem T1) (typ_mem true T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_all T1 T2) ->
      typing E e2 T1 ->
      wft E T2 ->
      typing E (trm_app e1 e2) T2
  | typing_appvar : forall T1 E e1 e2 T2 T2' M,
      typing E e1 (typ_all T1 T2) ->
      typing E e2 T1 ->
      has E e2 M ->
      T2' = open_t T2 e2 ->
      wft E T2' ->
      typing E (trm_app e1 e2) T2'
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T.

(** One-step reduction *)

Inductive red : trm -> trm -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      term e2 ->
      red e1 e1' ->
      red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (trm_app e1 e2) (trm_app e1 e2')
  | red_abs : forall V e1 v2,
      term (trm_abs V e1) ->
      value v2 ->
      red (trm_app (trm_abs V e1) v2) (open_e e1 v2).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall e e' T,
  typing empty e T ->
  red e e' ->
  typing empty e' T.

Definition progress := forall e T,
  typing empty e T ->
     value e
  \/ exists e', red e e'.

(***************************************************************************
* Preservation and Progress for System-F with Subtyping - Infrastructure   *
***************************************************************************)

(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free variables in a type *)

Fixpoint fv_t (T : typ) {struct T} : vars :=
  match T with
  | typ_top         => \{}
  | typ_sel t       => fv_e t
  | typ_mem b T1   => (fv_t T1)
  | typ_all T1 T2   => (fv_t T1) \u (fv_t T2)
  end

(** Computing free variables in a term *)

with fv_e (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs V e1  => (fv_t V) \u (fv_e e1)
  | trm_mem T     => fv_t T
  | trm_app e1 e2 => (fv_e e1) \u (fv_e e2)
  end.

(** Substitution for free type variables in types. *)

Fixpoint subst_t (z : var) (u : trm) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_sel t       => typ_sel (subst_e z u t)
  | typ_mem b T1    => typ_mem b (subst_t z u T1)
  | typ_all T1 T2   => typ_all (subst_t z u T1) (subst_t z u T2)
  end

(** Substitution for free term variables in terms. *)

with subst_e (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs V e1  => trm_abs (subst_t z u V) (subst_e z u e1)
  | trm_mem T1    => trm_mem (subst_t z u T1)
  | trm_app e1 e2 => trm_app (subst_e z u e1) (subst_e z u e2)
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors type term wft wfe ok okt value red.

Hint Resolve
  sub_top sub_refl_sel
  typing_var typing_app typing_sub.

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : typ => fv_t x) in
  let D := gather_vars_with (fun x : trm => fv_e x) in
  let E := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D \u E).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- wft ?E _ => E
  | |- wfe ?E _ => E
  | |- sub ?E _ _  => E
  | |- has ?E _ _ => E
  | |- typing ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; auto*.

Scheme typ_mut := Induction for typ Sort Prop
with   trm_mut := Induction for trm Sort Prop.
Combined Scheme typ_trm_mutind from typ_mut, trm_mut.

Scheme type_mut := Induction for type Sort Prop
with term_mut := Induction for term Sort Prop.
Combined Scheme lc_mutind from type_mut, term_mut.

Scheme wft_mut := Induction for wft Sort Prop
with wfe_mut := Induction for wfe Sort Prop.
Combined Scheme wf_mutind from wft_mut, wfe_mut.

Scheme sub_mut := Induction for sub Sort Prop
with has_mut := Induction for has Sort Prop.
Combined Scheme sub_has_mutind from sub_mut, has_mut.

(* ********************************************************************** *)
(** * Properties of Substitutions *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_lc_core : (forall T j v u i, i <> j ->
  (open_t_rec j v T) = open_t_rec i u (open_t_rec j v T) ->
  T = open_t_rec i u T) /\ (forall e j v u i, i <> j ->
  open_e_rec j v e = open_e_rec i u (open_e_rec j v e) ->
  e = open_e_rec i u e).
Proof.
  apply typ_trm_mutind;
  try (introv IH1 IH2 Neq H);
  try (introv IH Neq H);
  try (introv Neq H);
  simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_rec_lc : (forall T,
  type T -> forall u k, T = open_t_rec k u T) /\ (forall e,
  term e -> forall u k, e = open_e_rec k u e).
Proof.
  apply lc_mutind; intros; simpl; f_equal*.
  pick_fresh x. apply* ((proj1 open_rec_lc_core) T2 0 (trm_fvar x)).
  pick_fresh x. apply* ((proj2 open_rec_lc_core) e1 0 (trm_fvar x)).
Qed.

Lemma open_t_var_type : forall x T,
  type T -> T open_t_var x = T.
Proof.
  intros. unfold open_t. rewrite* <- (proj1 open_rec_lc).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : (forall T z u,
  z \notin fv_t T -> subst_t z u T = T) /\ (forall e z u,
  z \notin fv_e e -> subst_e z u e = e).
Proof.
  apply typ_trm_mutind; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open_rec : (forall T1 t2 x u n, term u ->
  subst_t x u (open_t_rec n t2 T1) =
  open_t_rec n (subst_e x u t2) (subst_t x u T1)) /\ (forall t1 t2 x u n, term u ->
  subst_e x u (open_e_rec n t2 t1) =
  open_e_rec n (subst_e x u t2) (subst_e x u t1)).
Proof.
  apply typ_trm_mutind; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- (proj2 open_rec_lc).
Qed.

Lemma subst_t_open_t : forall T1 t2 x u, term u ->
  subst_t x u (open_t T1 t2) =
  open_t (subst_t x u T1) (subst_e x u t2).
Proof.
  unfold open_t. auto* (proj1 subst_open_rec).
Qed.

Lemma subst_e_open_e : forall t1 t2 x u, term u ->
  subst_e x u (open_e t1 t2) =
  open_e (subst_e x u t1) (subst_e x u t2).
Proof.
  unfold open_e. auto* (proj2 subst_open_rec).
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_t_open_t_var : forall x y u T, y <> x -> term u ->
  (subst_t x u T) open_t_var y = subst_t x u (T open_t_var y).
Proof.
  introv Neq Wu. rewrite* subst_t_open_t.
  simpl. case_var*.
Qed.

Lemma subst_e_open_e_var : forall x y u e, y <> x -> term u ->
  (subst_e x u e) open_e_var y = subst_e x u (e open_e_var y).
Proof.
  introv Neq Wu. rewrite* subst_e_open_e.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_t_intro : forall x T2 u,
  x \notin fv_t T2 -> term u ->
  open_t T2 u = subst_t x u (T2 open_t_var x).
Proof.
  introv Fr Wu. rewrite* subst_t_open_t.
  rewrite* (proj1 subst_fresh). simpl. case_var*.
Qed.

Lemma subst_e_intro : forall x t2 u,
  x \notin fv_e t2 -> term u ->
  open_e t2 u = subst_e x u (t2 open_e_var x).
Proof.
  introv Fr Wu. rewrite* subst_e_open_e.
  rewrite* (proj2 subst_fresh). simpl. case_var*.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_lc :
  (forall T, type T -> forall z u, term u -> type (subst_t z u T)) /\
  (forall e, term e -> forall z u, term u -> term (subst_e z u e)).
Proof.
  apply lc_mutind; intros; simpl; auto.
  apply_fresh* type_all as X. rewrite* subst_t_open_t_var.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_e_open_e_var.
Qed.

Lemma subst_t_type : forall T z u,
  type T -> term u -> type (subst_t z u T).
Proof.
  intros. apply* (proj1 subst_lc).
Qed.

Lemma subst_e_term : forall e1 z e2,
  term e1 -> term e2 -> term (subst_e z e2 e1).
Proof.
  intros. apply* (proj2 subst_lc).
Qed.

Lemma subst_e_value : forall e1 z e2,
  value e1 ->  term e2 -> value (subst_e z e2 e1).
Proof.
  intros. inversion H; subst; simpl.
  - apply value_abs.
    assert (trm_abs (subst_t z e2 V) (subst_e z e2 e0) = subst_e z e2 (trm_abs V e0)) as A. {
      simpl. reflexivity.
    }
    rewrite A. apply* subst_e_term.
  - apply value_mem.
    assert (trm_mem (subst_t z e2 V) = subst_e z e2 (trm_mem V)) as A. {
      simpl. reflexivity.
    }
    rewrite A. apply* subst_e_term.
Qed.

Lemma value_is_term: forall e, value e -> term e.
Proof.
  introv H. inversion H; subst; eauto.
Qed.

Hint Resolve subst_t_type subst_e_term subst_e_value value_is_term.

(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma wf_lc : (forall E T, wft E T -> type T) /\
              (forall E e, wfe E e -> term e).
Proof.
  apply wf_mutind; eauto.
Qed.

Lemma wft_type : forall E T,
  wft E T -> type T.
Proof.
  intros. eapply (proj1 wf_lc); eauto.
Qed.

Lemma wfe_term : forall E e,
  wfe E e -> term e.
Proof.
  intros. eapply (proj2 wf_lc); eauto.
Qed.

(** Through weakening *)

Lemma wf_weaken :
  (forall E0 T, wft E0 T ->
   forall E F G, E0 = E & G ->
                 ok (E & F & G) ->
                 wft (E & F & G) T)
    /\
  (forall E0 e, wfe E0 e ->
   forall E F G, E0 = E & G ->
                 ok (E & F & G) ->
                 wfe (E & F & G) e).
Proof.
  apply wf_mutind; intros; subst; eauto.
  apply_fresh* wft_all as Y. apply_ih_bind* H0.
  apply (@wfe_var U). apply* binds_weaken.
  apply_fresh* wfe_abs as y. apply_ih_bind* H0.
Qed.

Lemma wft_weaken : forall G T E F,
  wft (E & G) T ->
  ok (E & F & G) ->
  wft (E & F & G) T.
Proof.
  intros. eapply (proj1 wf_weaken); eauto.
Qed.

Lemma wft_weaken_empty : forall T E,
  wft empty T ->
  ok E ->
  wft E T.
Proof.
  intros.
  assert (E = empty & E & empty) as A. {
    rewrite concat_empty_l. rewrite concat_empty_r. reflexivity.
  }
  rewrite A. apply wft_weaken.
  rewrite concat_empty_l. auto.
  rewrite concat_empty_l. rewrite concat_empty_r. auto.
Qed.

Lemma wfe_weaken : forall G T E F,
  wfe (E & G) T ->
  ok (E & F & G) ->
  wfe (E & F & G) T.
Proof.
  intros. eapply (proj2 wf_weaken); eauto.
Qed.

Lemma wfe_weaken_empty : forall T E,
  wfe empty T ->
  ok E ->
  wfe E T.
Proof.
  intros.
  assert (E = empty & E & empty) as A. {
    rewrite concat_empty_l. rewrite concat_empty_r. reflexivity.
  }
  rewrite A. apply wfe_weaken.
  rewrite concat_empty_l. auto.
  rewrite concat_empty_l. rewrite concat_empty_r. auto.
Qed.

(** Through narrowing *)

Lemma wf_narrow : (forall E0 T, wft E0 T -> forall V F U E x,
  E0 = (E & x ~ V & F) ->
  ok (E & x ~ U & F) ->
  wft (E & x ~ U & F) T)
  /\
(forall E0 e, wfe E0 e -> forall V F U E x,
  E0 = (E & x ~ V & F) ->
  ok (E & x ~ U & F) ->
  wfe (E & x ~ U & F) e).
Proof.
  apply wf_mutind; intros; subst; eauto.
  apply_fresh* wft_all as Y. apply_ih_bind* H0.
  destruct (binds_middle_inv b) as [K|[K|K]]; try destructs K.
    applys wfe_var. apply* binds_concat_right.
    subst. applys wfe_var. apply~ binds_middle_eq.
    applys wfe_var. apply~ binds_concat_left.
     apply* binds_concat_left.
  apply_fresh* wfe_abs as y. apply_ih_bind* H0.
Qed.

Lemma wft_narrow : forall V F U T E x,
  wft (E & x ~ V & F) T ->
  ok (E & x ~ U & F) ->
  wft (E & x ~ U & F) T.
Proof.
  intros. eapply (proj1 wf_narrow); eauto.
Qed.

(** Through substitution *)

Lemma wf_subst : (forall E0 T, wft E0 T -> forall F Q E Z u,
  E0 = E & Z ~ Q & F ->
  (value u \/ exists x, trm_fvar x = u) -> wfe E u ->
  ok (E & map (subst_t Z u) F) ->
  wft (E & map (subst_t Z u) F) (subst_t Z u T)) /\
  (forall E0 e, wfe E0 e -> forall F Q E Z u,
  E0 = E & Z ~ Q & F ->
  (value u \/ exists x, trm_fvar x = u) -> wfe E u ->
  ok (E & map (subst_t Z u) F) ->
  wfe (E & map (subst_t Z u) F) (subst_e Z u e)).
Proof.
  apply wf_mutind; intros; subst; simpl; eauto.
  - destruct o as [? | [? ?]].
    + apply* wft_sel. left. apply subst_e_value. assumption. apply* wfe_term.
    + subst. simpl. case_var*.
      * apply_empty* wft_weaken.
      * apply* wft_sel. rewrite* <- ((proj2 subst_fresh) (trm_fvar x) Z u).
        simpl. auto.
  - apply_fresh* wft_all as Y.
    lets: wft_type.
    rewrite* subst_t_open_t_var.
    apply_ih_map_bind* H0. apply* wfe_term.
  - case_var*.
    + apply_empty* (proj2 wf_weaken).
    + destruct (binds_concat_inv b) as [?|[? ?]].
      apply (@wfe_var (subst_t Z u U)).
       apply~ binds_concat_right.
      destruct (binds_push_inv H3) as [[? ?]|[? ?]].
        subst. false~.
        applys wfe_var. apply* binds_concat_left.
  - apply_fresh* wfe_abs as y.
    lets: (proj2 wf_lc).
    rewrite* subst_e_open_e_var.
    apply_ih_map_bind* H0.
Qed.

Lemma wft_subst : forall F Q E Z u T,
  wft (E & Z ~ Q & F) T ->
  (value u \/ exists x, trm_fvar x = u) -> wfe E u ->
  ok (E & map (subst_t Z u) F) ->
  wft (E & map (subst_t Z u) F) (subst_t Z u T).
Proof.
  intros. eapply (proj1 wf_subst); eauto.
Qed.

Lemma wft_subst_empty : forall Q Z u T,
  wft (Z ~ Q) T ->
  (value u \/ exists x, trm_fvar x = u) -> wfe empty u ->
  wft empty (subst_t Z u T).
Proof.
  intros.
  assert (empty & map (subst_t Z u) empty = empty) as A. {
    rewrite map_empty. rewrite concat_empty_l. reflexivity.
  }
  rewrite <- A. eapply wft_subst; eauto.
  rewrite concat_empty_l. rewrite concat_empty_r. eauto.
  rewrite A. eauto.
Qed.

(** Through type reduction *)

Lemma wft_open : forall E u T1 T2,
  ok E ->
  wft E (typ_all T1 T2) ->
  (value u \/ exists x, trm_fvar x = u) -> wfe E u ->
  wft E (open_t T2 u).
Proof.
  introv Ok WA VU WU. inversions WA. pick_fresh X.
  auto* wft_type. rewrite* (@subst_t_intro X).
  lets K: (@wft_subst empty).
  specializes_vars K. clean_empty K. apply* K.
  apply* wfe_term.
Qed.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1; auto.
Qed.

Hint Extern 1 (ok _) => apply ok_from_okt.

(** Extraction from an assumption in a well-formed environments *)

Lemma wft_from_env_has : forall x U E,
  okt E -> binds x U E -> wft E U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
    false (empty_push_inv H0).
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       apply_empty* wft_weaken.
       apply_empty* wft_weaken.
Qed.

(** Extraction from a well-formed environment *)

Lemma wft_from_okt : forall x T E,
  okt (E & x ~ T) -> wft E T.
Proof.
  intros. inversions* H.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. subst. assumption.
Qed.

(** Automation *)

Lemma wft_weaken_right : forall T E F,
  wft E T ->
  ok (E & F) ->
  wft (E & F) T.
Proof.
  intros. apply_empty* wft_weaken.
Qed.

Hint Resolve wft_weaken_right.
Hint Resolve wft_from_okt.
Hint Immediate wft_from_env_has.
Hint Resolve wft_subst.

(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E x T,
  okt (E & x ~ T) -> okt E /\ wft E T /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. eauto.
Qed.

Lemma okt_push_type : forall E x T,
  okt (E & x ~ T) -> type T.
Proof. intros. applys wft_type. forwards*: okt_push_inv. Qed.

Hint Immediate okt_push_type.

(** Through narrowing *)

Lemma okt_narrow : forall V (E F:env) U x,
  okt (E & x ~ V & F) ->
  wft E U ->
  okt (E & x ~ U & F).
Proof.
  introv O W. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_inv O).
  rewrite concat_assoc in *.
  lets (?&?&?): (okt_push_inv O).
  applys~ okt_push. applys* wft_narrow.
Qed.

(** Through substitution *)

Lemma okt_subst : forall Q Z u (E F:env),
  okt (E & Z ~ Q & F) ->
  (value u \/ exists x, trm_fvar x = u) -> wfe E u ->
  okt (E & map (subst_t Z u) F).
Proof.
 introv O V W. induction F using env_ind.
  rewrite map_empty. rewrite concat_empty_r in *.
   lets*: (okt_push_inv O).
  rewrite map_push. rewrite concat_assoc in *.
   lets*: (okt_push_inv O).
   apply okt_push. apply* IHF. apply* wft_subst. auto*.
Qed.

(** Automation *)

Hint Resolve okt_narrow okt_subst wft_weaken.


(* ********************************************************************** *)
(** ** Environment is unchanged by substitution from a fresh name *)

Ltac destruct_notin_union :=
  match goal with
    | H: _ \notin _ \u _ |- _ => eapply notin_union in H; destruct H
  end.

Lemma notin_fv_open_rec : (forall T k y x,
  x \notin fv_t (open_t_rec k (trm_fvar y) T) ->
  x \notin fv_t T) /\ (forall e k y x,
  x \notin fv_e (open_e_rec k (trm_fvar y) e) ->
  x \notin fv_e e).
Proof.
  apply typ_trm_mutind; simpl; intros;
  repeat destruct_notin_union; eauto using notin_union_l.
Qed.

Lemma notin_fv_t_open : forall y x T,
  x \notin fv_t (T open_t_var y) ->
  x \notin fv_t T.
Proof.
  unfold open_t. intros. apply* (proj1 notin_fv_open_rec).
Qed.

Lemma notin_fv_e_open : forall y x e,
  x \notin fv_e (e open_e_var y) ->
  x \notin fv_e e.
Proof.
  unfold open_e. intros. apply* (proj2 notin_fv_open_rec).
Qed.

Lemma notin_fv_wf_rec :
  (forall E T,
     wft E T -> forall x, x # E -> x \notin fv_t T) /\
  (forall E e,
     wfe E e -> forall x, x # E -> x \notin fv_e e).
Proof.
  apply wf_mutind; intros; simpl; eauto.
  notin_simpl; auto. pick_fresh Y. apply* (@notin_fv_t_open Y).
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv b H.
  notin_simpl; auto. pick_fresh y. apply* (@notin_fv_e_open y).
Qed.

Lemma notin_fv_wf : forall E x T,
  wft E T -> x # E -> x \notin fv_t T.
Proof.
  intros. eapply (proj1 notin_fv_wf_rec); eauto.
Qed.

Lemma map_subst_id : forall G z u,
  okt G -> z # G -> G = map (subst_t z u) G.
Proof.
  induction 1; intros Fr; autorewrite with rew_env_map; simpl.
  auto.
  rewrite* <- IHokt. rewrite* (proj1 subst_fresh). apply* notin_fv_wf.
Qed.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_has_regular : (forall E S T,
  sub E S T -> okt E /\ wft E S /\ wft E T) /\ (forall E p T,
  has E p T -> okt E /\ wft E (typ_sel p) /\ wft E T).
Proof.
  apply sub_has_mutind; intros; try auto*.
  splits*. destruct H as [? [? A]]. inversion A; subst. assumption.
  splits*. destruct H as [? [? A]]. inversion A; subst. assumption.
  split. auto*. split;
   apply_fresh* wft_all as Y;
    forwards~: (H0 Y); apply_empty* (@wft_narrow T1).
  splits*. destruct H as [? [? A]]. inversion A; subst. assumption.
  splits*. apply wft_sel. left. apply value_mem. apply* wfe_term. apply* wfe_mem.
Qed.

Lemma sub_regular : forall E S T,
  sub E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  intros. apply* (proj1 sub_has_regular).
Qed.

Lemma has_regular : forall E p T,
  has E p T -> okt E /\ wft E (typ_sel p) /\ wft E T.
Proof.
  intros. apply* (proj2 sub_has_regular).
Qed.

Lemma has_regular_e : forall E p T,
  has E p T -> (value p \/ (exists x, trm_fvar x = p)) /\ wfe E p.
Proof.
  intros. apply has_regular in H. destruct H as [? [A ?]].
  inversion A; subst. split; assumption.
Qed.

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ wfe E e /\ wft E T.
Proof.
  induction 1.
  splits*.
  splits.
   pick_fresh y. specializes H0 y. destructs~ H0.
    forwards*: okt_push_inv.
   apply_fresh* wfe_abs as y.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
       forwards*: okt_push_inv.
     forwards~ K: (H0 y). destructs K. auto.
   apply_fresh* wft_all as Y.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
      forwards*: okt_push_inv.
     forwards~ K: (H0 Y). destructs K.
      forwards*: okt_push_inv.
  splits*.
  splits*.
  splits*.
  splits*. destructs~ (sub_regular H0).
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; auto*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

Lemma red_regular : forall t t',
  red t t' -> term t /\ term t'.
Proof.
  induction 1; split; auto* value_regular.
  inversions H. pick_fresh y. rewrite* (@subst_e_intro y).
Qed.

(** Automation *)

Hint Extern 1 (okt ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj31 (sub_regular H))
  | H: has _ _ _ |- _ => apply (proj31 (has_regular H))
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (wft ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj33 (typing_regular H))
  | H: sub E T _ |- _ => apply (proj32 (sub_regular H))
  | H: sub E _ T |- _ => apply (proj33 (sub_regular H))
  | H: has E _ T |- _ => apply (proj33 (has_regular H))
  end.

Hint Extern 1 (wfe ?E ?e) =>
  match goal with
  | H: typing E e _ |- _ => apply (proj32 (typing_regular H))
  | H: has E e _ |- _ => apply (proj2 (has_regular_e H))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (@wft_type E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (wfe_term (proj32 (typing_regular H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular H))
  end.

(***************************************************************************
* Preservation and Progress for System-F with Subtyping - Proofs           *
***************************************************************************)

(** In parentheses are given the label of the corresponding
  lemma in the description of the POPLMark Challenge. *)


(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  okt E ->
  wft E T ->
  sub E T T .
Proof.
  introv Ok WI. lets W: (wft_type WI). gen E.
  induction W; intros; inversions WI; eauto.
  destruct b. apply* sub_mem_true. apply* sub_mem_false.
  apply_fresh* sub_all as Y.
Qed.

(* ********************************************************************** *)
(** Weakening (2) *)

Lemma sub_has_weakening : (forall E0 S T, sub E0 S T -> forall E F G,
   E0 = E & G ->
   okt (E & F & G) ->
   sub (E & F & G) S T) /\ (forall E0 p T, has E0 p T -> forall E F G,
   E0 = E & G ->
   okt (E & F & G) ->
   has (E & F & G) p T).
Proof.
  apply sub_has_mutind; intros; subst; auto.
  apply* sub_sel1.
  apply* sub_sel2.
  apply* sub_mem_false.
  apply* sub_mem_true.
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
  apply* sub_trans.
  apply* has_var. apply* binds_weaken.
  apply* has_mem.
Qed.

Lemma sub_weakening : forall E F G S T,
   sub (E & G) S T ->
   okt (E & F & G) ->
   sub (E & F & G) S T.
Proof.
  intros. apply* (proj1 sub_has_weakening).
Qed.

Lemma sub_weakening1 : forall E F G S T,
   sub E S T ->
   okt (E & F & G) ->
   sub (E & F & G) S T.
Proof.
  intros.
  assert (E & F & G = E & (F & G) & empty) as A. {
    rewrite concat_empty_r. rewrite concat_assoc. reflexivity.
  }
  rewrite A.
  apply* sub_weakening.
  rewrite concat_empty_r. assumption.
  rewrite <- A. assumption.
Qed.

Lemma sub_weakening_empty : forall E S T,
   sub empty S T ->
   okt E ->
   sub E S T.
Proof.
  intros.
  assert (empty & E & empty = E) as A. {
    rewrite concat_empty_r. rewrite concat_empty_l. reflexivity.
  }
  rewrite <- A.
  apply* sub_weakening.
  rewrite concat_empty_r. assumption.
  rewrite A. assumption.
Qed.

Lemma has_weakening : forall E F G p T,
   has (E & G) p T ->
   okt (E & F & G) ->
   has (E & F & G) p T.
Proof.
  intros. apply* (proj2 sub_has_weakening).
Qed.

Lemma has_weakening_empty : forall E p T,
   has empty p T ->
   okt E ->
   has E p T.
Proof.
  intros.
  assert (empty & E & empty = E) as A. {
    rewrite concat_empty_r. rewrite concat_empty_l. reflexivity.
  }
  rewrite <- A.
  apply* has_weakening.
  rewrite concat_empty_r. assumption.
  rewrite A. assumption.
Qed.

(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

Hint Resolve wft_narrow.

Lemma sub_has_narrowing_aux :
  (forall E0 S T, sub E0 S T ->
   forall Q E F z P,
   E0 = (E & z ~ Q & F) ->
   sub E P Q ->
   sub (E & z ~ P & F) S T)
  /\
  (forall E0 p T, has E0 p T ->
   forall Q E F z P,
   E0 = (E & z ~ Q & F) ->
   sub E P Q ->
   has (E & z ~ P & F) p T).
Proof.
  Hint Constructors sub has.
  apply sub_has_mutind; intros; subst; eauto.
  apply* sub_top.
  apply* sub_refl_sel.
  apply_fresh* sub_all as Y. apply_ih_bind H0; eauto.
  tests EQ: (x = z).
    lets M: (@okt_narrow Q).
    apply binds_middle_eq_inv in b0. subst.
    eapply has_var. apply* M. apply binds_middle_eq.
      eapply ok_from_okt in o. eapply ok_middle_inv in o. destruct o as [o1 o2]. apply o2.
      eapply sub_trans. eapply sub_weakening1; eauto. eapply H; eauto.
      auto*.
    eapply has_var; eauto. binds_cases b0; auto.
  apply* has_mem.
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (E & Z ~ Q & F) S T ->
  sub (E & Z ~ P & F) S T.
Proof.
  intros.
  apply* (proj1 sub_has_narrowing_aux).
Qed.

Lemma sub_narrowing_empty : forall Q Z P S T,
  sub empty P Q ->
  sub (Z ~ Q) S T ->
  sub (Z ~ P) S T.
Proof.
  intros.
  rewrite <- (concat_empty_r (Z ~ P)).
  rewrite <- (concat_empty_l (Z ~ P)).
  eapply sub_narrowing; eauto.
  rewrite concat_empty_r. rewrite concat_empty_l. auto.
Qed.

End NarrowTrans.

(* ********************************************************************** *)
(** Substitution preserves subtyping (10) *)

Lemma has_value_var : forall E u T,
  has E u T ->
  (value u \/ exists x, trm_fvar x = u).
Proof.
  intros. apply has_regular_e in H. destruct H as [A ?].
  apply A.
Qed.

Hint Resolve has_value_var.

Lemma sub_has_through_subst_z : (forall E0 S T, sub E0 S T -> forall Q E F Z u x P,
  E0 = (E & Z ~ Q & F) ->
  trm_fvar x = u -> binds x P E -> sub E P Q ->
  sub (E & map (subst_t Z u) F) (subst_t Z u S) (subst_t Z u T)) /\
  (forall E0 p T, has E0 p T -> forall Q E F Z u x P,
  E0 = (E & Z ~ Q & F) ->
  trm_fvar x = u -> binds x P E -> sub E P Q ->
  has (E & map (subst_t Z u) F) (subst_e Z u p) (subst_t Z u T)).
Proof.
  apply sub_has_mutind; intros; subst; simpl.
  - apply* sub_top. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
  - simpl. apply* sub_refl_sel.
    assert (typ_sel (subst_e Z (trm_fvar x) t) = subst_t Z (trm_fvar x) (typ_sel t)) as A by auto.
    rewrite A. auto*. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
  - apply* sub_sel1.
  - apply* sub_sel2.
  - apply* sub_mem_false.
  - apply* sub_mem_true.
  - apply_fresh* sub_all as X.
    rewrite* subst_t_open_t_var. rewrite* subst_t_open_t_var.
    apply_ih_map_bind* H0.
  - apply* sub_trans.
  - case_var.
    + apply binds_middle_eq_inv in b0; eauto. subst.
      eapply has_var. apply* okt_subst.
      apply binds_concat_left_ok. apply ok_from_okt. apply* okt_subst. eassumption.
      eapply sub_trans.
      instantiate (1:=(subst_t Z (trm_fvar x0) Q)).
      apply_empty* sub_weakening1. rewrite (proj1 subst_fresh). auto.
      apply* (@notin_fv_wf E0).
      eapply H; eauto.
    + assert (forall u, subst_t Z u (typ_mem b T) = typ_mem b (subst_t Z u T)) as A. {
        intros. simpl. reflexivity.
      }
      destruct (binds_concat_inv b0) as [?|[? ?]].
      * eapply has_var. auto*.
        apply binds_concat_right. apply binds_map. eassumption.
        instantiate (1:=b). rewrite <- A. eapply H; eauto.
      * applys has_var. apply* okt_subst. instantiate (1:=TX).
        eapply binds_concat_left_inv in H1. apply* binds_concat_left. auto*.
        instantiate (1:=b). rewrite <- A.
        assert (TX = subst_t Z (trm_fvar x0) TX) as B. {
          rewrite (proj1 subst_fresh). reflexivity.
          eapply binds_concat_left_inv in H1.
          apply* (@notin_fv_wf E0). apply* wft_from_env_has.
          auto*.
        }
        rewrite B. eapply H; eauto.
  - apply* has_mem. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
Qed.

(* ********************************************************************** *)
(** * Properties of Typing *)

(* ********************************************************************** *)
(** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T ->
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as x. forwards~ K: (H x).
   apply_ih_bind (H0 x); eauto.
  apply* typing_mem.
  apply* typing_app.
  eapply typing_appvar; eauto. eapply (proj2 sub_has_weakening); eauto.
  apply* typing_sub. apply* sub_weakening.
Qed.

(************************************************************************ *)
(** Preservation by Type Narrowing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (E & X ~ Q & F) e T ->
  typing (E & X ~ P & F) e T.
Proof.
  introv PsubQ Typ. gen_eq E': (E & X ~ Q & F). gen F.
  inductions Typ; introv EQ; subst; simpl.
  - binds_cases H0.
    + apply* typing_var.
    + subst. apply* typing_sub. apply* sub_weakening1.
    + apply* typing_var.
  - apply_fresh* typing_abs as y. apply_ih_bind* H0.
  - apply* typing_mem. apply* wft_narrow.
  - apply* typing_app. apply* wft_narrow.
  - apply* typing_appvar. apply* (proj2 sub_has_narrowing_aux). apply* wft_narrow.
  - apply* typing_sub. apply* (@sub_narrowing Q).
Qed.

Lemma typing_narrowing_empty : forall Q X P e T,
  sub empty P Q ->
  typing (X ~ Q) e T ->
  typing (X ~ P) e T.
Proof.
  intros.
  rewrite <- (concat_empty_r (X ~ P)).
  rewrite <- (concat_empty_l (X ~ P)).
  eapply typing_narrowing; eauto.
  rewrite concat_empty_r. rewrite concat_empty_l. auto.
Qed.

(************************************************************************ *)
(** Preservation by Substitution (8) *)

Lemma typing_through_subst_z : forall U E F z T e u x P,
  typing (E & z ~ U & F) e T ->
  trm_fvar x = u -> binds x P E -> sub E P U ->
  typing (E & (map (subst_t z u) F)) (subst_e z u e) (subst_t z u T).
Proof.
  introv TypT EqU Bi TypU.
  inductions TypT; introv; subst; simpl.
  - case_var.
    + binds_get H0.
      rewrite (proj1 subst_fresh).
      apply typing_sub with (S:=P).
      apply_empty typing_weakening. apply* typing_var.
      apply* okt_subst. apply_empty* sub_weakening.
      apply* (@notin_fv_wf E).
    + binds_cases H0.
      rewrite (proj1 subst_fresh). eapply typing_var; eauto.
      apply (@notin_fv_wf E). eapply wft_from_env_has. auto*. eapply B0. auto*.
      apply* typing_var.
  - apply_fresh* typing_abs as y.
    rewrite* subst_e_open_e_var. rewrite* subst_t_open_t_var.
    rewrite <- concat_assoc_map_push.
    eapply H0; eauto. rewrite concat_assoc. auto.
  - apply* typing_mem. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
  - eapply typing_app. eapply IHTypT1; eauto. eapply IHTypT2; eauto.
    apply* wft_subst.
    apply ok_from_okt. apply* okt_subst.
  - eapply typing_appvar. eapply IHTypT1; eauto. eapply IHTypT2; eauto.
    apply* (proj2 sub_has_through_subst_z).
    eapply subst_t_open_t. auto*. apply* wft_subst.
    apply ok_from_okt. apply* okt_subst.
  - eapply typing_sub. eapply IHTypT; eauto.
    eapply (proj1 sub_has_through_subst_z); eauto.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Inductive possible_types : trm -> typ -> Prop :=
| pt_top : forall v, value v -> wfe empty v -> possible_types v typ_top
| pt_mem_true : forall T T', sub empty T T' -> sub empty T' T -> possible_types (trm_mem T) (typ_mem true T')
| pt_mem_false : forall T U, sub empty T U -> possible_types (trm_mem T) (typ_mem false U)
| pt_all : forall L V V' e1 T1 T1',
  (forall X, X \notin L -> typing (X ~ V) (e1 open_e_var X) (T1 open_t_var X)) ->
  sub empty V' V ->
  (forall X, X \notin L -> sub (X ~ V') (T1 open_t_var X) (T1' open_t_var X)) ->
  possible_types (trm_abs V e1) (typ_all V' T1')
| pt_sel : forall v p S,
  possible_types v S ->
  has empty p (typ_mem true S) ->
  possible_types v (typ_sel p)
.

Lemma possible_types_value : forall p T,
  possible_types p T ->
  value p.
Proof.
  introv Hpt. induction Hpt; eauto.
  - apply value_abs. apply_fresh* term_abs as y.
    assert (y \notin L) as Fr by auto.
    specialize (H y Fr). apply typing_regular in H.
    destruct H as [? [A ?]]. apply* wfe_term.
Qed.

Lemma possible_types_wfe : forall p T,
  possible_types p T ->
  wfe empty p.
Proof.
  introv Hpt. induction Hpt; eauto.
  - apply_fresh* wfe_abs as y.
    assert (y \notin L) as FrL by auto. specialize (H y FrL).
    apply typing_regular in H. destruct H as [? [A ?]].
    rewrite concat_empty_l. assumption.
Qed.

Lemma has_empty_var_false: forall x T,
  has empty (trm_fvar x) T ->
  False.
Proof.
  intros.
  remember (trm_fvar x) as p. generalize dependent x.
  remember empty as E. gen HeqE.
  induction H; intros; subst; eauto.
  - apply* binds_empty_inv.
  - inversion Heqp.
Qed.

Lemma has_empty_mem_eq: forall p b1 b2 S U,
  has empty p (typ_mem b1 S) ->
  has empty p (typ_mem b2 U) ->
  S = U.
Proof.
  introv HS HU.
  inversion HS; subst; eauto; inversion HU; subst; eauto;
  try solve [false; apply* binds_empty_inv];
  try solve [destruct H as [x ?]; inversion H].
Qed.

Lemma has_empty_value: forall p T,
  has empty p T ->
  value p.
Proof.
  intros. apply has_regular_e in H.
  destruct H as [[HV | [x Eq]] Hwf].
  - assumption.
  - subst. inversion Hwf; subst. false. apply* binds_empty_inv.
Qed.

Lemma has_empty_mem_b: forall b b' p T,
  has empty p (typ_mem b T) ->
  has empty p (typ_mem b' T).
Proof.
  intros.
  assert (value p) as HV by solve [apply* has_empty_value].
  inversion H; subst.
  - inversion HV.
  - apply* has_mem.
Qed.

Lemma has_trm_mem_empty: forall E T M,
  has E (trm_mem T) M -> wft empty T ->
  has empty (trm_mem T) M.
Proof.
  introv Hhas Hwf. inversion Hhas; subst; eauto.
  - apply* has_mem.
Qed.

Lemma possible_types_closure : forall v T U,
  possible_types v T ->
  sub empty T U ->
  possible_types v U.
Proof.
  introv Hpt Hsub. remember empty as E. gen HeqE. generalize dependent v.
  induction Hsub; intros; subst; eauto;
  try solve [false; apply* binds_empty_inv].
  - apply pt_top. apply* possible_types_value. apply* possible_types_wfe.
  - inversion Hpt; subst.
    assert (S = U) as Eq. {
      apply* has_empty_mem_eq.
    }
    subst. assumption.
  - apply* pt_sel.
  - inversion Hpt; subst; apply* pt_mem_false; eapply sub_trans; eassumption.
  - inversion Hpt; subst. apply* pt_mem_true; eapply sub_trans; eassumption.
  - inversion Hpt; subst. apply_fresh* pt_all as y.
    eapply sub_trans; eassumption.
    eapply sub_trans.
      eapply sub_narrowing_empty. eassumption. auto*.
      assert (y \notin L) as Fr by auto. specialize (H y Fr).
      rewrite concat_empty_l in H. apply H.
Qed.

Lemma possible_types_typing : forall v T,
  typing empty v T -> value v ->
  possible_types v T.
Proof.
  introv Ht Hv.
  remember Ht as Hc. clear HeqHc.
  remember empty as E. generalize HeqE. generalize Hc.
  induction Ht; intros; subst; eauto; try solve [inversion Hv].
  - eapply typing_regular in Hc. destruct Hc as [? [? Hc]].
    inversion Hc; subst.
    apply_fresh pt_all as Y.
    assert (Y \notin L) as Fr by eauto.
    specialize (H Y Fr). rewrite concat_empty_l in H. eapply H.
    eapply sub_reflexivity; eauto. eapply sub_reflexivity; eauto.
    rewrite <- concat_empty_l. eauto.
    assert (Y \notin L0) as Fr by eauto.
    specialize (H7 Y Fr). rewrite concat_empty_l in H7. eapply H7.
  - apply pt_mem_true. apply* sub_reflexivity. apply* sub_reflexivity.
  - eapply possible_types_closure; eauto.
Qed.

Lemma typing_inv_abs : forall S1 e1 T,
  typing empty (trm_abs S1 e1) T ->
  forall U1 U2, sub empty T (typ_all U1 U2) ->
     sub empty U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (x ~ S1) (e1 open_e_var x) (S2 open_t_var x) /\ sub (x ~ U1) (S2 open_t_var x) (U2 open_t_var x).
Proof.
  introv Typ Hsub.
  apply possible_types_typing in Typ; eauto.
  assert (possible_types (trm_abs S1 e1) (typ_all U1 U2)) as Hc. {
    eapply possible_types_closure; eauto.
  }
  inversion Hc; subst.
  repeat eexists; eauto.
Qed.

(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_all U1 U2) ->
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ.
  eapply possible_types_typing in Typ; eauto.
  inversion Typ; subst; eauto.
Qed.

Lemma canonical_form_mem : forall t b T,
  value t -> typing empty t (typ_mem b T) ->
  exists V, t = trm_mem V.
Proof.
  introv Val Typ.
  eapply possible_types_typing in Typ; eauto.
  inversion Typ; subst; eauto.
Qed.

Lemma loose_sub_sel1: forall E p P U,
  has E p P ->
  sub E P (typ_mem false U) ->
  sub E (typ_sel p) U.
Proof.
  admit.
Qed.

Lemma loose_sub_sel2: forall E p P S,
  has E p P ->
  sub E P (typ_mem true S) ->
  sub E S (typ_sel p).
Proof.
  admit.
Qed.

Lemma sub_has_through_subst : (forall E0 S T, sub E0 S T -> forall Q Z F u,
  E0 = (Z ~ Q & F) ->
  possible_types u Q ->
  sub (map (subst_t Z u) F) (subst_t Z u S) (subst_t Z u T)) /\
  (forall E0 p T, has E0 p T -> forall Q F Z u,
  E0 = (Z ~ Q & F) ->
  possible_types u Q ->
  exists P, has (map (subst_t Z u) F) (subst_e Z u p) P /\ sub (map (subst_t Z u) F) P (subst_t Z u T)).
Proof.
  apply sub_has_mutind; intros; subst; simpl;
  try assert (wfe empty u) as Hwu by solve [
    apply wfe_weaken_empty; [ apply* possible_types_wfe |
    apply ok_from_okt in o; auto ]];
  try assert (value u) as Hvu by solve [ apply* possible_types_value ];
  try assert (empty & (map (subst_t Z u) F) = map (subst_t Z u) F) as EqF by solve [
    rewrite concat_empty_l; auto ].
  - apply* sub_top.
    rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
    rewrite <- EqF. apply* wft_subst. rewrite concat_empty_l. eauto.
    apply ok_from_okt. apply* okt_subst. rewrite concat_empty_l. eauto.
  - simpl. apply* sub_refl_sel.
    rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
    assert (typ_sel (subst_e Z u t) = subst_t Z u (typ_sel t)) as A by auto.
    rewrite A.
    rewrite <- EqF. apply* wft_subst. rewrite concat_empty_l. eauto.
    apply ok_from_okt. apply* okt_subst. rewrite concat_empty_l. eauto.
  - edestruct H as [P [IH1 IH2]]; eauto. eapply loose_sub_sel1; eauto.
  - edestruct H as [P [IH1 IH2]]; eauto. eapply loose_sub_sel2; eauto.
  - apply* sub_mem_false.
  - apply* sub_mem_true.
  - apply_fresh* sub_all as X.
    rewrite* subst_t_open_t_var. rewrite* subst_t_open_t_var.
    assert (map (subst_t Z u) F & X ~ subst_t Z u T1 = map (subst_t Z u) (F & X ~ T1)) as A. {
     rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite A. eapply H0; eauto. rewrite concat_assoc. reflexivity.
  - apply* sub_trans.
  - case_var.
    + rewrite <- concat_empty_l in b0. rewrite concat_assoc in b0.
      apply binds_middle_eq_inv in b0; eauto. subst.
      inversion H1; subst.
      * exists (typ_mem true T). split.
        apply has_mem; eauto.
        rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        eapply wft_weaken_empty. auto*.
        apply ok_from_okt. rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        rewrite (proj1 subst_fresh).
        apply* sub_weakening_empty. apply sub_mem_true; eauto.
        rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        eapply notin_fv_wf; eauto.
      * exists (typ_mem true T). split.
        apply has_mem; eauto.
        rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        eapply wft_weaken_empty. auto*.
        apply ok_from_okt. rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        rewrite (proj1 subst_fresh).
        apply* sub_weakening_empty. apply sub_mem_false; eauto.
        rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        eapply notin_fv_wf; eauto.
      * rewrite concat_empty_l. auto*.
    + rewrite <- concat_empty_l in b. rewrite concat_assoc in b.
      destruct (binds_concat_inv b) as [?|[? ?]].
      * eexists. split. eapply has_var; eauto.
        rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        simpl. eapply sub_reflexivity.
        rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
        assert (typ_mem b0 (subst_t Z u T0) = subst_t Z u (typ_mem b0 T0)) as A. {
          simpl. reflexivity.
        }
        assert (wft (Z ~ Q & F) (typ_mem b0 T0)) as B. {
          eapply wft_from_env_has. eauto.
          rewrite concat_empty_l in b. eapply b.
        }
        rewrite <- EqF. rewrite A. eapply wft_subst. rewrite concat_empty_l. eauto.
        eauto. eauto.
        apply ok_from_okt. apply* okt_subst. rewrite concat_empty_l. eauto.
      * rewrite concat_empty_l in H0. apply binds_single_inv in H0. destruct H0.
        subst. false*.
  - inversion H0; subst.
    assert (typ_mem b0 (subst_t Z u T0) = subst_t Z u (typ_mem b0 T0)) as A. {
      simpl. reflexivity.
    }
    destruct b0.
    * eexists. split. eapply has_mem.
      rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
      rewrite <- EqF. apply* wft_subst. rewrite concat_empty_l. eauto.
      apply ok_from_okt. apply* okt_subst. rewrite concat_empty_l. eauto.
      eapply sub_reflexivity.
      rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
      rewrite A.
      rewrite <- EqF. apply* wft_subst. rewrite concat_empty_l. eauto.
      apply ok_from_okt. apply* okt_subst. rewrite concat_empty_l. eauto.
    * eexists. split. eapply has_mem.
      rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
      rewrite <- EqF. apply* wft_subst. rewrite concat_empty_l. eauto.
      apply ok_from_okt. apply* okt_subst. rewrite concat_empty_l. eauto.
      eapply sub_reflexivity.
      rewrite <- EqF. apply* okt_subst. rewrite concat_empty_l. eauto.
      rewrite A.
      rewrite <- EqF. apply* wft_subst. rewrite concat_empty_l. eauto.
      apply ok_from_okt. apply* okt_subst. rewrite concat_empty_l. eauto.
  - destruct e as [z ?]. subst. simpl.
    admit. (* tricky because of non-generalization *)
Grab Existential Variables.
pick_fresh y. apply y.
pick_fresh y. apply y.
pick_fresh y. apply y.
pick_fresh y. apply y.
Qed.

Lemma sub_through_subst : forall Q Z S T u,
  sub (Z ~ Q) S T ->
  possible_types u Q ->
  sub empty (subst_t Z u S) (subst_t Z u T).
Proof.
  introv Hsub Hpt.
  inductions Hsub; introv; simpl subst_t;
  try assert (wfe empty u) as Hwu by solve [ apply* possible_types_wfe ];
  try assert (value u) as Hvu by solve [ apply* possible_types_value ].
  - apply* sub_top. apply* wft_subst_empty.
  - simpl. apply* sub_refl_sel.
    assert (typ_sel (subst_e Z u t) = subst_t Z u (typ_sel t)) as A by auto.
    rewrite A. apply* wft_subst_empty.
  - inversion H; subst.
    + apply binds_single_inv in H1. destruct H1. subst.
      inversion Hpt; subst. simpl. rewrite If_l; eauto. rewrite (proj1 subst_fresh).
      eapply sub_trans. eapply sub_sel1. eapply has_mem; eauto. eauto.
      apply* notin_fv_wf.
    + apply has_trm_mem_empty in H; eauto.
      rewrite (proj2 subst_fresh). rewrite (proj1 subst_fresh).
      apply* sub_sel1. apply* notin_fv_wf. simpl. apply* notin_fv_wf.
    + destruct H0 as [x Eq]. subst.
    edestruct H as [IH | IH]; eauto.
    + apply* sub_sel1.
    + destruct IH as [Eq [P [IH1 IH2]]]. rewrite Eq.
      eapply sub_trans.
      eapply sub_sel1. eapply has_weakening_empty. eapply has_empty_mem_b. eassumption.
      auto*. assumption.
  - apply* sub_sel2.
  - apply* sub_mem_false.
  - apply* sub_mem_true.
  - apply_fresh* sub_all as X.
    rewrite* subst_t_open_t_var. rewrite* subst_t_open_t_var.
    apply_ih_map_bind* H0.
  - apply* sub_trans.
  - case_var.
    + apply binds_middle_eq_inv in b; eauto. subst.
      apply has_sub with (T:=P). eexists. reflexivity. apply has_var. apply* okt_subst.
      apply binds_concat_left_ok. apply ok_from_okt. apply* okt_subst. assumption.
      rewrite (proj1 subst_fresh). apply_empty* sub_weakening1.
      apply* (@notin_fv_wf E0).
    + destruct (binds_concat_inv b) as [?|[? ?]].
      apply* has_var.
      destruct (binds_push_inv H0) as [[? ?]|[? ?]].
        subst. false~.
        applys has_var. apply* okt_subst. apply* binds_concat_left.
        rewrite (proj1 subst_fresh). assumption.
        apply* (@notin_fv_wf E0). apply* wft_from_env_has.
  - apply* has_mem. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
  - eapply has_sub.
    destruct e as [z ?]. subst. simpl.
    case_var. eexists. reflexivity. eexists. reflexivity.
    eauto. eauto.
Qed.

Lemma sub_has_through_subst : (forall E0 S T, sub E0 S T -> forall Q Z u,
  E0 = (Z ~ Q) ->
  possible_types u Q ->
  sub empty (subst_t Z u S) (subst_t Z u T)).
Proof.
  eapply sub_ind; intros; subst; simpl;
  try assert (wfe E0 u) as Hwu by solve [
    apply wfe_weaken_empty; [ apply* possible_types_wfe |
    apply ok_from_okt in o; apply ok_remove in o; auto ]];
  try assert (value u) as Hvu by solve [ apply* possible_types_value ].
  - apply* sub_top. apply* wft_subst.
  - simpl. apply* sub_refl_sel.
    assert (typ_sel (subst_e Z u t) = subst_t Z u (typ_sel t)) as A by auto.
    rewrite A. apply* wft_subst.
  - edestruct H as [IH | IH]; eauto.
    + apply* sub_sel1.
    + destruct IH as [Eq [P [IH1 IH2]]]. rewrite Eq.
      eapply sub_trans.
      eapply sub_sel1. eapply has_weakening_empty. eapply has_empty_mem_b. eassumption.
      auto*. assumption.
  - apply* sub_sel2.
  - apply* sub_mem_false.
  - apply* sub_mem_true.
  - apply_fresh* sub_all as X.
    rewrite* subst_t_open_t_var. rewrite* subst_t_open_t_var.
    apply_ih_map_bind* H0.
  - apply* sub_trans.
  - case_var.
    + apply binds_middle_eq_inv in b; eauto. subst.
      apply has_sub with (T:=P). eexists. reflexivity. apply has_var. apply* okt_subst.
      apply binds_concat_left_ok. apply ok_from_okt. apply* okt_subst. assumption.
      rewrite (proj1 subst_fresh). apply_empty* sub_weakening1.
      apply* (@notin_fv_wf E0).
    + destruct (binds_concat_inv b) as [?|[? ?]].
      apply* has_var.
      destruct (binds_push_inv H0) as [[? ?]|[? ?]].
        subst. false~.
        applys has_var. apply* okt_subst. apply* binds_concat_left.
        rewrite (proj1 subst_fresh). assumption.
        apply* (@notin_fv_wf E0). apply* wft_from_env_has.
  - apply* has_mem. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
  - eapply has_sub.
    destruct e as [z ?]. subst. simpl.
    case_var. eexists. reflexivity. eexists. reflexivity.
    eauto. eauto.
Qed.

Lemma sub_has_through_subst : (forall E0 S T, sub E0 S T -> forall Q E F Z u,
  E0 = (E & Z ~ Q & F) ->
  possible_types u Q ->
  sub (E & map (subst_t Z u) F) (subst_t Z u S) (subst_t Z u T)) /\
  (forall E0 p T, has E0 p T -> forall Q E F Z u,
  E0 = (E & Z ~ Q & F) ->
  possible_types u Q ->
  ((has (E & map (subst_t Z u) F) (subst_e Z u p) (subst_t Z u T)) \/
   ((subst_e Z u p)=u /\ exists P, has empty u (typ_mem true P) /\ sub (E & map (subst_t Z u) F) (typ_mem true P) (subst_t Z u T)))).
Proof.
  apply sub_has_mutind; intros; subst; simpl;
  try assert (wfe E0 u) as Hwu by solve [
    apply wfe_weaken_empty; [ apply* possible_types_wfe |
    apply ok_from_okt in o; apply ok_remove in o; auto ]];
  try assert (value u) as Hvu by solve [ apply* possible_types_value ].
  - apply* sub_top. apply* wft_subst.
  - simpl. apply* sub_refl_sel.
    assert (typ_sel (subst_e Z u t) = subst_t Z u (typ_sel t)) as A by auto.
    rewrite A. apply* wft_subst.
  - edestruct H as [IH | IH]; eauto.
    + apply* sub_sel1.
    + destruct IH as [Eq [P [IH1 IH2]]]. rewrite Eq.
      eapply sub_trans.
      eapply sub_sel1. eapply has_weakening_empty. eapply has_empty_mem_b. eassumption.
      auto*. assumption.
  - apply* sub_sel2.
  - apply* sub_mem_false.
  - apply* sub_mem_true.
  - apply_fresh* sub_all as X.
    rewrite* subst_t_open_t_var. rewrite* subst_t_open_t_var.
    apply_ih_map_bind* H0.
  - apply* sub_trans.
  - case_var.
    + apply binds_middle_eq_inv in b; eauto. subst.
      apply has_sub with (T:=P). eexists. reflexivity. apply has_var. apply* okt_subst.
      apply binds_concat_left_ok. apply ok_from_okt. apply* okt_subst. assumption.
      rewrite (proj1 subst_fresh). apply_empty* sub_weakening1.
      apply* (@notin_fv_wf E0).
    + destruct (binds_concat_inv b) as [?|[? ?]].
      apply* has_var.
      destruct (binds_push_inv H0) as [[? ?]|[? ?]].
        subst. false~.
        applys has_var. apply* okt_subst. apply* binds_concat_left.
        rewrite (proj1 subst_fresh). assumption.
        apply* (@notin_fv_wf E0). apply* wft_from_env_has.
  - apply* has_mem. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
  - eapply has_sub.
    destruct e as [z ?]. subst. simpl.
    case_var. eexists. reflexivity. eexists. reflexivity.
    eauto. eauto.
Qed.

Lemma typing_through_subst_z : forall U E F z T e u x P,
  typing (E & z ~ U & F) e T ->
  trm_fvar x = u -> binds x P E -> sub E P U ->
  typing (E & (map (subst_t z u) F)) (subst_e z u e) (subst_t z u T).
Proof.
  introv TypT EqU Bi TypU.
  inductions TypT; introv; subst; simpl.
  - case_var.
    + binds_get H0.
      rewrite (proj1 subst_fresh).
      apply typing_sub with (S:=P).
      apply_empty typing_weakening. apply* typing_var.
      apply* okt_subst. apply_empty* sub_weakening.
      apply* (@notin_fv_wf E).
    + binds_cases H0.
      rewrite (proj1 subst_fresh). eapply typing_var; eauto.
      apply (@notin_fv_wf E). eapply wft_from_env_has. auto*. eapply B0. auto*.
      apply* typing_var.
  - apply_fresh* typing_abs as y.
    rewrite* subst_e_open_e_var. rewrite* subst_t_open_t_var.
    rewrite <- concat_assoc_map_push.
    eapply H0; eauto. rewrite concat_assoc. auto.
  - apply* typing_mem. apply* wft_subst. apply ok_from_okt. apply* okt_subst.
  - eapply typing_app. eapply IHTypT1; eauto. eapply IHTypT2; eauto.
    apply* wft_subst.
    apply ok_from_okt. apply* okt_subst.
  - eapply typing_appvar. eapply IHTypT1; eauto. eapply IHTypT2; eauto.
    apply* (proj2 sub_has_through_subst_z).
    eapply subst_t_open_t. auto*. apply* wft_subst.
    apply ok_from_okt. apply* okt_subst.
  - eapply typing_sub. eapply IHTypT; eauto.
    eapply (proj1 sub_has_through_subst_z); eauto.
Qed.

Lemma typing_through_subst : forall V y v e T,
  typing (y ~ V) e T ->
  value v -> typing empty v V ->
  typing empty (subst_e y v e) (subst_t y v T).
Proof.
  admit.
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma value_red_contra: forall e e',
  value e -> red e e' -> False.
Proof.
  introv Hv Hr. inversion Hv; subst; inversion Hr; subst; eauto.
Qed.

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen_eq E: (@empty typ). gen e'.
  induction Typ; introv QEQ; introv Red;
   try solve [inversion Typ; congruence]; try solve [ inversion Red ].
  - (* case: app *)
    inversions Red; try solve [ apply* typing_app ].
    destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
     apply* sub_reflexivity.
     pick_fresh X. forwards~ K: (P2 X). destruct K.
      rewrite* (@subst_e_intro X).
      erewrite <- (proj1 subst_fresh).
      eapply typing_through_subst.
      eapply typing_sub. eapply typing_narrowing_empty. eapply P1. eassumption.
      rewrite <- (@open_t_var_type X).
      assert (X \notin L) as FrL by auto.
      specialize (P2 X FrL). destruct P2 as [P2t P2s].
      eassumption. apply* wft_type. assumption. assumption. auto*.
  - (* case: appvar *)
    inversions Red; try solve [ apply* typing_appvar ].
    lets HV2: (has_empty_value H). false. eapply value_red_contra in HV2; eauto.
    destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_t_intro X).
     rewrite* (@subst_e_intro X).
     eapply typing_through_subst.
     eapply typing_sub. eapply typing_narrowing_empty. eapply P1. eassumption.
     assert (X \notin L) as FrL by auto.
     specialize (P2 X FrL). destruct P2 as [P2t P2s].
     eassumption. assumption. assumption.
  - (* case sub *)
    apply* typing_sub.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)

(* ********************************************************************** *)
(** Progress Result (16) *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
  induction Typ; intros EQ; subst.
  - (* case: var *)
    false* binds_empty_inv.
  - (* case: abs *)
    left*.
  - (* case: mem *)
    left*.
  - (* case: app *)
    right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (open_e e3 e2).
  - (* case: appvar *)
    right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (open_e e3 e2).
  - (* case: sub *)
    auto*.
Qed.

