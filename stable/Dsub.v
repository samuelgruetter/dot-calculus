(*
 DSub (D<:)
 T ::= Top | x.Type | { Type = T } | { Type <: T } | (z: T) -> T^z
 t ::= x | { Type = T } | lambda x:T.t | t t
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

Inductive sub_mode : Set :=
  | notrans : sub_mode
  | oktrans : sub_mode.

Inductive sub : sub_mode -> env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      okt E ->
      wft E S ->
      sub notrans E S typ_top
  | sub_refl_sel : forall E t,
      okt E ->
      wft E (typ_sel t) ->
      sub notrans E (typ_sel t) (typ_sel t)
  | sub_sel1 : forall E U t,
      has E t (typ_mem false U) ->
      sub notrans E (typ_sel t) U
  | sub_sel2 : forall E S S1 t,
      has E t (typ_mem true S1) ->
      sub oktrans E S S1 ->
      sub notrans E S (typ_sel t)
  | sub_mem_false : forall E b1 T1 T2,
      sub oktrans E T1 T2 ->
      sub notrans E (typ_mem b1 T1) (typ_mem false T2)
  | sub_mem_true : forall E T1 T2,
      sub oktrans E T1 T2 -> sub oktrans E T2 T1 ->
      sub notrans E (typ_mem true T1) (typ_mem true T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub oktrans E T1 S1 ->
      (forall x, x \notin L ->
          sub oktrans (E & x ~ T1) (S2 open_t_var x) (T2 open_t_var x)) ->
      sub notrans E (typ_all S1 S2) (typ_all T1 T2)
  | sub_trans_ok : forall E T1 T2,
      sub notrans E T1 T2 ->
      sub oktrans E T1 T2
  | sub_trans : forall E T1 T2 T3,
      sub oktrans E T1 T2 ->
      sub oktrans E T2 T3 ->
      sub oktrans E T1 T3

with has : env -> trm -> typ -> Prop :=
  | has_var : forall E x T,
      okt E ->
      binds x T E ->
      has E (trm_fvar x) T
  | has_mem : forall E T,
      okt E -> wft E T ->
      has E (trm_mem T) (typ_mem true T)
  | has_sub : forall E p T U,
      has E p T ->
      sub oktrans E T U ->
      has E p U
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
  | typing_app : forall T1 E e1 e2 T2 T2',
      typing E e1 (typ_all T1 T2) ->
      typing E e2 T1 ->
      T2' = open_t T2 e2 ->
      wft E T2' ->
      typing E (trm_app e1 e2) T2'
  | typing_sub : forall S E e T,
      typing E e S ->
      sub oktrans E S T ->
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

Definition preservation := forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.

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
  | |- sub _ ?E _ _  => E
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

Lemma sub_has_regular : (forall m E S T,
  sub m E S T -> okt E /\ wft E S /\ wft E T) /\ (forall E p T,
  has E p T -> okt E /\ wft E (typ_sel p) /\ wft E T).
Proof.
  apply sub_has_mutind; intros; try auto*.
  splits*. destruct H as [? [? A]]. inversion A; subst. assumption.
  split. auto*. split;
   apply_fresh* wft_all as Y;
    forwards~: (H0 Y); apply_empty* (@wft_narrow T1).
  splits*. apply wft_sel. left. apply value_mem. apply* wfe_term. apply* wfe_mem.
Qed.

Lemma sub_regular : forall m E S T,
  sub m E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  intros. apply* (proj1 sub_has_regular).
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
  | H: sub _ _ _ _ |- _ => apply (proj31 (sub_regular H))
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (wft ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj33 (typing_regular H))
  | H: sub _ E T _ |- _ => apply (proj32 (sub_regular H))
  | H: sub _ E _ T |- _ => apply (proj33 (sub_regular H))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (@wft_type E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub _ ?E T _ |- _ => go E
  | H: sub _ ?E _ T |- _ => go E
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj32 (typing_regular H))
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
  sub notrans E T T .
Proof.
  Hint Resolve sub_trans_ok.
  introv Ok WI. lets W: (wft_type WI). gen E.
  induction W; intros; inversions WI; eauto.
  destruct b. apply* sub_mem_true. apply* sub_mem_false.
  apply_fresh* sub_all as Y.
Qed.

(* ********************************************************************** *)
(** Weakening (2) *)

Lemma sub_has_weakening : (forall m E0 S T, sub m E0 S T -> forall E F G,
   E0 = E & G ->
   okt (E & F & G) ->
   sub m (E & F & G) S T) /\ (forall E0 p T, has E0 p T -> forall E F G,
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
  apply* has_sub.
Qed.

Lemma sub_weakening : forall m E F G S T,
   sub m (E & G) S T ->
   okt (E & F & G) ->
   sub m (E & F & G) S T.
Proof.
  intros. apply* (proj1 sub_has_weakening).
Qed.

Lemma sub_weakening1 : forall m E F G S T,
   sub m E S T ->
   okt (E & F & G) ->
   sub m (E & F & G) S T.
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

(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

Definition transitivity_on Q := forall E S T,
  sub oktrans E S Q -> sub oktrans E Q T -> sub oktrans E S T.

Hint Unfold transitivity_on.

Hint Resolve wft_narrow.

Lemma sub_narrowing_aux : forall Q m F E z P S T,
  transitivity_on Q ->
  sub m (E & z ~ Q & F) S T ->
  sub oktrans E P Q ->
  sub m (E & z ~ P & F) S T.
Proof.
  introv TransQ SsubT PsubQ.
  inductions SsubT; introv.
  apply* sub_top.
  apply* sub_refl_sel.
  tests EQ: (x = z).
    lets M: (@okt_narrow Q).
    apply (@sub_sel1 P).
      asserts~ N: (ok (E & z ~ P & F)).
       lets: ok_middle_inv_r N.
       apply~ binds_middle_eq.
      apply TransQ.
        do_rew* concat_assoc (apply_empty* sub_weakening).
        binds_get H. auto*.
    apply* (@sub_sel1 T). binds_cases H; auto.
  tests EQ: (x = z).
    lets M: (@okt_narrow Q).
    apply (@sub_sel2 P) with (S1:=S1).
      asserts~ N: (ok (E & z ~ P & F)).
       lets: ok_middle_inv_r N.
       apply~ binds_middle_eq.
      apply TransQ.
        do_rew* concat_assoc (apply_empty* sub_weakening).
        binds_get H. auto*. auto*.
    apply* (@sub_sel2 T). binds_cases H; auto.
  apply* sub_selc1.
  apply* sub_selc2.
  apply* sub_mem_false.
  apply* sub_mem_true.
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
  apply* sub_trans_ok.
  apply* sub_trans.
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof.
  intro Q. introv SsubQ QsubT.
  eapply sub_trans; eauto.
Qed.

Lemma sub_narrowing : forall Q m E F Z P S T,
  sub oktrans E P Q ->
  sub m (E & Z ~ Q & F) S T ->
  sub m (E & Z ~ P & F) S T.
Proof.
  intros.
  apply* sub_narrowing_aux.
  apply* sub_transitivity.
Qed.

Inductive notvar : typ -> Prop :=
  | notvar_top   : notvar typ_top
  | notvar_mem   : forall b T, notvar (typ_mem b T)
  | notvar_all   : forall T1 T2, notvar (typ_all T1 T2).

Hint Constructors notvar.

Lemma sub_trans_notvar : forall E T1 T2 T3,
  notvar T2 ->
  sub notrans E T1 T2 ->
  sub notrans E T2 T3 ->
  sub notrans E T1 T3.
Proof.
  introv Hnotsel H12 H23.
  inversion Hnotsel; subst.
  - (* case top *)
    inversion H23; subst.
    + apply* sub_top.
    + apply* sub_sel2. apply* sub_trans.
    + apply* sub_selc2. apply* sub_trans.
  - (* case mem *)
    inversion H23; subst.
    + apply* sub_top.
    + apply* sub_sel2. eapply sub_trans; eauto.
    + apply* sub_selc2. eapply sub_trans; eauto.
    + inversion H12; subst.
      * eapply sub_sel1; eauto.
        eapply sub_trans. eapply H0. eapply sub_trans_ok. eapply sub_mem_false.
        eapply sub_trans_ok. assumption.
      * eapply sub_selc1; eauto.
        eapply sub_trans. eassumption. eapply sub_trans_ok.
        eapply sub_mem_false. assumption.
      * eapply sub_mem_false; eauto using sub_trans, sub_trans_ok.
      * eapply sub_mem_false; eauto using sub_trans, sub_trans_ok.
    + inversion H12; subst.
      * eapply sub_sel1; eauto.
        eapply sub_trans. eapply H0. eapply sub_trans_ok. eapply sub_mem_false.
        eapply sub_trans_ok. assumption.
      * eapply sub_selc1; eauto.
        eapply sub_trans. eassumption. eapply sub_trans_ok.
        eapply sub_mem_true. assumption. assumption.
      * eapply sub_mem_true; eauto using sub_trans, sub_trans_ok.
  - (* case all *)
    inversion H12; inversion H23; subst; auto.
    + apply* sub_sel2; eauto using sub_trans, sub_trans_ok.
    + apply* sub_selc2; eauto using sub_trans, sub_trans_ok.
    + apply* sub_sel1; eauto using sub_trans, sub_trans_ok.
      eapply sub_trans. eapply H0. eapply sub_trans_ok.
      eapply sub_mem_false. eapply sub_trans_ok. assumption.
    + apply* sub_selc1; eauto using sub_trans, sub_trans_ok.
    + apply* sub_selc1; eauto using sub_trans, sub_trans_ok.
    + apply* sub_selc1; eauto using sub_trans, sub_trans_ok.
    + apply* sub_sel2; eauto using sub_trans, sub_trans_ok.
    + apply* sub_selc2; eauto using sub_trans, sub_trans_ok.
    + apply sub_all with (L:=L \u L0); eauto using sub_trans.
      intros Y Fr.
      apply sub_trans with (T2:=(T4 open_t_var Y)).
      assert ((E & Y ~ T6) = (E & Y ~ T6 & empty)) as A. {
        rewrite concat_empty_r. reflexivity.
      }
      rewrite A.
      apply* (@sub_narrowing T0).
      rewrite concat_empty_r.
      eauto.
      eauto.
Qed.

Inductive follow_ub : env -> typ -> typ -> Prop :=
  | follow_ub_nil : forall E T,
      wft E T ->
      follow_ub E T T
  | follow_ub_cons : forall E x TX Hi T,
      binds x TX E ->
      sub oktrans E TX (typ_mem false Hi) ->
      follow_ub E Hi T ->
      follow_ub E (typ_sel (trm_fvar x)) T
  | follow_ub_cons_c : forall E Hi T,
      follow_ub E Hi T ->
      follow_ub E (typ_sel (trm_mem Hi)) T.

Inductive follow_lb : env -> typ -> typ -> Prop :=
  | follow_lb_nil : forall E T,
      wft E T ->
      follow_lb E T T
  | follow_lb_cons : forall E x TX Lo T,
      binds x TX E ->
      sub oktrans E TX (typ_mem true Lo) ->
      follow_lb E (typ_sel (trm_fvar x)) T ->
      follow_lb E Lo T
  | follow_lb_cons_c : forall E Lo T,
      follow_lb E (typ_sel (trm_mem Lo)) T ->
      follow_lb E Lo T.


Hint Constructors follow_ub.
Hint Constructors follow_lb.

Lemma follow_lb_reg : forall E T1 T2,
  follow_lb E T1 T2 ->
  wft E T1 /\ wft E T2.
Proof.
  introv H. induction H; auto.
  split.
  apply sub_regular in H0. destruct H0 as [? [? A]]. inversion A; subst. assumption.
  inversion IHfollow_lb. auto.
  destruct IHfollow_lb as [A B].
  split. inversion A; subst.  inversion H3; subst. assumption. assumption.
Qed.

Lemma invert_follow_lb : forall E T1 T2,
  follow_lb E T1 T2 ->
  (T1 = T2) \/
  (exists t1 t2 Hi, (typ_sel X2) = T2 /\
    binds X1 (bind_sub T1 Hi) E /\
    sub oktrans E T1 Hi /\
    follow_lb E (typ_fvar X1) (typ_fvar X2)) \/
  ().
Proof.
  intros.
  induction H.
  auto.
  destruct IHfollow_lb as [IH | IH].
  subst.
  right. exists X X Hi. auto.
  right.
    destruct IH as [X1 [X2 [Hi' [Heq [IH1 [IH2 IH3]]]]]].
    subst.
    exists X X2 Hi. auto.
Qed.

Definition st_middle (E: env) (B C: typ) : Prop :=
  B = C \/
  sub notrans E typ_top C \/
  (notvar B /\ sub notrans E B C).

Definition chain (E: env) (A D: typ): Prop :=
  (exists B C, follow_ub E A B /\ st_middle E B C /\ follow_lb E C D).

Lemma empty_chain: forall E T, wft E T -> chain E T T.
Proof.
  intros.
  unfold chain. unfold st_middle.
  exists T T.
  auto.
Qed.

Lemma chain3sub: forall E C1 C2 D,
  sub notrans E C1 C2 ->
  follow_lb E C2 D ->
  sub notrans E C1 D.
Proof.
  introv Hst Hflb.
  induction Hflb.
  assumption.
  apply IHHflb.
  eapply sub_trans_tvar_lower; eauto using sub_trans_ok.
Qed.

Lemma chain2sub: forall E B1 B2 C D,
  sub notrans E B1 B2 ->
  st_middle E B2 C ->
  follow_lb E C D ->
  sub notrans E B1 D.
Proof.
  introv Hst Hm Hflb.
  unfold st_middle in Hm.
  destruct Hm as [Hm | [Hm | [Hm1 Hm2]]]; subst.
  apply (chain3sub Hst Hflb).
  apply chain3sub with (C2:=C).
    apply sub_trans_notvar with (T2:=typ_top); auto.
    apply Hflb.
  apply chain3sub with (C2:=C).
    apply sub_trans_notvar with (T2:=B2); auto.
    apply Hflb.
Qed.


Lemma chain1sub: forall E A B C D,
  okt E ->
  follow_ub E A B ->
  st_middle E B C ->
  follow_lb E C D ->
  sub notrans E A D.
Proof.
  introv Hok Hfub Hm Hflb.
  induction Hfub.
  apply chain2sub with (B2:=T) (C:=C); try assumption.
    apply sub_reflexivity; auto.
  apply* sub_trans_tvar.
    apply sub_trans_ok.
    apply* IHHfub.
Qed.

Lemma prepend_chain: forall E A1 A2 D,
  sub oktrans E A1 A2 ->
  chain E A2 D ->
  chain E A1 D.
Proof.
  fix 5.
  introv Hsub Hch.
  unfold chain in *. unfold st_middle in *.
  inversion Hsub; inversion H; subst.
  - (* case top *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]]; subst.
    + exists A1 typ_top. auto 10.
    + exists A1 C. auto 10.
    + exists A1 C. auto 10.
  - (* case bot *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    exists typ_bot C.
    assert (wft E C) as HwfC. {
      apply follow_lb_reg in Hch3. inversion Hch3. assumption.
    }
    auto 10.
  - (* case refl_tvar *)
    assumption.
  - (* case trans_tvar *)
    set (IH := (prepend_chain E T3 A2 D H5 Hch)).
    destruct IH as [B [C [IH1 [IH2 IH3]]]].
    exists B C.
    split.
    eapply follow_ub_cons. eassumption. assumption. assumption.
    split; assumption.
  - (* case trans_tvar_lower *)
    set (Hch' := Hch).
    destruct Hch' as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    + destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
      subst.
      apply (prepend_chain E A1 T0 D H5).
      exists T0 T0.
      set (Hflb := (follow_lb_cons H0 H4 Hch3)).
      auto.
      exists A1 C.
      splits.
      apply follow_ub_nil. auto.
      right. left. apply Hch2. apply Hch3.
      inversion Hch2a.
    + assert (bind_sub Lo Hi = bind_sub T0 T3) as Heq. {
        eapply binds_func; eassumption.
      }
      inversions Heq.
      apply (prepend_chain E A1 T0 D H5).
      apply (prepend_chain E T0 T3 D H4).
      exists B C.
      splits.
      assumption.
      assumption.
      assumption.
  - (* case arrow *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    exists (typ_arrow S1 S2) C.
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
    subst.
    auto 10.
    auto 10.
    set (Hst := (sub_trans_notvar (notvar_arrow _ _) H Hch2b)).
    auto 10.
  - (* case refl_all *)
    assumption.
  - (* case all *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    exists (typ_all S0 S1 S2) C.
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
    subst.
    auto 10.
    auto 10.
    set (Hst := (sub_trans_notvar (notvar_all _ _ _) H Hch2b)).
    auto 10.
  - (* case trans_ok *)
    apply (prepend_chain E _ _ _ H (prepend_chain E _ _ _ H0 Hch)).
  - (* case trans *)
    apply (prepend_chain E _ _ _ H (prepend_chain E _ _ _ H0 Hch)).
Qed.

Lemma sub_trans_pushback : forall E T1 T3,
  sub oktrans E T1 T3 ->
  sub notrans E T1 T3.
Proof.
  introv Hst.
  inversion Hst; subst.
  assumption.
  assert (wft E T3) as HwfT3 by auto.
  assert (okt E) as Hok by auto.
  set (Hch := (prepend_chain H (prepend_chain H0 (empty_chain HwfT3)))).
  unfold chain in Hch.
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  apply (chain1sub Hok Hch1 Hch2 Hch3).
Qed.

End NarrowTrans.

Lemma contra_all_mem: forall E V T1 U,
  sub E (typ_all V T1) (typ_mem false U) ->
  False.
Proof.
  introv Hsub. remember (typ_all V T1) as LHS. remember (typ_mem false U) as RHS.
  gen HeqLHS. gen HeqRHS. gen V T1 U.
  induction Hsub; intros; try solve [inversion HeqRHS]; try solve [inversion HeqLHS].
  subst. inversion Hsub1; subst.
  assert (H
  eapply IHHsub2. reflexivity.
Lemma mem_inv_val: forall u Q U E F,
  value u ->
  typing E u Q ->
  sub (E & F) Q (typ_mem false U) ->
  exists S, sub (E & F) S U /\ trm_mem S = u.
Proof.
  introv VU TU Sub. gen VU. generalize dependent F. generalize dependent U.
  induction TU; intros; subst; try solve [inversion VU].
  inversion Sub

Lemma mem_inv: forall u Q U E F,
  (value u \/ (exists x, trm_fvar x = u)) ->
  typing E u Q ->
  sub (E & F) Q (typ_mem false U) ->
  (exists S, sub (E & F) S U /\
  (trm_mem S = u \/ (exists x, trm_fvar x = u /\ binds x S E))).
Proof.
  introv VU.  destruct VU as [VU | [x Eq]].

(* ********************************************************************** *)
(** Substitution preserves subtyping (10) *)

Lemma sub_through_subst : forall Q E F Z S T u,
  sub (E & Z ~ Q & F) S T ->
  (value u \/ exists x, trm_fvar x = u) -> typing E u Q ->
  sub (E & map (subst_t Z u) F) (subst_t Z u S) (subst_t Z u T).
Proof.
  introv SsubT VU TU.
  assert (wfe E u) as WU by solve [apply typing_regular in TU; auto*].
  inductions SsubT; introv.
  - apply* sub_top.
  - simpl. apply* sub_refl_sel.
    assert (typ_sel (subst_e Z u t) = subst_t Z u (typ_sel t)) as A by auto.
    rewrite A. auto*.
  - simpl. case_var.
    + apply binds_middle_eq_inv in H; eauto. subst.
      apply sub_selc1.
      assert (sub (E & map (subst_tb Z P) F) (typ_mem true P) (typ_mem false (subst_t Z (trm_mem P) U))) as A. {
        apply (@sub_transitivity Q).
        apply_empty* sub_weakening.
        rewrite* <- ((proj1 subst_fresh) Q Z (trm_mem P)).
        apply* (@notin_fv_wf E).
      }
      inversion A; subst. apply* sub_selc1.
    + binds_cases H.
      * apply sub_sel1 with (T:=T). auto.
        rewrite* <- ((proj1 subst_fresh) T Z (trm_mem P)).
        apply* (@notin_fv_wf E). apply* wft_from_env_has.
      * apply sub_sel1 with (T:=subst_tb Z P T).
        rewrite* (@map_subst_id E Z (trm_mem P)).
        auto*.
  - repeat unfold subst_tb at 2; simpl subst_t. case_var.
    + apply binds_middle_eq_inv in H; eauto. subst.
      assert (sub (E & map (subst_tb Z P) F) (typ_mem true P) (typ_mem true (subst_t Z (trm_mem P) S1))) as A. {
        apply (@sub_transitivity Q).
        apply_empty* sub_weakening.
        rewrite* <- ((proj1 subst_fresh) Q Z (trm_mem P)).
        apply* (@notin_fv_wf E).
      }
      inversion A; subst. apply sub_selc2.
      apply (@sub_transitivity (subst_tb Z P S1)). auto*. auto*.
    + binds_cases H.
      * apply sub_sel2 with (T:=T) (S1:=subst_tb Z P S1). auto.
        rewrite* <- ((proj1 subst_fresh) T Z (trm_mem P)).
        apply* (@notin_fv_wf E). apply* wft_from_env_has.
        auto*.
      * apply sub_sel2 with (T:=subst_tb Z P T) (S1:=subst_tb Z P S1).
        rewrite* (@map_subst_id E Z (trm_mem P)).
        auto*. auto*.
  - admit.
  - admit.
  - admit.
  - admit.
  - apply_fresh* sub_all as X.
    rewrite* subst_t_open_t_var. rewrite* subst_t_open_t_var.
    apply_ih_map_bind* H0.
    apply* term_mem. apply* wft_type.
    apply* term_mem. apply* wft_type.
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
  - apply* typing_sub. apply* (@sub_narrowing Q).
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (E & x ~: U & F) e T ->
  typing E u U ->
  typing (E & F) (subst_ee x u e) T.
Proof.
  introv TypT TypU. inductions TypT; introv; simpl.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    rewrite* subst_ee_open_te_var.
    apply_ih_bind* H0.
  apply* typing_tapp. apply* sub_strengthening.
  apply* typing_sub. apply* sub_strengthening.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (E & Z ~<: Q & F) e T ->
  sub E P Q ->
  typing (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ PsubQ.
  inductions Typ; introv; simpls subst_tt; simpls subst_te.
  apply* typing_var. rewrite* (@map_subst_tb_id E Z P).
   binds_cases H0; unsimpl_map_bind*.
  apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var.
    apply_ih_map_bind* H0.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P (bind_sub V)).
    rewrite* subst_te_open_te_var.
    rewrite* subst_tt_open_tt_var.
    apply_ih_map_bind* H0.
  rewrite* subst_tt_open_tt. apply* typing_tapp.
    apply* sub_through_subst_tt.
  apply* typing_sub. apply* sub_through_subst_tt.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (trm_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) S2 /\ sub E S2 U2.
Proof.
  introv Typ. gen_eq e: (trm_abs S1 e1). gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub. auto* (@sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (trm_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X \notin L ->
     typing (E & X ~<: U1) (e1 open_te_var X) (S2 open_tt_var X)
     /\ sub (E & X ~<: U1) (S2 open_tt_var X) (U2 open_tt_var X).
Proof.
  intros E S1 e1 T H. gen_eq e: (trm_tabs S1 e1). gen S1 e1.
  induction H; intros S1 b EQ U1 U2 Sub; inversion EQ.
  inversions Sub. splits. auto.
   exists T1. let L1 := gather_vars in exists L1.
   intros Y Fr. splits.
    apply_empty* (@typing_narrowing S1). auto.
  auto* (@sub_transitivity T).
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red;
   try solve [ inversion Red ].
  (* case: app *)
  inversions Red; try solve [ apply* typing_app ].
  destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).
       apply* (@typing_sub S2). apply_empty* sub_weakening.
       auto*.
  (* case: tapp *)
  inversions Red; try solve [ apply* typing_tapp ].
  destruct~ (typing_inv_tabs Typ (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_te_intro X).
     rewrite* (@subst_tt_intro X).
     (* todo: apply empty here *)
     asserts_rewrite (E = E & map (subst_tb X T) empty).
       rewrite map_empty. rewrite~ concat_empty_r.
     apply* (@typing_through_subst_te T1).
       rewrite* concat_empty_r.
  (* case sub *)
  apply* typing_sub.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow U1 U2) ->
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_arrow U1 U2). gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. inversion H.
      false (binds_empty_inv H0).
      inversions H0. forwards*: IHTyp.
Qed.

Lemma canonical_form_tabs : forall t U1 U2,
  value t -> typing empty t (typ_all U1 U2) ->
  exists V, exists e1, t = trm_tabs V e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_all U1 U2). gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. inversion H.
      false* binds_empty_inv.
      inversions H0. forwards*: IHTyp.
Qed.

(* ********************************************************************** *)
(** Progress Result (16) *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty bind). lets Typ': Typ.
  induction Typ; intros EQ; subst.
  (* case: var *)
  false* binds_empty_inv.
  (* case: abs *)
  left*.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (open_ee e3 e2).
  (* case: tabs *)
  left*.
  (* case: tapp *)
  right. destruct~ IHTyp as [Val1 | [e1' Rede1']].
    destruct (canonical_form_tabs Val1 Typ) as [S [e3 EQ]].
      subst. exists* (open_te e3 T).
      exists* (trm_tapp e1' T).
  (* case: sub *)
  auto*.
Qed.

