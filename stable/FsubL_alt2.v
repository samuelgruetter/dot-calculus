(***************************************************************************
  Preservation and Progress for System-F
  with Subtyping, Bottom and Lower Bounds

- based on the POPLMark solution of
  Brian Aydemir & Arthur Charguéraud, March 2007
  cf. https://github.com/samuelgruetter/dot-calculus/blob/master/ln/Fsub_Definitions.v
  cf. https://github.com/samuelgruetter/dot-calculus/blob/master/ln/Fsub_Infrastructure.v
  cf. https://github.com/samuelgruetter/dot-calculus/blob/master/ln/Fsub_Part1A.v

- compared to FsubL, simpler pushback argument

***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.
Implicit Types X : var.

(***************************************************************************
* Definitions                                                              *
***************************************************************************)

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ : Set :=
  | typ_top   : typ
  | typ_bot   : typ
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ -> typ -> typ.

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_tabs : typ -> typ -> trm -> trm
  | trm_tapp : trm -> typ -> trm.

(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_bot         => typ_bot
  | typ_bvar J      => If K = J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T0 T1 T2   => typ_all (open_tt_rec K U T0) (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm_app e1 e2 => trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | trm_tabs VS VU e1 => trm_tabs (open_tt_rec K U VS) (open_tt_rec K U VU)  (open_te_rec (S K) U e1)
  | trm_tapp e1 V => trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Definition open_te t U := open_te_rec 0 U t.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs V (open_ee_rec (S k) f e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm_tabs VS VU e1 => trm_tabs VS VU (open_ee_rec k f e1)
  | trm_tapp e1 V => trm_tapp (open_ee_rec k f e1) V
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_bot :
      type typ_bot
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T0 T1 T2,
      type T0 ->
      type T1 ->
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (typ_all T0 T1 T2).

(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1,
      type V ->
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs V e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2)
  | term_tabs : forall L VS VU e1,
      type VS ->
      type VU ->
      (forall X, X \notin L -> term (e1 open_te_var X)) ->
      term (trm_tabs VS VU e1)
  | term_tapp : forall e1 V,
      term e1 ->
      type V ->
      term (trm_tapp e1 V).

(** Binding are either mapping type or term variables. *)

Inductive bind : Set :=
  | bind_sub : typ -> typ -> bind
  | bind_typ : typ -> bind.

(** Environment is an associative list of bindings. *)

Definition env := LibEnv.env bind.

(** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  subtyping relation in E. This predicates implies
  that T is a type *)

Inductive wft : env -> typ -> Prop :=
  | wft_top : forall E,
      wft E typ_top
  | wft_bot : forall E,
      wft E typ_bot
  | wft_var : forall T0 T1 E X,
      binds X (bind_sub T0 T1) E ->
      wft E (typ_fvar X)
  | wft_arrow : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_arrow T1 T2)
  | wft_all : forall L E T0 T1 T2,
      wft E T0 ->
      wft E T1 ->
      (forall X, X \notin L ->
        wft (E & X ~ bind_sub T0 T1) (T2 open_tt_var X)) ->
      wft E (typ_all T0 T1 T2).

(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_sub : forall E X T0 T1,
      okt E -> wft E T0 -> wft E T1 -> X # E -> okt (E & X ~ bind_sub T0 T1)
  | okt_typ : forall E x T,
      okt E -> wft E T -> x # E -> okt (E & x ~ bind_typ T).

(** Subtyping relation *)

Inductive sub_mode : Set :=
  | notrans : sub_mode
  | oktrans : sub_mode.

Inductive sub : sub_mode -> env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      okt E ->
      wft E S ->
      sub notrans E S typ_top
  | sub_bot : forall E T,
      okt E ->
      wft E T ->
      sub notrans E typ_bot T
  | sub_refl_tvar : forall E X,
      okt E ->
      wft E (typ_fvar X) ->
      sub notrans E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall T0 T1 E T X,
      binds X (bind_sub T0 T1) E ->
      sub oktrans E T1 T ->
      sub notrans E (typ_fvar X) T
  | sub_trans_tvar_lower : forall T0 T1 E T X,
      binds X (bind_sub T0 T1) E ->
      sub oktrans E T T0 ->
      sub notrans E T (typ_fvar X)
  | sub_arrow : forall E S1 S2 T1 T2,
      sub oktrans E T1 S1 ->
      sub oktrans E S2 T2 ->
      sub notrans E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S0 S1 S2 T0 T1 T2,
      sub oktrans E S0 T0 ->
      sub oktrans E T1 S1 ->
      (forall X, X \notin L ->
          sub oktrans (E & X ~ bind_sub T0 T1) (S2 open_tt_var X) (T2 open_tt_var X)) ->
      sub notrans E (typ_all S0 S1 S2) (typ_all T0 T1 T2)
  | sub_trans_ok : forall E T1 T2,
      sub notrans E T1 T2 ->
      sub oktrans E T1 T2
  | sub_trans : forall E T1 T2 T3,
      sub oktrans E T1 T2 ->
      sub oktrans E T2 T3 ->
      sub oktrans E T1 T3.

(** Typing relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x (bind_typ T) E ->
      typing E (trm_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~ bind_typ V) (e1 open_ee_var x) T1) ->
      typing E (trm_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (trm_app e1 e2) T2
  | typing_tabs : forall L E VS VU e1 T1,
      (forall X, X \notin L ->
        typing (E & X ~ bind_sub VS VU) (e1 open_te_var X) (T1 open_tt_var X)) ->
      typing E (trm_tabs VS VU e1) (typ_all VS VU T1)
  | typing_tapp : forall T0 T1 E e1 T T2,
      typing E e1 (typ_all T0 T1 T2) ->
      sub oktrans E T0 T ->
      sub oktrans E T T1 ->
      typing E (trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub oktrans E S T ->
      typing E e T.

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1)
  | value_tabs : forall VS VU e1, term (trm_tabs VS VU e1) ->
                 value (trm_tabs VS VU e1).

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
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (trm_tapp e1 V) (trm_tapp e1' V)
  | red_abs : forall V e1 v2,
      term (trm_abs V e1) ->
      value v2 ->
      red (trm_app (trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : forall V0 V1 e1 V2,
      term (trm_tabs V0 V1 e1) ->
      type V2 ->
      red (trm_tapp (trm_tabs V0 V1 e1) V2) (open_te e1 V2).

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
* Infrastructure                                                           *
***************************************************************************)

(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | typ_top         => \{}
  | typ_bot         => \{}
  | typ_bvar J      => \{}
  | typ_fvar X      => \{X}
  | typ_arrow T1 T2 => (fv_tt T1) \u (fv_tt T2)
  | typ_all T0 T1 T2   => (fv_tt T0) \u (fv_tt T1) \u (fv_tt T2)
  end.

(** Computing free type variables in a term *)

Fixpoint fv_te (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{}
  | trm_abs V e1  => (fv_tt V) \u (fv_te e1)
  | trm_app e1 e2 => (fv_te e1) \u (fv_te e2)
  | trm_tabs VS VU e1 => (fv_tt VS) \u (fv_tt VU) \u (fv_te e1)
  | trm_tapp e1 V => (fv_tt V) \u (fv_te e1)
  end.

(** Computing free term variables in a type *)

Fixpoint fv_ee (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs V e1  => (fv_ee e1)
  | trm_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  | trm_tabs VS VU e1 => (fv_ee e1)
  | trm_tapp e1 V => (fv_ee e1)
  end.

(** Substitution for free type variables in types. *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_bot         => typ_bot
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => If X = Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T0 T1 T2   => typ_all (subst_tt Z U T0) (subst_tt Z U T1) (subst_tt Z U T2)
  end.

(** Substitution for free type variables in terms. *)

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm_app e1 e2 => trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs VS VU e1 => trm_tabs (subst_tt Z U VS) (subst_tt Z U VU)  (subst_te Z U e1)
  | trm_tapp e1 V => trm_tapp (subst_te Z U e1) (subst_tt Z U V)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs V e1  => trm_abs V (subst_ee z u e1)
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm_tabs VS VU e1 => trm_tabs VS VU (subst_ee z u e1)
  | trm_tapp e1 V => trm_tapp (subst_ee z u e1) V
  end.

(** Substitution for free type variables in environment. *)

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_sub T0 T1 => bind_sub (subst_tt Z P T0) (subst_tt Z P T1)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors type term wft ok okt value red.

Hint Resolve
  sub_top sub_bot sub_refl_tvar sub_arrow
  typing_var typing_app typing_tapp typing_sub.

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv_te x) in
  let D := gather_vars_with (fun x : trm => fv_ee x) in
  let E := gather_vars_with (fun x : typ => fv_tt x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D \u E \u F).

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
  | |- sub _ ?E _ _  => E
  | |- typing ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; auto*.

(** Tactic to undo when Coq does too much simplification *)

Ltac unsimpl_map_bind_sub :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U0) (subst_tt ?Z ?P ?U1) ] =>
    unsimpl ((subst_tb Z P) (B U0 U1)) end.

Ltac unsimpl_map_bind_typ :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U) ] =>
    unsimpl ((subst_tb Z P) (B U)) end.

Tactic Notation "unsimpl_map_bind_sub" "*" :=
  unsimpl_map_bind_sub; auto*.

Tactic Notation "unsimpl_map_bind_typ" "*" :=
  unsimpl_map_bind_typ; auto*.


(* ********************************************************************** *)
(** * Properties of Substitutions *)

(* ********************************************************************** *)
(** ** Properties of type substitution in type *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_tt_rec_type_core : forall T j V U i, i <> j ->
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof.
  induction T; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_tt_rec_type : forall T U,
  type T -> forall k, T = open_tt_rec k U T.
Proof.
  induction 1; intros; simpl; f_equal*. unfolds open_tt.
  pick_fresh X. apply* (@open_tt_rec_type_core T2 0 (typ_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_tt T -> subst_tt Z U T = T.
Proof.
  induction T; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P n, type P ->
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1).
Proof.
  introv WP. generalize n.
  induction T1; intros k; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_tt_rec_type.
Qed.

Lemma subst_tt_open_tt : forall T1 T2 X P, type P ->
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof.
  unfold open_tt. auto* subst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_tt_open_tt_var : forall X Y U T, Y <> X -> type U ->
  (subst_tt X U T) open_tt_var Y = subst_tt X U (T open_tt_var Y).
Proof.
  introv Neq Wu. rewrite* subst_tt_open_tt.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_tt_intro : forall X T2 U,
  X \notin fv_tt T2 -> type U ->
  open_tt T2 U = subst_tt X U (T2 open_tt_var X).
Proof.
  introv Fr Wu. rewrite* subst_tt_open_tt.
  rewrite* subst_tt_fresh. simpl. case_var*.
Qed.


(* ********************************************************************** *)
(** ** Properties of type substitution in terms *)

Lemma open_te_rec_term_core : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros; simpl in *; inversion H; f_equal*; f_equal*.
Qed.

Lemma open_te_rec_type_core : forall e j Q i P, i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
   e = open_te_rec i P e.
Proof.
  induction e; intros; simpl in *; inversion H0; f_equal*;
  match goal with H: ?i <> ?j |- ?t = open_tt_rec ?i _ ?t =>
   apply* (@open_tt_rec_type_core t j) end.
Qed.

Lemma open_te_rec_term : forall e U,
  term e -> forall k, e = open_te_rec k U e.
Proof.
  intros e U WF. induction WF; intros; simpl;
    f_equal*; try solve [ apply* open_tt_rec_type ].
  unfolds open_ee. pick_fresh x.
   apply* (@open_te_rec_term_core e1 0 (trm_fvar x)).
  unfolds open_te. pick_fresh X.
   apply* (@open_te_rec_type_core e1 0 (typ_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_te_fresh : forall X U e,
  X \notin fv_te e -> subst_te X U e = e.
Proof.
  induction e; simpl; intros; f_equal*; auto* subst_tt_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_te_open_te : forall e T X U, type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T).
Proof.
  intros. unfold open_te. generalize 0.
  induction e; intros; simpls; f_equal*;
  auto* subst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_te_open_te_var : forall X Y U e, Y <> X -> type U ->
  (subst_te X U e) open_te_var Y = subst_te X U (e open_te_var Y).
Proof.
  introv Neq Wu. rewrite* subst_te_open_te.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_te_intro : forall X U e,
  X \notin fv_te e -> type U ->
  open_te e U = subst_te X U (e open_te_var X).
Proof.
  introv Fr Wu. rewrite* subst_te_open_te.
  rewrite* subst_te_fresh. simpl. case_var*.
Qed.


(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_ee_rec_type_core : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv H; simpls; inversion H; f_equal*.
Qed.

Lemma open_ee_rec_term : forall u e,
  term e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_ee. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).
  unfolds open_te. pick_fresh X.
   apply* (@open_ee_rec_type_core e1 0 (typ_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_ee e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> term u ->
  (subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_ee e -> term u ->
  open_ee e u = subst_ee x u (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Interactions between type substitutions in terms and opening
  with term variables in terms. *)

Lemma subst_te_open_ee_var : forall Z P x e,
  (subst_te Z P e) open_ee_var x = subst_te Z P (e open_ee_var x).
Proof.
  introv. unfold open_ee. generalize 0.
  induction e; intros; simpl; f_equal*. case_nat*.
Qed.

(** Interactions between term substitutions in terms and opening
  with type variables in terms. *)

Lemma subst_ee_open_te_var : forall z u e X, term u ->
  (subst_ee z u e) open_te_var X = subst_ee z u (e open_te_var X).
Proof.
  introv. unfold open_te. generalize 0.
  induction e; intros; simpl; f_equal*.
  case_var*. symmetry. auto* open_te_rec_term.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_tt_type : forall T Z P,
  type T -> type P -> type (subst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* type_all as X. rewrite* subst_tt_open_tt_var.
Qed.

Lemma subst_te_term : forall e Z P,
  term e -> type P -> term (subst_te Z P e).
Proof.
  lets: subst_tt_type. induction 1; intros; simpl; auto.
  apply_fresh* term_abs as x. rewrite* subst_te_open_ee_var.
  apply_fresh* term_tabs as x. rewrite* subst_te_open_te_var.
Qed.

Lemma subst_ee_term : forall e1 Z e2,
  term e1 -> term e2 -> term (subst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
  apply_fresh* term_tabs as Y. rewrite* subst_ee_open_te_var.
Qed.

Hint Resolve subst_tt_type subst_te_term subst_ee_term.


(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma wft_type : forall E T,
  wft E T -> type T.
Proof.
  induction 1; eauto.
Qed.

(** Through weakening *)

Lemma wft_weaken : forall G T E F,
  wft (E & G) T ->
  ok (E & F & G) ->
  wft (E & F & G) T.
Proof.
  intros. gen_eq K: (E & G). gen E F G.
  induction H; intros; subst; eauto.
  (* case: var *)
  apply (@wft_var T0 T1). apply* binds_weaken.
  (* case: all *)
  apply_fresh* wft_all as Y. apply_ih_bind* H2.
Qed.

Lemma wft_weaken_empty : forall T F,
  wft empty T ->
  ok F ->
  wft F T.
Proof.
  intros. lets A: (@wft_weaken empty T empty F).
  repeat rewrite concat_empty_r in *. repeat rewrite concat_empty_l in *.
  apply* A.
Qed.

(** Through narrowing *)

Lemma wft_narrow : forall V0 V1 F U0 U1 T E X,
  wft (E & X ~ bind_sub V0 V1 & F) T ->
  ok (E & X ~ bind_sub U0 U1 & F) ->
  wft (E & X ~ bind_sub U0 U1 & F) T.
Proof.
  intros. gen_eq K: (E & X ~ bind_sub V0 V1 & F). gen E F.
  induction H; intros; subst; eauto.
  destruct (binds_middle_inv H) as [K|[K|K]]; try destructs K.
    applys wft_var. apply* binds_concat_right.
    subst. applys wft_var. apply~ binds_middle_eq.
    applys wft_var. apply~ binds_concat_left.
     apply* binds_concat_left.
  apply_fresh* wft_all as Y. apply_ih_bind* H2.
Qed.

(** Through strengthening *)

Lemma wft_strengthen : forall E F x U T,
 wft (E & x ~ bind_typ U & F) T -> wft (E & F) T.
Proof.
  intros. gen_eq G: (E & x ~ bind_typ U & F). gen F.
  induction H; intros F EQ; subst; auto.
  apply* (@wft_var T0 T1).
  destruct (binds_concat_inv H) as [?|[? ?]].
    apply~ binds_concat_right.
    destruct (binds_push_inv H1) as [[? ?]|[? ?]].
      subst. false.
      apply~ binds_concat_left.
  (* todo: binds_cases tactic *)
  apply_fresh* wft_all as Y. apply_ih_bind* H2.
Qed.

(** Through type substitution *)

Lemma wft_subst_tb : forall F Q0 Q1 E Z P T,
  wft (E & Z ~ bind_sub Q0 Q1 & F) T ->
  wft E P ->
  ok (E & map (subst_tb Z P) F) ->
  wft (E & map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  introv WT WP. gen_eq G: (E & Z ~ bind_sub Q0 Q1 & F). gen F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt; auto.
  case_var*.
    apply_empty* wft_weaken.
    destruct (binds_concat_inv H) as [?|[? ?]].
      apply (@wft_var (subst_tt Z P T0) (subst_tt Z P T1)).
       apply~ binds_concat_right.
       unsimpl_map_bind_sub. apply binds_map.
       assumption.
      destruct (binds_push_inv H1) as [[? ?]|[? ?]].
        subst. false~.
        applys wft_var. apply* binds_concat_left.
  apply_fresh* wft_all as Y.
   unsimpl ((subst_tb Z P) (bind_sub T0 T1)).
   lets: wft_type.
   rewrite* subst_tt_open_tt_var.
   apply_ih_map_bind* H0.
Qed.

Lemma wft_subst_tb_empty : forall F Q0 Q1 Z P T,
  wft (Z ~ bind_sub Q0 Q1 & F) T ->
  wft empty P ->
  ok (map (subst_tb Z P) F) ->
  wft (map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  intros.
  lets A: (@wft_subst_tb F Q0 Q1 empty Z P T).
  repeat rewrite concat_empty_l in *. apply* A.
Qed.

(** Through type reduction *)

Lemma wft_open : forall E U T0 T1 T2,
  ok E ->
  wft E (typ_all T0 T1 T2) ->
  wft E U ->
  wft E (open_tt T2 U).
Proof.
  introv Ok WA WU. inversions WA. pick_fresh X.
  auto* wft_type. rewrite* (@subst_tt_intro X).
  lets K: (@wft_subst_tb empty).
  specializes_vars K. clean_empty K. apply* K.
  (* todo: apply empty ? *)
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

(** Extraction from a subtyping assumption in a well-formed environments *)

Lemma wft_from_env_has_sub : forall x U0 U1 E,
  okt E -> binds x (bind_sub U0 U1) E -> wft E U0 /\ wft E U1.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
    false (empty_push_inv H0).
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H4. split; apply_empty* wft_weaken.
       split; apply_empty* wft_weaken.
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H3.
       split; apply_empty* wft_weaken.
Qed.

(** Extraction from a typing assumption in a well-formed environments *)

Lemma wft_from_env_has_typ : forall x U E,
  okt E -> binds x (bind_typ U) E -> wft E U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
    false (empty_push_inv H0).
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H4.
       apply_empty* wft_weaken.
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H3. apply_empty* wft_weaken.
       apply_empty* wft_weaken.
Qed.

(** Extraction from a well-formed environment *)

Lemma wft_from_okt_typ : forall x T E,
  okt (E & x ~ bind_typ T) -> wft E T.
Proof.
  intros. inversions* H.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. false.
  destruct (eq_push_inv H0) as [? [? ?]]. inversions~ H4.
Qed.

Lemma wft_from_okt_sub : forall x T0 T1 E,
  okt (E & x ~ bind_sub T0 T1) -> wft E T0 /\ wft E T1.
Proof.
  intros. inversions* H.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. inversions~ H5.
  destruct (eq_push_inv H0) as [? [? ?]]. false.
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
Hint Resolve wft_from_okt_typ wft_from_okt_sub.
Hint Immediate wft_from_env_has_sub wft_from_env_has_typ.
Hint Resolve wft_subst_tb wft_subst_tb_empty.


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E X B,
  okt (E & X ~ B) -> (exists T0 T1, B = bind_sub T0 T1) \/ (exists T, B = bind_typ T).
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). subst*.
    lets (?&?&?): (eq_push_inv H). subst*.
Qed.

Lemma okt_push_sub_inv : forall E X T0 T1,
  okt (E & X ~ bind_sub T0 T1) -> okt E /\ wft E T0 /\ wft E T1 /\ X # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
    lets (?&?&?): (eq_push_inv H). false.
Qed.

Lemma okt_push_sub_type : forall E X T0 T1,
  okt (E & X ~ bind_sub T0 T1) -> type T0 /\ type T1.
Proof. intros. split; applys wft_type; forwards*: okt_push_sub_inv. Qed.

Lemma okt_push_typ_inv : forall E x T,
  okt (E & x ~ bind_typ T) -> okt E /\ wft E T /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). false.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
Qed.

Lemma okt_push_typ_type : forall E X T,
  okt (E & X ~ bind_typ T) -> type T.
Proof. intros. applys wft_type. forwards*: okt_push_typ_inv. Qed.

Hint Immediate okt_push_sub_type okt_push_typ_type.

(** Through narrowing *)

Lemma okt_narrow : forall V0 V1 (E F:env) U0 U1 X,
  okt (E & X ~ bind_sub V0 V1 & F) ->
  wft E U0 -> wft E U1 ->
  okt (E & X ~ bind_sub U0 U1 & F).
Proof.
  introv O W0 W1. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_sub_inv O).
  rewrite concat_assoc in *.
   lets [[T0 [T1 Hsub]] | [T Htyp]]: (okt_push_inv O); subst.
     lets (?&?&?&?): (okt_push_sub_inv O).
      applys~ okt_sub; applys* wft_narrow.
     lets (?&?&?): (okt_push_typ_inv O).
      applys~ okt_typ. applys* wft_narrow.
Qed.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F:env),
  okt (E & x ~ bind_typ T & F) ->
  okt (E & F).
Proof.
 introv O. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_typ_inv O).
  rewrite concat_assoc in *.
   lets [[U0 [U1 Hsub]] | [U Htyp]]: (okt_push_inv O); subst.
     lets (?&?&?&?): (okt_push_sub_inv O).
      applys~ okt_sub; applys* wft_strengthen.
     lets (?&?&?): (okt_push_typ_inv O).
      applys~ okt_typ. applys* wft_strengthen.
Qed.

(** Through type substitution *)

Lemma okt_subst_tb : forall Q0 Q1 Z P (E F:env),
  okt (E & Z ~ bind_sub Q0 Q1 & F) ->
  wft E P ->
  okt (E & map (subst_tb Z P) F).
Proof.
 introv O W. induction F using env_ind.
  rewrite map_empty. rewrite concat_empty_r in *.
   lets*: (okt_push_sub_inv O).
  rewrite map_push. rewrite concat_assoc in *.
   lets [[U0 [U1 Hsub]] | [U Htyp]]: (okt_push_inv O); subst.
     lets (?&?&?&?): (okt_push_sub_inv O).
      applys~ okt_sub; applys* wft_subst_tb.
     lets (?&?&?): (okt_push_typ_inv O).
      applys~ okt_typ. applys* wft_subst_tb.
Qed.

Lemma okt_subst_tb_empty : forall Q0 Q1 Z P (F:env),
  okt (Z ~ bind_sub Q0 Q1 & F) ->
  wft empty P ->
  okt (map (subst_tb Z P) F).
Proof.
  intros.
  lets A: (@okt_subst_tb Q0 Q1 Z P empty F).
  repeat rewrite concat_empty_l in *. apply* A.
Qed.

(** Automation *)

Hint Resolve okt_narrow okt_subst_tb okt_subst_tb_empty wft_weaken.
Hint Immediate okt_strengthen.


(* ********************************************************************** *)
(** ** Environment is unchanged by substitution from a fresh name *)

Lemma notin_fv_tt_open : forall Y X T,
  X \notin fv_tt (T open_tt_var Y) ->
  X \notin fv_tt T.
Proof.
 introv. unfold open_tt. generalize 0.
 induction T; simpl; intros k Fr; auto.
 specializes IHT1 k. specializes IHT2 k. auto.
 specializes IHT1 k. specializes IHT2 k. specializes IHT3 (S k). auto.
Qed.

Lemma notin_fv_wf : forall E X T,
  wft E T -> X # E -> X \notin fv_tt T.
Proof.
  induction 1; intros Fr; simpl.
  eauto.
  eauto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H Fr.
  notin_simpl; auto.
  notin_simpl; auto. pick_fresh Y. apply* (@notin_fv_tt_open Y).
Qed.

Lemma map_subst_tb_id : forall G Z P,
  okt G -> Z # G -> G = map (subst_tb Z P) G.
Proof.
  induction 1; intros Fr; autorewrite with rew_env_map; simpl.
  auto.
  rewrite* <- IHokt.
    rewrite* subst_tt_fresh. rewrite* subst_tt_fresh.
    apply* notin_fv_wf. apply* notin_fv_wf.
  rewrite* <- IHokt. rewrite* subst_tt_fresh. apply* notin_fv_wf.
Qed.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_regular : forall m E S T,
  sub m E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  induction 1. auto*. auto*. auto*. auto*. auto*. jauto_set; auto. (* auto* too slow *)
  auto*.
  split. auto*.
   inversion IHsub1 as [_ [HwfS0 HwfT0]].
   inversion IHsub2 as [_ [HwfT1 HwfS1]].
   split;
   apply_fresh wft_all as Y; try assumption;
   forwards~: (H2 Y);
   apply_empty* (@wft_narrow T0 T1).
   auto*. auto*.
Qed.

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e /\ wft E T.
Proof.
  induction 1.
  splits*.
  splits.
   pick_fresh y. specializes H0 y. destructs~ H0.
    forwards*: okt_push_typ_inv.
   apply_fresh* term_abs as y.
     pick_fresh y. specializes H0 y. destructs~ H0.
      forwards*: okt_push_typ_inv.
     specializes H0 y. destructs~ H0.
   pick_fresh y. specializes H0 y. destructs~ H0.
    apply* wft_arrow.
      forwards*: okt_push_typ_inv.
      apply_empty* wft_strengthen.
  splits*. destructs IHtyping1. inversion* H3.
  splits.
   pick_fresh y. specializes H0 y. destructs~ H0.
    forwards*: okt_push_sub_inv.
   apply_fresh* term_tabs as y.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
       forwards*: okt_push_sub_inv.
       inversion H4 as [_ [Hwf _]]. apply wft_type with (E:=E). assumption.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
       forwards*: okt_push_sub_inv.
       inversion H4 as [_ [_ [Hwf _]]]. apply wft_type with (E:=E). assumption.
     forwards~ K: (H0 y). destructs K. auto.
   apply_fresh* wft_all as Y.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
      forwards*: okt_push_sub_inv.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
      forwards*: okt_push_sub_inv.
     forwards~ K: (H0 Y). destructs K.
      forwards*: okt_push_sub_inv.
  splits*; destructs (sub_regular H0).
   apply* term_tapp. applys* wft_type.
   applys* wft_open T0 T1.
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
  inversions H. pick_fresh y. rewrite* (@subst_ee_intro y).
  inversions H. pick_fresh Y. rewrite* (@subst_te_intro Y).
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
* Proofs                                                                   *
***************************************************************************)

(** In parentheses are given the label of the corresponding
  lemma in the description of the POPLMark Challenge. *)


(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma sub_reflexivity : forall m E T,
  okt E ->
  wft E T ->
  sub m E T T .
Proof.
  introv Ok WI. lets W: (wft_type WI). gen E.
  destruct m; induction W; intros; inversions WI; eauto using sub_trans_ok.
  apply sub_arrow; apply sub_trans_ok; auto.
  apply_fresh sub_all as Y; eauto using sub_trans_ok.
  apply sub_trans_ok. apply_fresh* sub_all as Y.
Qed.

(* ********************************************************************** *)
(** Weakening (2) *)

Lemma sub_weakening : forall m E F G S T,
   sub m (E & G) S T ->
   okt (E & F & G) ->
   sub m (E & F & G) S T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok; auto.
  (* case: fvar trans *)
  apply* sub_trans_tvar. apply* binds_weaken.
  (* case: fvar trans lower *)
  apply sub_trans_tvar_lower with (T0:=T0) (T1:=T1); auto.
  apply* binds_weaken.
  (* case: all *)
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
  (* case: trans_ok *)
  apply* sub_trans_ok.
  (* case: trans *)
  apply* sub_trans.
Qed.

Lemma sub_weakening_empty : forall m F G S T,
   sub m G S T ->
   okt (F & G) ->
   sub m (F & G) S T.
Proof.
  intros.
  lets A: (@sub_weakening m empty F G S T).
  repeat rewrite concat_empty_l in *. apply* A.
Qed.

(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

Definition transitivity_on Q := forall E S T,
  sub oktrans E S Q -> sub oktrans E Q T -> sub oktrans E S T.

Hint Unfold transitivity_on.

Hint Resolve wft_narrow.

Lemma sub_narrowing_aux : forall Q0 Q1 m F E Z P0 P1 S T,
  transitivity_on Q0 ->
  transitivity_on Q1 ->
  sub m (E & Z ~ bind_sub Q0 Q1 & F) S T ->
  sub oktrans E Q0 P0 ->
  sub oktrans E P1 Q1 ->
  sub m (E & Z ~ bind_sub P0 P1 & F) S T.
Proof.
  introv TransQ0 TransQ1 SsubT Q0subP0 P1subQ1.
  inductions SsubT; introv.
  apply* sub_top.
  apply* sub_bot.
  apply* sub_refl_tvar.
  tests EQ: (X = Z).
    lets M: (@okt_narrow Q0 Q1).
    apply (@sub_trans_tvar P0 P1).
      asserts~ N: (ok (E & Z ~ bind_sub P0 P1 & F)).
       lets: ok_middle_inv_r N.
       apply~ binds_middle_eq.
      apply TransQ1.
        do_rew* concat_assoc (apply_empty* sub_weakening).
        binds_get H. inversion H0. subst. auto*.
    apply* (@sub_trans_tvar T0 T1). binds_cases H; auto.
  tests EQ: (X = Z).
    lets M: (@okt_narrow Q0 Q1).
    apply (@sub_trans_tvar_lower P0 P1).
      asserts~ N: (ok (E & Z ~ bind_sub P0 P1 & F)).
       lets: ok_middle_inv_r N.
       apply~ binds_middle_eq.
      apply TransQ0.
        binds_get H. inversion H0. subst. auto*.
        do_rew* concat_assoc (apply_empty* sub_weakening).
    apply* (@sub_trans_tvar_lower T0 T1). binds_cases H; auto.
  apply* sub_arrow.
  apply_fresh* sub_all as Y. apply_ih_bind H0.
    auto.
    apply TransQ1.
    apply TransQ0.
    auto.
    auto.
    auto.
    auto.
  apply* sub_trans_ok.
  apply *sub_trans.
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof.
  intro Q. introv SsubQ QsubT.
  apply* sub_trans.
Qed.

Lemma sub_narrowing : forall Q0 Q1 m E F Z P0 P1 S T,
  sub oktrans E Q0 P0 ->
  sub oktrans E P1 Q1 ->
  sub m (E & Z ~ bind_sub Q0 Q1 & F) S T ->
  sub m (E & Z ~ bind_sub P0 P1 & F) S T.
Proof.
  intros.
  apply* sub_narrowing_aux.
  apply* sub_transitivity.
  apply* sub_transitivity.
Qed.

Lemma sub_narrowing_empty : forall Q0 Q1 m Z P0 P1 S T,
  sub oktrans empty Q0 P0 ->
  sub oktrans empty P1 Q1 ->
  sub m (Z ~ bind_sub Q0 Q1) S T ->
  sub m (Z ~ bind_sub P0 P1) S T.
Proof.
  intros.
  rewrite <- (concat_empty_r (Z ~ bind_sub P0 P1)).
  rewrite <- (concat_empty_l (Z ~ bind_sub P0 P1)).
  apply* sub_narrowing.
  rewrite concat_empty_r. rewrite concat_empty_l. auto.
Qed.

Inductive notvar : typ -> Prop :=
  | notvar_top   : notvar typ_top
  | notvar_bot   : notvar typ_bot
  | notvar_arrow : forall T1 T2, notvar (typ_arrow T1 T2)
  | notvar_all   : forall T0 T1 T2, notvar (typ_all T0 T1 T2).

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
    + apply* sub_trans_tvar_lower.
      apply* sub_trans. apply sub_trans_ok. assumption.
  - (* case bot *)
    inversion H12; subst.
    + apply* sub_bot.
    + apply* sub_trans_tvar.
      apply* sub_trans. apply sub_trans_ok. assumption.
  - (* case arrow *)
    inversion H12; inversion H23; subst; auto.
    + apply* sub_trans_tvar; eauto using sub_trans, sub_trans_ok.
    + apply* sub_trans_tvar; eauto using sub_trans, sub_trans_ok.
    + apply* sub_trans_tvar_lower; eauto using sub_trans, sub_trans_ok.
    + apply* sub_arrow; eauto using sub_trans, sub_trans_ok.
  - (* case all *)
    inversion H12; inversion H23; subst; auto.
    + apply* sub_trans_tvar; eauto using sub_trans, sub_trans_ok.
    + apply* sub_trans_tvar; eauto using sub_trans, sub_trans_ok.
    + apply* sub_trans_tvar_lower; eauto using sub_trans, sub_trans_ok.
    + apply sub_all with (L:=L \u L0); eauto using sub_trans.
      intros Y Fr.
      apply sub_trans with (T2:=(T5 open_tt_var Y)).
      apply_empty* (@sub_narrowing T0 T4).
      eauto.
Qed.

Lemma sub_trans_pushback_empty : forall T1 T3,
  sub oktrans empty T1 T3 ->
  sub notrans empty T1 T3.
Proof.
  introv Hst. remember empty as E. generalize dependent HeqE.
  induction Hst; intros; subst; eauto.
  false. apply* binds_empty_inv.
  false. apply* binds_empty_inv.
  apply_fresh* sub_all as Y.
  assert (wft empty T2) as HwfT2 by auto.
  assert (notvar T2) as N. {
    inversion HwfT2; subst; auto.
    inversion HwfT2; subst.
    false. apply* binds_empty_inv.
  }
  eapply sub_trans_notvar. apply N. eapply IHHst1; eauto. eapply IHHst2; eauto.
Qed.

End NarrowTrans.

(* ********************************************************************** *)
(** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q0 Q1 m F Z S T P,
  sub m (Z ~ bind_sub Q0 Q1 & F) S T ->
  sub oktrans empty Q0 P ->
  sub oktrans empty P Q1 ->
  sub oktrans (map (subst_tb Z P) F) (subst_tt Z P S) (subst_tt Z P T).
Proof.
  introv SsubT Q0subP PsubQ1. lets R: (sub_regular Q0subP).
  destruct R as [_ [_ Pwf]].
  inductions SsubT; introv; simpl subst_tt.
  apply sub_trans_ok. apply* sub_top.
  apply sub_trans_ok. apply* sub_bot.
  case_var.
    apply* sub_reflexivity. apply* wft_weaken_empty.
    apply* sub_reflexivity.
    inversions H0. binds_cases H3.
      apply* (@wft_var (subst_tt Z P T0) (subst_tt Z P T1)). unsimpl_map_bind_sub*.
  case_var.
    apply (@sub_transitivity Q1).
      apply_empty* sub_weakening_empty.
      rewrite* <- (@subst_tt_fresh Z P Q1).
        rewrite <- concat_empty_l in H. rewrite concat_assoc in H. binds_get H.
        rewrite concat_empty_l. apply ok_from_okt. eapply proj1.
        eapply sub_regular. eauto.
        inversion H0. subst. auto*.
        apply* (@notin_fv_wf empty).
    apply sub_trans_ok. apply* (@sub_trans_tvar (subst_tt Z P T0) (subst_tt Z P T1)).
        binds_cases H; unsimpl_map_bind_sub*.
  case_var.
    apply (@sub_transitivity Q0).
    rewrite* <- (@subst_tt_fresh Z P Q0).
    rewrite <- concat_empty_l in H. rewrite concat_assoc in H. binds_get H.
    rewrite concat_empty_l. apply ok_from_okt. eapply proj1.
    eapply sub_regular. eauto.
    inversion H0. subst. auto*.
    apply* (@notin_fv_wf empty).
    apply_empty* sub_weakening_empty.
    apply sub_trans_ok. apply* (@sub_trans_tvar_lower (subst_tt Z P T0) (subst_tt Z P T1)).
    binds_cases H; unsimpl_map_bind_sub*.
  apply sub_trans_ok. apply* sub_arrow.
  apply sub_trans_ok. apply_fresh* sub_all as X.
   unsimpl (subst_tb Z P (bind_sub T0 T1)).
   repeat rewrite* subst_tt_open_tt_var.
   assert (map (subst_tb Z P) F & X ~ subst_tb Z P (bind_sub T0 T1) =
           map (subst_tb Z P) (F & X ~ bind_sub T0 T1)) as A. {
     rewrite map_concat. rewrite map_single. reflexivity.
   }
   rewrite A. apply* H0. rewrite concat_assoc. reflexivity.
  apply* IHSsubT.
  apply* sub_trans.
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
  apply* typing_app.
  apply_fresh* typing_tabs as X. forwards~ K: (H X).
   apply_ih_bind (H0 X); eauto.
   apply typing_regular in K.
   inversion K as [HOK _].
   apply wft_from_okt_sub in HOK.
   inversion HOK as [HS HU].
   apply okt_sub; auto.
  apply* typing_tapp; apply* sub_weakening.
  apply* typing_sub. apply* sub_weakening.
Qed.

(* ********************************************************************** *)
(** Strengthening (6) *)

Lemma sub_strengthening : forall x U m E F S T,
  sub m (E & x ~ bind_typ U & F) S T ->
  sub m (E & F) S T.
Proof.
  intros x U m E F S T SsubT.
  inductions SsubT; introv; auto* wft_strengthen.
  (* case: fvar trans *)
  apply* (@sub_trans_tvar T0 T1). binds_cases H; auto*.
  (* case: fvar trans lower *)
  apply* (@sub_trans_tvar_lower T0 T1). binds_cases H; auto*.
  (* case: all *)
  apply_fresh* sub_all as X. apply_ih_bind* H0.
  (* case: trans_ok *)
  apply* sub_trans_ok.
  (* case: trans *)
  apply* sub_trans.
Qed.

(************************************************************************ *)
(** Preservation by Type Narrowing (7) *)

Lemma typing_narrowing : forall Q0 Q1 E F X P0 P1 e T,
  sub oktrans E Q0 P0 ->
  sub oktrans E P1 Q1 ->
  sub oktrans E P0 P1 ->
  typing (E & X ~ bind_sub Q0 Q1 & F) e T ->
  typing (E & X ~ bind_sub P0 P1 & F) e T.
Proof.
  introv Q0subP0 P1subQ1 P0subP1 Typ. gen_eq E': (E & X ~ bind_sub Q0 Q1 & F). gen F.
  inductions Typ; introv EQ; subst; simpl.
  binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply* typing_app.
  apply_fresh* typing_tabs as Y. apply_ih_bind* H0.
  apply* typing_tapp; apply* (@sub_narrowing Q0 Q1).
  apply* typing_sub. apply* (@sub_narrowing Q0 Q1).
Qed.

Lemma typing_narrowing_empty : forall Q0 Q1 X P0 P1 e T,
  sub oktrans empty Q0 P0 ->
  sub oktrans empty P1 Q1 ->
  sub oktrans empty P0 P1 ->
  typing (X ~ bind_sub Q0 Q1) e T ->
  typing (X ~ bind_sub P0 P1) e T.
Proof.
  intros.
  rewrite <- (concat_empty_r (X ~ bind_sub P0 P1)).
  rewrite <- (concat_empty_l (X ~ bind_sub P0 P1)).
  apply* typing_narrowing.
  rewrite concat_empty_r. rewrite concat_empty_l. auto.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (E & x ~ bind_typ U & F) e T ->
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
  apply* typing_tapp; apply* sub_strengthening.
  apply* typing_sub. apply* sub_strengthening.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma typing_through_subst_te : forall Q0 Q1 F Z e T P,
  typing (Z ~ bind_sub Q0 Q1 & F) e T ->
  sub oktrans empty Q0 P ->
  sub oktrans empty P Q1 ->
  typing (map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ Q0subP PsubQ1.
  inductions Typ; introv; simpls subst_tt; simpls subst_te.
  apply* typing_var.
   binds_cases H0; unsimpl_map_bind_typ*.
  apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var.
    assert (map (subst_tb Z P) F & y ~ subst_tb Z P (bind_typ V)=
            map (subst_tb Z P) (F & y ~ bind_typ V)) as A. {
      rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite A. apply* H0. rewrite concat_assoc. reflexivity.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P (bind_sub VS VU)).
    rewrite* subst_te_open_te_var.
    rewrite* subst_tt_open_tt_var.
    assert (map (subst_tb Z P) F & Y ~ subst_tb Z P (bind_sub VS VU)=
            map (subst_tb Z P) (F & Y ~ bind_sub VS VU)) as A. {
      rewrite map_concat. rewrite map_single. reflexivity.
    }
    rewrite A. apply* H0. rewrite concat_assoc. reflexivity.
  rewrite* subst_tt_open_tt. apply* typing_tapp.
    apply* sub_through_subst_tt.
    apply* sub_through_subst_tt.
  apply* typing_sub. apply* sub_through_subst_tt.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Inductive possible_types : trm -> typ -> Prop :=
| pt_top : forall v, value v -> possible_types v typ_top
| pt_arrow : forall L V V' e1 T1 T1',
  (forall x, x \notin L -> typing (x ~ bind_typ V) (e1 open_ee_var x) T1) ->
  sub oktrans empty V' V ->
  sub oktrans empty T1 T1' ->
  possible_types (trm_abs V e1) (typ_arrow V' T1')
| pt_all : forall L VS VS' VU VU' e1 T1 T1',
  (forall X, X \notin L -> typing (X ~ bind_sub VS VU) (e1 open_te_var X) (T1 open_tt_var X)) ->
  sub oktrans empty VS VS' ->
  sub oktrans empty VU' VU ->
  (forall X, X \notin L -> sub oktrans (X ~ bind_sub VS' VU') (T1 open_tt_var X) (T1' open_tt_var X)) ->
  possible_types (trm_tabs VS VU e1) (typ_all VS' VU' T1')
.

Lemma possible_types_closure : forall v T U,
  possible_types v T ->
  sub notrans empty T U ->
  possible_types v U.
Proof.
  introv Hpt Hsub. generalize dependent U. induction Hpt; intros.
  - inversion Hsub; subst.
    + eapply pt_top; eauto.
    + false. eapply binds_empty_inv; eauto.
  - inversion Hsub; subst.
    + eapply pt_top; eauto. eapply value_abs; eauto.
      apply_fresh term_abs as y; eauto.
      assert (y \notin L) as Fr by eauto.
      specialize (H y Fr).
      eapply typing_regular in H. destruct H as [? [A ?]].
      eapply A.
    + false. eapply binds_empty_inv; eauto.
    + eapply pt_arrow; eauto.
      eapply sub_trans; eauto.
      eapply sub_trans; eauto.
  - inversion Hsub; subst.
    + eapply pt_top; eauto. eapply value_tabs; eauto.
      apply_fresh term_tabs as Y; eauto.
      assert (Y \notin L) as Fr by eauto.
      specialize (H Y Fr).
      eapply typing_regular in H. destruct H as [? [A ?]].
      eapply A.
    + false. eapply binds_empty_inv; eauto.
    + apply_fresh pt_all as Y. eauto.
      eapply sub_trans; eauto.
      eapply sub_trans; eauto.
      eapply sub_trans.
      eapply sub_narrowing_empty. eauto. eauto. eapply H2. eauto.
      assert (Y \notin L0) as Fr by eauto.
      specialize (H10 Y Fr). simpl in H10. rewrite concat_empty_l in H10. eapply H10.
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
    apply_fresh pt_arrow as y.
    assert (y \notin L) as Fr by eauto.
    specialize (H y Fr). rewrite concat_empty_l in H. eapply H.
    eapply sub_reflexivity; eauto. eapply sub_reflexivity; eauto.
  - eapply typing_regular in Hc. destruct Hc as [? [? Hc]].
    inversion Hc; subst.
    apply_fresh pt_all as Y.
    assert (Y \notin L) as Fr by eauto.
    specialize (H Y Fr). rewrite concat_empty_l in H. eapply H.
    eapply sub_reflexivity; eauto. eapply sub_reflexivity; eauto.
    eapply sub_reflexivity; eauto.
    rewrite <- concat_empty_l. eauto.
    assert (Y \notin L0) as Fr by eauto.
    specialize (H9 Y Fr). rewrite concat_empty_l in H9. eapply H9.
  - eapply possible_types_closure; eauto.
    eapply sub_trans_pushback_empty; eauto.
Qed.

Lemma typing_inv_abs : forall S1 e1 T,
  typing empty (trm_abs S1 e1) T ->
  forall U1 U2, sub notrans empty T (typ_arrow U1 U2) ->
     sub oktrans empty U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (x ~ bind_typ S1) (e1 open_ee_var x) S2 /\ sub oktrans empty S2 U2.
Proof.
  introv Typ.
  remember (trm_abs S1 e1) as v.
  assert (value v) as Hv. {
    subst. eapply value_abs. eapply typing_regular in Typ. destruct Typ as [? [A ?]].
    eapply A.
  }
  gen S1 e1.
  assert (possible_types v T) as Hpt. {
    eapply possible_types_typing; eauto.
  }
  clear Typ. clear Hv.
  inversion Hpt; subst; introv Eqv Hsub; try solve [inversion Hsub].
  inversion Hsub; subst. inversion Eqv; subst.
  split.
  eapply sub_trans; eauto.
  eexists. exists L.
  intros y Fr.
  specialize (H y Fr).
  split. eapply H.
  eapply sub_trans; eauto.
Qed.

Lemma typing_inv_tabs : forall S10 S11 e1 T,
  typing empty (trm_tabs S10 S11 e1) T ->
  forall U10 U11 U2, sub notrans empty T (typ_all U10 U11 U2) -> sub oktrans empty U10 U11 ->
     sub oktrans empty S10 U10 /\ sub oktrans empty U11 S11
  /\ exists S2, exists L, forall X, X \notin L ->
     typing (X ~ bind_sub U10 U11) (e1 open_te_var X) (S2 open_tt_var X)
     /\ sub oktrans (X ~ bind_sub U10 U11) (S2 open_tt_var X) (U2 open_tt_var X).
Proof.
  introv Typ.
  remember (trm_tabs S10 S11 e1) as v.
  assert (value v) as Hv. {
    subst. eapply value_tabs. eapply typing_regular in Typ. destruct Typ as [? [A ?]].
    eapply A.
  }
  gen S10 S11 e1.
  assert (possible_types v T) as Hpt. {
    eapply possible_types_typing; eauto.
  }
  clear Typ. clear Hv.
  inversion Hpt; subst; introv Eqv Hsub; try solve [inversion Hsub].
  inversion Eqv; subst. inversion Hsub; subst; introv HsubU.

  splits.
  eapply sub_trans; eauto.
  eapply sub_trans; eauto.
  eexists. exists (L \u L0).
  intros Y Fri.
  assert (Y \notin L) as Fr by auto.
  assert (Y \notin L0) as Fr0 by auto.
  splits.
  specialize (H Y Fr).
  eapply typing_narrowing_empty.
  eapply sub_trans. eapply H0. eauto.
  eapply sub_trans. eauto. eauto.
  eauto.
  eauto.
  specialize (H2 Y Fr). specialize (H12 Y Fr0). rewrite concat_empty_l in H12.
  eapply sub_trans.
  eapply sub_narrowing_empty. eauto. eauto. eapply H2. eapply H12.
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen_eq E: (@empty bind). gen e'.
  induction Typ; introv QEQ; introv Red;
   try solve [inversion Typ; congruence]; try solve [ inversion Red ].
  (* case: app *)
  inversions Red; try solve [ apply* typing_app ].
  destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).
       apply* (@typing_sub S2). rewrite concat_empty_l. auto*. apply_empty* sub_weakening_empty.
       auto*.
  (* case: tapp *)
  inversions Red; try solve [ apply* typing_tapp ].
  destruct~ (typing_inv_tabs Typ (U10:=T0) (U11:=T1) (U2:=T2)) as [P1 [S20 [S21 [L P2]]]].
    apply* sub_reflexivity.
    apply* (@sub_transitivity T).
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_te_intro X).
     rewrite* (@subst_tt_intro X).
     erewrite <- map_empty.
     apply* (@typing_through_subst_te T0 T1).
     rewrite concat_empty_r.
     apply* typing_sub.
  (* case sub *)
  apply* typing_sub.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma value_not_bot : forall t T,
  value t -> typing empty t T -> T <> typ_bot.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  induction Typ; introv EQE;
    try solve [ inversion Val; congruence ].
  subst. apply sub_trans_pushback_empty in H.
  inversion H; subst; try solve [ congruence ].
  induction T; try solve [ congruence ].
  apply IHTyp; auto.
  apply binds_empty_inv in H0. inversion H0.
Qed.

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow U1 U2) ->
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_arrow U1 U2). gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. apply sub_trans_pushback_empty in H. inversion H.
      apply value_not_bot in Typ; try assumption. congruence.
      false (binds_empty_inv H0).
      inversions H0. forwards*: IHTyp.
Qed.

Lemma canonical_form_tabs : forall t U0 U1 U2,
  value t -> typing empty t (typ_all U0 U1 U2) ->
  exists V0 V1, exists e1, t = trm_tabs V0 V1 e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_all U0 U1 U2). gen U0 U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. apply sub_trans_pushback_empty in H. inversion H.
      apply value_not_bot in Typ; try assumption. congruence.
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
    destruct (canonical_form_tabs Val1 Typ) as [S0 [S1 [e3 EQ]]].
      subst. exists* (open_te e3 T).
      exists* (trm_tapp e1' T).
  (* case: sub *)
  auto*.
Qed.
