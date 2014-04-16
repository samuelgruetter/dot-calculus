(***************************************************************************
* Preservation and Progress for System-F with Subtyping - Part 1A          *
* Brian Aydemir & Arthur Charguéraud, March 2007                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ : Set :=
  | typ_top   : typ
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ -> typ.

(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_bvar J      => If K = J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2   => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (typ_all T1 T2).

(** Binding are either mapping type or term variables. 
 [X ~<: T] is a subtyping asumption and [x ~: T] is
 a typing assumption *)

Inductive bind : Set :=
  | bind_sub : typ -> bind.

Notation "X ~<: T" := (X ~ bind_sub T)
  (at level 31, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)

Definition env := LibEnv.env bind.

(** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  subtyping relation in E. This predicates implies
  that T is a type *)

Inductive wft : env -> typ -> Prop :=
  | wft_top : forall E, 
      wft E typ_top
  | wft_var : forall U E X,
      binds X (bind_sub U) E ->
      wft E (typ_fvar X) 
  | wft_arrow : forall E T1 T2,
      wft E T1 -> 
      wft E T2 -> 
      wft E (typ_arrow T1 T2)
  | wft_all : forall L E T1 T2,
      wft E T1 ->
      (forall X, X \notin L -> 
        wft (E & X ~<: T1) (T2 open_tt_var X)) ->
      wft E (typ_all T1 T2).

(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_sub : forall E X T,
      okt E -> wft E T -> X # E -> okt (E & X ~<: T).

(** Subtyping relation *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      okt E ->
      wft E S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      okt E ->
      wft E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X, X \notin L ->
          sub (E & X ~<: T1) (S2 open_tt_var X) (T2 open_tt_var X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2).

(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | typ_top         => \{}
  | typ_bvar J      => \{}
  | typ_fvar X      => \{X}
  | typ_arrow T1 T2 => (fv_tt T1) \u (fv_tt T2)
  | typ_all T1 T2   => (fv_tt T1) \u (fv_tt T2)
  end.

(** Substitution for free type variables in types. *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => If X = Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2   => typ_all (subst_tt Z U T1) (subst_tt Z U T2)
  end.

(** Substitution for free type variables in environment. *)
(* check *)
Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors type wft ok okt.

Hint Resolve 
  sub_top sub_refl_tvar sub_arrow.

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let E := gather_vars_with (fun x : typ => fv_tt x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u E \u F).

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
  | |- sub ?E _ _  => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty E);
  eapply lemma; try rewrite concat_empty.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; auto*.

(** Tactic to undo when Coq does too much simplification *)   

Ltac unsimpl_map_bind :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U) ] =>
    unsimpl ((subst_tb Z P) (B U)) end.

Tactic Notation "unsimpl_map_bind" "*" :=
  unsimpl_map_bind; auto*.


(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma type_from_wft : forall E T,
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
  intros. gen_eq (E & G) as K. gen E F G.
  induction H; intros; subst; eauto.
  (* case: var *)
  apply (@wft_var U). apply* binds_weaken.
  (* case: all *)
  apply_fresh* wft_all as Y. apply_ih_bind* H1.
Qed.

(** Through narrowing *)

Lemma wft_narrow : forall V F U T E X,
  wft (E & X ~<: V & F) T ->
  ok (E & X ~<: U & F) -> 
  wft (E & X ~<: U & F) T.
Proof.
  intros. gen_eq (E & X ~<: V & F) as K. gen E F.
  induction H; intros; subst; eauto.
  binds_cases H.
    eapply wft_var. apply* binds_concat_ok.
    destruct (binds_single_inv B1). subst.
     apply (@wft_var U). apply* binds_mid.
    eapply wft_var. apply* binds_prepend.
  apply_fresh* wft_all as Y. apply_ih_bind* H1.
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

Lemma wft_from_env_has_sub : forall x U E,
  okt E -> binds x (bind_sub U) E -> wft E U.
Proof.
  unfold binds. induction E as [|(y,a)]; simpl; intros Ok B; env_fix.
  contradictions.
  case_var.
    inversions B. inversions Ok. apply_empty* wft_weaken.
    apply_empty* wft_weaken. inversions* Ok.
Qed.

Hint Immediate wft_from_env_has_sub.

(** Extraction from a well-formed environment *)

Lemma wft_from_okt_sub : forall x T E,
  okt (E & x ~<: T) -> wft E T.
Proof.
  intros. inversions* H.
Qed.
Hint Resolve wft_from_okt_sub.



(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Through narrowing *)

Lemma okt_narrow : forall V E F U X,
  okt (E & X ~<: V & F) ->
  wft E U ->
  okt (E & X ~<: U & F).
Proof.
  induction F as [|(Y,B)]; simpl; introv Ok Wf; env_fix; inversions Ok.
  auto. 
  apply okt_sub; auto. use wft_narrow. 
Qed.

(** Automation *)

Hint Resolve okt_narrow  wft_weaken.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_regular : forall E S T,
  sub E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  induction 1. auto*. auto*. auto*. auto*. (* Coq bug here? *)
  split. auto*. split;
   apply_fresh* wft_all as Y;
    destructi~ (H1 Y); apply_empty* (@wft_narrow T1). 
Qed.

(** Automation *)

Hint Extern 1 (okt ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj31 (sub_regular H))
  end.

Hint Extern 1 (wft ?E ?T) =>
  match goal with
  | H: sub E T _ |- _ => apply (proj32 (sub_regular H))
  | H: sub E _ T |- _ => apply (proj33 (sub_regular H))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (@type_from_wft E); auto in
  match goal with
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end.

(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  okt E -> 
  wft E T -> 
  sub E T T .
Proof.
  introv Ok WI. poses W (type_from_wft WI). gen E.
  induction W; intros; inversions WI; eauto.
  apply_fresh* sub_all as Y.
Qed.

(* ********************************************************************** *)
(** Weakening (2) *)

Lemma sub_weakening : forall E F G S T,
   sub (E & G) S T -> 
   okt (E & F & G) ->
   sub (E & F & G) S T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst; auto.
  (* case: fvar trans *)
  apply* sub_trans_tvar. apply* binds_weaken.
  (* case: all *)
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.
 
(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Hint Unfold transitivity_on.

Hint Resolve wft_narrow.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (E & Z ~<: Q & F) S T ->
  sub E P Q ->
  sub (E & Z ~<: P & F) S T.
Proof.
  introv TransQ SsubT PsubQ.
  gen_eq (E & Z ~<: Q & F) as G. gen F.
  induction SsubT; introv EQ; subst.
  apply* sub_top.
  apply* sub_refl_tvar.
  case (X == Z); intros EQ; subst.
    apply (@sub_trans_tvar P); puts (@okt_narrow Q).
      apply* binds_mid. 
      apply TransQ.
        do_rew* concat_assoc (apply_empty* sub_weakening).
        binds_get H. auto*.
    apply* (@sub_trans_tvar U).
    binds_cases H; auto.
  apply* sub_arrow.
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof.
  intro Q. introv SsubQ QsubT. asserts* W (type Q).
  gen E S T. gen_eq Q as Q' eq. gen Q' eq.
  induction W; intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversions EQ;
      intros T QsubT; inversions QsubT; 
        eauto 4 using sub_trans_tvar.
  (* case: all / top -> only needed to fix well-formedness,
     by building back what has been deconstructed too much *)
  assert (sub E (typ_all S1 S2) (typ_all T1 T2)). 
    apply_fresh* sub_all as y. 
  auto*.
  (* case: all / all *)
  apply_fresh sub_all as Y. auto*. 
  forward~ (H0 Y) as K. apply (K (T2 open_tt_var Y)); auto.
  puts (IHW T1). apply_empty* (@sub_narrowing_aux T1).
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (E & Z ~<: Q & F) S T ->
  sub (E & Z ~<: P & F) S T.
Proof.
  intros. 
  apply* sub_narrowing_aux. 
  apply* sub_transitivity.
Qed.

End NarrowTrans.
