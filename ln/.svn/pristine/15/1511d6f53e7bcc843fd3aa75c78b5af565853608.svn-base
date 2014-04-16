(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Infrastructure             *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require List.
Require Import ML_Definitions.

(* ====================================================================== *)
(** * Additional Definitions used in the Proofs *)

(* ********************************************************************** *)
(** ** Free Type Variables *)

(** Computing free variables of a list of terms. *)

Definition typ_fv_list :=
  LibList.fold_right (fun t acc => typ_fv t \u acc) \{}.

(** Computing free variables of a type scheme. *)

Definition sch_fv M := 
  typ_fv (sch_type M).


(* ********************************************************************** *)
(** ** Free Term Variables *)

(** Computing free variables of a term. *)

Fixpoint trm_fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i j  => \{}
  | trm_fvar x    => \{x}
  | trm_abs t1    => (trm_fv t1)
  | trm_fix t1    => (trm_fv t1)
  | trm_let t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_match t1 p1 b t2 => (trm_fv t1) \u (trm_fv b) \u (trm_fv t2)
  | trm_app t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_unit      => \{}
  | trm_nat n     => \{}
  | trm_add       => \{}
  | trm_pair t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_inj1 t1   => (trm_fv t1)
  | trm_inj2 t1   => (trm_fv t1)
  | trm_loc l     => \{}
  | trm_ref t1    => (trm_fv t1)
  | trm_get t1    => (trm_fv t1)
  | trm_set t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_raise t1    => (trm_fv t1)
  | trm_catch t1 t2 => (trm_fv t1) \u (trm_fv t2)
  end.

(* ********************************************************************** *)
(** ** Free Variables in Environments *)

(** Computing free type variables of the values of an environment. *)

Definition env_fv := 
  fv_in_values sch_fv.

(** Computing free type variables of the values for store typing. *)

Definition phi_fv := 
  fv_in_values typ_fv.


(* ********************************************************************** *)
(** ** Type substitution for free names *)

(** Substitution for names for types *)

Fixpoint typ_subst (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar i      => typ_bvar i
  | typ_fvar X      => If X = Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_unit        => typ_unit  
  | typ_nat         => typ_nat  
  | typ_prod T1 T2  => typ_prod (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_sum T1 T2   => typ_sum (typ_subst Z U T1) (typ_subst Z U T2)
  | typ_ref T1      => typ_ref (typ_subst Z U T1) 
  end.

(** Iterated substitution for types  *)

Fixpoint typ_substs (Zs : list var) (Us : list typ) (T : typ)
   {struct Zs} : typ :=
  match Zs, Us with
  | Z::Zs', U::Us' => typ_substs Zs' Us' (typ_subst Z U T)
  | _, _ => T
  end.    

(** Substitution for names for schemes. *)

Definition sch_subst Z U M := 
  Sch (sch_arity M) (typ_subst Z U (sch_type M)).

(** Iterated substitution for schemes. *)

Definition sch_substs Zs Us M := 
  Sch (sch_arity M) (typ_substs Zs Us (sch_type M)).

(* ********************************************************************** *)
(** ** Term substitution for free names *)

(** Computing free variables of a list of terms. *)

Definition trm_fv_list :=
  LibList.fold_right (fun t acc => trm_fv t \u acc) \{}.

(** Substitution for names *)

Fixpoint trm_subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i j  => trm_bvar i j
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs (trm_subst z u t1)
  | trm_fix t1    => trm_fix (trm_subst z u t1)
  | trm_let t1 t2 => trm_let (trm_subst z u t1) (trm_subst z u t2)
  | trm_match t1 p1 e t2 => trm_match (trm_subst z u t1) p1 
                               (trm_subst z u e)
                               (trm_subst z u t2)
  | trm_app t1 t2 => trm_app (trm_subst z u t1) (trm_subst z u t2)
  | trm_unit      => trm_unit
  | trm_nat n     => trm_nat n
  | trm_add       => trm_add
  | trm_pair t1 t2 => trm_pair (trm_subst z u t1) (trm_subst z u t2)
  | trm_inj1 t1  => trm_inj1 (trm_subst z u t1) 
  | trm_inj2 t1  => trm_inj2 (trm_subst z u t1) 
  | trm_loc l     => trm_loc l
  | trm_ref t1    => trm_ref (trm_subst z u t1)
  | trm_get t1    => trm_get (trm_subst z u t1)
  | trm_set t1 t2 => trm_set (trm_subst z u t1) (trm_subst z u t2)
  | trm_raise t1    => trm_raise (trm_subst z u t1)
  | trm_catch t1 t2 => trm_catch (trm_subst z u t1) (trm_subst z u t2)
  end.

Notation "[ z ~> u ] t" := (trm_subst z u t) (at level 68).

(** Iterated substitution *)

Fixpoint substs (zs : list var) (us : list trm) (t : trm)
   {struct zs} : trm :=
  match zs, us with
  | z::zs', u::us' => substs zs' us' ([z ~> u]t)
  | _, _ => t
  end.    

(** Predicate caraterizing lists of a given number of terms *)

Definition terms := list_for_n term.

(* ********************************************************************** *)
(** ** Iterated typing *)

(** Iterated typing *)

Inductive typings (E : env) (P : phi) : list trm -> list typ -> Prop :=
  | typings_nil : typings E P nil nil 
  | typings_cons : forall ts Us t U,
      typings E P ts Us ->
      typing E P t U ->
      typings E P (t::ts) (U::Us).



(* ====================================================================== *)
(** * Tactics *)

(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : trm => trm_fv x) in
  let E := gather_vars_with (fun x : typ => typ_fv x) in
  let F := gather_vars_with (fun x : list trm => trm_fv_list x) in
  let G := gather_vars_with (fun x : list typ => typ_fv_list x) in
  let H := gather_vars_with (fun x : env => env_fv x) in
  let I := gather_vars_with (fun x : sch => sch_fv x) in
  let J := gather_vars_with (fun x : phi => phi_fv x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "pick_freshes" constr(n) ident(x) :=
  let L := gather_vars in (pick_freshes_gen L n x).

Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base_simple T gather_vars.

Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto*.


(* ********************************************************************** *)
(** ** Automation *)

Hint Constructors type term phi_ok sto_ok pat_typing typing value red typings.

Lemma trm_def_fresh : trm_fv trm_def = \{}.
Proof. auto.
Qed.
Lemma typ_def_fresh : typ_fv typ_def = \{}.
Proof.
  auto.
Qed.

Hint Extern 1 (_ \notin trm_fv trm_def) =>
  rewrite trm_def_fresh.
Hint Extern 1 (_ \notin typ_fv typ_def) =>
  rewrite typ_def_fresh.
Hint Extern 1 (_ \notin typ_fv typ_exn) =>
  rewrite typ_exn_fresh.


Hint Extern 1 (terms _ _) => split; auto.
Hint Extern 1 (types _ _) => split; auto.

(* ====================================================================== *)
(** ** Properties of iterated operator *)
 
(* TODO: use a common definition *)

Lemma typ_fv_list_nil :
  typ_fv_list nil = \{}.
Proof. auto. Qed.

Lemma typ_fv_list_cons : forall t ts,
  typ_fv_list (t :: ts) = typ_fv t \u typ_fv_list ts.
Proof. intros. unfold typ_fv_list. rew_list~. Qed.

Lemma typ_fv_list_app : forall ts1 ts2,
  typ_fv_list (ts1 ++ ts2) = typ_fv_list ts1 \u typ_fv_list ts2.
Proof.
  induction ts1; intros; rew_app.
  rewrite* union_empty_l.
  rewrite typ_fv_list_cons. rewrite IHts1. rewrite* union_assoc.
Qed.

Lemma trm_fv_list_nil :
  trm_fv_list nil = \{}.
Proof. auto. Qed.

Lemma trm_fv_list_cons : forall t ts,
  trm_fv_list (t :: ts) = trm_fv t \u trm_fv_list ts.
Proof. intros. unfold trm_fv_list. rew_list~. Qed.

Lemma trm_fv_list_app : forall ts1 ts2,
  trm_fv_list (ts1 ++ ts2) = trm_fv_list ts1 \u trm_fv_list ts2.
Proof.
  induction ts1; intros; rew_app.
  rewrite* union_empty_l.
  rewrite trm_fv_list_cons. rewrite IHts1. rewrite* union_assoc.
Qed.

Lemma typ_fvars_nil :
  typ_fvars nil = nil.
Proof. auto. Qed.

Lemma typ_fvars_cons : forall t ts,
  typ_fvars (t::ts) = typ_fvar t :: typ_fvars ts.
Proof. auto. Qed.

Lemma trm_fvars_nil :
  trm_fvars nil = nil.
Proof. auto. Qed.

Lemma trm_fvars_cons : forall t ts,
  trm_fvars (t::ts) = trm_fvar t :: trm_fvars ts.
Proof. auto. Qed.

Lemma typings_concat : forall E P ts1 Us1 ts2 Us2,
  typings E P ts1 Us1 ->
  typings E P ts2 Us2 ->
  typings E P (ts1++ts2) (Us1++Us2).
Proof.
  induction ts1; introv Typ1 Typ2; inversions Typ1; simpls*.
  rew_app; auto*.
Qed.


(* ====================================================================== *)
(** * Properties of terms *)

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
  pick_fresh x. forwards~ K: (H0 x) .
   apply* (@open_rec_term_core t1 0 (trm_fvars (x::nil))).
  pick_fresh x. pick_fresh f. forwards~ K: (H0 x f).
   apply* (@open_rec_term_core t1 0 (trm_fvars (f::x::nil))).
  pick_fresh x. forwards~ K: (H1 x).
   apply* (@open_rec_term_core t2 0 (trm_fvars (x::nil))).
  pick_freshes (pat_arity p) xs. forwards~ K: (H1 xs).
   apply* (@open_rec_term_core b 0 (trm_fvars xs)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin trm_fv t -> 
  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; f_equal*. case_var*.
Qed.

Lemma subst_fresh_list : forall z u ts,
  z \notin trm_fv_list ts ->
  ts = LibList.map (trm_subst z u) ts.
Proof.
  induction ts; intros Fr; rew_map.
  auto. rewrite trm_fv_list_cons in Fr. 
   fequal. rewrite~ subst_fresh. auto.
Qed.

Lemma subst_fresh_trm_fvars : forall z u xs,
  fresh (\{z}) (length xs) xs ->
  trm_fvars xs = LibList.map (trm_subst z u) (trm_fvars xs).
Proof.
  intros. apply subst_fresh_list.
  induction xs; rew_list in *. 
    rewrite trm_fvars_nil. rewrite~ trm_fv_list_nil.
    rewrite trm_fvars_cons. rewrite trm_fv_list_cons. simpl.
     simpl in H. destruct H. specializes~ IHxs.
Qed.

Lemma substs_fresh : forall xs us t, 
  fresh (trm_fv t) (length xs) xs -> 
  substs xs us t = t.
Proof.
  induction xs; intros us t Fr.
  auto.
  rew_list in Fr. simpl in Fr. inversions Fr. 
   simpl. destruct us. auto. rewrite* subst_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ (LibList.map (trm_subst x u) t2).
Proof.
  intros. unfold open, opens. simpl. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. unfold trm_nth. 
   apply list_map_nth. apply* subst_fresh.
  case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_vars : forall x ys u t, 
  fresh \{x} (length ys) ys -> 
  term u ->
  ([x ~> u]t) ^ ys = [x ~> u] (t ^ ys).
Proof.
  introv Fr Tu. rewrite* subst_open. 
  unfold trm_fvars. f_equal.
  induction ys; rew_map. auto.
  rew_list in Fr. simpl in Fr. destruct Fr.
   simpl. case_var. f_equal*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma substs_intro_ind : forall t xs us vs, 
  fresh (trm_fv t \u trm_fv_list vs \u trm_fv_list us) (length xs) xs -> 
  terms (length xs) us ->
  terms (length vs) vs ->
  t ^^ (vs ++ us) = substs xs us (t ^^ (vs ++ (trm_fvars xs))).
Proof.
  induction xs; introv Fr Tu Tv; 
   destruct Tu; destruct us; tryfalse. simpl; auto.
  inversions H0. rew_list in Fr. simpl in Fr. destruct Fr as [Fra Frxs].
  rew_list in H. simpl in H. inverts H.
  simpl. rewrite app_last. rewrite trm_fvars_cons.
  rewrite trm_fv_list_cons in Frxs,Fra.
  forwards K: (IHxs us (vs++t0::nil)); clear IHxs.
    rewrite trm_fv_list_app. rewrite trm_fv_list_cons. rewrite~ trm_fv_list_nil.
    auto. 
    split~. inversions Tv. apply* Forall_app.
  rewrite K. clear K. 
  f_equal. rewrite~ subst_open. rewrite~ subst_fresh.
  f_equal. rew_map. simpl. case_var; tryfalse.
  f_equal. apply~ subst_fresh_list.
  f_equal. apply* subst_fresh_trm_fvars.
Qed.

Lemma substs_intro : forall xs t us, 
  fresh (trm_fv t \u trm_fv_list us) (length xs) xs -> 
  terms (length xs) us ->
  t ^^ us = substs xs us (t ^ xs).
Proof.
  intros. apply* (@substs_intro_ind t xs us nil).
  rewrite~ trm_fv_list_nil.
Qed.


(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh term_abs. intros y Fr.
   rewrite* subst_open_vars.
  apply_fresh term_fix. intros y f Fr.
   rewrite* subst_open_vars.
  apply_fresh term_let. auto. intros y Fr.
   rewrite* subst_open_vars.
  apply_fresh* term_match. intros ys Fr.
   rewrite* subst_open_vars.
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

(* Bodys are stable by substitution *)

Lemma subst_bodys : forall z u n t,
  term u -> bodys n t -> bodys n ([z ~> u]t).
Proof.
  introv. intros Wu [L Bt]. exists (L \u \{z}).
  introv Fr. rewrite~ subst_open_vars.
Qed.

Hint Resolve subst_bodys.


(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> bodys 1 t1.
Proof.
  intros. unfold bodys. inverts H.
  exists L. introv Fr.
  destruct xs; simpls. false.
  destruct xs; simpls. auto. false*.
Qed.

Lemma body_to_term_abs : forall t1,
  bodys 1 t1 -> term (trm_abs t1).
Proof. 
  destruct 1. apply_fresh* term_abs.
Qed.

Lemma term_fix_to_body : forall t1,
  term (trm_fix t1) -> bodys 2 t1.
Proof.
  intros. unfold bodys. inverts H.
  exists L. introv Fr.
  destruct xs; simpls. false.
  destruct xs; simpls. false*.
  destruct xs; simpls. auto. false*.
Qed.

Lemma body_to_term_fix : forall t1,
  bodys 2 t1 -> term (trm_fix t1).
Proof.
   destruct 1. apply_fresh* term_fix.
Qed.

Lemma term_let_to_body : forall t1 t2, 
  term (trm_let t1 t2) -> bodys 1 t2.
Proof.
  intros. unfold bodys. inverts H.
  exists L. introv Fr.
  destruct xs; simpls. false.
  destruct xs; simpls. auto. false*.
Qed.

Lemma body_to_term_let : forall t1 t2,
  term t1 -> bodys 1 t2 -> term (trm_let t1 t2).
Proof. 
  destruct 2. apply_fresh* term_let.
Qed.

Lemma term_match_to_body : forall t1 t2 b p, 
  term (trm_match t1 p b t2) -> bodys (pat_arity p) b.
Proof.
  intros. unfold bodys. inversions* H.
Qed.

Lemma body_to_term_match : forall t1 t2 b p,
  term t1 -> term t2 -> bodys (pat_arity p) b -> 
  term (trm_match t1 p b t2).
Proof. 
  destruct 3. apply_fresh* term_match.
Qed.
 
Hint Resolve body_to_term_abs term_abs_to_body
             body_to_term_fix term_fix_to_body
             body_to_term_match
             body_to_term_let.

Hint Extern 1 (bodys (pat_arity ?p) ?e) =>
  match goal with H: context [trm_match ?t1 p e ?t2] |- _ =>
    apply (@term_match_to_body t1 t2) end.

Hint Extern 1 (bodys 1 ?t2) =>
  match goal with H: context [trm_let ?t1 t2] |- _ =>
    apply (@term_let_to_body t1) end.

(** ** Opening a body with a term gives a term *)

Lemma open_terms : forall t us,
  bodys (length us) t ->
  terms (length us) us -> 
  term (t ^^ us).
Proof. 
  introv [L K] WT. pick_freshes (length us) xs. lets Fr': Fr.
  rewrite (fresh_length Fr) in WT, Fr'.
  rewrite~ (@substs_intro xs). apply* substs_terms.
Qed.

Hint Resolve open_terms.

(** The matching function returns a list of terms of the expected length. *)

Lemma pat_match_terms : forall p t ts,
  (pat_match p t) = Some ts -> term t -> 
  terms (pat_arity p) ts.
Proof.
  induction p; simpl; introv EQ TT;
   try solve [ inversions EQ; auto ]; 
   destruct t; inverts EQ as EQ; inversions TT; auto*.
  remember (pat_match p1 t1) as K1. symmetry in HeqK1.
   remember (pat_match p2 t2) as K2. symmetry in HeqK2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions EQ. unfolds terms. apply* list_for_n_concat.
Qed.

(* ====================================================================== *)
(** * Properties of types *)

(** Open on a type is the identity. *)

Lemma typ_open_type : forall T Us,
  type T -> T = typ_open T Us.
Proof.
  introv W. induction T; simpls; inversions W; f_equal*.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma typ_subst_fresh : forall X U T, 
  X \notin typ_fv T -> 
  typ_subst X U T = T.
Proof.
  intros. induction T; simpls; f_equal*. case_var*. 
Qed.

Lemma typ_subst_fresh_list : forall z u ts,
  z \notin typ_fv_list ts ->
  ts = LibList.map (typ_subst z u) ts.
Proof.
  induction ts; simpl; intros Fr.
  auto.
  rewrite typ_fv_list_cons in Fr.
   rew_map. f_equal. rewrite~ typ_subst_fresh. auto.
Qed.

Lemma typ_subst_fresh_trm_fvars : forall z u xs,
  fresh (\{z}) (length xs) xs ->
  typ_fvars xs = LibList.map (typ_subst z u) (typ_fvars xs).
Proof.
  intros. apply typ_subst_fresh_list.
  induction xs.
  unfold typ_fvars. rew_map. rewrite~ typ_fv_list_nil. 
  unfold typ_fvars. rew_map. 
   rew_length in H. simpl in H. destruct H.
   rewrite typ_fv_list_cons. simple~.
Qed.

Lemma typ_substs_fresh : forall xs us t, 
  fresh (typ_fv t) (length xs) xs -> 
  typ_substs xs us t = t.
Proof.
  induction xs; simpl; intros us t Fr.
  auto. destruct us. auto.
  inversions Fr. rewrite* typ_subst_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma typ_subst_open : forall X U T1 T2, type U -> 
  typ_subst X U (typ_open T1 T2) = 
   typ_open (typ_subst X U T1) (LibList.map (typ_subst X U) T2).
Proof.
  intros. induction T1; intros; simpl; f_equal*.
  apply list_map_nth. apply* typ_subst_fresh. 
  case_var*. apply* typ_open_type.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma typ_subst_open_vars : forall X Ys U T, 
  fresh \{X} (length Ys) Ys -> 
  type U ->
     typ_open_vars (typ_subst X U T) Ys
   = typ_subst X U (typ_open_vars T Ys).
Proof.
  introv Fr Tu. unfold typ_open_vars.
  rewrite* typ_subst_open. f_equal.
  induction Ys.
  auto.
  rew_length in Fr. simpl in Fr. destruct Fr.
   unfold typ_fvars. rew_map. simpl. case_var. f_equal*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma typ_substs_intro_ind : forall T Xs Us Vs, 
  fresh (typ_fv T \u typ_fv_list Vs \u typ_fv_list Us) (length Xs) Xs -> 
  types (length Xs) Us ->
  types (length Vs) Vs ->
  typ_open T (Vs ++ Us) = typ_substs Xs Us (typ_open T (Vs ++ (typ_fvars Xs))).
Proof.
  induction Xs; introv Fr Tu Tv.
  destruct Us. auto. inverts Tu; false.
  destruct Us. inverts Tu; false. simpl. 
  destruct Tu as [E M]. rew_length in *. simpl in Fr. inverts Fr.
  rewrite typ_fv_list_cons in *. rewrite typ_fvars_cons.
  inversions M. rewrite app_last.
  forwards K: (IHXs Us (Vs++t::nil)); clear IHXs.
     rewrite typ_fv_list_app. rewrite typ_fv_list_cons. rewrite~ typ_fv_list_nil.
    auto. 
    split~. inversions Tv. apply* Forall_app.  
  rewrite K. clear K. 
  f_equal. rewrite~ typ_subst_open. rewrite~ typ_subst_fresh.
  f_equal. rew_map. simpl. case_var; tryfalse.
  f_equal. apply~ typ_subst_fresh_list.
  f_equal. apply* typ_subst_fresh_trm_fvars.
Qed.

Lemma typ_substs_intro : forall Xs Us T, 
  fresh (typ_fv T \u typ_fv_list Us) (length Xs) Xs -> 
  types (length Xs) Us ->
  (typ_open T Us) = typ_substs Xs Us (typ_open_vars T Xs).
Proof.
  intros. apply~ (@typ_substs_intro_ind T Xs Us nil).
  change (typ_fv_list nil) with (\{}:vars). auto*.
Qed.

(** Types are stable by type substitution *)

Lemma typ_subst_type : forall T Z U,
  type U -> type T -> type (typ_subst Z U T).
Proof.
  induction 2; simpls*. case_var*.
Qed.

Hint Resolve typ_subst_type.

(** Types are stable by iterated type substitution *)

Lemma typ_substs_types : forall Xs Us T,
  types (length Xs) Us ->
  type T ->
  type (typ_substs Xs Us T).
Proof.
  induction Xs; destruct Us; simpl; introv TU TT; auto.
  destruct TU. simpls. inversions H. inversions* H0.
Qed.

(** List of types are stable by type substitution *)

Lemma typ_subst_type_list : forall Z U Ts n,
  type U -> types n Ts -> 
  types n (LibList.map (typ_subst Z U) Ts).
Proof.
  unfold types, list_for_n.
  induction Ts; destruct n; simpl; intros TU [EQ TT]. 
  auto. auto. inversion EQ.
  rew_length in EQ. rew_list. inversions TT. 
   forwards [M ?]: (IHTs n). auto. auto. rewrite~ M. 
Qed.

(** ** Opening a body with a list of types gives a type *)

Lemma typ_open_types : forall T Us,
  typ_body (length Us) T ->
  types (length Us) Us -> 
  type (typ_open T Us).
Proof. 
  introv [L K] WT. pick_freshes (length Us) Xs. lets Fr': Fr.
  rewrite (fresh_length Fr) in WT, Fr'.
  rewrite~ (@typ_substs_intro Xs). apply* typ_substs_types.
Qed.


(* ====================================================================== *)
(** * Properties of schemes *)

(** Substitution for a fresh name is identity. *)

Lemma sch_subst_fresh : forall X U M, 
  X \notin sch_fv M -> 
  sch_subst X U M = M.
Proof.
  intros. destruct M as [n T]. unfold sch_subst.
  rewrite* typ_subst_fresh.
Qed.

(** Trivial lemma to unfolding definition of [sch_subst] by rewriting. *)

Lemma sch_subst_fold : forall Z U T n,
  Sch n (typ_subst Z U T) = sch_subst Z U (Sch n T).
Proof.
  auto.
Qed. 

(** Distributivity of type substitution on opening of scheme. *)

Lemma sch_subst_open : forall Z U M Us,
   type U ->
    typ_subst Z U (sch_open M Us)
  = sch_open (sch_subst Z U M) (LibList.map (typ_subst Z U) Us).
Proof.
  unfold sch_open. intros. destruct M. simpl.
  rewrite* <- typ_subst_open.
Qed.

(** Distributivity of type substitution on opening of scheme with variables. *)

Lemma sch_subst_open_vars : forall Z U M Xs,
   fresh (\{Z}) (length Xs) Xs -> 
   type U ->
    typ_subst Z U (sch_open_vars M Xs)
  = sch_open_vars (sch_subst Z U M) Xs.
Proof.
  unfold sch_open_vars. intros. destruct M.
  rewrite* <- typ_subst_open_vars.
Qed.

(** Schemes are stable by type substitution. *)

Lemma sch_subst_type : forall Z U M,
  type U -> scheme M -> scheme (sch_subst Z U M).
Proof.
  unfold scheme, sch_subst. intros Z U [n T] TU S.
  simpls. destruct S as [L K]. exists (L \u \{Z}).
  introv Fr. rewrite* typ_subst_open_vars.
Qed.

Hint Resolve sch_subst_type.

(** Scheme arity is preserved by type substitution. *)

Lemma sch_subst_arity : forall X U M, 
  sch_arity (sch_subst X U M) = sch_arity M.
Proof.
  auto.
Qed.

(** ** Opening a scheme with a list of types gives a type *)

Lemma sch_open_types : forall M Us,
  scheme M ->
  types (sch_arity M) Us ->
  type (sch_open M Us).
Proof. 
  unfold scheme, sch_open. intros [n T] Us WB [Ar TU].
  simpls. subst n. apply* typ_open_types.
Qed.

Hint Resolve sch_open_types.


(* ====================================================================== *)
(** * Helper lemams*)

Lemma factorize_map : forall Z U xs Us,
  length xs = length Us ->
   xs ~* (LibList.map (Sch 0) (LibList.map (typ_subst Z U) Us))
 = (map (sch_subst Z U) (xs ~* (LibList.map (Sch 0) Us))).
Proof.
  induction xs; introv E; destruct Us; tryfalse.
  rew_map. rewrite singles_nil. rewrite~ map_empty.
  rew_length in E. inverts E. do 2 rewrite LibList.map_cons.
  rewrite map_cons. do 2 rewrite singles_cons.
  rewrite map_push. fequals~. 
Qed.


(* ====================================================================== *)
(** * Properties of store *)

Lemma phi_ok_binds : forall P l T,
   phi_ok P -> binds l T P -> type T.
Proof.
  introv O B. induction P using env_ind.
  false* binds_empty_inv.
  inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). subst.
     lets [[? ?]|[? ?]]: (binds_push_inv B); subst~.
Qed.

Lemma sto_ok_binds : forall mu l t,
   sto_ok mu -> binds l t mu -> term t.
Proof.
  introv O B. induction mu using env_ind.
  false* binds_empty_inv.
  inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). subst.
     lets [[? ?]|[? ?]]: (binds_push_inv B); subst~.
Qed.

Hint Resolve phi_ok_binds sto_ok_binds.


(* ====================================================================== *)
(** * Properties of judgments *)


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  induction 1; auto*.
Qed.

(** A typing relation is restricted to well-formed objects. *)

(* Helper tactics to name all the hypotheses *)

Tactic Notation "split4" "in" ident(H) :=
  let H1 := fresh in let H2 := fresh in
  let H3 := fresh in let H4 := fresh in
  destruct H as [H1 [H2 [H3 H4]]].

Lemma typing_regular : forall E P e T,
  typing E P e T -> ok E /\ phi_ok P /\ term e /\ type T.
Proof.
  intros. induction H; try solve [ splits* 4 ].
  pick_fresh x. forwards~ K: (H1 x). split4 in K.
   lets: (ok_concat_inv H2). splits*.
   apply_fresh term_abs. intros y Fry. forwards* K2: (H1 y).
  pick_fresh x. pick_fresh f. forwards~ K: (H1 f x). split4 in K.
    lets [Ok1 ?]: (ok_concat_inv H2). lets: (ok_concat_inv Ok1). splits*.
   apply_fresh term_fix. intros g y Fry. forwards* K2: (H1 g y).
  pick_fresh x. forwards~ K: (H4 x). split4 in K.
   lets: (ok_concat_inv H5). splits*. lets: value_regular.
   apply_fresh* term_let. intros y Fry. forwards* K2: (H4 y).
  pick_freshes (pat_arity p) xs. forwards~ K: (H2 xs). split4 in K.
   lets: (ok_concat_inv H4). splits*.
   apply_fresh* term_match. intros ys Frys. forwards* K2: (H2 ys).
  split4 in IHtyping1. inversions* H4.
  split4 in IHtyping. inversions* H3.
Qed. 

(** A fails relation only holds on pairs of locally-closed terms. *)

Lemma fails_regular : forall t e,
  fails t e -> term t /\ term e.
Proof.
  lets: value_regular. induction 1; jauto.
Qed.

(** A reduction relation only holds only on well-formed objects. *)

Lemma red_regular : forall c c',
  red c c' -> 
     (term (fst c) /\ term (fst c'))
  /\ (sto_ok (snd c) /\ sto_ok (snd c')).
Proof.
  lets: value_regular. induction 1; simpl; jauto.
  splits_all~. forwards~ K: pat_match_terms H4.
   rewrite (proj1 K) in H2, K. apply* open_terms.
  lets: (fails_regular H2). jauto.
Qed.

(** Number of types in pattern typing environment matches pattern arity *)

Lemma pat_typing_arity : forall Us p T,
  Us \= p ~: T -> length Us = pat_arity p.
Proof. introv H. induction H; rew_length; simpl; auto. Qed.

Lemma pat_typing_arity_elim : forall xs Us p T L,
  Us \= p ~: T -> fresh L (pat_arity p) xs -> length xs = length Us.
Proof.
  introv H F. lets: (fresh_length F).
  lets: (pat_typing_arity H). congruence.
Qed. 


(* ********************************************************************** *)
(** ** Automation for well-formedness *)

(** Automation for reasoning on well-formedness. *)

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: typing E _ _ _ |- _ => apply (proj1 (typing_regular H))
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ _ t _ |- _ => apply (proj43 (typing_regular H))
  | H: red (t,_) _ |- _ => apply (proj41 (red_regular H))
  | H: red _ (t,_) |- _ => apply (proj42 (red_regular H))
  | H: value t |- _ => apply (value_regular H)
  | H: fails t _ |- _ => apply (proj1 (fails_regular H))
  | H: fails _ t |- _ => apply (proj2 (fails_regular H))
  end.

Hint Extern 1 (sto_ok ?mu) =>
  match goal with
  | H: red (_,mu) _ |- _ => apply (proj1 (proj2 (red_regular H)))
  | H: red _ (_,mu) |- _ => apply (proj2 (proj2 (red_regular H)))
  | H: sto_typing _ mu |- _ => apply (proj42 H)
  end.

Hint Extern 1 (phi_ok ?P) =>
  match goal with
  | H: typing _ P _ _ |- _ => apply (proj42 (typing_regular H))
  | H: sto_typing P _ |- _ => apply (proj41 H)
  end.

Hint Extern 1 (type ?T) => match goal with
  | H: typing _ _ _ T |- _ => apply (proj44 (typing_regular H))
  end.


