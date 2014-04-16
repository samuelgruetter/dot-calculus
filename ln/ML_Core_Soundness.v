(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Charguéraud, March 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import List LibLN 
  ML_Core_Definitions
  ML_Core_Infrastructure.

(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars L E t M := forall Xs, 
  fresh L (sch_arity M) Xs ->
  E |= t ~: (M ^ Xs).

Definition has_scheme E t M := forall Vs,
  types (sch_arity M) Vs -> 
  E |= t ~: (M ^^ Vs).

(* ********************************************************************** *)
(** Type substitution preserves typing *)

Lemma typing_typ_subst : forall F Z U E t T,
  Z \notin (env_fv E) -> 
  type U -> 
  E & F |= t ~: T -> 
  E & (map (sch_subst Z U) F) |= t ~: (typ_subst Z U T).
Proof.
  introv. intros WVs Dis Typ. gen_eq G: (E & F). gen F.
  induction Typ; introv EQ; subst; simpls typ_subst.
  rewrite~ sch_subst_open. apply* typing_var.
    binds_cases H0.
      apply* binds_concat_left.
       rewrite* sch_subst_fresh. lets: (fv_in_values_binds B).
       unfolds subset. unfolds notin. eauto.
       (* todo: use a lemma to deal with the inclusion *)
      auto*.
    rewrite~ sch_subst_arity. apply* typ_subst_type_list.
  apply_fresh* typing_abs as y.
   rewrite sch_subst_fold.   
   apply_ih_map_bind* H1.
  apply_fresh* (@typing_let (sch_subst Z U M) (L1 \u \{Z})) as y.
    simpl in Fry. rewrite* <- sch_subst_open_vars.
    apply_ih_map_bind* H2.
  auto*.
Qed.

(* ********************************************************************** *)
(** Iterated type substitution preserves typing *)

Lemma typing_typ_substs : forall Zs Us E t T,
  fresh (env_fv E) (length Zs) Zs -> 
  types (length Zs) Us ->
  E |= t ~: T -> 
  E |= t ~: (typ_substs Zs Us T).
Proof.
  induction Zs; destruct Us; simpl; introv Fr WU Tt;
   destruct Fr; inversions WU; 
   simpls; try solve [ auto | false* ].
  inversions H2. inversions H1.
  apply* IHZs. apply_empty* typing_typ_subst.
Qed.

(* ********************************************************************** *)
(** Type schemes of terms can be instantiated *)

Lemma has_scheme_from_vars : forall L E t M,
  has_scheme_vars L E t M ->
  has_scheme E t M.
Proof.
  intros L E t [n T] H Vs TV. unfold sch_open. simpls.
  pick_freshes n Xs.
  rewrite (fresh_length Fr) in TV, H.
  rewrite~ (@typ_substs_intro Xs Vs T).
  unfolds has_scheme_vars, sch_open_vars. simpls.
  apply* typing_typ_substs.
Qed.

(* ********************************************************************** *)
(** A term that has type T has type scheme "forall(no_var).T" *)

Lemma has_scheme_from_typ : forall E t T,
  E |= t ~: T -> has_scheme E t (Sch 0 T).
Proof.
  intros_all. unfold sch_open. simpls.
  rewrite* <- typ_open_type.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H1.
  apply_fresh* (@typing_let M L1) as y. apply_ih_bind* H2.
  auto*.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by term substitution *)

Lemma typing_trm_subst : forall F M E t T z u, 
  E & z ~ M & F |= t ~: T ->
  has_scheme E u M -> 
  term u ->
  E & F |= (trm_subst z u t) ~: T.
Proof.
  introv Typt. intros Typu Wu. 
  gen_eq G: (E & z ~ M & F). gen F.
  induction Typt; introv EQ; subst; simpl trm_subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y. 
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H1. 
  apply_fresh* (@typing_let M0 L1) as y. 
   rewrite* trm_subst_open_var. 
   apply_ih_bind* H2. 
  auto*.
Qed.

(* ********************************************************************** *)
(** Preservation: typing is preserved by reduction *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; subst; inversions Red.
  pick_fresh x. rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst. 
   apply* (@has_scheme_from_vars L1). 
  apply* (@typing_let M L1).
  inversions Typ1. pick_fresh x. 
   rewrite* (@trm_subst_intro x). 
   apply_empty* typing_trm_subst.
   apply* has_scheme_from_typ.
  auto*.
  auto*.
Qed. 

(* ********************************************************************** *)
(** Progress: typed terms are values or can reduce *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (empty:env). lets Typ': Typ.
  induction Typ; intros; subst. 
  false* binds_empty_inv.
  left*. 
  right. pick_freshes (sch_arity M) Ys.
    destruct~ (@H0 Ys) as [Val1 | [t1' Red1]]. 
      exists* (t2 ^^ t1). 
      exists* (trm_let t1' t2).
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]]. 
    destruct~ IHTyp2 as [Val2 | [t2' Red2]]. 
      inversions Typ1; inversion Val1. exists* (t0 ^^ t2).
      exists* (trm_app t1 t2'). 
    exists* (trm_app t1' t2).
Qed.


