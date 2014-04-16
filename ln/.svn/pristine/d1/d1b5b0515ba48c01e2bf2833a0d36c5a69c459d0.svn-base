(***************************************************************************
* Safety for STLC with Exceptions - Proofs                                 *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN 
  STLC_Exn_Definitions 
  STLC_Exn_Infrastructure.

(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply* typing_app.
  apply* typing_raise.
  apply* typing_catch.  
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F E t T z u U,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; introv Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  apply* typing_app.
  apply* typing_raise.
  apply* typing_catch. 
Qed.

(** Fails always returns a term of type exception. *)

Lemma fails_to_exception : forall E t T e,
  fails t e -> 
  E |= t ~: T -> 
  E |= e ~: typ_exn.
Proof.
  introv Fail Typ. induction Typ; inversions* Fail.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; inversions Red.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
   apply_empty* typing_subst.
  apply* typing_app.
  apply* typing_app.
  apply* typing_raise.
  apply* typing_catch.
  assumption.
  apply* typing_app. apply* fails_to_exception.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (empty : env). lets Typ': Typ.
  induction Typ; intros; subst.
  false* binds_empty_inv.
  branch* 1.
  right. destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' Red1]]].
    destruct~ IHTyp2 as [Val2 | [[e Fail2] | [t2' Red2]]].
      right. inversions Typ1; inversions Val1. exists* (t0 ^^ t2).
      left. exists* e.
      right. exists* (trm_app t1 t2').
    left. exists* e.
    right. exists* (trm_app t1' t2).
  right. destruct~ IHTyp as [Val1 | [[e Fail] | [t1' Red1]]].
    left. exists* t1.
    left. exists* e.
    right. exists* (trm_raise t1').
  branch 3. destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' Red2]]].
    exists* t2.
    exists* (trm_app t1 e).
    exists* (trm_catch t1 t2').
Qed.



