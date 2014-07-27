(***************************************************************************
* Safety for STLC in Wright & Felleisen style - Proofs                     *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN 
  STLC_Core_WF_Definitions 
  STLC_Core_WF_Infrastructure.


(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply* typing_app.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F E t T z u U,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; intros G Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  apply* typing_app.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ Red. gen T.
  induction Red; intros T Typ.
  (* case: beta *)
  inversions Typ. inversions H4.
  pick_fresh x. rewrite* (@subst_intro x).
  apply_empty* typing_subst.
  (* case: ctx *)
  gen t' T. induction C; simpls; intros t' Red SR T Typ.
  auto*.
  inversions Typ. apply* typing_app.
  inversions Typ. apply* typing_app.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ.
  cuts K: (value t \/ exists c, exists t0, exists t0', 
                     red t0 t0' /\ t = ctx_of c t0).
  destruct K as [Val | [C [t1a [t1'a [Red Ctx]]]]]; subst*.
  gen_eq E: (empty : env). lets Typ': Typ.
  induction Typ; intros; subst.
  false (binds_empty_inv H0).
  left*.
  right. destruct~ IHTyp1 as [Val1 | [C [t1a [t1'a [Red1 Ctx1]]]]].
    destruct~ IHTyp2 as [Val2 | [C [t2a [t2a' [Red2 Ctx2]]]]].
      inversions Typ1; inversions Val1.
        exists ctx_hole (trm_app (trm_abs t0) t2) (t0 ^^ t2). split*.
        subst. exists (ctx_app_2 C Val1). eauto.
      subst. asserts* W: (term t2). exists (ctx_app_1 C W). eauto.
Qed.

