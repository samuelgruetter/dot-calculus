(***************************************************************************
* Safety for STLC with References - Proofs                                 *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN STLC_Ref_Definitions STLC_Ref_Infrastructure.

(* ********************************************************************** *)
(** * Proofs *)

Hint Constructors typing.

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F P t T,
   (E & G) ! P |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) ! P |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F E P t T z u U,
  (E & z ~ U & F) ! P |= t ~: T ->
  E ! P |= u ~: U ->
  (E & F) ! P |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; introv Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(** Typing is preserved by an extension of store typing. *)

Lemma typing_stability : forall P E P' t T,
  E ! P |= t ~: T ->
  extends P P' ->
  E ! P' |= t ~: T.
Proof.
  introv Typ Ext. induction* Typ.
Qed.

Hint Resolve typing_stability.


(** Store typing preserved by allocation of a well-typed term. *)

Lemma sto_typing_push : forall P mu l t T,
  P |== mu ->
  empty ! P |= t ~: T ->
  l # mu -> l # P ->
  (P & l ~ T) |== (mu & l ~ t).
Proof.
  unfold sto_typing. introv [StoOk [Dom Ext]]. splits 3.
    auto.
    intros l0 Fr. simpl_dom. lets: (Dom l0).
      asserts* Fr2: (l <> l0). asserts* Fr3: (l0 # P). auto.
    intros l' T' Has. binds_cases Has.
      destruct (Ext _ _ B) as [t' [Hast' Typt']].
       exists* t'. 
      subst. exists* t.
Qed.    

(** A simple short-hand to help clarifying the following proof.
  It simply destruct the induction hypothesis into smaller pieces. *)

Ltac pres H t' mu' :=
  let P' := fresh "P'" in
  let Ext := fresh "Ext" in
  let Typt' := fresh "Typt'" in
  let TypSto' := fresh "TypSto'" in
  destruct~ (H (@refl_equal env empty) t' mu') 
                  as [P' [Ext [Typt' TypSto']]].  


(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t' mu'. gen_eq E: (empty : env). 
  induction Typ; intros EQ t' mu' Red TypSto; subst; 
   inversions Red. (* todo env_fix.*)
  exists P. inversions Typ1. splits~ 3.
    pick_fresh x. rewrite* (@subst_intro x).
     apply_empty* typing_subst.
  pres IHTyp1 t1' mu'. exists* P'. 
  pres IHTyp2 t2' mu'. exists* P'. 
  exists (P & l ~ T).
   asserts Fr: (l # P). lets: (proj32 TypSto). auto.
   splits~ 3. apply* sto_typing_push.
  pres IHTyp t1' mu'. exists* P'. 
  exists P. splits~ 3. 
    inversions Typ. 
     destruct~ ((proj33 TypSto) l T) as [t [Hast Typt]].
     rewrite~ (binds_func H4 Hast).
  pres IHTyp t1' mu'. exists* P'. 
  exists P. inversions Typ1. splits~ 3.
    destruct TypSto as [StoOk [Dom Map]]. splits~ 3.
     intros. tests: (l = l0). 
       exists t2. split~. rewrite~ (binds_func H H6).
       destruct (Map _ _ H) as [t [Has Typ]]. exists* t.  
  pres IHTyp1 t1' mu'. exists* P'. 
  pres IHTyp2 t2' mu'. exists* P'.
Qed.


(** Progression (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (empty : env). lets Typ': Typ.
  induction Typ; intros; subst.
  false* binds_empty_inv. 
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' [mu' Red1]]].
    destruct~ IHTyp2 as [Val2 | [t2' [mu' Red2]]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2) mu. 
      exists* (trm_app t1 t2') mu'. 
    exists* (trm_app t1' t2).
  left*.
  left*.
  right. destruct~ IHTyp as [Val1 | [t1' [mu' Red1]]].
    destruct (var_fresh (dom mu)) as [l Fr].
     exists* (trm_loc l) (mu & l ~ t1).
    exists* (trm_ref t1') mu'. 
  right. destruct~ IHTyp as [Val1 | [t1' [mu' Red1]]].
    inversions Val1; inversions Typ.  
     destruct ((proj33 H0) _ _ H5) as [t' [Has' Typt']].
     exists* t' mu.
    exists* (trm_get t1') mu'.
  right. destruct~ IHTyp1 as [Val1 | [t1' [mu' Red1]]]. 
    destruct~ IHTyp2 as [Val2 | [t2' [mu' Red2]]].
      inversions Val1; inversions Typ1.  
       destruct ((proj33 H0) _ _ H5) as [t' [Has' Typt']].
       exists* trm_unit (mu & l ~ t2). 
      exists* (trm_set t1 t2') mu'. 
    exists* (trm_set t1' t2) mu'.
Qed.

 
