(***************************************************************************
* Safety for STLC with Datatypes - Proofs                                  *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import List LibLN 
  STLC_Data_Definitions 
  STLC_Data_Infrastructure.

(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs. intros y Fr. 
   do_rew* concat_assoc (apply* H0).
  apply_fresh* typing_fix. intros y f Fr2.
   do_rew_2* concat_assoc (apply* H0).
  apply_fresh* (@typing_match T Us). intros xs Fr.
    do_rew* concat_assoc (apply* H1).
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F U E t T z u,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq (E & z ~ U & F) as G. gen F.
  induction Typt; introv Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs. intros y Fr.
   rewrite* subst_open_vars.
   do_rew concat_assoc (apply* H0).
  apply_fresh typing_fix. intros y f Fr.
   rewrite* subst_open_vars.
   do_rew_2 concat_assoc (apply* H0).
  apply_fresh* (@typing_match T Us). intros xs Fr.
   rewrite* subst_open_vars.
   do_rew* concat_assoc (apply* H1).
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(** Typing is preserved by iterated substitution. *)

Lemma typing_substs : forall Us E xs ts t T,
   length xs = length ts ->
   typings E ts Us ->
   E & (iter_push xs Us) |= t ~: T ->
   E |= substs xs ts t ~: T.
Proof.
  intros Us E xs. gen Us E. 
  induction xs; simpl; introv Le Typts Typt. auto.
  destruct ts; simpls; inversions Le. inversions Typts. 
  rewrite iter_push_cons in Typt. 
  rewrite <- concat_assoc in Typt.
  apply* (@IHxs Us0).
  apply* typing_subst.
Qed.

(** Typing the result of pattern matching. *)

Lemma typing_pattern_match : forall p t T E ts Us,
  Some ts = pat_match p t ->
  E |= t ~: T ->
  Us \= p ~: T ->
  typings E ts Us.
Proof.
  induction p; introv EQ Typt Typp; destruct t; 
   inversion Typp; inversion EQ; auto; subst; inversions Typt; auto*.
  remember (pat_match p1 t1) as K1. 
   remember (pat_match p2 t2) as K2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions H6. apply* typings_concat.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; inversions Red.
  pick_freshes (pat_arity p) xs.
   forward~ (@pat_match_terms p t1 ts) as K.
   rewrite (fresh_length _ _ _ Fr) in K.
   rewrite* (@substs_intro xs).
   apply~ (@typing_substs Us). unfolds terms. auto. 
   apply~ (@typing_pattern_match p t1 T).
  auto*.
  auto*.
  inversions Typ1. pick_fresh x.
    rewrite* (@substs_intro (x::nil)). unfolds substs.
    apply_empty* typing_subst.
  inversions Typ1. pick_fresh f. pick_fresh x.
    rewrite* (@substs_intro (x::f::nil)). unfolds substs.
    apply_empty* typing_subst.
    apply_empty* typing_subst. 
    apply_empty* typing_weaken. 
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty : env) as E. poses Typ' Typ.
  induction Typ; intros; subst.
  contradictions. 
  left*. 
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    remember (pat_match p t1) as r. symmetry in Heqr. destruct r as [ts|]. 
      exists* (e ^^ ts). 
      exists* t2.
    exists* (trm_match t1' p e t2).
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1.
        exists* (t0 ^^ (t2::nil)). 
        exists* (t0 ^^ (t2::(trm_fix t0)::nil)).
      exists* (trm_app t1 t2'). 
    exists* (trm_app t1' t2).
  left*.
  destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
     right. exists* (trm_pair t1 t2').
     right. exists* (trm_pair t1' t2).
  destruct~ IHTyp as [Val1 | [t1' Red1]].
    right. exists* (trm_inj1 t1').
  destruct~ IHTyp as [Val1 | [t1' Red1]].
    right. exists* (trm_inj2 t1').
Qed.


