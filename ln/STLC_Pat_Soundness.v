(***************************************************************************
* Safety for STLC with Patterns - Proofs                                  *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import List LibLN 
  STLC_Pat_Definitions 
  STLC_Pat_Infrastructure.


(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. inductions Typ with gen_eq H:(E & G) 
   and gen G, introv end; introv Ok.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs. 
   do_rew* concat_assoc (apply* H0).
  apply_fresh* typing_let as xs. 
    do_rew* concat_assoc (apply* H1).
  auto*.
  auto*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F U E t T z u,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. inductions Typt with gen_eq G:(E & z ~ U & F)
   and gen F, introv end; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs. 
   rewrite* subst_open_vars.
   do_rew concat_assoc (apply* H0).
  apply_fresh* typing_let as xs.
   rewrite* subst_open_vars.
   do_rew* concat_assoc (apply* H1).
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
  intros Us E xs. inductions xs with gen Us E end; 
   simpl; introv Le Typts Typt. auto.
  destruct ts; simpls; inversions Le. inversions Typts. 
  rewrite iter_push_cons in Typt. 
  rewrite <- concat_assoc in Typt.
  apply* (@IHxs Us0).
  apply* typing_subst.
Qed.

(** Typing the result of pattern matching. *)

Lemma typing_pattern_match : forall p t T E ts Us,
  Pat_match ts p t ->
  E |= t ~: T ->
  Pat_typing Us p T ->
  typings E ts Us.
Proof.
  introv Pat. induction Pat; introv Typt Typp.
Admitted.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; inversions Red.
  pick_freshes (pat_arity p1) xs.
   asserts_skip: (terms (length xs) ts).
   rewrite* (@substs_intro xs).
   apply~ (@typing_substs Us). unfolds~ terms.
   apply~ (@typing_pattern_match p1 t1 T).
  auto*.
  inversions Typ1. pick_fresh x.
    rewrite* (@substs_intro (x::nil)). unfolds substs.
    apply_empty* typing_subst.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(** Lemma : well-typed pattern matching never fails. *)

Lemma matching_successful : forall p Us v T,
  empty |= v ~: T ->
  value v ->
  Pat_typing Us p T ->
  exists vs, Pat_match vs p v.
Proof.

  (* todo : prouver que :
  pat_typing Us p T ->   (* induction là dessus *)
  binds p ns ->
  empty |= v ~: T -> 
  value v ->
  exists ms, .


   *)
  
Admitted.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ with gen_eq E:(empty:env).
  false. 
  left*. 
  right. destruct~ IHTyp as [Val1 | [t1' Red1]].
    destruct~ (@matching_successful p1 Us t1 T) as [vs Eq].
     exists~ (t2 ^^ vs).
    exists* (trm_let p1 t1' t2).
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1.
       exists* (t0 ^^ (t2::nil)). 
      exists* (trm_app t1 t2'). 
    exists* (trm_app t1' t2).
  destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
     right. exists* (trm_pair t1 t2').
     right. exists* (trm_pair t1' t2).
Qed.


