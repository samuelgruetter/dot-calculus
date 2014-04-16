(***************************************************************************
* Safety for STLC with Patterns - Proofs                                  *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import List LibLN 
  STLC_PatOpen_Definitions 
  STLC_PatOpen_Infrastructure.


(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. inductions Typ gen G end; introv Ok.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs. 
   do_rew* concat_assoc (apply* H0).
  apply_fresh* typing_let as xs. 
    do_rew* concat_assoc (apply* H2).
  auto*.
  auto*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall M F E t T m,
  ((E & M) & F) |= t ~: T ->
  dom m = dom M ->
  typings E m M ->
  (E & F) |= subst m t ~: T.
Proof.
  introv Typt Dom Typm. inductions Typt gen F end;
   introv; simpl subst.
  sets_eq r: (get x m). symmetry in EQr. destruct r.
    fold (binds x t m) in EQr.
     lets T1 B Typt: (Typm _ _ EQr).
        (*TODO: x in dom m, therefore x # F*) 
     skip_rewrite (T = T1). (* car binds x T M *)
     apply_empty* typing_weaken.
    apply~ typing_var.
    eapply binds_remove. eauto.
    rewrite <- Dom. apply~ get_none_inv.
  apply_fresh typing_abs. 
   rewrite (@subst_open_vars).
   do_rew concat_assoc (apply* H0).
  apply_fresh* typing_let as xs.
   rewrite* subst_open_vars.
   do_rew* concat_assoc (apply* H2).
  auto*.
  auto*.
Qed.

(** Typing the result of pattern matching. *)

Hint Resolve binds_single_eq.

Lemma typing_pattern_match : forall p t T E m M,
  pat_match p t m ->
  E |= t ~: T ->
  M \= p ~: T ->
  typings E m M.
Proof.
  introv Pat. inductions Pat gen E M T end; 
   introv Typt Typp; intros y vy By.
  inverts Typp. exists T.
   destruct (binds_single_inv By). subst~.
  inverts Typp. false.  
  inverts Typp as K11 K12 Dis. inverts Typt.
   skip Bcase: (binds y vy i1 \/ binds y vy i2). clear By.
   destruct Bcase as [B | B].
   forwards* R: IHPat1. destruct (R _ _ B) as [T [? ?]].
    exists T. split~. skip: (y # E2).
     (* binds y E1 -> disjoint E1 E2 -> y # E2 *)
     apply~ binds_concat_left.
   forwards* R: IHPat2. destruct (R _ _ B) as [T [? ?]].
    exists T. split~. skip: (y # E1).
     apply~ binds_concat_right.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma pat_match_terms : forall xs ts p t, 
  pat_match p t (xs ~* ts) -> forall L n, 
  fresh L n xs ->
  n = (length ts) ->
  terms (length xs) ts.
Proof.
  introv Pat Fr. 
 lets B: (proj33 (pat_match_regular Pat)).
 intros.  subst. split. 
 rewrite~ (fresh_length Fr). 
 apply~ (@terms_of_singles_terms xs).
Qed.

Lemma preservation_result : preservation.
Proof.
  introv Typ. inductions Typ gen t' end;
   introv Red; inversions Red.
  pick_freshes (pat_arity p1) xs.
   forwards~ K: (H10 xs). clear H10.
   forwards* K': (pat_match_terms _ _ K).
   rewrite* (@subst_intro xs).
   apply_empty* (@typing_subst (xs~*Us)).
   lets: (fresh_length Fr).
   do 2 (rewrite dom_singles; try congruence).
   apply* typing_pattern_match. 
  auto*.
  inversions Typ1. pick_fresh x.
   rewrite* (@subst_intro (x::nil)).
   apply_empty* (@typing_subst (x~S)).
   rewrite singles_one.
   apply* typing_pattern_match.   
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(** Lemma : well-typed pattern matching never fails. *)

Lemma matching_successful : forall p M v T,
  M \= p ~: T ->
  empty |= v ~: T ->
  value v ->
  exists m, pat_match p v m /\ dom m = dom M.
Proof.
  introv Typp. inductions Typp gen v end; introv Typv Valv.
  eauto.
  eauto.
  inverts Typv; inverts Valv.
   forwards* [i1 [Mat1 Dom1]]: IHTypp1.
   forwards* [i2 [Mat2 Dom2]]: IHTypp2.
   exists (i1 & i2). split. 
     apply* pat_match_pair.
      rewrite (pat_binds_fct (proj1 (pat_match_regular Mat1)) 
                             (pat_typing_regular Typp1)).
      rewrite (pat_binds_fct (proj1 (pat_match_regular Mat2)) 
                             (pat_typing_regular Typp2)). auto.
     do 2 rewrite dom_concat. congruence.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  false. 
  left*. 
  right. destruct~ IHTyp as [Val1 | [t1' Red1]].
    pick_freshes (pat_arity p1) xs.
    forwards~ K: (H0 xs). clear H0. clear H1 H2. 
    destruct~ (matching_successful (v:=t1) K) as [m [Mat Dom]].
     rewrite (@singles_keys_values _ m) in *.
     exists (t2 ^^ (values m)). apply_fresh* red_let as ys.
     skip_rewrite (length (values m) = length (keys m)).
     skip_rewrite (keys m = xs). rewrite~ (fresh_length Fr).
     skip. (* renaming of matching ! *)
    exists* (trm_let p1 t1' t2). cuts~ : (pattern p1).
      lets _ M: (typing_regular Typ'). inversions~ M.
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


