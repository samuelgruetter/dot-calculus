(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require Import ML_Definitions ML_Infrastructure.


(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars L E P t M := forall Xs, 
  fresh L (sch_arity M) Xs ->
  E ! P |= t ~: (M ^ Xs).

Definition has_scheme E P t M := forall Vs,
  types (sch_arity M) Vs -> 
  E ! P |= t ~: (M ^^ Vs).

(* ********************************************************************** *)
(** Type substitution preserves typing of patterns *)

Lemma pat_typing_typ_subst : forall Z U Us p T,
  Us \= p ~: T ->
  LibList.map (typ_subst Z U) Us \= p ~: typ_subst Z U T.
Proof.
  induction 1; simpls*. rew_map; auto. rew_map; auto.
Qed.  

(* ********************************************************************** *)
(** Type substitution preserves typing of expressions *)

Lemma typing_typ_subst : forall F P Z U E t T,
  Z \notin (env_fv E) -> Z \notin (phi_fv P) -> type U -> 
  E & F ! P |= t ~: T -> 
  E & (map (sch_subst Z U) F) ! P |= t ~: (typ_subst Z U T).
Proof.
  introv. intros Fr1 Fr2 WVs Typ. gen_eq G: (E & F). gen F.
  induction Typ; intros F EQ; subst; simpls typ_subst.
  rewrite~ sch_subst_open. apply* typing_var.
    binds_cases H1.
      apply* binds_concat_left.
       rewrite* sch_subst_fresh. applys~ (@fv_in_values_binds sch) B.
      auto*.
    rewrite~ sch_subst_arity. apply* typ_subst_type_list.
  apply_fresh* typing_abs. intros y Fr.
   rewrite sch_subst_fold.   
   apply_ih_map_bind* H1.
  apply_fresh* typing_fix. intros f y Fr.
   applys_eq* H1 4. do 2 rewrite <- concat_assoc. fequal.
   do 2 rewrite map_concat. do 2 rewrite map_single.
   do 2 rewrite concat_assoc. fequals.
  apply_fresh* (@typing_let (sch_subst Z U M) (L1 \u \{Z})).
   simpl. intros Ys Fr. rewrite* <- sch_subst_open_vars.
   intros y Fr. apply_ih_map_bind* H4.
  apply_fresh* (@typing_match (typ_subst Z U T) 
                              (LibList.map (typ_subst Z U) Us)).
    apply* pat_typing_typ_subst.
    intros xs Fr. 
     rewrite factorize_map; [| apply* pat_typing_arity_elim ].
     rewrite <- concat_assoc. rewrite <- map_concat.
     apply* H1. rewrite* concat_assoc.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  apply* typing_loc. rewrite* typ_subst_fresh.
   applys~ (@fv_in_values_binds typ) H1.
  auto*.
  auto*.
  apply* typing_set.
  apply* typing_raise.
   rewrite* <- (@typ_subst_fresh Z U typ_exn). 
  apply* typing_catch. 
   rewrite* <- (@typ_subst_fresh Z U typ_exn). 
Qed.

(* ********************************************************************** *)
(** Iterated type substitution preserves typing *)

Lemma typing_typ_substs : forall Zs Us E P t T,
  fresh (env_fv E \u phi_fv P) (length Zs) Zs -> 
  types (length Zs) Us ->
  E ! P |= t ~: T -> 
  E ! P |= t ~: (typ_substs Zs Us T).
Proof.
  induction Zs; destruct Us; simpl; introv Fr WU Tt;
   destruct Fr; inversions WU; 
   simpls; try solve [ auto | false* ].
  inverts H2. inverts H1.
  apply* IHZs. apply_empty* typing_typ_subst.
Qed.

(* ********************************************************************** *)
(** Type schemes can be instantiated *)

Lemma has_scheme_from_vars : forall L E P t M,
  has_scheme_vars L E P t M ->
  has_scheme E P t M.
Proof.
  intros L E P t [n T] H Vs TV. unfold sch_open. simpls.
  pick_freshes n Xs.
  rewrite (fresh_length Fr) in TV, H.
  rewrite~ (@typ_substs_intro Xs Vs T).
  unfolds has_scheme_vars, sch_open_vars. simpls.
  apply* typing_typ_substs.
Qed.

(* ********************************************************************** *)
(** A term that has type T has type scheme "forall(no_var).T" *)

Lemma has_scheme_from_typ : forall E P t T,
  E ! P |= t ~: T -> 
  has_scheme E P t (Sch 0 T).
Proof.
  intros_all. unfold sch_open. simpls. rewrite* <- typ_open_type.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall G E F P t T,
   (E & G) ! P |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) ! P |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs. intros y Fr. 
   do_rew* concat_assoc (apply* H1).
  apply_fresh* typing_fix. intros f y Fr2.
   do_rew_2 concat_assoc (apply* H1). auto. auto.
  apply_fresh* (@typing_let M L1). intros y Fr.
   do_rew* concat_assoc (apply* H4).
  apply_fresh* (@typing_match T Us). intros xs Fr.
    do_rew* concat_assoc (apply* H1).
    apply* (@ok_singles sch (pat_arity p)). 
    do 2 rewrite dom_concat. auto.
    rewrite length_map. apply* pat_typing_arity_elim.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(* ********************************************************************** *)
(** Values are preserved by term substitution *)

Lemma value_fv : forall z u t, 
  value u -> value t -> value ([z ~> u]t).
Proof.
  introv Valu Valt. induction Valt; simpls*.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by term substitution *)

Lemma typing_trm_subst : forall F M E P t T z u, 
  E & z ~ M & F ! P |= t ~: T ->
  has_scheme E P u M -> 
  value u ->
  E & F ! P |= (trm_subst z u t) ~: T.
Proof.
  introv Typt. intros Typu Valu. 
  gen_eq G: (E & z ~ M & F). gen F.
  induction Typt; intros G EQ; subst; simpl trm_subst.
  case_var.
    binds_get H1. apply_empty* typing_weaken.
    binds_cases H1; apply* typing_var.
  apply_fresh* typing_abs. intros y Fr.
   rewrite* subst_open_vars.
   do_rew* concat_assoc (apply* H1).
  apply_fresh* typing_fix. intros f y Fr.
   rewrite* subst_open_vars.
   do_rew_2 concat_assoc (apply* H1). auto.
  apply_fresh* (@typing_let M0 L1); try intros y Fr.
   apply* value_fv. 
   rewrite* subst_open_vars. do_rew* concat_assoc (apply* H4).
  apply_fresh* (@typing_match T Us). intros xs Fr.
   rewrite* subst_open_vars.
   do_rew* concat_assoc (apply* H1).
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
  auto*.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by iterated term substitution. *)

Lemma typing_trm_substs : forall Us E P xs ts t T,
   length xs = length ts ->
   typings E P ts Us ->
   (E & xs ~* (LibList.map (Sch 0) Us)) ! P |= t ~: T ->
   Forall value ts ->
   E ! P |= substs xs ts t ~: T.
Proof.
  introv EQ Typts Typt Val. gen Us ts t T.
  induction xs; destruct ts; intros; tryfalse.
  inversions Typts. inversions Val. rew_map in Typt. 
   rewrite singles_nil,concat_empty_r in Typt. auto.
  rew_length in EQ. inverts EQ as EQ.
   inversions Typts. inversions Val. rew_map in Typt. 
   rewrite singles_cons in Typt. rewrite concat_assoc in Typt.
   simpl. apply* (@IHxs Us0).
   apply_empty* typing_trm_subst. 
   apply* has_scheme_from_typ. apply_empty* typing_weaken.
   lets~ : (proj1 (typing_regular Typt)).
Qed.

(* ********************************************************************** *)
(** The result of pattern matching is a list of well-typed terms. *)

Lemma typing_pattern_match : forall p t T E P ts Us,
  Some ts = pat_match p t ->
  E ! P |= t ~: T ->
  Us \= p ~: T ->
  typings E P ts Us.
Proof.
  induction p; introv H1 H2 H0; destruct t; 
   inversion H0; inversion H1; auto; subst; inversions H2; auto*.
  remember (pat_match p1 t1) as K1. 
   remember (pat_match p2 t2) as K2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions H9. apply* typings_concat.
Qed.

(* ********************************************************************** *)
(** The result of pattern matching applied to a value is a list of values. *)

Lemma pattern_match_values : forall p t ts,
  Some ts = pat_match p t ->
  value t ->
  Forall value ts.
Proof.
  induction p; introv EQ Val; 
   destruct t; simpl in EQ; inversion EQ; auto; inversions Val; auto*.
  remember (pat_match p1 t1) as K1. 
   remember (pat_match p2 t2) as K2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions EQ. apply* Forall_app.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by an extension of store typing. 
    (This result is added to hints because we use it many times. *)

Lemma typing_stability : forall P E P' t T,
  E ! P |= t ~: T ->
  extends P P' -> 
  phi_ok P' ->
  E ! P' |= t ~: T.
Proof.
  introv Typ Ext. induction* Typ.
Qed.

Hint Resolve typing_stability.

(* ********************************************************************** *)
(** Store typing preserved by allocation of a well-typed term. *)

Lemma sto_typing_push : forall P mu l t T,
  P |== mu ->
  empty ! P |= t ~: T ->
  l # mu -> l # P ->
  (P & l ~ T) |== (mu & l ~ t).
Proof.
  unfold sto_typing. introv [PhiOk [StoOk [Dom Ext]]]. splits 4.
    auto.
    auto.
    intros l0 Fr. simpls. lets: (Dom l0). 
      asserts* Frl0: (l0 # P). auto.
    intros l' T' Has. binds_cases Has.
      destruct (Ext _ _ B) as [t' [Hast' Typt']].
       exists* t'. 
      subst. exists* t.
Qed.   

(* ********************************************************************** *)
(** Fails always returns an exception. *)

Lemma fails_to_exception : forall E P t T e,
  fails t e -> 
  E ! P |= t ~: T -> 
  E ! P |= e ~: typ_exn.
Proof.
  introv Fail Typ. induction Typ; inversions* Fail.
  pick_freshes (sch_arity M) Xs. forwards*: (H2 Xs).
Qed.

(* ********************************************************************** *)
(** Preservation: typing is preserved by reduction *)

(* A tactic to help us name nicely all the hypotheses *)
Ltac pres H t' mu' :=
  let P' := fresh "P'" in
  let Ext := fresh "Ext" in
  let Typt' := fresh "Typt'" in
  let TypSto' := fresh "TypSto'" in
  destruct~ (H (@refl_equal env empty) t' mu') 
                  as [P' [Ext [Typt' TypSto']]].  

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t' mu'. gen_eq E: (empty : env).
  induction Typ; intros EQ t' mu' Red TypSto; subst; 
   inversions Red. 
  exists P. splits~ 3. 
   pick_fresh x. forwards~ K: (H3 x). clear H2 H3 H4.
   rewrite~ (@substs_intro (x::nil)).
     simpl. apply_empty* typing_trm_subst.
      apply* (@has_scheme_from_vars L1).
     rewrite trm_fv_list_cons, trm_fv_list_nil. auto.
  exists P. splits~ 3. clear H1 IHTyp1 IHTyp2.
   forwards~ Wts: (@pat_match_terms _ _ _ H13).
   pick_freshes (pat_arity p) xs.
   rewrite~ (@substs_intro xs);
    [| rewrite~ <- (fresh_length Fr)].
   forwards~ K: (H0 xs). 
   rewrite (proj1 Wts) in Fr, Wts.
   apply_empty* (@typing_trm_substs Us). 
     rewrite* (fresh_length Fr).
     apply* typing_pattern_match.
     apply* pattern_match_values.
  exists P. splits~ 3.
  pres IHTyp1 t1' mu'. exists* P'.
  exists P. splits~ 3. 
   inversions Typ1. 
   pick_fresh x. forwards~ K: (H8 x). clear H8 IHTyp1 IHTyp2.
   rewrite~ (@substs_intro (x::nil)).
     simpl. apply_empty* typing_trm_subst.
      apply* has_scheme_from_typ.
     rewrite trm_fv_list_cons, trm_fv_list_nil. auto.
  exists P. splits~ 3. 
   inversions Typ1.
   pick_fresh f. pick_fresh x. rewrite~ (@substs_intro (x::f::nil)).
    apply_empty* (@typing_trm_substs (S::(typ_arrow S T)::nil)).
      rew_map. do 2 rewrite singles_cons. rewrite singles_nil.
       rewrite concat_empty_l. applys* H8.
      do 2 rewrite trm_fv_list_cons. rewrite trm_fv_list_nil. auto.
  exists P. splits~ 3. inversions Typ1. inversions* H4.
  pres IHTyp1 t1' mu'. exists* P'.
  pres IHTyp2 t2' mu'. exists* P'.
  pres IHTyp1 t1' mu'. exists* P'.
  pres IHTyp2 t2' mu'. exists* P'.
  pres IHTyp t1' mu'. exists* P'.
  pres IHTyp t1' mu'. exists* P'.
  exists (P & l ~ T). lets: (proj43 TypSto).
   splits~ 3. apply* sto_typing_push. 
  pres IHTyp t1' mu'. exists* P'. 
  exists P. splits~ 3. 
   inversions Typ. 
   destruct~ ((proj44 TypSto) l T) as [t [Hast Typt]].
   rewrite~ (binds_func H4 Hast).
  pres IHTyp t1' mu'. exists* P'.
  exists P. inversions Typ1. splits~ 3. 
   destruct TypSto as [PhiOk [StoOk [Dom Map]]]. splits~ 4.
    intros. tests: (l = l0). 
      exists t2. split~. rewrite~ (binds_func H H7).
      destruct (Map _ _ H) as [t [Has Typ]]. exists* t.  
  pres IHTyp1 t1' mu'. exists* P'.
  pres IHTyp2 t2' mu'. exists* P'.
  pres IHTyp t1' mu'. exists* P'. 
  exists* P.
  exists P. splits~ 3.
    apply* typing_app. apply* fails_to_exception.
  pres IHTyp2 t2' mu'. exists* P'.
Qed.

(* ********************************************************************** *)
(** A value cannot be reduced (needed for the let case of progress). *)

Lemma red_value_false : forall t, value t ->
  forall t' mu mu', (t, mu) --> (t', mu') -> False.
Proof.
  induction 1; introv Red; inversions* Red.
  inversions H5. inversions H5.
Qed.

(* ********************************************************************** *)
(** Progress: typed terms are values or can reduce *)

Hint Constructors fails.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (empty:env). lets Typ': Typ.
  induction Typ; intros; subst. 
  false* binds_empty_inv.
  branch* 1.
  branch* 1.
  asserts* K: (empty ! P |= (trm_let t1 t2) ~: T2).
   pick_freshes (sch_arity M) Ys.
    forwards~ [Val1 | [[e Fail] | [t1' [mu' Red1]]]]: (@H2 Ys).
     branch 3. exists* (t2 ^^ (t1::nil)) mu.
     branch 2. exists* e.
     false. apply* (red_value_false H Red1). 
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    branch 3. remember (pat_match p t1) as K. destruct K as [ts|].
      exists* (b ^^ ts) mu.
      exists* t2 mu.
    branch 2. exists* e. 
    branch 3. exists* (trm_match t1' p b t2) mu'.
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
      inversions Typ1; inversion Val1. 
        branch 3. exists* (t0 ^^ (t2::nil)) mu.
        branch 3. exists* (t0 ^^ (t2::(trm_fix t0)::nil)) mu. 
        branch 3. subst. inversions H. inversions Val2; inversions Typ2. 
           exists* (trm_nat (n + n0)) mu.
           inversions H5.
        branch 1. inversions Val2; inversions Typ2. 
          auto*.
          inversions H4.
        branch 2. exists* e.
        branch 3. exists* (trm_app t1 t2') mu'.
    branch 2. exists* e. 
    branch 3. exists* (trm_app t1' t2) mu'.
  branch* 1.
  branch* 1.  
  branch* 1.
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
      branch 2. exists* e.
      branch 3. exists* (trm_pair t1 t2').
    branch 2. exists* e.
    branch 3. exists* (trm_pair t1' t2).
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    branch 2. exists* e.
    branch 3. exists* (trm_inj1 t1') mu'.
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    branch 2. exists* e.
    branch 3. exists* (trm_inj2 t1') mu'.
  branch* 1.
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct (var_fresh (dom mu)) as [l Fr].
      branch 3. exists* (trm_loc l) (mu & l ~ t1).
      branch 2. exists* e.
    branch 3. exists* (trm_ref t1') mu'. 
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    inversions Val1; inversions Typ.
      inversion H4.  
      destruct ((proj44 H0) _ _ H6) as [t' [Has' Typt']].
       branch 3. exists* t' mu.
    branch 2. exists* e.
    branch 3. exists* (trm_get t1') mu'.
  destruct~ IHTyp1 as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
      inversions Val1; inversions Typ1.  
        inversion H4.
        destruct ((proj44 H0) _ _ H6) as [t' [Has' Typt']].
         branch 3. exists* trm_unit (mu & l ~ t2).
      branch 2. exists* e. 
      branch 3. exists* (trm_set t1 t2') mu'. 
    branch 2. exists* e.
    branch 3. exists* (trm_set t1' t2) mu'.
  destruct~ IHTyp as [Val1 | [[e Fail] | [t1' [mu' Red1]]]].
    branch 2. exists* t1. 
    branch 2. exists* e. 
    branch 3. exists* (trm_raise t1') mu'. 
  destruct~ IHTyp2 as [Val2 | [[e Fail] | [t2' [mu' Red2]]]].
    branch 3. exists* t2 mu. 
    branch 3. exists* (trm_app t1 e) mu.
    branch 3. exists* (trm_catch t1 t2') mu'. 
Qed.




