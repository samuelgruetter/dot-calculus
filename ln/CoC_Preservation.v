(***************************************************************************
* Calculus of Constructions - Subject Reduction                            *
* Arthur Charguéraud, April 2007                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoC_Definitions CoC_Infrastructure CoC_Conversion.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Inversion Lemmas for Subtyping *)

Lemma less_type_any_inv : forall T1 T2,
  less T1 T2 -> forall i1, conv T1 (trm_type i1) -> 
  exists i2, i1 <= i2 /\ conv T2 (trm_type i2).
Proof.
  induction 1; intros i1 C1.
  exists* i1.
  lets: (conv_type_type_inv C1). subst. exists* j.
  false. apply (conv_type_prod_inv (equiv_sym C1)).
  exists* i1.
  destruct (IHless1 _ C1) as [i2 [Le2 C2]].
   destruct (IHless2 _ C2) as [i3 [Le3 C3]].
   exists i3. auto* (Le.le_trans i1 i2 i3).
Qed.

Lemma less_type_type_inv : forall i j,
  less (trm_type i) (trm_type j) -> i <= j.
Proof.
  introv Le.
  destruct (@less_type_any_inv _ _ Le i) as [i' [Lei C]]. auto.
  lets: (conv_type_type_inv C). subst*.
Qed.

Lemma less_prod_any_inv : forall P1 P2,
  less P1 P2 -> forall U1 T1, conv P1 (trm_prod U1 T1) ->
  exists U2, exists T2, conv P2 (trm_prod U2 T2) 
  /\ conv U1 U2 
  /\ exists L, forall x, x \notin L -> less (T1 ^ x) (T2 ^ x).
Proof.
  induction 1; intros U1 T1 C1.
  exists U1 T1. 
   asserts* K: (term (trm_prod U1 T1)). inversions K.
   splits.
     apply* (@equiv_trans beta t1).
     auto.
     exists_fresh. auto.
  false. apply (conv_type_prod_inv C1).
  exists U' T'. 
   asserts* K: (less (trm_prod U T) (trm_prod U' T')).  
   destruct (conv_prod_prod_inv C1) as [C11 [L1 C12]].
   splits.
    auto.
    apply* (@equiv_trans beta U).
    exists_fresh. intros. apply (@less_trans (T ^ x)).
      forwards*: (C12 x). auto.
  exists U1 T1. asserts* K: (term (trm_prod U1 T1)). inversions* K.
  destruct (IHless1 _ _ C1) as [U2 [T2 [C2 [C21 [L2 C22]]]]].
   destruct (IHless2 _ _ C2) as [U3 [T3 [C3 [C31 [L3 C32]]]]].
   exists U3 T3. splits.
     auto.
     apply* (@equiv_trans beta U2).
     exists_fresh. intros. apply* (@less_trans (T2 ^ x)).
Qed.

Lemma less_prod_prod_inv : forall U1 T1 U2 T2,
  less (trm_prod U1 T1) (trm_prod U2 T2) -> 
     conv U1 U2
  /\ exists L, forall x, x \notin L -> less (T1 ^ x) (T2 ^ x).
Proof.
  introv Le.
  destruct (@less_prod_any_inv _ _ Le U1 T1) 
    as [U2' [T2' [C [C1' [L' C2']]]]]; auto.
  destruct (conv_prod_prod_inv C) as [C1 [L C2]].
  splits.
    apply* (@equiv_trans beta U2'). 
    exists_fresh. intros. apply (@less_trans (T2' ^ x)).
      auto.
      forwards*: (C2 x).
Qed.


(* ********************************************************************** *)
(** ** Inversion Lemmas for Typing *)

Lemma typing_prod_inv : forall E U T P,
  typing E (trm_prod U T) P -> exists i, exists k,
     less (trm_type i) P
  /\ typing E U (trm_type k)
  /\ (i = k \/ i = 0)
  /\ exists L, forall x, x \notin L -> typing (E & x ~ U) (T ^ x) (trm_type i).
Proof.
  introv Typ. gen_eq P1: (trm_prod U T). 
  induction Typ; intros; subst; tryfalse.
  inversions H2. exists* i k.
  destruct~ IHTyp1 as [i' [k' [EQi [TypU [Univ [L TypT]]]]]].
  exists i' k'. auto* (@less_trans T0).
Qed.

Lemma typing_abs_inv : forall E V t P,
  typing E (trm_abs V t) P -> exists T, exists i,
     typing E (trm_prod V T) (trm_type i)
  /\ less (trm_prod V T) P
  /\ exists L, forall x, x \notin L -> typing (E & x ~ V) (t ^ x) (T ^ x).
Proof.
  introv Typ. gen_eq u: (trm_abs V t).
  induction Typ; intros; subst; tryfalse.
  inversions H1. exists* T i.
  destruct~ IHTyp1 as [T' [i' [TypP [LeP [L TypB]]]]].
  exists T' i'. auto* (@less_trans T).
Qed.

Lemma typing_prod_type_inv : forall E U T i,
  typing E (trm_prod U T) (trm_type i) ->
  exists L, forall x, x \notin L -> 
      typing (E & x ~ U) (T ^ x) (trm_type i).
Proof.
  introv Typ. 
  destruct (typing_prod_inv Typ) as [i' [k' [Le [TypU [Uni [L TypT]]]]]].
  exists (L \u dom E). intros.
  inversion Le; apply* (@typing_sub (trm_type i') (i+1)). 
Qed.


(* ********************************************************************** *)
(** Typing preserved by Weakening *)

Lemma typing_weaken : forall G E F t T,
  typing (E & G) t T ->
  wf (E & F & G) -> 
  typing (E & F & G) t T.
Proof.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; eauto.
  (* case: var *)
  apply* typing_var. apply* binds_weaken.
  (* case: trm_prod *)
  apply_fresh* (@typing_prod k) as y. apply_ih_bind* H0.
  (* case: trm_abs *)
  apply_fresh* (@typing_abs i) as y.
  forwards TypP: (IHTyp G); auto.
  destruct (typing_prod_inv TypP) as [i' [k' [_ [TypU _]]]].
  apply_ih_bind* H0.
Qed.


(* ********************************************************************** *)
(** ** Subtyping preserved by Substitution *)

Lemma less_red_out : red_out less.
Proof.
  intros_all. lets: conv_red_out; induction H0; simpl; auto.
  apply_fresh* less_prod as y. cross*.
  apply* (@less_trans ([x ~> u]U)).
Qed.


(* ********************************************************************** *)
(** Typing preserved by Substitution *)

Lemma typing_substitution : forall V (F:env) v (E:env) x t T,
  typing E v V ->
  typing (E & x ~ V & F) t T ->
  typing (E & (map (subst x v) F)) (subst x v t) (subst x v T).
Proof.
  introv Typv Typt.
  gen_eq G: (E & x ~ V & F). gen F. 
  apply typing_induct with
   (P := fun (G:env) t T (Typt : typing G t T) => 
      forall (F:env), G = E & x ~ V & F -> 
      typing (E & map (subst x v) F) ([x ~> v]t) ([x ~> v]T))
   (P0 := fun (G:env) (W:wf G) => 
      forall F, G = E & x ~ V & F -> 
      wf (E & (map (subst x v) F))); 
   intros; subst; simpls subst. 
  (* case: trm_type *)
  auto*.
  (* case: var *)
  case_var.
    binds_mid~. rewrite* subst_fresh. apply_empty* typing_weaken.
    apply~ typing_var. destruct~ (binds_not_middle_inv b) as [K|[Fr K]].
      rewrite* subst_fresh.
  (* case: trm_prod *)
  apply_fresh* (@typing_prod k) as y.
   cross; auto. apply_ih_map_bind* H0. 
  (* case: trm_abs *)
  apply_fresh* (@typing_abs i) as y.
   cross; auto. apply_ih_map_bind* H0.
  (* case: trm_app *)
  rewrite* subst_open.
  (* case: sub *)
  apply* (@typing_sub ([x ~> v]T0)). apply* less_red_out.
  (* case: wf nil *)
  false (empty_middle_inv H).
  (* case: wf cons *)
  change LibEnv.env with LibEnv.env in *.
  induction F using env_ind.
    rewrite concat_empty_r in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_empty. rewrite~ concat_empty_r.
    clear IHF. rewrite concat_assoc in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_push. rewrite concat_assoc. apply* (@wf_cons i). 
  (* case: conclusion *)
  auto.
Qed.


(* ********************************************************************** *)
(** Types are Themselves Well-typed *)

Lemma typing_wf_from_context : forall x U (E:env),
  binds x U E -> 
  wf E -> 
  exists i, typing E U (trm_type i).
Proof.
  introv B W. induction E using env_ind. 
  false* binds_empty_inv. 
  destruct (binds_push_inv B) as [[? ?]|[? ?]]. 
    subst. inversions W. false (empty_push_inv H0).
     destruct (eq_push_inv H) as [? [? ?]]. subst.
     exists i. apply_empty* typing_weaken.
    destruct (wf_push_inv W). forwards~ [k P]: IHE.
     exists k. apply_empty* typing_weaken.
Qed.

Lemma typing_wf_from_typing : forall E t T,
  typing E t T ->
  exists i, typing E T (trm_type i).
Proof.
  induction 1.
  exists* ((i+1)+1).
  destruct* (typing_wf_from_context H0).
  exists* (i+1).
  exists* i.
  destruct IHtyping1 as [i Typ]. 
   destruct (typing_prod_inv Typ) as [i' [k' [Le [TypU [Uni [L TypT]]]]]].
   exists i'.
   pick_fresh x. rewrite~ (@subst_intro x).
   unsimpl ([x ~> u](trm_type i')).
   apply_empty* (@typing_substitution U).
  exists* i.
Qed.


(* ********************************************************************** *)
(** Typing preserved by Subtyping in Environment *)

Inductive env_less : env -> env -> Prop :=
  | env_less_head : forall E U U' x, 
      less U U' -> 
      env_less (E & x ~ U) (E & x ~ U')
  | env_less_tail : forall E E' x U,
      term U -> env_less E E' -> env_less (E & x ~ U) (E' & x ~ U).

Hint Constructors env_less.

Lemma env_less_binds : forall x U E E',
  env_less E' E -> wf E -> wf E' -> binds x U E -> 
     binds x U E' 
  \/ exists U', exists i, 
      binds x U' E' /\ less U' U /\ typing E' U (trm_type i).
Proof.
  introv Le. induction Le; intros WfE WfE' Has.
  destruct (binds_push_inv Has) as [[? ?]|[? ?]]. 
    subst. right. inversions WfE. false (empty_push_inv H1).
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     exists U0 i. splits~. apply_empty* typing_weaken.  
    left. apply~ binds_push_neq.
  destruct (binds_push_inv Has) as [[? ?]|[? ?]].
    subst. left. apply~ binds_push_eq.
    inversions keep WfE. false (empty_push_inv H3).
     inversions WfE'. false (empty_push_inv H6).
     destruct (eq_push_inv H5) as [? [? ?]]. subst.
     destruct (wf_push_inv WfE).
     destruct IHLe as [|[U' [i' [P1 [P2 P3]]]]]; auto. 
      right. exists U' i'. splits~. apply_empty* typing_weaken.
Qed. 

Lemma typing_sub_env : forall E E' t T,
  typing E t T -> 
  env_less E' E -> 
  wf E' -> 
  typing E' t T.
Proof.
 introv Typ. gen E'. induction Typ; intros E' C W; eauto.
 destruct (env_less_binds C H W H0) as [B |[U' [i [B [Le Typ]]]]].
   apply* typing_var.
   apply* (@typing_sub U' i).
  apply_fresh (@typing_prod k) as y; auto. apply* (H0 y).
  forwards~ TypP: (IHTyp E').
  destruct (typing_prod_inv TypP) as [i' [k [_ [Typt1 _]]]]. 
  apply_fresh (@typing_abs i) as y; auto. apply* (H0 y).
Qed.


(* ********************************************************************** *)
(** Subject Reduction - Induction *)

Lemma subject_reduction_ind : forall E t t' T,
  typing E t T -> beta t t' -> typing E t' T.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red;
   try solve [ apply* typing_sub ]; inversions Red.

  (* case: trm_prod 1 *)
  apply_fresh* (@typing_prod k) as y.
   apply (@typing_sub_env (E & y ~ U)); eauto 7. 

  (* case: trm_prod 2 *)
  apply_fresh* (@typing_prod k) as y.

  (* case: trm_abs 1 *)
  forwards~ Typt1'T: (IHTyp (trm_prod t1' T)).
  destruct (typing_prod_type_inv Typt1'T) as [L2 TypT].
  apply* (@typing_sub (trm_prod t1' T) i).
    apply_fresh less_prod as y.
      auto.
      forwards*: (H y).
    apply_fresh* (@typing_abs i) as y.
     forwards~ K: (TypT y).
     apply (@typing_sub_env (E & y ~ U)); eauto 7.

  (* case: trm_abs 2 *)
  apply_fresh* (@typing_abs i) as y.

  (* case: trm_app - beta reduction *)
  destruct (typing_abs_inv Typ1) as [T' [i [TypP [LeP [L1 Typt2]]]]].
  destruct (typing_prod_inv TypP) as [i' [k [EQi [Typt1 [Uni [L2 TypT']]]]]].
  destruct (less_prod_prod_inv LeP) as [C [L3 LeT]].
  destruct (typing_wf_from_typing Typ1) as [j TypUT].
  destruct (typing_prod_type_inv TypUT) as [L4 TypT].
  pick_fresh x.
   rewrite* (@subst_intro x t2).
   rewrite* (@subst_intro x T).
  apply_empty (@typing_substitution t1).
    apply* (@typing_sub U k).
    apply (@typing_sub (T' ^ x) j); auto.
     apply* (@typing_sub_env (E & x ~ U)).

  (* case: trm_app 1 *)
  auto*.

  (* case: trm_app 2 *)
  destruct (typing_wf_from_typing Typ1) as [i TypUT].
  destruct (typing_prod_type_inv TypUT) as [L TypT].
  apply* (@typing_sub (T ^^ t2') i).
    apply less_conv. apply* conv_from_open_beta.
    pick_fresh x. rewrite* (@subst_intro x T).
     unsimpl (subst x u (trm_type i)).
     apply_empty* (@typing_substitution U).

Qed.

(* ********************************************************************** *)
(** Subject Reduction - Beta preserves typing  *)

Lemma subject_reduction_result : subject_reduction beta.
Proof.
  introv Red Typ. apply* subject_reduction_ind.
Qed.

(* ********************************************************************** *)
(** Subject Reduction - Beta Star preserves typing  *)

Lemma subject_reduction_star_result : 
  subject_reduction (beta star).
Proof.
  introv H. induction* H. apply* subject_reduction_result.
Qed.


