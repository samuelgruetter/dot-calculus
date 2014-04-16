(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Proofs                   *
* Arthur Charguéraud, January 2009                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN 
  STLC_Mut_Definitions 
  STLC_Mut_Infrastructure.

Definition ltac_tag_prop (n : nat) (A : Type) (x : A) := x.

Ltac tag_goal n :=
 match goal with |- ?G => 
   change G with (ltac_tag_prop n G) end.

Ltac intros_until_tag :=
  match goal with 
  | |- ltac_tag_prop _ _ => idtac
  | |- ?P -> ?Q => 
     let H := fresh in
     intro H; unfold ltac_tag_subst in H; 
     intros_until_tag
  | |- forall _, _ => 
     intro; intros_until_tag
  end.

Ltac intros_for_tag tac1 tac2 :=
  match goal with 
   | |- ltac_tag_prop 1 _ => tac1
   | |- ltac_tag_prop 2 _ => tac2
   | |- _ => idtac
 end.

Ltac mut_induct lemma tac1 tac2 :=
  apply lemma;
  intros_until_tag;
  unfold ltac_tag_prop in *|- ;
  intros_for_tag tac1 tac2.

Lemma demo : 
   (forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T)
/\ (forall G E F v T,
   (E & G) \= v ~: T -> 
   ok (E & F & G) ->
   (E & F & G) \= v ~: T).
Proof.
  evar (A':Prop); evar (B':Prop).
  cuts P Q: (A' /\ B'); subst A' B'; 
   [ split; [ clear Q | clear P; rename Q into P ] | ].
  match type of P with ?T =>
  change T with (ltac_tag_prop 1 T) in P end.
  introv Typt. gen_eqs Typt. 
   gen E F G. tag_goal 1. gen aux t T.
   match goal with H: ltac_tag_prop 1 _ |- _ => 
     unfold ltac_tag_prop in H; apply H end.
  introv Typt. gen_eqs Typt. 
   gen E F G. tag_goal 2. gen aux v T. apply P.
  mut_induct typing_val_trm_induct
    ltac:(introv Ok) ltac:(introv Ok).
  (*
   apply typing_val_trm_induct;
   intros_until_tag;
   unfold ltac_tag_prop in *|- ;
   match goal with 
   | |- ltac_tag_prop 1 _ => introv Ok
   | |- ltac_tag_prop 2 _ => introv Ok
   end.
  *)
  apply* typing_val_var. apply* binds_weaken.
  apply_fresh* typing_val_abs. apply_ih_bind* H0.
  apply* typing_trm_val.
  apply* typing_trm_app.
Qed.



(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : 
   (forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T)
/\ (forall G E F v T,
   (E & G) \= v ~: T -> 
   ok (E & F & G) ->
   (E & F & G) \= v ~: T).
Proof.
  evar (A':Prop); evar (B':Prop).
  cuts P Q: (A' /\ B'); subst A' B'; 
   [ split; [ clear Q | clear P; rename Q into P ] | ].
  introv Typt. gen_eqs Typt. 
   gen E F G. gen aux t T. apply P.
  introv Typt. gen_eqs Typt. 
   gen E F G. gen aux v T. apply P.

  apply typing_val_trm_induct; intros_all.
  apply* typing_val_var. apply* binds_weaken. skip.
  apply_fresh* typing_val_abs. apply_ih_bind* Hyp0.

  apply* typing_trm_val.
  apply* typing_trm_app.
Qed.

(* TODO

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F U E t T z u,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. inductions Typt gen F end; introv; simpl.
  case_var. 
    binds_mid~. apply_empty* typing_weaken.
    apply~ typing_var. apply* binds_subst.
  apply_fresh typing_abs.
   rewrite* subst_open_var. 
   apply_ih_bind* H0.
  apply* typing_app.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. inductions Typ gen t' end; 
   introv Red; inversions Red.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
   apply_empty* typing_subst.
  apply* typing_app. 
  apply* typing_app.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  false. 
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2).
      exists* (trm_app t1 t2'). 
    exists* (trm_app t1' t2).
Qed.

*)

