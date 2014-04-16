(***************************************************************************
* Confluence property for parallel reductions in the ISK system            *
* Arthur Charguéraud, January 2009, updated November 2011                  *
***************************************************************************)

(** NOT COMPLETE: contains only the diamond property for parallel reductions *)

Require Import LibTactics.
Set Implicit Arguments.


(* ********************************************************************** *)
(** Definitions *)

Inductive term : Set :=
  | I : term
  | K : term
  | S : term
  | App : term -> term -> term.

Definition relation := term -> term -> Prop.

Inductive base : relation :=
  | base_I : forall M, 
     base (App I M) M
  | base_K : forall M N, 
     base (App (App K M) N) M
  | base_S : forall F G N, 
     base (App (App (App S F) G) N) (App (App F N) (App G N)).

Inductive para : relation :=
  | para_refl : forall M, 
      para M M
  | para_base : forall M N, 
      base M N -> para M N
  | para_app : forall M1 M2 N1 N2,
      para M1 M2 -> para N1 N2 -> para (App M1 N1) (App M2 N2).

Hint Constructors base para.


(* ********************************************************************** *)
(** Facts *)

Definition not_base T := forall M, ~ (base T M).

Lemma not_base_I : not_base I.
Proof. introv H. inverts H. Qed.

Lemma not_base_K : forall M, ~ (base K M).
Proof. introv H. inverts H. Qed.

Lemma not_base_S : forall M, ~ (base S M).
Proof. introv H. inverts H. Qed.

Lemma not_base_K_arg : forall M N, ~ (base (App K M) N).
Proof. introv H. inverts H. Qed.

(** The above lemmas are not actually used in the later proofs because
    they are derivable by a simple inversion *)


(* ********************************************************************** *)
(** Lemmas *)

Lemma base_functional : forall M N1 N2,
  base M N1 -> base M N2 -> N1 = N2.
Proof. introv H1 H2. inverts H1; inverts~ H2. Qed.

Lemma join_base_base : forall M N1 N2,
  base M N1 -> base M N2 -> exists Q, para N1 Q /\ para N2 Q.
Proof. introv H1 H2. rewrite* (base_functional H1 H2). Qed.

Lemma para_app_k : forall M N,
  para (App K M) N -> exists P, para M P /\ N = App K P.
Proof.
  introv H. inverts H as.
    exists* M.
    introv B. inverts B.
    introv B1 B2. exists N2. split~. fequals. 
     inverts B1 as H. auto. inverts H.
Qed.

Lemma para_app_s : forall F1 G1 N,
  para (App (App S F1) G1) N ->
  exists F2 G2,
    para F1 F2 /\ para G1 G2 /\ N = App (App S F2) G2.
Proof.
   introv H. inverts H as.
   exists~ F1 G1.
   introv B1. inverts B1.
   introv B1 B2. inverts B1.
     exists~ F1 N2.
     inverts H.
     exists N0 N2. splits~.
       inverts H1 as H. auto. inverts H.
Qed.

Lemma base_app_para : forall M1 M2 N1 N2 P,
  base (App M1 N1) P -> (para M1 M2) -> (para N1 N2) ->
  exists Q, para P Q /\ para (App M2 N2) Q.
Proof.
  introv R0 R1 R2. inverts R0.
    exists N2. split~. inverts R1 as H. auto. inverts~ H.
    lets (Q&R3&EQ): (para_app_k R1). subst. exists* Q.
    lets (F2&G2&R3&R4&EQ): (para_app_s R1). subst.
      exists* (App (App F2 N2) (App G2 N2)). 
Qed.

Lemma join_base_para : forall M N1 N2,
  base M N1 -> para M N2 ->
  exists Q, para N1 Q /\ para N2 Q.
Proof.
  introv R1 R2. inverts R2.
  exists* N1.
  applys join_base_base; eauto.
  applys base_app_para; eauto.
Qed.

Lemma para_diamond :
  forall M N P, para M N -> para M P -> 
  exists Q, para N Q /\ para P Q.
Proof.
  introv R1 R2. gen P. induction R1; intros.
  exists* P.
  applys join_base_para; eauto.
  inverts R2.  
    exists* (App M2 N2).
    forwards* (Q&R3&R4): base_app_para H R1_1 R1_2.
    forwards~ (Q1&R3&R4): IHR1_1 M3.
     forwards* (Q2&R5&R6): IHR1_2 N3.
Qed.


(* ********************************************************************** *)
(** Additional definitions *)

Inductive red : relation :=
  | red_base : forall M N,
      base M N -> red M N
  | red_app1 : forall M1 M2 N,
      red M1 M2 -> red (App M1 N) (App M2 N)
  | red_app2 : forall M N1 N2,
      red N1 N2 -> red (App M N1) (App M N2).

Hint Constructors red.

