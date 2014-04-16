(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists accessed with integers instead of natural numbers                 *
**************************************************************************)

Set Implicit Arguments. 
Generalizable Variables A B.
Require Import LibTactics LibLogic LibOperation LibReflect
  LibProd LibNat LibInt LibOption LibWf.
Require Export LibList LibNat.
Require Import LibInt.
Open Local Scope comp_scope.

(** Set up specialized automation for this file *)

Ltac auto_tilde ::= eauto with maths.

(* ********************************************************************** *)
(** * Z indices *)

Section Zindices.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types i : int.

Definition ZNth i l x := 
  Nth (abs i) l x /\ 0 <= i.

Definition ZInbound i l := 
  0 <= i /\ i < length l.

Definition ZUpdate i x l l' :=
  Update (abs i) x l l' /\ 0 <= i.

Lemma ZNth_here : forall i x l,
  i = 0 -> ZNth i (x::l) x.
Proof. intros. subst. split~. constructor. Qed. 

Lemma ZNth_zero : forall x l,
  ZNth 0 (x::l) x.
Proof. intros. apply~ ZNth_here. Qed.

Lemma ZNth_next : forall i j x y l,
  ZNth j l x -> i = j+1 -> ZNth i (y::l) x.
Proof.
  introv [H P] M. subst. split~.
  applys_eq* Nth_next 3. rew_abs_pos~. 
Qed.
 
Lemma ZNth_app_l : forall i x l1 l2,
  ZNth i l1 x -> ZNth i (l1 ++ l2) x.
Proof. introv [H P]. split~. apply~ Nth_app_l. Qed.

Lemma ZNth_app_r : forall i j x l1 l2,
  ZNth j l2 x -> i = j + length l1 -> ZNth i (l1 ++ l2) x.
Proof.
  introv [H P]. split~. subst. 
  apply* Nth_app_r. rew_abs_pos~. 
Qed.

Lemma ZNth_nil_inv : forall i x,
  ZNth i nil x -> False.
Proof. introv [H P]. apply* Nth_nil_inv. Qed.

Lemma ZNth_cons_inv : forall i x l,
  ZNth i l x -> 
     (exists q, l = x::q /\ i = 0)
  \/ (exists y q j, l = y::q /\ ZNth j q x /\ i = j+1).
Proof.
  introv [H P]. forwards~: (@abs_pos i).
  destruct (Nth_cons_inv H); intuit.
  left. exists___. split~. 
  right. exists___. splits~.
   split. rewrite* abs_pos_nat. math.
   math.
Qed.

Lemma ZNth_inboud : forall i l,
   ZInbound i l -> exists x, ZNth i l x.
Proof.
  introv [P U]. gen_eq n: (abs i). 
  gen i l. induction n; intros; 
    forwards~: (@abs_pos i); destruct l; rew_length in U; try math.
  math_rewrite (i = 0). exists __. split~. constructor.
  forwards~ [x [M P']]: (>> IHn (i-1) l).
    forwards~: (@abs_spos i).
    exists x. split~. rewrite~ (@abs_spos i). constructor~.
Qed.

Lemma ZInbound_zero : forall x l,
  ZInbound 0 (x::l).
Proof. split; rew_list~. Qed. 

Lemma ZInbound_zero_not_nil : forall x l,
  l <> nil -> ZInbound 0 l.
Proof. intros. split~. destruct l; tryfalse. rew_list~. Qed.

Lemma ZInbound_cons : forall i j x l,
  ZInbound j l -> j = i-1 -> ZInbound i (x::l).
Proof. introv [P U] H. split; rew_list~. Qed. 

Lemma ZInbound_nil_inv : forall i,
  ZInbound i nil -> False.
Proof. introv [P U]. rew_list in U. math. Qed.

Lemma ZInbound_cons_inv : forall i x l,
  ZInbound i (x::l) -> i = 0 \/ (i <> 0 /\ ZInbound (i-1) l).
Proof.
  introv [P U]. rew_length in U. tests: (i = 0).
    left~.
    right~. split. math. split~.
Qed.

Lemma ZInbound_cons_pos_inv : forall i x l,
  ZInbound i (x::l) -> i <> 0 -> ZInbound (i-1) l.
Proof.
  introv H P. destruct* (ZInbound_cons_inv H).
Qed.

Lemma ZInbound_one_pos_inv : forall i x,
  ZInbound i (x::nil) -> i <> 0 -> False.
Proof.
  intros. eapply ZInbound_nil_inv. apply* ZInbound_cons_pos_inv.
Qed.

Lemma ZInbound_app_l_inv : forall i l1 l2,
  ZInbound i (l1++l2) -> i < length l1 -> ZInbound i l1.
Proof. introv [P U] H. split~. Qed. 

Lemma ZInbound_app_r_inv : forall i j l1 l2,
  ZInbound j (l1++l2) -> j = length l1 + i -> i >= 0 -> ZInbound i l2.
Proof. introv [P U] R H. rew_length in U. split~. Qed.

Lemma ZUpdate_here : forall x y l,
  ZUpdate 0 x (y::l) (x::l).
Proof. split~. apply Update_here. Qed.

Lemma ZUpdate_cons : forall i j x y l l',
  ZUpdate j x l l' -> i = j+1 -> ZUpdate i x (y::l) (y::l').
Proof.
  introv [U P] H. split~. applys_eq~ Update_cons 4.
  subst. rew_abs_pos~.
Qed.  

Lemma ZUpdate_app_l : forall i x l1 l1' l2,
  ZUpdate i x l1 l1' -> ZUpdate i x (l1++l2) (l1'++l2).
Proof. introv [U P]. split~. apply~ Update_app_l. Qed.

Lemma ZUpdate_app_r : forall i j x l1 l2 l2',
  ZUpdate j x l2 l2' -> i = j + length l1 -> ZUpdate i x (l1++l2) (l1++l2').
Proof.
  introv [U P] H. split~. apply~ Update_app_r. 
  subst. rew_abs_pos~.
Qed.

Lemma ZUpdate_not_nil : forall i x l1 l2,
  ZUpdate i x l1 l2 -> l2 <> nil.
Proof. introv [U P]. apply~ Update_not_nil. Qed.

Lemma ZUpdate_length : forall i x l l',
  ZUpdate i x l l' -> length l = length l'.
Proof. introv [U P]. apply~ Update_length. Qed. 

End Zindices.


(* ********************************************************************** *)
(** * Restore default automation *)

Ltac auto_tilde ::= auto_tilde_default.

