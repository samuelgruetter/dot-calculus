(**************************************************************************
* TLC: A library for Coq                                                  *
* Examples for LibFix                                                     *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibTactics LibLogic LibReflect LibFunc LibEpsilon LibList 
  LibInt LibNat LibProd LibSum LibRelation LibWf LibFix LibStream.
Require Import Div2.
Open Scope nat_scope.
Open Scope comp_scope.

(** Setting up of automation *)

Hint Resolve lt_wf : wf.

Ltac auto_tilde ::= auto with wf.
Ltac auto_star ::= try solve [ auto | false | math | intuition eauto ].

Hint Resolve list_equiv_equiv.


(* ********************************************************************** *)
(** * COFE for streams *)

(** Definition of stream ordered family of requiv *)

Definition stream_mod_family A (E:binary A) : family nat (stream A) := 
  nat_family (bisimilar_mod_upto E).

(** Special case of comparing stream values wrt equality *)

Definition stream_family A := stream_mod_family (@eq A).

(** Similarity for this OFE is equal to stream bisimilarity *)

Lemma stream_mod_similarity : forall A (E:binary A),
  bisimilar_mod E = similar (stream_mod_family E).
Proof.
  intros. apply prop_ext_2. intros s1 s2.
  unfold similar. simpl. split.
  intros. apply~ bisimilar_mod_to_upto.
  intros. apply~ bisimilar_mod_take.
Qed.

Hint Resolve stream_mod_similarity.

Lemma stream_similarity : forall A,
  @bisimilar A = similar (stream_family A).
Proof. intros. apply stream_mod_similarity. Qed.

Hint Resolve stream_similarity.

(** Completeness of the OFE *)

Hint Unfold list_equiv.
Hint Constructors Forall2.

Lemma stream_mod_cofe : forall A {IA:Inhab A} (E:binary A),
  equiv E -> COFE (stream_mod_family E).
Proof.
  introv IA Equiv. apply nat_cofe. typeclass.
  intros. apply~ bisimilar_mod_upto_equiv.
  introv H. exists (diagonal (fun i => u (S i)) 0).
  induction i; unfolds.
    simple~.
    apply~ bisimilar_mod_upto_succ. apply~ (trans_sym_1 (u i)).
    rewrite stream_diagonal_nth. math_rewrite~ (i + 0 = i).
Qed.

Lemma stream_cofe : forall A {IA:Inhab A}, COFE (stream_family A).
Proof. intros. apply~ stream_mod_cofe. Qed.

Hint Resolve @stream_cofe.


(* ********************************************************************** *)
(** * Constant stream -- basic corecursive value *)

Definition Const1 const1 := (1%nat) ::: const1.

Definition const1 := FixValMod (@bisimilar nat) Const1.

Lemma const1_fix : const1 === Const1 const1.
Proof. 
  applys (FixValMod_fix (stream_family nat)); auto~. typeclass.
  intros i s1 s2 H. simpls. destruct~ i.
  unfolds. simpl. constructor~. apply* H.
Qed.
 

(* ********************************************************************** *)
(** * Constant stream -- basic corecursion *)

Definition Const const (n:nat) := n ::: const n.

Definition const := FixFunMod (@bisimilar nat) Const.

Lemma const_fix : forall n, const n === Const const n.
Proof.
  intros. 
  applys (FixFunMod_corec (stream_family nat) (@pred_true nat)); auto*.
  apply stream_cofe.
  clear n. intros i n s1 s2 _ H. simpls. destruct~ i.
  unfolds. simpl. constructor~. apply* H. 
Qed.


(* ********************************************************************** *)
(** * Polymorphic Constant stream -- basic corecursion with polymorphism *)

Definition PConst A pconst (n:A) := n ::: pconst n.

Definition pconst `{IA:Inhab A} := FixFunMod (@bisimilar A) (@PConst A).

Lemma pconst_fix : forall A {IA:Inhab A} (n:A), 
  pconst n === PConst pconst n.
Proof.
  intros. 
  applys* (FixFunMod_corec (stream_family A) (@pred_true A)).
  clears n. intros i n s1 s2 _ H. simpls. destruct~ i.
  unfolds. simpl. constructor~. apply* H. 
Qed.

Lemma pconst_spec : forall A {IA:Inhab A} (x:A),
  LibStream.const x === pconst x.
Proof.
  intros.
  apply bisimilar_mod_take. induction i. simple~.
  apply* sym_elim. apply* trans_sym_2.
   apply bisimilar_mod_to_upto. apply pconst_fix.
   simpl. constructor~. 
Qed.

(* ********************************************************************** *)
(** * Mutually-defined stream -- basic corecursion *)
(* u = 1::2::3::1::2::3::1::2::3::1::2::3::1::2::3::...*)

Definition MU (mu mv : stream nat) := (1%nat) ::: mv.
Definition MV (mu mv : stream nat) := (2%nat) ::: ((3%nat) ::: mu).

Definition muv := FixValModMut2 (@bisimilar nat) (@bisimilar nat) MU MV.
Definition mu := fst muv.
Definition mv := snd muv.

Lemma uv_fix : mu === MU mu mv /\ mv === MV mu mv.
Proof.
  applys (FixValModMut2_fix 
    (prod_family (stream_family nat) (stream_family nat))).
  apply tuple2_from_proj.
  unfold bisimilar. rewrite stream_mod_similarity. apply prod_similar.
  apply prod_cofe; typeclass.
  intros i u1 v1 u2 v2 H. simpls. destruct~ i. split.
    unfolds. simpl. constructor~. apply* H. 
    unfolds. simpl. constructor~. destruct i. simple~. simpl.
     constructor~. apply* H.
Qed.

(* ********************************************************************** *)
(** * Stream of natural numbers *)

Definition Nats nats (n:nat) := n ::: nats (S n).

Definition nats := FixFunMod (@bisimilar nat) Nats.

Lemma nats_fix : forall (n:nat), 
  nats n === Nats nats n.
Proof.
  intros. 
  applys (FixFunMod_corec (stream_family nat) (@pred_true nat)); auto*.
  apply stream_cofe.
  clears n. intros i n s1 s2 _ H. simpls. destruct~ i.
  unfolds. simpl. constructor~. apply* H. 
Qed.


(* ********************************************************************** *)
(** * Filter on streams *)

Definition dist_to_next A (P:A->Prop) (s:stream A) := 
  epsilon (first_st_at P s).

Lemma eventually_to_dist : forall A (P:A->Prop) s,
  eventually P s -> exists n, first_st_at P s n.
Proof.
  introv H. induction H. exists 0. simple~.
  destruct (classic (P x)).
    exists 0. simple~.
    destruct IHeventually as [n Pn]. exists (S n). simple~.
Qed.

Lemma eventually_dist_cons : forall A (P:A->Prop) s x,
  eventually P s -> ~ P x -> 
  dist_to_next P s < dist_to_next P (x:::s).
Proof.
  introv H Nx. unfold dist_to_next.
  spec_epsilon as n Pn. apply~ eventually_to_dist.
  spec_epsilon as n' Pn'. apply~ eventually_to_dist.
   apply~ eventually_tail.
  clearbody n n'. destruct n'; simpl in Pn'; tryfalse.
  rewrite* (@first_st_at_unique n n' A P s).
Qed.

Section MyFilters.
Context (A:Type) {IA:Inhab A}.
Variable (P:A->Prop).

Definition Filter filter s :=
  let '(x:::s') := s in 
  let s'' := filter s' in
  If P x then x:::s'' else s''.

Definition filter := FixFunMod (@bisimilar A) Filter.

Lemma filter_fix : forall s,
  infinitely_often P s ->
  filter s === Filter filter s.
Proof.
  applys~ (FixFunMod_mixed_partial 
    (stream_family A)  
    (measure (dist_to_next P))
    (infinitely_often P)
    (@bisimilar A)). 
  intros i s f1 f2 Ps H. simpls.
  destruct s. simpl. unfolds. destruct i. simple~.
   inverts Ps as Ps' Ev. case_if as C.
     simpl. constructor~. apply~ H. left*.
     inverts Ev as Ev.
       false.
       apply~ H. right. split~. apply~ eventually_dist_cons.
Qed.       
     
 
End MyFilters.


(* ********************************************************************** *)
(** * The log function -- basic recursion *)

(** Definition of the functional *)

Definition Log log n :=
 If n <= 1 then 0 else 1 + log (div2 n).

(** Construction of the fixed point *)

Definition log := FixFun Log. 

Lemma fix_log : forall n, 
  log n = Log log n.
Proof. 
  applys~ (FixFun_fix (@lt nat _)). 
  introv H. unfolds. case_if~. 
  fequals. apply H. apply* div2_lt.
Qed.

(** Example of unfolding of the body *)

Lemma log_double : forall n, n > 0 ->
  log(2*n) = 1 + log n.
Proof.
  introv Pos. rewrite fix_log. unfold Log.
  case_if*. fequals. rewrite~ div2_double.
Qed.

(** Example of reasoning by induction *)

Lemma log_grows : forall n m, 
  m <= n -> log m <= log n.
Proof.
  induction n using peano_induction. introv Le.
  do 2 rewrite fix_log. unfolds Log.
  (do 2 case_if); auto*.
  rew_nat. apply H. apply* div2_lt. apply~ div2_grows. 
Qed.

(*
Extraction Language Haskell.
Extraction Inline Log.
Set Extraction Optimize.
Extraction log.
*)

(* ********************************************************************** *)
(** * Loop on odd numbers -- partial function *)

(** The function [F] defined in this module returns [1] 
    on any even number and "loops" on any odd number.
    It does not actually loop, since when a recursive
    call is not made on a smaller argument, the recursion
    is stopped and a dummy value is returned. *)

Require Import Even.

Definition Only_even only_even n :=
  If n = 0 then 1 else 
  If n = 1 then 1 + only_even 1 else
  only_even (n - 2).

Definition only_even := FixFun Only_even.

Lemma only_even_fix : forall n, even n ->
  only_even n = Only_even only_even n.
Proof.
  applys~ (FixFun_fix_partial (@lt nat _)).
  intros f1 f2 n Pn IH. unfolds. case_if~. case_if as C.
  subst. inverts Pn as Pn'. inverts Pn'.
  apply* IH. inverts Pn as Pn'; tryfalse. inverts Pn'. simpl. rew_nat~.
Qed.


(* ********************************************************************** *)
(** * GCD function (binary currified function, by measure) *)

Definition Gcd gcd x y :=
  If x = 0 then y else
  If y = 0 then x else
  If x <= y then gcd x (y-x) else gcd (x-y) y.

(** The measure is the sum of the arguments *)

Definition gcd := FixFun2 Gcd.

Lemma fix_gcd : forall x y, 
  gcd x y = Gcd gcd x y.
Proof.
  applys~ (FixFun2_fix (measure2 plus)).
  unfold measure2. introv IH. unfolds.
  case_if~. case_if~. case_if. apply* IH. apply* IH.
Qed.


(* ********************************************************************** *)
(** * Zero function (nested recursion) *)

(** [zero n] is a function that always returns [0]. *)

Definition Zero zero n :=
  If n = 0 then 0 else zero (zero (n-1)).

Definition zero := FixFun Zero.

Implicit Arguments FixFun_fix_partial_inv [A B F f].

Lemma zero_fix : forall x, zero x = Zero zero x 
              /\ forall x, zero x = 0.
Proof.
  forwards~ [H1 H2]: (FixFun_fix_partial_inv lt pred_true (fun (x y : nat) => y = 0) _ (F:=Zero)).
  introv _ H. unfold Zero. case_if~. 
  forwards* [H1 H2]: (H (x-1)). rewrite <- H1. rewrite H2. apply* H.
Qed.


(* ********************************************************************** *)
(** * Ackerman's function (nested non-primitive recursion, two arguments) *)

Ltac emaths := eauto with maths.

Definition Ack ack m n :=
  If m = 0 then n+1 else 
  If n = 0 then ack (m-1) 1 else
  ack (m-1) (ack m (n-1)).

Definition ack := FixFun2 Ack.

Lemma fix_ack : forall m n,
  ack m n = Ack ack m n.
Proof.
  applys~ (FixFun2_fix (lexico2 (@lt nat _) (@lt nat _))).
  introv IH. unfolds. case_if~. case_if~. 
  apply IH. emaths. 
  rewrite IH. fequals~. emaths. emaths.
Qed.


(* ********************************************************************** *)
(** * McCarthy's 91 function (nested recursion) *)

(** [McCarthy n] returns [n-10] if [n > 100] and returns
    [91] otherwise. It is defined using nested recursion. *)

Definition McCarthy mcCarthy n :=
  If n > 100 
    then n - 10
    else mcCarthy (mcCarthy (n + 11)).

Definition mcCarthy := FixFun McCarthy.

Definition McCarthy_post n r :=
  If n > 100 then r = n - 10 else r = 91.

Lemma McCarthy_fix_post : 
     (forall n, mcCarthy n = McCarthy mcCarthy n)
  /\ (forall n, McCarthy_post n (mcCarthy n)).
Proof.
  sets meas: (fun n => If n > 100 then 0 else 101 - n).
  applys~ (FixFun_fix_inv (measure meas)). introv IH. 
  unfold McCarthy. unfold McCarthy_post. case_if~.
  forwards [K1 K2]: IH (x+11). unfold measure, meas. case_if; case_if*. 
  rewrite <- K1 in *. sets y: (f1(x+11)). unfolds in K2.
  forwards [L1 L2]: IH y. unfold measure, meas. case_if; case_if*. case_if*. 
  rewrite <- L1 in *. sets z: (f1 y). unfolds in L2. split~.
  case_if*. case_if*.
Qed.

(** Corrolaries *)

Lemma McCarthy_fix : forall n, 
  mcCarthy n = McCarthy mcCarthy n.
Proof. apply (proj1 (McCarthy_fix_post)). Qed.

Lemma McCarthy_spec_gt100 : forall n,
  n > 100 -> mcCarthy n = n - 10.
Proof.
  introv Lt. lets H: (proj2 McCarthy_fix_post n). unfolds in H. case_if*.
Qed.

Lemma McCarthy_spec_le100 : forall n,
  n <= 100 -> mcCarthy n = 91.
Proof.
  introv Le. lets H: (proj2 McCarthy_fix_post n). unfolds in H. case_if*.
Qed.



(* ********************************************************************** *)
(** * Integer division (binary function) *)

Require Import Arith. (* todo : needed?*)

(** [div n m] returns a pair [(q,r)] such that  
    [n = q*m + r] with [r < m]. Its definition involves
    non-structural recursion. *)

Definition Div div n m :=
  If n < m then (0,n) 
  else let (q,r) := div (n-m) m : nat*nat in 
       (q+1,r).

Definition div := FixFun2 Div.

Lemma fix_div : forall n m, m <> 0 -> 
  div n m = Div div n m.
Proof.
  applys~ (FixFun2_fix_partial (measure (@fst nat nat))).
  introv Posm IH. unfold Div. case_if~.
  rewrite~ IH. unfolds. simpl. math. 
Qed.



(* ********************************************************************** *)
(** * A function on trees -- higher-order recursion *)

Definition Mem A (x:A) l := Exists (=x) l. (* todo: move *)

(** The congruence rule for [map] on lists *)

Lemma map_congr : forall A B (f1 f2 : A->B) l,
  (forall x, Mem x l -> f1 x = f2 x) ->
  LibList.map f1 l = LibList.map f2 l.
Proof. Hint Constructors Exists. Hint Unfold Mem.
  introv H. induction l. auto. rew_map. fequals~.
Qed.

(** Definition of trees *)

Inductive tree : Type := 
  | leaf : nat -> tree
  | node : list tree -> tree.

Instance tree_inhab : Inhab tree.
Proof. intros. apply (prove_Inhab (leaf 0)). Qed.

(** An induction principle for trees *)

Section Tree_induct.
Variables
(P : tree -> Prop)
(Q : list tree -> Prop) 
(P1 : forall n, P (leaf n)) 
(P2 : forall l, Q l -> P (node l)) 
(Q1 : Q nil)
(Q2 : forall t l, P t -> Q l -> Q (t::l)).

Fixpoint tree_induct_gen (T : tree) : P T :=
  match T as x return P x with
  | leaf n => P1 n
  | node l => P2
      ((fix tree_list_induct (l : list tree) : Q l :=
      match l as x return Q x with 
      | nil   => Q1
      | t::l' => Q2 (tree_induct_gen t) (tree_list_induct l')
      end) l)
  end.

End Tree_induct.

Lemma tree_induct : forall (P : tree -> Prop),
  (forall n : nat, P (leaf n)) ->
  (forall l : list tree, 
    (forall t, Mem t l -> P t) -> P (node l)) ->
  forall T : tree, P T.
Proof.
  introv Hl Hn. eapply tree_induct_gen with (Q := fun l =>
    forall t, Mem t l -> P t); intros.
  auto. auto. inversions H. inversions~ H1.
Qed.

(** Definition of immediate subtrees *)

Inductive subtree : binary tree :=
  | subtree_intro : forall t l, 
     Mem t l -> subtree t (node l). 

Hint Constructors subtree.

Lemma subtree_wf : wf subtree.
Proof.
  intros t. induction t using tree_induct;
  constructor; introv K; inversions~ K.
Qed.

(** Definition of the [treeincr] function *)

Definition Treeincr treeincr t :=
  match t with
  | leaf n => leaf (S n)
  | node l => node (LibList.map treeincr l)
  end.

Definition treeincr := FixFun Treeincr.

Lemma treeincr_fix : forall t, 
  treeincr t = Treeincr treeincr t.
Proof.
  applys (FixFun_fix subtree).
  reflexivity. apply subtree_wf.
  introv H. unfold Treeincr. destruct x.
    auto.
    fequals. apply~ map_congr.
Qed.



(* ********************************************************************** *)
(** * An example with cofinite trees *)

Require Import LibNat.

(** Definition of [itree], trees with possibly-infinite branches *)

CoInductive itree : Type :=   
  | itree_leaf : nat -> itree
  | itree_node : itree -> itree -> itree.

(** The type [itree] is inhabited *)

Instance itree_inhab : Inhab itree.
Proof. intros. apply (prove_Inhab (itree_leaf 0)). Qed.

(** Similarity up to level [i] between two trees *)

Fixpoint itree_similar_upto (i:nat) (m1 m2: itree) :=
  match i with 
  | O => True
  | S i' => match m1,m2 with 
     | itree_leaf n1, itree_leaf n2 => n1 = n2
     | itree_node t11 t12, itree_node t21 t22 => 
           itree_similar_upto i' t11 t21
        /\ itree_similar_upto i' t12 t22
     | _, _ => False
     end
  end.

(** Similarity upto is an equivalence *)

Lemma itree_similar_upto_equiv : 
  forall i, equiv (itree_similar_upto i).
Proof.
  constructor; unfolds.
  induction i; intros; simple~. destruct~ x. 
  induction i; intros; simple~. destruct x; destruct y; simpls*.
  induction i; intros; simple~. destruct x; destruct y; destruct z; simpls*.
Qed.

Hint Resolve itree_similar_upto_equiv.
Hint Extern 1 (itree_similar_upto ?i _ _) => 
  apply (@equiv_refl _ _ (itree_similar_upto_equiv i)).

(** Construction of the COFE for the family [itree] *)

Definition itree_family := Build_family lt itree_similar_upto.

Definition itree_left t :=
  match t with
  | itree_leaf n => arbitrary
  | itree_node t1 t2 => t1
  end.

Definition itree_right t :=
  match t with
  | itree_leaf n => arbitrary
  | itree_node t1 t2 => t2
  end.

Definition shifts A (u:nat->A) :=
  fun n => u (S n).

CoFixpoint itree_diagonal (u:nat->itree) : itree :=
  match u 0 with
  | itree_leaf n => itree_leaf n
  | itree_node t1 t2 =>
      itree_node (itree_diagonal (itree_left \o shifts u))
                 (itree_diagonal (itree_right \o shifts u))
  end.
 
Lemma itree_family_COFE : COFE itree_family.
Proof.
  apply~ nat_cofe'. typeclass.
  introv H. exists (itree_diagonal (shifts u)).
  cuts M: (forall k i u, i <= k -> 
    (forall i j : nat, i < j -> itree_similar_upto (S i) (u i) (u j)) ->
      itree_similar_upto (S i) (u k) (itree_diagonal u)).
    intros i. destruct i. simple~.
    sets u': (shifts u). change (u (S i)) with (u' i).
    apply M. math.
      intros i' j' Ri'j'. unfold u', shifts. apply H. math. 
  clears u. induction k using peano_induction; introv Lik Coh.
  tests: (k = 0). math_rewrite (i = 0). simpl. destruct~ (u 0).
  unfolds. fold itree_similar_upto.
  forwards S0: (>> Coh 0 k __). math. simpl in S0.
  unfold itree_diagonal; fold itree_diagonal.
  sets_eq <- u0: (u 0). sets_eq <- uk: (u k).
  destruct u0 as [|t01 t02]; destruct uk as [|tk1 tk2]; auto_false.
  split. (* todo: find a way to factorize both sides *)
  (* left subtree *)
  destruct i. simple~.
  sets u': (itree_left \o shifts u).
  asserts_rewrite (tk1 = u' (k-1)).
    unfold u'. unfold compose, shifts, itree_left.
    math_rewrite (S (k - 1) = k). rewrite~ EQuk.
  apply H; try math. intros i' j' Li'j'.
  unfold u'. unfold compose, shifts, itree_left.
  sets_eq i'': (S i'). sets_eq j'': (S j').
  forwards Ssi: (Coh i'' j''). math.
  simpl in Ssi. destruct (u i''); destruct (u j''); auto_false*.
  (* right subtree *)
  destruct i. simple~.
  sets u': (itree_right \o shifts u).
  asserts_rewrite (tk2 = u' (k-1)).
    unfold u'. unfold compose, shifts. unfold itree_right.
    math_rewrite (S (k - 1) = k). rewrite~ EQuk.
  apply H; try math. intros i' j' Li'j'.
  unfold u'. unfold compose, shifts, itree_left.
  sets_eq i'': (S i'). sets_eq j'': (S j').
  forwards Ssi: (Coh i'' j''). math.
  simpl in Ssi. destruct (u i''); destruct (u j''); auto_false*.
Qed.

(** Two equivalent definitions of similarity between two trees,
    one using an coinductive predicate and another constructed
    as the intersection of the "similarity-upto" relations. *)

CoInductive itree_similar : binary itree :=
  | itree_similar_leaf : forall n,
      itree_similar (itree_leaf n) (itree_leaf n)
  | itree_similar_node : forall t11 t12 t21 t22 : itree, 
      itree_similar t11 t21 ->
      itree_similar t12 t22 ->
      itree_similar (itree_node t11 t12) (itree_node t21 t22).

Hint Constructors itree_similar.

Lemma itree_similar_eq : itree_similar = similar itree_family.
Proof.
  apply prop_ext_2. intros t1 t2. iff H.
  intros i. hnf. gen t1 t2. induction i; simpl; introv H.
   auto. inversions~ H.
  hnf in H. gen t1 t2. cofix IH.
   intros t1 t2. destruct t1; destruct t2;
    introv H; lets H1: (H 1); simpl in H1; inversions H1; constructor.
      apply IH. intros i. lets_simpl HSi: (H (S i)). auto*.
      apply IH. intros i. lets_simpl HSi: (H (S i)). auto*.
Qed.


(** A first corecursive operation: the "product" of two trees.
   Note that it always add a head element. *)

Definition Product product m1 m2 :=
  match m1,m2 with 
  | itree_node t11 t12, itree_node t21 t22 => 
     itree_node (product t11 t22) (product t12 t21) 
  | _, _ => itree_node m1 m2
  end.

Definition product := FixFun2Mod itree_similar Product.

(** We prove that [product] satisfies the fixed point equation *)

Lemma product_fixpoint : forall m1 m2, 
  itree_similar (product m1 m2) (Product product m1 m2).
Proof. 
  apply (FixFun2Mod_corec itree_family).
  reflexivity. apply itree_similar_eq. apply itree_family_COFE.
  simpl. introv H. destruct i. simple~. unfold Product.
  destruct x1; destruct x2; simpl; auto with maths.
Qed.

(** And we show that it is productive wrt its arguments *)

Lemma product_incr_similarity : forall i m1 m1' m2 m2',
   itree_similar_upto i m1 m1' ->
   itree_similar_upto i m2 m2' ->
   itree_similar_upto (S i) (product m1 m2) (product m1' m2').
Proof.
  induction i using peano_induction.
  change (itree_similar_upto) with (family_sim itree_family).
  introv K1 K2. (* todo: setoid rewrite *)
  eapply cofe_similar_modulo. apply itree_family_COFE.
    rewrite <- itree_similar_eq. apply product_fixpoint.
    rewrite <- itree_similar_eq. apply product_fixpoint.
  simpl in K1, K2 |- *.
  destruct m1; destruct m2; simpl; auto.  
  destruct m1'; destruct m2'; simple~. destruct~ i. inversions K1.
  destruct m1'; destruct m2'; simple~. destruct~ i. inversions K1.
  destruct m1'; destruct m2'; simple~. destruct~ i. inversions K2.
  destruct m1'; destruct m2'; simple~; destruct~ i.
    inversions K1. inversions K1. inversions K2.
    simpl in K1, K2. destruct K1. destruct K2. auto with maths.
Qed.

(** A second corecursive function, which is not guarded:
    it is productive only because the function [product] 
    is productive. *)

Definition Makeitree makeitree m :=
  match m with
  | itree_node t1 t2 => product (makeitree t1) (makeitree t2)
  | itree_leaf n => itree_leaf (S n)
  end.

Definition makeitree := FixFunMod itree_similar Makeitree.

(** Still, we can establish the fixed point equation for our function *)

Lemma makeitree_fixpoint : forall m, 
  itree_similar (makeitree m) (Makeitree makeitree m).
Proof.
  apply (FixFunMod_corec_total itree_family).
  reflexivity. apply itree_similar_eq. apply itree_family_COFE.
  introv H. unfold Makeitree. simpl. destruct x.
  auto.
  destruct i. auto. apply product_incr_similarity.
    apply H; simpl; auto with maths. 
    apply H; simpl; auto with maths. 
Qed.



(* ********************************************************************** *)
(** * Verification of a recursive parser in CPS form *)


Ltac auto_tilde ::= auto with wf.


(* ---------------------------------------------------------------------- *)
(** ** The assertion construction *)

(** The expression [ ##P## v ] is equivalent to [v],
    with the assertion that [P] holds. If [P] does not hold,
    then the expression is undefined. *)

Definition asserts (P:Prop) (A:Type) `{Inhab A} (v:A) := 
  If P then v else arbitrary.

Notation "'##' P '##' v" := (asserts P v) (at level 69).

Tactic Notation "case_asserts" := 
  unfold asserts; case_if.
Tactic Notation "case_asserts" "~" := 
  case_asserts; auto~.


(* ---------------------------------------------------------------------- *)
(** ** Definition of the data types *)

Inductive regexp : Type := 
  | regexp_null : regexp
  | regexp_empty : regexp
  | regexp_char : nat -> regexp
  | regexp_alt : regexp -> regexp -> regexp
  | regexp_seq : regexp -> regexp -> regexp
  | regexp_star : regexp -> regexp.

Definition text := list nat.

Definition arg_type := (regexp * text * (text -> bool))%type.


(* ---------------------------------------------------------------------- *)
(** ** Definition of the regexp parser as an optimal fixed point *)

Definition Parse (parse : arg_type -> bool) (p : arg_type) : bool := 
  let '(r,s,k) := p in
  match r with
  | regexp_null => false
  | regexp_empty => k s
  | regexp_char c => 
     match s with 
     | nil => false
     | c'::s' => If c = c' then k s' else false
     end
  | regexp_alt r1 r2 => parse (r1,s,k) || parse (r2,s,k)
  | regexp_seq r1 r2 => parse (r1,s,(fun s' => parse (r2,s',k)))
  | regexp_star r1 => k s || parse (r1,s,(fun s' => parse (r,s',k)))
  end.

Definition parse := FixFun Parse.

(** At this point, the function [parse] exists and can thus
    be mentioned in other definitions. *)


(* ---------------------------------------------------------------------- *)
(** ** Domain of the parser *)

(** [productive r] is the same as [not (nullable r)];
    it asserts that [r] consumes at least one character *)

Fixpoint productive (r:regexp) : Prop :=
  match r with
  | regexp_null => True
  | regexp_empty => False
  | regexp_char c => True
  | regexp_alt r1 r2 => productive r1 /\ productive r2
  | regexp_seq r1 r2 => productive r1 \/ productive r2
  | regexp_star r1 => False
  end.

(** [normal r] ensures that expressions under a star are productive *)

Fixpoint normal (r:regexp) : Prop :=
  match r with
  | regexp_null => True
  | regexp_empty => True
  | regexp_char c => True
  | regexp_alt r1 r2 => normal r1 /\ normal r2
  | regexp_seq r1 r2 => normal r1 /\ normal r2
  | regexp_star r1 => productive r1 /\ normal r1
  end.  

Hint Unfold productive normal. 

(** Definition of the domain *)

Definition parse_dom (p:arg_type) :=
  let '(r,s,k) := p in normal r.


(* ---------------------------------------------------------------------- *)
(** ** Termination relation for the parser *)

(** Sub-expression order for [regexp] *)

Inductive regexp_sub : binary regexp :=
  | regexp_sub_seq_1 : forall r1 r2,
      regexp_sub r1 (regexp_seq r1 r2)
  | regexp_sub_seq_2 : forall r1 r2,
      regexp_sub r2 (regexp_seq r1 r2)
  | regexp_sub_alt_1 : forall r1 r2,
      regexp_sub r1 (regexp_alt r1 r2)
  | regexp_sub_alt_2 : forall r1 r2,
      regexp_sub r2 (regexp_alt r1 r2)
  | regexp_sub_star : forall r1,
      regexp_sub r1 (regexp_star r1).

Hint Constructors regexp_sub.

Lemma regexp_sub_wf : wf regexp_sub.
Proof. intros r. induction r; constructor; intros r' le; inverts~ le. Qed.

Hint Resolve regexp_sub_wf : wf.

(** [text_sub] is the transitive closure of the sub-list order *)

Definition text_sub : binary text := tclosure (@list_sub _).

Lemma text_sub_wf : wf text_sub.
Proof. lets: tclosure_wf. unfold text_sub. prove_wf. Qed.

Hint Resolve text_sub_wf : wf.

Lemma text_sub_once : forall s c,
  text_sub s (c::s).
Proof. intros. apply~ tclosure_once. Qed.

Lemma text_sub_trans : trans text_sub.
Proof. apply tclosure_trans. Qed.

Hint Resolve text_sub_trans text_sub_once.

Lemma text_sub_app : forall s s1 s2,
  s = s1 ++ s2 -> large text_sub s2 s.
Proof.
  intros. subst. induction s1; rew_list. auto.
  inverts IHs1.
    left. applys~ (@trans_elim text) (s1++s2).
    rewrite <- H. left. apply text_sub_once.
Qed.

(** [parse_sub] is the termination relation used for [parse];
    It is the lexicographical order [(s,r)] *)

Definition parse_sub : binary (regexp * text) := 
  lexico2 regexp_sub text_sub.

Lemma parse_sub_wf : wf parse_sub.
Proof. prove_wf. Qed.

Hint Unfold parse_sub.
Hint Resolve parse_sub_wf : wf.

(** [parse_arg_sub] is similar to [parse_sub] except that
    it takes triples of the form [(r,s,k)] as arguments *)

Definition parse_arg_sub : binary arg_type := 
  fun p1 p2 => let '(r1,s1,k1) := p1 in let '(r2,s2,k2) := p2 in
               parse_sub (r1,s1) (r2,s2).

Lemma parse_arg_sub_wf : wf parse_arg_sub.
Proof.
  intros [[r s] k].
  sets_eq p: (r,s). gen k r s. induction_wf IH: parse_sub_wf p.
  intros. subst p. constructor. intros [[r2 s2] k2] S. applys~ IH S. 
Qed.

Hint Unfold parse_arg_sub.
Hint Resolve parse_arg_sub_wf : wf.


(* ---------------------------------------------------------------------- *)
(** ** Auxiliary recursive function *)

(** [parse'] is a function equivalen to [parse] except that it includes
    some assertions in order to make termination more obvious. 
    Those assertions appear in-between [##] symbols. *)

Definition Parse' (parse : arg_type -> bool) (p : arg_type) : bool := 
  let '(r,s,k) := p in
  match r with
  | regexp_null => false
  | regexp_empty => k s
  | regexp_char c => 
     match s with 
     | nil => false
     | c'::s' => If c = c' then k s' else false
     end
  | regexp_alt r1 r2 => parse (r1,s,k) || parse (r2,s,k)
  | regexp_seq r1 r2 => parse (r1,s,(fun s' => parse (r2,s',k)))
  | regexp_star r1 => k s || parse (r1,s,(fun s' => ##text_sub s' s## parse (r,s',k)))
  end.

Definition parse' := FixFun Parse'.

(** Remark: I will show further on how to factorize the definitions
    of [Parse] and [Parse'] so as to avoid the duplication of code. *)


(* ---------------------------------------------------------------------- *)
(** ** Proof of termination of the auxiliary function *)

(** Thanks to the assertions it contains, [parse'] is a total function
    that satisfies a contraction condition, and thus satisfies the
    fixed point equation for [Parse']. *)

Lemma parse'_fix : forall p, 
  parse' p = Parse' parse' p.
Proof. 
  applys~ (FixFun_fix parse_arg_sub).
  intros f1 f2 [[r s] k] H. unfolds. destruct r; auto.
  fequal; auto 7.
  rewrite H; [|auto 7]. fequals_rec.
   apply func_ext_1. intros s'. apply~ H.
  fequal. rewrite H; [|auto 7]. fequals_rec. 
   apply func_ext_1. intros s'. case_asserts; auto 7.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of the auxiliary function *)

(** [select_sub r] is equivalent to the strict sub-text relation
    when [r] is [productive], and it is otherwise equivalent to
    the large sub-text relation. *)

Definition select_sub (r:regexp) : binary text := 
  If productive r then text_sub else large text_sub.

(** The key result consists in showing that, when [r] is is normal form,
    the computation of [parse' (r,s,k)] is not affected by the evaluations
    of the assertions. *)

Lemma parse'_cont : forall r s k1 k2, normal r ->
  (forall s', select_sub r s' s -> k1 s' = k2 s') ->
  parse' (r,s,k1) = parse' (r,s,k2).
Proof.
  intros r s. sets_eq p: (r,s). gen r s. induction_wf IH: parse_sub_wf p.
  introv P N E. subst p. do 2 rewrite parse'_fix. unfolds. destruct r; simpl in N.
  auto.
  apply E. hnf. rewrite~ If_r.
  destruct s as [|c' s']. auto. case_if~. apply E. unfolds. rewrite~ If_l.
  inverts N. asserts M: (forall r s', (r = r1 \/ r = r2) -> select_sub r s' s ->
                select_sub (regexp_alt r1 r2) s' s).
    introv C S. hnf in S |- *. simpl. case_if.
      destruct H1. case_if. auto. inverts C; tryfalse.
      case_if~.
   fequals.
     applys~ IH. auto 7. eauto 8.
     applys~ IH. auto 7. eauto 8.
  inverts N. applys~ IH. intros s' S'. applys~ IH. 
    intros s'' S''. apply E. hnf in S',S''|-*. simpl.
    tests: (productive r1); tests: (productive r2).
      rewrite~ If_l. applys* (@trans_elim text) s'.
      rewrite~ If_l. applys* (@large_strict_trans text) s'.
      rewrite~ If_l. applys* (@strict_large_trans text) s'.
      rewrite If_r; [|rew_logic';auto]. applys~ (@large_trans text) s'.
  fequals.
    apply E. unfold select_sub. simpl. rewrite~ If_r.
  inverts N. applys~ IH. auto 7. intros s' S'. case_asserts~.
   applys~ IH. hnf in S'. rewrite~ If_l in S'.
   intros s'' S''. apply E. hnf in S'' |- *. simpls. case_if; tryfalse.
   inverts S''. left. applys* trans_elim. auto.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Proof of the fixed point equation for [parse] *)

(** The first step consists in proving that [parse'] 
    is a fixed point for [Parse] on the domain. This is done
    by showing that the assertions in the continuations are
    irrelevant, using the lemma [parse'_cont]. Yet, the statement
    [ Lemma parse'_fix_Parse_simple : forall p, parse_dom p -> 
      parse' p = Parse parse' p. ] 
    is not strong enough. Indeed, we need to generalize this
    into a form where we replace [parse'] with an arbitrary
    other total function that behave like [parse'] on the domain. *)
   
Lemma parse'_fix_Parse : 
  fixed_point (pfunc_equal parse_dom) Parse parse'.
Proof.
  intros f Hf [[r s] k] N. asserts E: (pfunc_equal parse_dom f parse').
    unfolds. apply~ equiv_sym. clear Hf.
  rewrite~ E. rewrite parse'_fix.
  unfold Parse, Parse'. destruct r; auto; simpl in N.
  inverts N. fequals; rewrite~ E.
  inverts N. rewrite~ E. apply~ parse'_cont. intros s' S'. rewrite~ E.
  inverts N. fequals. rewrite~ E. apply~ parse'_cont. intros s' S'.
   hnf in S'. rewrite~ If_l in S'. case_asserts; auto_false. rewrite~ E. simple~.
Qed.

(** The second step consists in proving that the functional [Parse]
    satisfies a contraction condition. This is almost the standard
    contraction condition, except that [f1] is specialized as [parse'].
    In this proof, we exploit the fact that [parse'] depends only
    a subdomain of its continuation. Remark: the statement is equivalent
    to [rec_contractive' eq parse_dom Parse parse_arg_sub parse']. *)

Lemma Parse_contractive_for_parse' : forall f' p, parse_dom p ->
  (forall q, parse_dom q -> parse_arg_sub q p -> parse' q = f' q) ->
  Parse parse' p = Parse f' p.
Proof.
  introv N IH. unfold Parse. destruct p as [[r s] k].
  hnf in N. destruct r; simpl in N; auto.
  inverts N. fequals; apply~ IH. 
  inverts N. erewrite parse'_cont; auto. apply~ IH. 
   simpl. intros s' S'. apply~ IH.
  inverts N. fequals. erewrite parse'_cont; auto. apply IH; auto 7.
   simpl. intros s' S'. hnf in S'. rewrite~ If_l in S'. apply~ IH; hnfs~.
Qed.

(** Third and last step: we can put all the pieces together.
    Since [parse'] is a generally-consistent fixed point for [Parse] 
    on the domain [parse_dom], [parse'] is extended by [parse], 
    which is the optimal fixed point of [Parse]. Hence, [parse] 
    and [parse'] agree on the domain [parse_dom]. It follows that
    [parse] satsifies the fixed point equation for [Parse] on the domain. *)

Lemma parse_fix : forall p, parse_dom p ->
  parse p = Parse parse p.
Proof.
  apply (FixFun_fix_partial' (P:=parse_dom) (R:=parse_arg_sub) (f':=parse')); auto~.
  applys Parse_contractive_for_parse'. apply parse'_fix_Parse.
Qed.

Corollary parse_fix' : forall r s k, normal r ->
  parse (r,s,k) = Parse parse (r,s,k).
Proof. intros. applys~ parse_fix. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Bonus: factorization of the definitions of [Parse] and [Parse'] *)

(** The idea is to define a single functional that takes as argument a
    function, which is intented to be instantiated either as [asserts]
    or as [ignore]. *)

Definition ignore (P:Prop) (A:Type) `{Inhab A} (v:A) := v.

Section Common.

Context (check : Prop -> forall A `{Inhab A}, A -> A).

Notation "'#' P '#' v" := (@check P _ _ v) (at level 69).

(** Here is the common definition to build [Parse] and [Parse']. *)

Definition Parse_common (parse : arg_type -> bool) (p : arg_type) : bool := 
  let '(r,s,k) := p in
  match r with
  | regexp_null => false
  | regexp_empty => k s
  | regexp_char c => 
     match s with 
     | nil => false
     | c'::s' => If c = c' then k s' else false
     end
  | regexp_alt r1 r2 => parse (r1,s,k) || parse (r2,s,k)
  | regexp_seq r1 r2 => parse (r1,s,(fun s' => parse (r2,s',k)))
  | regexp_star r1 => k s || parse (r1,s,(fun s' => #text_sub s' s# parse (r,s',k)))
  end.

End Common.

(** Here are the alternative definitions for [Parse] and [Parse']. *)

Definition Parse_alternative := Parse_common ignore.
Definition Parse'_alternative := Parse_common asserts.

(** Finally, we can check that the alternative definitions are convertible
    with the one we had written by hand previously. *)

Lemma Parse_alternative_correct : Parse = Parse_alternative.
Proof. reflexivity. Qed.

Lemma Parse'_alternative_correct : Parse' = Parse'_alternative.
Proof. reflexivity. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Reasoning about [parse] *)

(** The inductively-defined proposition [sem r s] asserts that the 
    string [s] matches the regular expression [r]. *)

Inductive sem : regexp -> text -> Prop :=
  | sem_empty : 
      sem regexp_empty nil
  | sem_char : forall c,
      sem (regexp_char c) (c::nil)
  | sem_alt_1 : forall r1 r2 s, 
      sem r1 s -> sem (regexp_alt r1 r2) s
  | sem_alt_2 : forall r1 r2 s, 
      sem r2 s -> sem (regexp_alt r1 r2) s
  | sem_seq : forall r1 r2 s1 s2,
      sem r1 s1 -> sem r2 s2 -> sem (regexp_seq r1 r2) (s1 ++ s2)
  | sem_star_void : forall r1,
      sem (regexp_star r1) nil
  | sem_star_step : forall r1 s1 s2,
      sem r1 s1 ->
      sem (regexp_star r1) s2 ->
      sem (regexp_star r1) (s1 ++ s2).

Hint Constructors sem.

(** Observe that if a string [s] matches a productive regular
    expression [r], then [s] is not the empty string. *)

Lemma sem_productive : forall r s,
  sem r s -> productive r -> s <> nil.
Proof.
  introv S. induction S; introv P; simpl in P; auto_false*.
  intros E. destruct (app_eq_nil_inv E). subst. destruct* P.
Qed.

(** The continuation [is_nil] holds only of the empty string *)

Definition is_nil (s:text) :=
  match s with nil => true | _ => false end.

(** The first result asserts that if [s] matches [r] semantically,
    then the [parse] function applied to [r] and [s] returns true. *)

Lemma sem_to_parse_ind : forall r s s' k,
  sem r s -> normal r -> k s' = true -> parse (r, s ++ s', k) = true.
Proof.
  introv S N K. gen s' k N. induction S; intros; 
   (rewrite parse_fix; [ | apply N ]); unfold Parse at 1; simpl in N; 
   (try match type of N with _ /\ _ => destruct N end).
  rew_list~.
  rew_list. rewrite~ If_l.
  rewrite~ IHS.
  rewrite IHS at 1; auto. rew_bool~.
  rew_list. auto.
  rew_list. rewrite~ K.
  rew_list. rewrite~ IHS1. rew_bool~.
Qed.

Corollary sem_to_parse : forall r s,
  sem r s -> normal r -> parse (r,s,is_nil) = true.
Proof. intros. forwards~ M: (@sem_to_parse_ind r s nil is_nil). rew_list~ in M. Qed.

(** The second result asserts the reciprocal: if the parse function
    applied to [r] and [s] returns true, then [s] matches [r] semantically. *)

Lemma parse_to_sem_ind : forall r s k, 
  normal r -> parse (r,s,k) = true ->  
  exists s1 s2, s = s1 ++ s2 /\ sem r s1 /\ k s2 = true.
Proof.
  introv N P. sets_eq p: (r,s). gen r s k.
  induction_wf IH: parse_sub_wf p. intros. subst p.
  rewrite~ parse_fix in P. unfold Parse in P. destruct r; 
   simpl in N; (try match type of N with _ /\ _ => destruct N end).
  false.
  exists (nil:text) s. splits~. 
  destruct s; tryfalse. case_if; tryfalse. 
   exists (n0::nil) s. splits~.
  case_eq (parse (r1,s,k)); intros P1.
    forwards~ (s1&s2&E&S&P'): IH P1. auto 7. exists~ s1 s2.
    rewrite P1 in P. rew_bool in P.
    forwards~ (s1&s2&E&S&P'): IH P. auto 7. exists~ s1 s2.
  forwards~ (s1&s2&E&S&P'): IH P. auto.
    forwards~ (s3&s4&E'&S'&K): IH P'. auto.   
    forwards M: text_sub_app E. subst s s2. exists (s1 ++ s3) s4. rew_list~.
  case_eq (k s); intros K.
    exists (nil:text) s. splits~.
    rewrite K in P. rew_bool in P.
    forwards~ (s1&s2&E&S&P'): IH P. auto.
    forwards~ (s3&s4&E'&S'&K'): IH P'; try solve [hnfs~].
      forwards M: text_sub_app E. inverts M. auto. false.
       applys~ sem_productive S. apply* app_eq_self_inv_r.
    subst s s2. exists (s1++s3) s4. rew_list~.
Qed.

Corollary parse_to_sem : forall r s, 
  normal r -> parse (r,s,is_nil) = true -> sem r s.
Proof.
  intros. forwards~ (s1&s2&E&S&K): (@parse_to_sem_ind r s is_nil). 
  subst. destruct s2; tryfalse. rew_list~ in *.
Qed.

(** We can reformulate those two results in the form of an
    equivalence between [sem] and [parse] *)

Theorem parse_iff_sem : forall r s, normal r -> 
  (parse (r,s,is_nil) = true <-> sem r s).
Proof. split. apply~ parse_to_sem. intros. apply~ sem_to_parse. Qed.

(** A similar, more general, result *)

Theorem parse_iff_sem_ind : forall r s k, normal r ->
  (parse (r,s,k) = true <-> (exists s1 s2, s = s1 ++ s2 /\ sem r s1 /\ k s2 = true)).
Proof.
  split. intros. apply~ parse_to_sem_ind.
  intros (s1&s2&?&?&?). subst. apply~ sem_to_parse_ind.
Qed.


