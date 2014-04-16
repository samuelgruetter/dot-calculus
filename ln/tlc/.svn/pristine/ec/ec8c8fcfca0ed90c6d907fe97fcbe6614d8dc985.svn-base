(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists                                                                   *
**************************************************************************)

Set Implicit Arguments. 
Generalizable Variables A B.
Require Import LibTactics LibLogic LibReflect LibOperation
 LibProd LibOption LibNat LibInt LibWf LibRelation.
Require Export List.
Open Local Scope nat_scope.
Open Local Scope comp_scope.



(** Fixing implicit arguments *)

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].


(* ********************************************************************** *)
(** * Inhabited *)

Instance list_inhab : forall A, Inhab (list A).
Proof. intros. apply (prove_Inhab nil). Qed.


(* ********************************************************************** *)
(** * Logical predicates *)

Section LogicList.
Variables A A1 A2 B C : Type.

(** [Forall P L] asserts that all the elements in the list [L]
    satisfy the predicate [P]. *)

Inductive Forall (P : A -> Prop) 
  : list A -> Prop :=
  | Forall_nil : 
      Forall P nil
  | Forall_cons : forall l x, 
      P x -> Forall P l -> 
      Forall P (x::l).

(** [Forall2 P L1 L2] asserts that the lists [L1] and [L2] 
    have the same length and that elements at corresponding
    indices are related by the binary relation [P]. *)

Inductive Forall2 (P : A -> B -> Prop) 
  : list A -> list B -> Prop :=
  | Forall2_nil : 
      Forall2 P nil nil
  | Forall2_cons : forall l1 l2 x1 x2, 
      P x1 x2 -> Forall2 P l1 l2 -> 
      Forall2 P (x1::l1) (x2::l2).

(** Similar to [Forall2] except that it relates three lists *)

Inductive Forall3 (P : A -> B -> C -> Prop) 
  : list A -> list B -> list C -> Prop :=
  | Forall3_nil : 
      Forall3 P nil nil nil
  | Forall3_cons : forall l1 l2 l3 x1 x2 x3, 
      P x1 x2 x3 -> Forall3 P l1 l2 l3 -> 
      Forall3 P (x1::l1) (x2::l2) (x3::l3).

(** [exists P L] asserts that there exists a value in the
    list [L] that satisfied the predicate [P]. *)

Inductive Exists (P : A -> Prop) 
  : list A -> Prop :=
  | Exists_here : forall l x, 
      P x -> Exists P (x::l)
  | Exists_next : forall l x, 
      Exists P l -> 
      Exists P (x::l).

(** [exists2 P L1 L2] asserts that there exists an index [n]
    such that the n-th element of [L1] and the n-th element
    of [L2] are related by the binary relation [P]. *)

Inductive Exists2 (P : A1 -> A2 -> Prop) 
  : list A1 -> list A2 -> Prop :=
  | Exists2_here : forall l1 l2 x1 x2,
      P x1 x2 -> Exists2 P (x1::l1) (x2::l2)
  | Exists2_next : forall l1 l2 x1 x2, 
      Exists2 P l1 l2 -> 
      Exists2 P (x1::l1) (x2::l2).

(** [filters P L L'] asserts that [L'] is the sublist of [L]
    made exactly of the elements of [L] that satisfy [P]. *)

Inductive Filters (P : A -> Prop) 
  : list A -> list A -> Prop :=
  | Filters_nil : Filters P nil nil
  | Filters_cons_yes : forall l l' x,
      P x -> Filters P l l' -> 
      Filters P (x::l) (x::l')
  | Filters_cons_no : forall l l' x,
      ~ (P x) -> Filters P l l' -> 
      Filters P (x::l) l'.

(** [Mem x l] asserts that [x] belongs to [M] *)

Inductive Mem (x:A) : list A -> Prop :=
  | Mem_here : forall l, 
      Mem x (x::l)
  | Mem_next : forall y l, 
      Mem x l -> 
      Mem x (y::l).

(** [Nth n L x] asserts that the n-th element of the list [L]
    exists and is exactly [x] *)

Inductive Nth : nat -> list A -> A -> Prop :=
  | Nth_here : forall l x,
      Nth 0 (x::l) x
  | Nth_next : forall y n l x, 
      Nth n l x ->
      Nth (S n) (y::l) x.

(** [Assoc x v l] asserts that [(x,v)] the first pair of the 
    form [(x,_)] in [l] *)

Inductive Assoc (x:A) (v:B) : list (A*B) -> Prop :=
  | Assoc_here : forall l , 
      Assoc x v ((x,v)::l)
  | Assoc_next : forall y l (w:B), 
      Assoc x v l -> x <> y ->
      Assoc x v ((y,w)::l).

(** [has pair x1 x2 l1 l2] asserts that there exists an
    index [n] such that the n-th element of [l1] is [x1]
    and the n-th element of [l2] is [x2] *)

Definition has_pair x1 x2 l1 l2 :=
  Exists2 (fun v1 v2 => v1 = x1 /\ v2 = x2) l1 l2.

Lemma has_pair_here : forall x1 x2 l1 l2,
  has_pair x1 x2 (x1::l1) (x2::l2).
Proof. intros. constructor~. Qed.

Lemma has_pair_next : forall x1 x2 y1 y2 l1 l2,
  has_pair x1 x2 l1 l2 ->
  has_pair x1 x2 (y1::l1) (y2::l2).
Proof. introv H. apply* Exists2_next. Qed.

End LogicList.


(* ********************************************************************** *)
(** * Operations *)

(* ---------------------------------------------------------------------- *)
(** ** Operations on lists *)

Section Folds.
Context {A B : Type}.
Implicit Types l a b : list A.
Implicit Types x : A. 

Fixpoint fold_right (f : A -> B -> B) (acc : B) l :=
  match l with
  | nil => acc
  | x::L' => f x (fold_right f acc L')
  end.

Fixpoint fold_left (f : A -> B -> B) (acc : B) l :=
  match l with
  | nil => acc
  | x::L' => fold_left f (f x acc) L'
  end.

End Folds.

Section Operations.
Variables (A B C : Type) (IA : Inhab A). 
Implicit Types l a b : list A.
Implicit Types x : A. 

Definition map (f : A -> C) :=
  nosimpl (fold_right (fun x acc => (f x)::acc) (@nil C)).

Definition filter (f : predb A) :=
  nosimpl (fold_right (fun x acc => if f x then x::acc else acc) (@nil A)).

Definition append l1 l2 :=
  nosimpl (fold_right (fun x (acc:list A) => x::acc) l2 l1).

Definition concat :=
  nosimpl (fold_right append (@nil A)).

Definition rev :=
  nosimpl (fold_left (fun x acc => x::acc) (@nil A)).

Definition length :=
  nosimpl (fold_right (fun x acc => 1+acc) 0).

Definition for_all (f : predb A) := 
  nosimpl (fold_right (fun x acc => acc && (f x)) true).

Definition exists_st (f : predb A) := 
  nosimpl (fold_right (fun x acc => acc || (f x)) false).

Definition count (f : predb A) :=
  nosimpl (fold_right (fun x acc => (if f x then 1 else 0) + acc) 0).

Fixpoint mem x l := 
  match l with
  | nil => false
  | y::l' => (x '= y) || mem x l'
  end.

Fixpoint remove x l :=
  match l with
  | nil => nil
  | y::l' => let acc := remove x l' in
             If x = y then acc else y::acc
  end.

Fixpoint removes l2 l1 :=
  match l2 with
  | nil => l1
  | x::l2' => removes l2' (remove x l1) 
  end.

Fixpoint split (l: list (A*B)) : (list A * list B) :=
  match l with 
  | nil => (nil,nil)
  | (a,b)::l' => let (la,lb) := split l' in (a::la, b::lb)
  end.

Fixpoint combine (la : list A) (lb : list B) : list (A*B) :=
  match la with
  | nil => nil
  | a::la' =>
    match lb with 
    | nil => arbitrary
    | b::lb' => (a,b)::(combine la' lb')
    end
  end.

Fixpoint drop (n:nat) (l: list A) : list A :=
  match n with 
  | 0 => l
  | S n' => match l with
    | nil => nil
    | a::l' => drop n' l'
    end
  end.

Fixpoint take (n:nat) (l: list A) : list A :=
  match n with 
  | 0 => nil
  | S n' => match l with
    | nil => nil
    | a::l' => a::(take n' l')
    end
  end.

Fixpoint nth n l : A :=
  match l with
  | nil => arbitrary 
  | x::L' => 
     match n with
     | 0 => x
     | S n' => nth n' L'
     end
  end.

End Operations.

Implicit Arguments fold_left [[A] [B]].
Implicit Arguments fold_right [[A] [B]].
Implicit Arguments append [[A]].
Implicit Arguments concat [[A]].
Implicit Arguments rev [[A]].
Implicit Arguments length [[A]].
Implicit Arguments mem [[A]].
Implicit Arguments remove [[A]].
Implicit Arguments removes [[A]].
Implicit Arguments nth [[A] [IA]].
(* todo: implicit arguments for the other functions *)


(* ---------------------------------------------------------------------- *)
(** ** Notation *)

(** [l1 ++ l2] concatenates two lists *)

Infix "++" := append (right associativity, at level 60) : list_scope.

(** [l & x] extends the list [l] with the value [x] at the right end *)

Notation "l & x" := (l ++ (x::nil)) 
  (at level 28, left associativity) : list_scope.


(* ********************************************************************** *)
(** * Properties of operations *)

Section AppFoldProperties.
Variable A B : Type.
Implicit Types x : A.
Implicit Types l : list A.

Lemma app_cons : forall x l1 l2,
  (x::l1) ++ l2 = x::(l1++l2).
Proof. auto. Qed.
Lemma app_nil_l : forall l,
  nil ++ l = l.
Proof. auto. Qed.
Lemma app_nil_r : forall l,
  l ++ nil = l.
Proof. induction l. auto. rewrite app_cons. fequals~. Qed.
Lemma app_assoc : forall l1 l2 l3,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. 
  intros. induction l1.
  rewrite_all~ app_nil_l. 
  rewrite_all~ app_cons. fequals~.
Qed.
Lemma app_last : forall x l1 l2,
  l1 ++ (x::l2) = (l1 & x) ++ l2.
Proof. intros. rewrite~ app_assoc. Qed.
Lemma app_last_sym : forall x l1 l2,
  (l1 & x) ++ l2 = l1 ++ (x::l2).
Proof. intros. rewrite~ <- app_last. Qed.
Lemma app_cons_one : forall x l,
  (x::nil) ++ l = x::l.
Proof. auto. Qed.


Section FoldRight.
Variables (f : A -> B -> B) (i : B).
Lemma fold_right_nil : 
  fold_right f i nil = i.
Proof. auto. Qed.
Lemma fold_right_cons : forall x l,
  fold_right f i (x::l) = f x (fold_right f i l) .
Proof. auto. Qed.
Lemma fold_right_app : forall l1 l2,
  fold_right f i (l1 ++ l2) = fold_right f (fold_right f i l2) l1.
Proof.
  intros. induction l1. auto. 
  rewrite app_cons. simpl. fequals~.
Qed.
Lemma fold_right_last : forall x l,
  fold_right f i (l & x) = fold_right f (f x i) l.
Proof. intros. rewrite~ fold_right_app. Qed.
End FoldRight.


Section FoldLeft.
Variables (f : A -> B -> B) (i : B).
Lemma fold_left_nil : 
  fold_left f i nil = i.
Proof. auto. Qed.
Lemma fold_left_cons : forall x l,
  fold_left f i (x::l) = fold_left f (f x i) l.
Proof. auto. Qed.
Lemma fold_left_app : forall l1 l2,
  fold_left f i (l1 ++ l2) = fold_left f (fold_left f i l1) l2.
Proof.
  intros. gen i. induction l1; intros. auto. 
  rewrite app_cons. simpl. rewrite~ IHl1.
Qed.
Lemma fold_left_last : forall x l,
  fold_left f i (l & x) = f x (fold_left f i l).
Proof. intros. rewrite~ fold_left_app. Qed.
End FoldLeft.

End AppFoldProperties.

Section LengthProperties.
Variable A : Type.
Implicit Types l : list A.

Lemma length_nil : 
  length (@nil A) = 0.
Proof. auto. Qed.
Lemma length_cons : forall x l,
  length (x::l) = 1 + length l.
Proof. auto. Qed.
Lemma length_app : forall l1 l2,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. unfold length at 1. rewrite fold_right_app.
  fold (length l2). induction l1; simple~.
Qed.
Lemma length_last : forall x l,
  length (l & x) = 1 + length l.
Proof. 
  intros. rewrite length_app.
  rewrite length_cons. rewrite length_nil.
  simpl. math.
Qed.
Lemma length_zero_inv : forall l,
  length l = 0%nat -> l = nil.
Proof.
  destruct l. auto. rewrite length_cons. intros. false. 
Qed.

End LengthProperties.

Section OperationProperties.
Variable A B : Type.
Implicit Types x : A.
Implicit Types l : list A.

Lemma rev_nil : 
  rev (@nil A) = nil.
Proof. auto. Qed.
Lemma rev_app : forall l1 l2,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. unfold rev. asserts K1: (forall l accu,
   fold_left (fun x acc => x :: acc) accu l =
   fold_left (fun x acc => x :: acc) nil l ++ accu).
   induction l; intros; simpl. auto. 
   rewrite IHl. rewrite (@IHl (a::nil)). rewrite~ app_last.
  asserts K2: (forall accu,
   fold_left (fun x acc => x :: acc) accu (l1 ++ l2) =
   fold_left (fun x acc => x :: acc) nil l2 ++
   fold_left (fun x acc => x :: acc) nil l1 ++ accu).
  induction l1; intros; simpl.
    do 2 rewrite app_nil_l. apply K1.
    rewrite IHl1. rewrite (@K1 l1 (a::nil)). rewrite~ app_last.
  lets K3: (@K2 nil). rewrite app_nil_r in K3. auto.
Qed.
Lemma rev_cons : forall x l,
  rev (x::l) = rev l & x.
Proof. intros. rewrite <- app_cons_one. rewrite~ rev_app. Qed.
Lemma rev_last : forall x l,
  rev (l & x) = x::(rev l).
Proof. intros. rewrite~ rev_app. Qed.
Lemma rev_cons_app : forall x l1 l2,
  rev (x :: l1) ++ l2 = rev l1 ++ (x::l2).
Proof. intros. rewrite rev_cons. rewrite~ <- app_last. Qed.
Lemma app_rev_cons : forall x l1 l2,
  l1 ++ rev (x :: l2) = (l1 ++ rev l2) & x.
Proof. intros. rewrite rev_cons. rewrite~ app_assoc. Qed.
Lemma rev_rev : forall l,
  rev (rev l) = l.
Proof. 
  induction l. auto. rewrite rev_cons. rewrite rev_last. fequals.
Qed.
Lemma length_rev : forall l, 
  length (rev l) = length l.
Proof.
  induction l. auto. rewrite rev_cons.
  rewrite length_last. rewrite~ length_cons.
Qed.

Lemma concat_nil : 
  concat (@nil (list A)) = nil.
Proof. auto. Qed.
Lemma concat_cons : forall l m,
  concat (l::m) = l ++ concat m.
Proof. auto. Qed.
Lemma concat_one : forall l,
  concat (l::nil) = l.
Proof.
  intros. rewrite concat_cons. rewrite concat_nil.
  rewrite~ app_nil_r. 
Qed.
Lemma concat_app : forall m1 m2 : list (list A),
  concat (m1 ++ m2) = concat m1 ++ concat m2.
Proof.
  induction m1; intros.
  rewrite concat_nil. do 2 rewrite~ app_nil_l.
  rewrite app_cons. do 2 rewrite concat_cons.
   rewrite app_assoc. fequals.
Qed.
Lemma concat_last : forall l m,
  concat (m & l) = concat m ++ l.
Proof. intros. rewrite~ concat_app. rewrite~ concat_one. Qed.

Section MapProp.
Variable f : A -> B.
Lemma map_nil : 
  map f nil = nil.
Proof. auto. Qed.
Lemma map_cons : forall x l,
  map f (x::l) = f x :: map f l.
Proof. auto. Qed.
Lemma map_app : forall l1 l2,
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof. 
  intros. unfold map.
  assert (forall accu,
    fold_right (fun x acc => f x :: acc) accu (l1 ++ l2) =
    fold_right (fun x acc => f x :: acc) nil l1 ++
     fold_right (fun x acc => f x :: acc) nil l2 ++ accu).
  induction l1; intros; simpl. 
   do 2 rewrite app_nil_l. gen accu.
   induction l2; intros; simpl.
     auto. 
     rewrite IHl2. rewrite~ app_cons.
   rewrite IHl1. rewrite~ app_cons.
  specializes H (@nil B). rewrite~ app_nil_r in H.
Qed.
Lemma map_last : forall x l,
  map f (l & x) = map f l & f x.
Proof. intros. rewrite~ map_app. Qed.
Lemma length_map : forall l,
  length (map f l) = length l.
Proof. 
  induction l. auto.
  rewrite map_cons. do 2 rewrite length_cons. auto.
Qed.
End MapProp.

Section FilterProp.
Variable f : A -> bool.
Lemma filter_nil : 
  filter f nil = nil.
Proof. auto. Qed.
Lemma filter_cons : forall x l,
  filter f (x::l) = if f x then x :: filter f l else filter f l.
Proof. auto. Qed.
Lemma filter_app : forall l1 l2,
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.  (* todo: factorise with map_app *)
  intros. unfold filter.
  assert (forall accu,
    fold_right (fun x acc => if f x then x::acc else acc) accu (l1 ++ l2) =
    fold_right (fun x acc => if f x then x::acc else acc) nil l1 ++
     fold_right (fun x acc => if f x then x::acc else acc) nil l2 ++ accu).
  induction l1; intros; simpl. 
   do 2 rewrite app_nil_l. gen accu.
   induction l2; intros; simpl.
     auto. 
     case_if. fequals. rewrite IHl2. rewrite~ app_cons. fequals.
    case_if. fequals. rewrite IHl1. rewrite~ app_cons. apply IHl1.
  specializes H (@nil A). rewrite~ app_nil_r in H.
Qed.
Lemma filter_last : forall x l,
  filter f (l & x) = filter f l ++ (if f x then x::nil else nil).
Proof. intros. rewrite~ filter_app. Qed.
(*later:
Lemma length_filter : forall l,
  length (filter f l) <= length l.
*)
End FilterProp.

Section MemProp.
Implicit Types k : A.
Lemma mem_nil : forall k,
  mem k nil = false.
Proof. auto. Qed.
Lemma mem_cons : forall k x l,
  mem k (x::l) = (k '= x) || (mem k l).
Proof. auto. Qed.
Lemma mem_app : forall f l1 l2,
  mem f (l1 ++ l2) = (mem f l1) || mem f l2.
Proof.
  intros. induction l1.
  rew_bool. rewrite~ app_nil_l.
  rewrite app_cons. simpl. rewrite~ IHl1.
  rewrite~ assoc_or.
Qed.
Lemma mem_last : forall k x l,
  mem k (l & x) = (k '= x) || (mem k l).
Proof. 
  intros. rewrite mem_app. simpl. 
  rewrite LibBool.comm_or. rew_bool. auto.
Qed.
Lemma mem_cons_eq : forall x l,
  mem x (x::l) = true.
Proof. intros. simpl. rewrite~ eqb_self. Qed.
Lemma mem_last_eq : forall x l,
  mem x (l & x) = true.
Proof. intros. rewrite mem_last. rewrite~ eqb_self. Qed.
End MemProp.

Lemma drop_struct : forall n l,
  n <= length l -> exists l', 
  length l' = n /\ l = l' ++ (drop n l).
Proof.
  induction n; introv Len.
    exists~ (@nil A).
    destruct l. rewrite length_nil in Len. math.
     destruct (IHn l) as [l' [Le Eq]].
      rewrite length_cons in Len. math.
     exists (a::l'). split. rewrite length_cons. rewrite~ Le.
     rewrite app_cons. simpl. fequals~.
Qed.
(* todo: missing properties of drop *)


Lemma take_nil : forall l, 
  take 0 l = nil.
Proof. auto. Qed.

Lemma take_cons : forall x l n, 
  take (S n) (x::l) = x :: (take n l).
Proof. auto. Qed.

Lemma take_cons_pred : forall x l n, 
  (n > 0) ->
  take n (x::l) = x :: (take (n-1) l).
Proof.
  introv H. destruct n. false; math. 
  simpl. fequals_rec. math.
Qed.

Lemma take_app_l : forall n l l', 
  (n <= length l) ->
  take n (l ++ l') = take n l.
Proof. 
  induction n; destruct l; introv H;
   try rewrite length_nil in H; 
   try rewrite length_cons in H; auto.
  math. 
  rewrite app_cons. do 2 rewrite take_cons. fequals.
   applys IHn. math.
Qed.

Lemma take_app_r : forall n l l', 
  (n >= length l) ->
  take n (l ++ l') = l ++ take (n - length l) l'.
Proof.
  intros. gen n. induction l; introv H. 
  rewrite length_nil in *. do 2 rewrite app_nil_l.
   fequals. math.
  rewrite length_cons in *. destruct n as [|n'].
    false. math. 
    do 2 rewrite app_cons. rewrite take_cons. 
    fequals. applys IHl. math.
Qed.

Lemma take_app_length : forall l l', 
  take (length l) (l ++ l') = l.
Proof.
  intros. rewrite take_app_r.
  asserts_rewrite (forall a, a - a = 0). math. 
  rewrite take_nil. apply app_nil_r. math.
Qed.
 
Lemma take_at_length : forall l, 
  take (length l) l = l.
Proof.
  intros. lets: (@take_app_length l nil).
  rewrite~ app_nil_r in H.
Qed.

  (* todo: or name as take_length ? *)
Lemma length_take : forall n l, 
  n <= length l ->
  length (take n l) = n.
Proof.
  induction n; introv H. 
  rewrite~ take_nil.
  destruct l. rewrite length_nil in H. math.
  rewrite take_cons.
   rewrite length_cons in *. rewrite IHn; math.
Qed.

Lemma take_struct : forall n l,
  n <= length l -> 
  exists l', length (take n l) = n 
          /\ l = (take n l) ++ l'.
Proof. (* todo: relate with drop ! *) 
  induction n; introv Len.
    exists~ l.
    destruct l. rewrite length_nil in Len. math. simpl.
     destruct (IHn l) as [l' [Le Eq]].
      rewrite length_cons in Len. math.
     exists l'. split. rewrite length_cons. rewrite~ Le.
     rewrite app_cons. fequals~.
Qed.

Lemma split_cons : forall {A1 A2} 
 (l1:list A1) (l2:list A2) (x1:A1) (x2:A2) (l:list (A1*A2)),
  (l1,l2) = split l ->
  split ((x1,x2)::l) = (x1::l1,x2::l2).
Proof.
  intros. destruct l; inverts H; simpl.
    auto.
    destruct p. simpl. destruct (split l). fequals.
Qed.
 
Lemma take_and_drop : forall n l f r,
  f = take n l -> r = drop n l -> n <= length l -> 
  l = f ++ r /\ length f = n /\ length r = length l - n.
Proof.
  induction n; introv F R L; simpls.
  subst. splits~. math.
  destruct l.
    rewrite length_nil in L. math.
    rewrite length_cons in L.
     forwards~ (F'&R'&L'): (>> IHn l (take n l) r). math.
     subst f. splits.
       rewrite app_cons. fequals.
       rewrite length_cons. math.
       rewrite length_cons. math.
Qed.
  

End OperationProperties.

Implicit Arguments length_zero_inv [A l].
Implicit Arguments take_struct [A].

Module TakeInt.
Require Import LibInt.
Section Facts.
Variables (A:Type).
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_cons_pred_int : forall x l (n:int), 
  n > 0 ->
  take (abs n) (x::l) = x :: (take (abs (n-1)) l).
Proof.
  introv Pos. rewrite take_cons_pred.
  rewrite abs_minus; try math. auto. apply~ abs_gt. 
Qed.

Lemma take_cons_int : forall x l (n:int), 
  n >= 0 ->
  take (abs (n+1)) (x::l) = x :: (take (abs n) l).
Proof.
  introv Pos. rewrite~ abs_plus.
  rewrite~ plus_comm. math.
Qed.

(* begin hide *)

Lemma take_last_int : forall l (n:int),
  n > 0 -> n <= length l -> exists x,
  take (abs n) l = (take (abs (n - 1)) l) & x.
Proof.
  introv Gt Le.
  destruct (take_struct (abs (n-1)) l) as (l'&L&E).
  apply abs_le. math.
  destruct l'.
    false. rewrite app_nil_r in E.
    asserts M: (forall A B (f:A->B) (x y:A), x = y -> f x = f y).
      introv Q. rewrite~ Q.
    asserts N: (forall A B (f:A->B) (x y:A), x = y -> f x <> f y -> False).
      introv Q D. apply D. apply M. auto.
    applys N (@length A) E.
    rewrite length_take. skip. skip. skip. (*TODO: under construction *)
Admitted.

(* end hide *)

End Facts.
End TakeInt.
Export TakeInt.



(* ********************************************************************** *)
(** * Association lists *)

(* ---------------------------------------------------------------------- *)
(** ** Operations *)

Section Assoc.
Context {A B : Type}.
Variables (IB:Inhab B).
Implicit Types x : A.
Implicit Types l : list (A*B).

Fixpoint assoc k l : B :=
  match l with 
  | nil => arbitrary
  | (x,v)::l' => If x = k then v else assoc k l' 
  end.

Definition mem_assoc k := 
  exists_st (fun p:A*B => k '= fst p).

Definition keys :=
  @map (A*B) A (@fst _ _).

Fixpoint remove_assoc k l : list (A*B) :=
  match l with 
  | nil => nil
  | (x,v)::l' => 
      If k = x 
        then l' 
        else (x,v)::(remove_assoc k l')
  end.

End Assoc.

Implicit Arguments assoc [[A] [B] [IB]].
Implicit Arguments mem_assoc [[A] [B]].
Implicit Arguments keys [[A] [B]].
Implicit Arguments remove_assoc [[A] [B]].


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section AssocProperties.
Variable (A B : Type) (IB:Inhab B).
Implicit Types x : A.
Implicit Types l : list (A*B).

Lemma assoc_cons : forall k x y l,
  assoc k ((x,y)::l) = If x = k then y else assoc k l.
Proof. auto. Qed.
Lemma assoc_here : forall x y l,
  assoc x ((x,y)::l) = y.
Proof. intros. simpl. case_if~. Qed.
Lemma assoc_next : forall x y k l,
  k '<> x -> assoc k ((x,y)::l) = assoc k l.
Proof. intros. simpl. fold_prop. case_if~. Qed.

Lemma keys_nil : 
  keys (@nil (A*B)) = nil.
Proof. auto. Qed.
Lemma keys_cons : forall x y l,
  keys ((x,y)::l) = x :: (keys l).
Proof. auto. Qed.
Lemma keys_app : forall l1 l2,
  keys (l1 ++ l2) = keys l1 ++ keys l2.
Proof. intros. applys map_app. Qed.
Lemma keys_last : forall x y l,
  keys (l & (x,y)) = (keys l) & x.
Proof. intros. rewrite~ keys_app. Qed.

Lemma remove_assoc_nil : forall x,
  remove_assoc x nil = (@nil (A*B)).
Proof. auto. Qed.
Lemma remove_assoc_cons : forall x x' y l,
  remove_assoc x ((x',y)::l) = 
    If x = x' then l else (x',y)::remove_assoc x l.
Proof. auto. Qed.

End AssocProperties.


(* ********************************************************************** *)
(* * Tactics for rewriting *)

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc 
 app_cons_one : rew_app. (* app_last *)
Hint Rewrite fold_right_nil fold_right_cons fold_right_app
 fold_right_last : rew_foldr.
Hint Rewrite fold_left_nil fold_left_cons fold_left_app
 fold_left_last : rew_foldl.
Hint Rewrite length_nil length_cons length_app
 length_last length_rev : rew_length.
Hint Rewrite rev_nil rev_app rev_cons rev_last rev_rev : rew_rev.
 (* +rev_cons_app *)
Hint Rewrite concat_nil concat_app concat_cons concat_last : rew_concat.
Hint Rewrite map_nil map_cons map_app map_last : rew_map.
Hint Rewrite mem_nil mem_cons mem_app mem_last 
 mem_cons_eq mem_last_eq : rew_mem.
Hint Rewrite keys_nil keys_cons keys_app keys_last : rew_keys.
Hint Rewrite assoc_cons assoc_here : rew_assoc.

Tactic Notation "rew_app" :=
  autorewrite with rew_app.
Tactic Notation "rew_foldr" :=
  autorewrite with rew_foldr rew_app.
Tactic Notation "rew_foldl" :=
  autorewrite with rew_foldl rew_app.
Tactic Notation "rew_length" :=
  autorewrite with rew_length.
Tactic Notation "rew_rev" :=
  autorewrite with rew_rev rew_app.
Tactic Notation "rew_concat" :=
  autorewrite with rew_concat rew_app.
Tactic Notation "rew_map" :=
  autorewrite with rew_map rew_app.
Tactic Notation "rew_mem" :=
  autorewrite with rew_mem rew_app.
Tactic Notation "rew_keys" :=
  autorewrite with rew_keys rew_app.
Tactic Notation "rew_assoc" :=
  autorewrite with rew_assoc rew_app.

Tactic Notation "rew_app" "in" hyp(H) :=
  autorewrite with rew_app in H.
Tactic Notation "rew_foldr" "in" hyp(H) :=
  autorewrite with rew_foldr rew_app in H.
Tactic Notation "rew_foldl" "in" hyp(H) :=
  autorewrite with rew_foldl rew_app in H.
Tactic Notation "rew_length" "in" hyp(H) :=
  autorewrite with rew_length in H.
Tactic Notation "rew_rev" "in" hyp(H) :=
  autorewrite with rew_rev rew_app in H.
Tactic Notation "rew_concat" "in" hyp(H) :=
  autorewrite with rew_concat rew_app in H.
Tactic Notation "rew_map" "in" hyp(H) :=
  autorewrite with rew_map rew_app in H.
Tactic Notation "rew_mem" "in" hyp(H) :=
  autorewrite with rew_mem rew_app in H.
Tactic Notation "rew_keys" "in" hyp(H) :=
  autorewrite with rew_keys rew_app in H.
Tactic Notation "rew_assoc" "in" hyp(H) :=
  autorewrite with rew_assoc rew_app in H.

Tactic Notation "rew_app" "in" "*" :=
  autorewrite with rew_app in *.
Tactic Notation "rew_foldr" "in" "*" :=
  autorewrite with rew_foldr rew_app in *.
Tactic Notation "rew_foldl" "in" "*" :=
  autorewrite with rew_foldl rew_app in *.
Tactic Notation "rew_length" "in" "*" :=
  autorewrite with rew_length in *.
Tactic Notation "rew_rev" "in" "*" :=
  autorewrite with rew_rev rew_app in *.
Tactic Notation "rew_concat" "in" "*" :=
  autorewrite with rew_concat rew_app in *.
Tactic Notation "rew_map" "in" "*" :=
  autorewrite with rew_map rew_app in *.
Tactic Notation "rew_mem" "in" "*" :=
  autorewrite with rew_mem rew_app in *.
Tactic Notation "rew_keys" "in" "*" :=
  autorewrite with rew_keys rew_app in *.
Tactic Notation "rew_assoc" "in" "*" :=
  autorewrite with rew_assoc rew_app in *.

Tactic Notation "rew_app" "~" :=
  rew_app; auto_tilde.
Tactic Notation "rew_rev" "~" :=
  rew_rev; auto_tilde.
Tactic Notation "rew_mem" "~" :=
  rew_mem; auto_tilde.
Tactic Notation "rew_length" "~" :=
  rew_length; auto_tilde.

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc 
 app_cons_one 
 fold_right_nil fold_right_cons fold_right_app
 fold_right_last 
 fold_left_nil fold_left_cons fold_left_app
 fold_left_last 
 length_nil length_cons length_app length_rev
 length_last 
 rev_nil rev_app rev_cons rev_last rev_rev
 concat_nil concat_app concat_cons concat_last 
  map_nil map_cons map_app map_last : rew_list.

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc 
 app_cons_one 
 mem_nil mem_cons mem_app mem_last 
 mem_cons_eq mem_last_eq 
 keys_nil keys_cons keys_app keys_last
 assoc_cons assoc_here : rew_lists.

Tactic Notation "rew_list" :=
  autorewrite with rew_list.
Tactic Notation "rew_list" "~" :=
  rew_list; auto_tilde.
Tactic Notation "rew_list" "*" :=
  rew_list; auto_star.
Tactic Notation "rew_list" "in" "*" :=
  autorewrite with rew_list in *.
Tactic Notation "rew_list" "~" "in" "*" :=
  rew_list in *; auto_tilde.
Tactic Notation "rew_list" "*" "in" "*" :=
  rew_list in *; auto_star.
Tactic Notation "rew_list" "in" hyp(H) :=
  autorewrite with rew_list in H.
Tactic Notation "rew_list" "~" "in" hyp(H) :=
  rew_list in H; auto_tilde.
Tactic Notation "rew_list" "*" "in" hyp(H) :=
  rew_list in H; auto_star.

Tactic Notation "rew_lists" :=
  autorewrite with rew_lists.
Tactic Notation "rew_lists" "~" :=
  rew_lists; auto_tilde.
Tactic Notation "rew_lists" "*" :=
  rew_lists; auto_star.
Tactic Notation "rew_lists" "in" "*" :=
  autorewrite with rew_lists in *.
Tactic Notation "rew_lists" "~" "in" "*" :=
  rew_lists in *; auto_tilde.
Tactic Notation "rew_lists" "*" "in" "*" :=
  rew_lists in *; auto_star.
Tactic Notation "rew_lists" "in" hyp(H) :=
  autorewrite with rew_lists in H.
Tactic Notation "rew_lists" "~" "in" hyp(H) :=
  rew_lists in H; auto_tilde.
Tactic Notation "rew_lists" "*" "in" hyp(H) :=
  rew_lists in H; auto_star.


(* ********************************************************************** *)
(** * Other definitions and results *)

(* ---------------------------------------------------------------------- *)
(** * TODO *)

(* todo *)

Definition is_head A (l:list A) (x:A) :=
  exists t, l = x::t.

Definition is_tail A (l:list A) (t:list A) :=
  exists x, l = x::t.

Definition is_last A (l:list A) (x:A) :=
  exists t, l = t&x.

Definition is_init A (l:list A) (t:list A) :=
  exists x, l = t&x.

Hint Unfold is_head is_tail is_last is_init.

Section IsProp.
Variables A : Type.
Implicit Types x : A.

Lemma is_last_one : forall x,
  is_last (x::nil) x.
Proof. intros. unfolds. exists~ (@nil A). Qed.

Lemma is_init_one : forall x,
  is_init (x::nil) nil.
Proof. intros. unfolds. exists~ x. Qed.

End IsProp.

Hint Immediate is_last_one.
Hint Immediate is_init_one.


(* ---------------------------------------------------------------------- *)
(** * Inversions on the structure of lists *)

Section Inversions.
Variables A : Type.
Implicit Types l : list A.

Lemma cons_neq_nil : forall x l, 
  x::l <> nil.
Proof. auto_false. Qed.

Lemma last_eq_nil_inv : forall a l,
  l & a = nil -> False.
Proof. induction l; rew_app; intros; false. Qed.

Lemma nil_eq_last_inv : forall a l,
  nil = l & a -> False.
Proof. intros. apply* last_eq_nil_inv. Qed.

Lemma rev_eq_nil_inv : forall l,
  rev l = nil -> l = nil.
Proof.
  destruct l; rew_rev; intros. auto. 
  false* last_eq_nil_inv. 
Qed.

Lemma nil_eq_rev_inv : forall l,
  nil = rev l -> l = nil.
Proof. introv H. apply~ rev_eq_nil_inv. Qed.

Lemma app_eq_nil_inv : forall l1 l2,
  l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
Proof. destruct l1; destruct l2; intros; tryfalse~; auto. Qed.

Lemma nil_eq_app_inv : forall l1 l2,
  nil = l1 ++ l2 -> l1 = nil /\ l2 = nil.
Proof. intros. symmetry in H. apply* app_eq_nil_inv. Qed.

Lemma app_eq_self_inv_r : forall l1 l2,
  l2 = l1 ++ l2 -> l1 = nil.
Proof.
  introv E. apply length_zero_inv.
  lets: (func_eq_1 length E). rew_length in H. math.
Qed.

Lemma app_eq_self_inv_l : forall l1 l2,
  l1 = l1 ++ l2 -> l2 = nil.
Proof.
  introv E. apply length_zero_inv.
  lets: (func_eq_1 length E). rew_length in H. math.
Qed.

Lemma app_rev_eq_nil_inv : forall l1 l2,
  l1 ++ rev l2 = nil -> l1 = nil /\ l2 = nil.
Proof.
  intros. lets H1 H2: (app_eq_nil_inv _ _ H).
  applys_to H2 rev_eq_nil_inv. auto*.
Qed.

Lemma nil_eq_app_rev_inv : forall l1 l2,
  nil = l1 ++ rev l2 -> l1 = nil /\ l2 = nil.
Proof. intros. apply* app_rev_eq_nil_inv. Qed.

(* todo: too specific? *)

Lemma nil_eq_last_val_app_inv : forall x l1 l2,
  nil = l1 & x ++ l2 -> False.
Proof. intros. destruct l1; inverts H. Qed.

Lemma cons_eq_last_val_app_inv : forall x y l1 l2 l,
  x :: l = l1 & y ++ l2 ->
  (l1 = nil /\ x = y /\ l = l2) \/ (exists l1', l1 = x::l1').
Proof.
  intros. destruct l1; rew_list in H; inverts H.
   left~. right*.
Qed.

Lemma last_inv : forall l,
  (length l > 0%nat) -> 
  exists x l', l = l' & x.
Proof.
  induction l; rew_length; introv H.
  false. math.
  destruct l.
    exists~ a (@nil A).
    destruct IHl as (x&l'&E). rew_length in *. math.
    exists x (a::l'). rewrite~ E.
Qed.   

Lemma app_not_empty_l : forall l1 l2,
  l1 <> nil -> l1 ++ l2 <> nil.
Proof. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

Lemma app_not_empty_r : forall l1 l2,
  l2 <> nil -> l1 ++ l2 <> nil.
Proof. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

End Inversions.

Implicit Arguments last_eq_nil_inv [A a l].
Implicit Arguments nil_eq_last_inv [A a l].
Implicit Arguments rev_eq_nil_inv [A l].
Implicit Arguments nil_eq_rev_inv [A l].
Implicit Arguments app_eq_nil_inv [A l1 l2].
Implicit Arguments nil_eq_app_inv [A l1 l2].
Implicit Arguments app_rev_eq_nil_inv [A l1 l2].
Implicit Arguments nil_eq_app_rev_inv [A l1 l2].
Implicit Arguments nil_eq_last_val_app_inv [A x l1 l2]. 
Implicit Arguments cons_eq_last_val_app_inv [A x y l1 l2 l].


(* ---------------------------------------------------------------------- *)
(* ** Function for mapping partial function on lists *)

Definition map_partial (A B : Type) (f : A -> option B) :=
  fix aux (l : list A) : option (list B) := match l with
    | nil => Some nil
    | x::l' => LibOption.apply_on (f x) (fun v =>
                 LibOption.map (cons v) (aux l'))
   end.

Lemma map_partial_inv : forall (A B:Type) (f: A->option B) lx ly,
  map_partial f lx = Some ly ->
  Forall2 (fun x y => f x = Some y) lx ly. 
Proof.
  induction lx; simpl map_partial; introv Eq.
  inverts Eq. apply Forall2_nil.
  lets fa Fa Eq2: (apply_on_inv Eq).
   lets ly1 Eqly ?: (map_on_inv Eq2). subst ly.
   apply* Forall2_cons.
Qed.

Implicit Arguments map_partial_inv [A B f lx ly].


(* ---------------------------------------------------------------------- *)
(* ** Induction principle on lists *)

Section ListSub.
Variable (A:Type).

Inductive list_sub : list A -> list A -> Prop :=
  | list_sub_cons : forall x l, 
      list_sub l (x::l).

Hint Constructors list_sub.
Lemma list_sub_wf : wf list_sub.
Proof.
  intros l. induction l;
  apply Acc_intro; introv H; inverts~ H. 
Qed.

End ListSub.

Implicit Arguments list_sub [[A]].
Hint Constructors list_sub.
Hint Resolve list_sub_wf : wf.


(* ********************************************************************** *)
(** * Properties of predicate on lists *)

Section PropProperties.
Variables A : Type.
Implicit Types l : list A.

Hint Constructors Forall.

Lemma Forall_app : forall P l1 l2, 
  Forall P l1 -> Forall P l2 -> 
  Forall P (l1 ++ l2).
Proof. introv H Px. induction H; rew_app; auto. Qed.

Lemma Forall_app_inv : forall P l1 l2, 
  Forall P (l1 ++ l2) ->
  Forall P l1 /\ Forall P l2.
Proof.
  intros. induction l1. auto.
  rew_app in H. inverts* H.
Qed.

Lemma Forall_last : forall P l x, 
  Forall P l -> P x -> 
  Forall P (l & x).
Proof. intros. apply~ Forall_app. Qed.

Lemma Exists_nil_inv : forall (P : A -> Prop),
  Exists P nil -> False.
Proof. introv H. invert* H. Qed.

Lemma Exists_cons_inv : forall (P : A -> Prop) l x,
  Exists P (x::l) -> P x \/ Exists P l.
Proof. induction l; introv H; inverts~ H. Qed.

End PropProperties.

Section ForallToConj.
Variables (A : Type) (P : A->Prop).
Hint Constructors Forall.
Ltac forall_to_conj_prove :=
  extens; iff H;
  repeat (match goal with H: Forall _ _ |- _ => inversion H end); 
  repeat (first [constructor | auto* ]).

Lemma Forall_to_conj_1 : forall x1,
  Forall P (x1::nil) = (P x1).
Proof. forall_to_conj_prove. Qed.

Lemma Forall_to_conj_2 : forall x1 x2,
  Forall P (x1::x2::nil) = (P x1 /\ P x2).
Proof. forall_to_conj_prove. Qed.

Lemma Forall_to_conj_3 : forall x1 x2 x3,
  Forall P (x1::x2::x3::nil) = (P x1 /\ P x2 /\ P x3).
Proof. forall_to_conj_prove. Qed.

Lemma Forall_to_conj_4 : forall x1 x2 x3 x4,
  Forall P (x1::x2::x3::x4::nil) = (P x1 /\ P x2 /\ P x3 /\ P x4).
Proof. forall_to_conj_prove. Qed.

End ForallToConj.

Hint Resolve has_pair_here has_pair_next.

Section PropProperties2.
Variables A1 A2 : Type.
Implicit Types l : list A1.
Implicit Types r : list A2.
Hint Constructors Forall2.

Lemma Forall2_app : forall P l1 l2 r1 r2, 
      Forall2 P l1 r1 -> Forall2 P l2 r2 ->
      Forall2 P (l1 ++ l2) (r1 ++ r2).
Proof. introv H H'. induction H; rew_app; auto. Qed.

Lemma Forall2_last : forall P l r x1 x2, 
      Forall2 P l r -> P x1 x2 ->
      Forall2 P (l & x1) (r & x2).
Proof. intros. apply~ Forall2_app. Qed.

Lemma Forall2_last_inv : forall P l1 r' x1, 
  Forall2 P (l1 & x1) r' ->
  exists (r2:list A2) x2, 
  r' = r2 & x2 /\ P x1 x2 /\ Forall2 P l1 r2.
Proof. 
  introv H. sets_eq l': (l1&x1). gen l1 x1.
  induction H; intros; subst.
  false* nil_eq_last_inv.
  destruct l0; rew_app in EQl'; inverts EQl'.
    inverts H0. exists~ (@nil A2) x2.
    forwards~ (r2'&x2'&?&?&?): IHForall2. subst. exists~ (x2::r2') x2'.   
Qed.

Lemma Forall2_length : forall P l r,
  Forall2 P l r -> length l = length r.
Proof.
  introv H. induction H. simple~. 
  do 2 rewrite~ length_cons. 
Qed.

Lemma Forall2_take : forall P n l r,
  Forall2 P l r ->
  Forall2 P (take n l) (take n r).
Proof. induction n; introv H; inverts H; simple~. Qed.

Hint Constructors Forall2.
Hint Resolve Forall2_last.

Lemma Forall2_rev : forall P l r,
  Forall2 P l r -> Forall2 P (rev l) (rev r).
Proof. induction l; introv M; inverts M; rew_rev; auto. Qed.

End PropProperties2.

Implicit Arguments Forall2_last_inv [A1 A2 P l1 r' x1].

(** [list_equiv E l1 l2] asserts that the lists [l1] and [l2]
    are equal when their elements are compared modulo E *)

Definition list_equiv (A:Type) (E:binary A) : binary (list A) :=
   Forall2 E.

Section ListEquiv.
Hint Constructors Forall2.

Lemma list_equiv_equiv : forall A (E:binary A),
  equiv E -> equiv (list_equiv E).
Proof.
  introv Equiv. unfold list_equiv. constructor.
  unfolds. induction x. auto. constructor*.
  unfolds. induction x; destruct y; introv H; inversions* H.
  unfolds. induction y; destruct x; destruct z; introv H1 H2;
   inversions H1; inversions* H2.
Qed.

End ListEquiv.

(* todo : inversion lemmas for other predicates *)

Section NthProperties.
Variables (A : Type) (IA : Inhab A).
Implicit Types l : list A.
Implicit Types x : A.
Implicit Types n : nat.
Hint Constructors Nth.

Lemma Nth_lt_length : forall n l x,
  Nth n l x -> n < length l.
Proof. 
  induction n; introv H; inverts H.
  rewrite length_cons. math.
  rewrite length_cons. simpl. rew_nat*.
Qed.

Lemma Nth_func: forall n l x1 x2,
  Nth n l x1 -> Nth n l x2 -> x1 = x2.
Proof. introv H1. induction H1; intro H2; inverts~ H2. Qed.

Lemma Nth_to_nth : forall n l x,
  Nth n l x -> nth n l = x.
Proof. introv H. induction~ H. Qed.

Lemma mem_Nth : forall l x,
  mem x l -> exists n, Nth n l x.
Proof. 
  intros. induction l.
  rewrite mem_nil in H. false.
  rewrite mem_cons in H. rew_reflect in H. destruct H.
   fold_prop. subst*.
   forwards* [n ?]: IHl.
Qed.

Implicit Arguments mem_Nth [l x].

Lemma mem_nth : forall l x,
  mem x l -> exists n, nth n l = x.
Proof.
  intros. forwards [n P]: (mem_Nth H).
  exists n. apply~ Nth_to_nth.
Qed.

Lemma Nth_app_l : forall n x l1 l2,
  Nth n l1 x -> Nth n (l1 ++ l2) x.
Proof. induction n; introv H; inverts H; rew_list*. Qed.

Lemma Nth_app_r : forall n m x l1 l2,
  Nth m l2 x -> n = (m + length l1)%nat -> Nth n (l1 ++ l2) x.
Proof.
  intros. subst. gen m. induction l1; introv H.
  rew_list. applys_eq~ H 3.
  rew_list. applys_eq* Nth_next 3. 
Qed.

Lemma Nth_app_inv : forall n x l1 l2,
  Nth n (l1++l2) x -> 
     (Nth n l1 x)
  \/ (exists m, n = (length l1 + m)%nat /\ Nth m l2 x).
Proof.
  introv. gen n. induction l1; introv H; rew_list in H.
  right. rew_length. exists~ n.
  inverts H. left~.
   forwards* M: IHl1. destruct M.
    left~. intuit. rew_length.
    right*. exists x0. split~. math.
Qed.

Lemma Nth_nil_inv : forall n x,
  Nth n nil x -> False.
Proof. introv H. inverts H. Qed.

Lemma Nth_cons_inv : forall n x l,
  Nth n l x -> 
     (exists q, l = x::q /\ n = 0%nat)
  \/ (exists y q m, l = y::q /\ Nth m q x /\ n = (m+1)%nat).
Proof.
  introv H. inverts H. left*.
  right. eauto 8 with maths. 
Qed.

End NthProperties.

(* ---------------------------------------------------------------------- *)
(* ** Mem *)

Section MemFacts.
Hint Constructors Mem.

Lemma Mem_nil_eq : forall A (x:A),
  Mem x nil = False.
Proof. intros. extens. iff H; inverts H. Qed.

Lemma Mem_cons_eq : forall A (x y:A) l,
  Mem x (y::l) = ((x = y) \/ (Mem x l)).
Proof. intros. extens. iff H; inverts~ H. Qed.

Lemma Mem_app_or_eq : forall (A:Type) (l1 l2 : list A) x,
  Mem x (l1 ++ l2) = (Mem x l1 \/ Mem x l2).
Proof.
  intros. extens. induction l1; rew_app.
  split. auto. introv [H|?]. inverts H. auto.
  iff M. inverts~ M. rewrite IHl1 in H0. destruct* H0.
   destruct M. inverts~ H. constructors. rewrite~ IHl1.  
   constructors. rewrite~ IHl1.  
Qed.

Lemma Mem_app_or : forall (A:Type) (l1 l2 : list A) x,
  Mem x l1 \/ Mem x l2 -> Mem x (l1 ++ l2).
Proof. intros. rewrite~ Mem_app_or_eq. Qed.

Lemma Mem_last : forall A (L:list A) x,
  Mem x (L & x).
Proof. intros. apply* Mem_app_or. Qed.

Lemma Mem_rev : forall A (L:list A) x,
  Mem x L -> Mem x (rev L).
Proof. introv H. induction H; rew_rev; apply~ Mem_app_or. Qed.

Lemma Mem_inv : forall A (L:list A) x y,
  Mem x (y::L) -> x = y \/ x <> y /\ Mem x L.
Proof. introv H. tests: (x = y). eauto. inverts H. false. eauto. Qed.

End MemFacts.

(* ---------------------------------------------------------------------- *)
(* ** Update of a functional list *)

Definition Update A (n:nat) (x:A) l l' :=
    length l' = length l 
  /\ (forall y m, Nth m l y -> m <> n -> Nth m l' y)
  /\ Nth n l' x.

Section UpdateProp.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types n : nat.
Hint Constructors Nth.

Lemma Update_here : forall x y l,
  Update 0 x (y::l) (x::l).
Proof. 
  intros. splits.
  rew_length~.
  introv M H. inverts* M.
  auto*.
Qed.

Lemma Update_cons : forall i x y l l',
  Update i x l l' -> Update (S i) x (y::l) (y::l').
Proof.
  introv (L&O&E). splits.
  rew_length~.
  introv M H. inverts* M.
  auto*.
Qed.

Lemma Update_app_l : forall i x l1 l1' l2,
  Update i x l1 l1' -> Update i x (l1++l2) (l1'++l2).
Proof.
  introv (L&O&E). splits.
  rew_length~.
  introv M H. destruct (Nth_app_inv _ _ M).
    apply~ Nth_app_l.
    intuit. apply* Nth_app_r. math.
  apply~ Nth_app_l.
Qed.

Lemma Update_app_r : forall i j x l1 l2 l2',
  Update j x l2 l2' -> i = (j + length l1)%nat -> Update i x (l1++l2) (l1++l2').
Proof.
  introv (L&O&E) Eq. splits.
  rew_length~.
  introv M H. destruct (Nth_app_inv _ _ M).
    apply~ Nth_app_l.
    intuit. apply* Nth_app_r. apply* O. math. math.
  apply* Nth_app_r.
Qed.

Lemma Update_length : forall i x l l',
  Update i x l l' -> length l = length l'.
Proof. introv (L&O&E). auto. Qed. 

Lemma Update_not_nil : forall i x l1 l2,
  Update i x l1 l2 -> l2 <> nil.
Proof. introv (L&O&E) K. subst. inverts E. Qed.

End UpdateProp.

