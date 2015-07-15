(**************************************************************************
* TLC: A library for Coq                                                  *
* Variable names                                                          *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibList LibLogic LibNat LibEpsilon LibReflect.
Require Export LibFset.


(* ********************************************************************** *)
(** * Abstract Definition of Variables *)

Module Type VariablesType.

Definition var := nat.

(** This type is inhabited. *)

Parameter var_inhab : Inhab var.

(** This type is comparable. *)
Parameter var_comp : Comparable var.
Instance var_comparable : Comparable var := var_comp.

(** We can build sets of variables. *)

Definition vars := fset var.

(** Finally, we have a means of generating fresh variables. *)

Parameter var_gen : vars -> var.
Parameter var_gen_spec : forall E, (var_gen E) \notin E.
Parameter var_fresh : forall (L : vars), { x : var | x \notin L }.

Definition var_gen_list (l : list nat) :=
  1 + fold_right plus O l.

End VariablesType.


(* ********************************************************************** *)
(** * Concrete Implementation of Variables *)

Module Export Variables : VariablesType.

Definition var := nat.

Lemma var_inhab : Inhab var.
Proof. apply (prove_Inhab 0). Qed.

Lemma var_comp : Comparable var.
Proof. apply nat_comparable. Qed.

Instance var_comparable : Comparable var := var_comp.

Definition vars := fset var.

Definition var_gen_list (l : list nat) :=
  1 + fold_right plus O l.

Lemma var_gen_list_spec : forall n l,
  n \in from_list l -> n < var_gen_list l.
Proof.
  unfold var_gen_list. induction l; introv I.
  rewrite from_list_nil in I. false (in_empty_elim I).
  rewrite from_list_cons in I. rew_list.
   rewrite in_union in I. destruct I as [H|H].
     rewrite in_singleton in H. subst. nat_math.
     specializes IHl H. nat_math.
Qed.

Definition var_gen (E : vars) : var :=
  var_gen_list (epsilon (fun l => E = from_list l)).

Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  intros. unfold var_gen. spec_epsilon as l.
  applys fset_finite. rewrite Hl. introv H.
  forwards M: var_gen_list_spec H. nat_math.
Qed.

Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof. intros L. exists (var_gen L). apply var_gen_spec. Qed.

End Variables.


(* ********************************************************************** *)
(** ** Lists of variables of given length and given freshness *)

(** Freshness of n variables from a set L and from one another. *)

Fixpoint fresh (L : vars) (n : nat) (xs : list var) {struct xs} : Prop :=
  match xs, n with
  | nil, O => True
  | x::xs', S n' => x \notin L /\ fresh (L \u \{x}) n' xs'
  | _,_ => False
  end.

Hint Extern 1 (fresh _ _ _) => simpl.

(* It is possible to build a list of n fresh variables. *)

Lemma var_freshes : forall L n, 
  { xs : list var | fresh L n xs }.
Proof.
  intros. gen L. induction n; intros L.
  exists* (nil : list var).
  destruct (var_fresh L) as [x Fr].
   destruct (IHn (L \u \{x})) as [xs Frs].
   exists* (x::xs).
Qed.


(* ********************************************************************** *)
(** ** Picking fresh names *)

(** [gather_vars_for_type T F] return the union of all the finite sets
  of variables [F x] where [x] is a variable from the context such that
  [F x] type checks. In other words [x] has to be of the type of the
  argument of [F]. The resulting union of sets does not contain any
  duplicated item. This tactic is an extreme piece of hacking necessary
  because the tactic language does not support a "fold" operation on
  the context. *)

Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | \{} => gather FH
      | context [FH] => fail 1
      | _ => gather (FH \u V)
      end
    | _ => V
    end in
  let L := gather (\{}:vars) in eval simpl in L.

(** [beautify_fset V] assumes that [V] is built as a union of finite
  sets and return the same set cleaned up: empty sets are removed and
  items are laid out in a nicely parenthesized way *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | ?E1 \u ?E2 => let Acc1 := go Acc E1 in
                     go Acc1 E2
     | \{}  => Acc
     | ?E1 => match Acc with
              | \{} => E1
              | _ => constr:(Acc \u E1)
              end
     end
  in go (\{}:vars) V.

(** [pick_fresh_gen L Y] expects [L] to be a finite set of variables
  and adds to the context a variable with name [Y] and a proof that
  [Y] is fresh for [L]. *)

Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_fresh L) as [Y Fr]).

(** [pick_fresh_gens L n Y] expects [L] to be a finite set of variables
  and adds to the context a list of variables with name [Y] and a proof 
  that [Y] is of length [n] and contains variable fresh for [L] and
  distinct from one another. *)

Ltac pick_freshes_gen L n Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_freshes L n) as [Y Fr]).




(* ********************************************************************** *)
(** ** Tactics for notin *)

Implicit Types x : var.

(** For efficiency, we avoid rewrites by splitting equivalence. *)

Lemma notin_singleton_r : forall x y,
  x \notin \{y} -> x <> y.
Proof. intros. rewrite~ <- notin_singleton. Qed.

Lemma notin_singleton_l : forall x y,
  x <> y -> x \notin \{y}.
Proof. intros. rewrite~ notin_singleton. Qed.

Lemma notin_singleton_swap : forall x y,
  x \notin \{y} -> y \notin \{x}.
Proof.
  intros. apply notin_singleton_l.
  apply sym_not_eq. apply~ notin_singleton_r.
Qed.

Lemma notin_union_r : forall x E F,
  x \notin (E \u F) -> (x \notin E) /\ (x \notin F).
Proof. intros. rewrite~ <- notin_union. Qed.

Lemma notin_union_r1 : forall x E F,
  x \notin (E \u F) -> (x \notin E).
Proof. introv. rewrite* notin_union. Qed.

Lemma notin_union_r2 : forall x E F,
  x \notin (E \u F) -> (x \notin F).
Proof. introv. rewrite* notin_union. Qed.

Lemma notin_union_l : forall x E F,
  x \notin E -> x \notin F -> x \notin (E \u F).
Proof. intros. rewrite~ notin_union. Qed.

Lemma notin_var_gen : forall E F,
  (forall x, x \notin E -> x \notin F) ->
  (var_gen E) \notin F.
Proof. intros. auto~ var_gen_spec. Qed.

Implicit Arguments notin_singleton_r    [x y].
Implicit Arguments notin_singleton_l    [x y].
Implicit Arguments notin_singleton_swap [x y].
Implicit Arguments notin_union_r  [x E F].
Implicit Arguments notin_union_r1 [x E F].
Implicit Arguments notin_union_r2 [x E F].
Implicit Arguments notin_union_l  [x E F].

(** Tactics to deal with notin.  *)

Ltac notin_solve_target_from x E H :=
  match type of H with 
  | x \notin E => constr:(H)
  | x \notin (?F \u ?G) =>  
     let H' :=
        match F with 
        | context [E] => constr:(notin_union_r1 H)
        | _ => match G with 
          | context [E] => constr:(notin_union_r2 H)
          | _ => fail 20
          end
        end in
     notin_solve_target_from x E H' 
  end.

Ltac notin_solve_target x E :=
  match goal with 
  | H: x \notin ?L |- _ =>
    match L with context[E] =>
      let F := notin_solve_target_from x E H in
      apply F 
    end
  | H: x <> ?y |- _ => 
     match E with \{y} => 
       apply (notin_singleton_l H)
     end
  end.

Ltac notin_solve_one :=
  match goal with
  | |- ?x \notin \{?y} => 
     apply notin_singleton_swap; 
     notin_solve_target y (\{x}) 
  | |- ?x \notin ?E => 
    notin_solve_target x E
  (* If x is an evar, tries to instantiate it.
     Problem: it might loop ! 
  | |- ?x \notin ?E => 
     match goal with y:var |- _ =>
       match y with 
       | x => fail 1
       | _ =>
         let H := fresh in cuts H: (y \notin E); 
         [ apply H | notin_solve_target y E ]
        end
     end
  *)
  end.

Ltac notin_simpl :=
  match goal with 
  | |- _ \notin (_ \u _) => apply notin_union_l; notin_simpl 
  | |- _ \notin (\{}) => apply notin_empty; notin_simpl
  | |- ?x <> ?y => apply notin_singleton_r; notin_simpl
  | |- _ => idtac
  end.

Ltac notin_solve_false :=
  match goal with 
  | H: ?x \notin ?E |- _ =>
    match E with context[x] =>
      apply (@notin_same _ x); 
      let F := notin_solve_target_from x (\{x}) H in
      apply F
    end 
  | H: ?x <> ?x |- _ => apply H; reflexivity
  end.

Ltac notin_false :=
  match goal with
  | |- False => notin_solve_false
  | _ => intros_all; false; notin_solve_false
  end.

Ltac notin_from_fresh_in_context :=
  repeat (match goal with H: fresh _ _ _ |- _ =>
    progress (simpl in H; destructs H) end).

Ltac notin_solve :=
  notin_from_fresh_in_context;
  first [ notin_simpl; try notin_solve_one
        | notin_false ].

Hint Extern 1 (_ \notin _) => notin_solve.
Hint Extern 1 (_ <> _ :> var) => notin_solve.
Hint Extern 1 ((_ \notin _) /\ _) => splits.

(* 
LATER:
  | |- ?x \notin ?E => 
	progress (unfold x); notin_simpl
  | |- (var_gen ?x) \notin _ =>
        apply notin_var_gen; intros; notin_simpl
*)

(* ********************************************************************** *)
(** ** Tactics for fresh *)

(* todo: cleanup proofs of fresh using calc_fset *)

Lemma fresh_union_r : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs /\ fresh L2 n xs.
Proof.
  induction xs; simpl; intros; destruct n;
  tryfalse*. auto.
  destruct H. split; split; auto.
  forwards*: (@IHxs (L1 \u \{a}) L2 n).
   rewrite union_comm.
   rewrite union_comm_assoc.
   rewrite* union_assoc.
  forwards*: (@IHxs L1 (L2 \u \{a}) n).
   rewrite* union_assoc.
Qed.

Lemma fresh_union_r1 : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs.
Proof. intros. forwards*: fresh_union_r. Qed.

Lemma fresh_union_r2 : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L2 n xs.
Proof. intros. forwards*: fresh_union_r. Qed.

Lemma fresh_union_l : forall xs L1 L2 n,
  fresh L1 n xs -> fresh L2 n xs -> fresh (L1 \u L2) n xs.
Proof.
  induction xs; simpl; intros; destruct n; tryfalse*. auto.
  destruct H. destruct H0. split~.
  forwards~ K: (@IHxs (L1 \u \{a}) (L2 \u \{a}) n). 
  rewrite <- (union_same \{a}).
  rewrite union_assoc.
  rewrite <- (union_assoc L1).
  rewrite (union_comm L2).
  rewrite (union_assoc L1).
  rewrite* <- union_assoc.
Qed.

Lemma fresh_empty : forall L n xs,
  fresh L n xs -> fresh \{} n xs.
Proof.
  intros. rewrite <- (union_empty_r L) in H.
  destruct* (fresh_union_r _ _ _ _ H).
Qed.

Lemma fresh_length : forall L n xs,
  fresh L n xs -> n = length xs.
Proof.
  intros. gen n L. induction xs; simpl; intros n L Fr;
    destruct n; tryfalse*. 
  auto.
  rew_length. rewrite* <- (@IHxs n (L \u \{a})).
Qed.

Lemma fresh_resize : forall L n xs,
  fresh L n xs -> forall m, m = n -> fresh L m xs.
Proof.
  introv Fr Eq. subst~.
Qed.

Lemma fresh_resize_length : forall L n xs,
  fresh L n xs -> fresh L (length xs) xs.
Proof.
  introv Fr. rewrite* <- (fresh_length _ _ _ Fr).
Qed.

Implicit Arguments fresh_union_r [xs L1 L2 n].
Implicit Arguments fresh_union_r1 [xs L1 L2 n].
Implicit Arguments fresh_union_r2 [xs L1 L2 n].
Implicit Arguments fresh_union_l [xs L1 L2 n].
Implicit Arguments fresh_empty  [L n xs].
Implicit Arguments fresh_length [L n xs].
Implicit Arguments fresh_resize [L n xs].
Implicit Arguments fresh_resize_length [L n xs].

Lemma fresh_single_notin : forall x xs n,
  fresh \{x} n xs ->
  x \notin from_list xs.
Proof.
  induction xs; destruct n; introv F; simpl in F; tryfalse.
  rewrite~ from_list_nil.
  destruct F as [Fr F']. lets [? ?]: (fresh_union_r F').
   specializes IHxs n. rewrite~ from_list_cons.
Qed.

Ltac fresh_solve_target_from E n xs H :=
  match type of H with 
  | fresh E n xs => constr:(H)
  | fresh E ?m xs => 
      match n with 
      | length xs => constr:(fresh_resize_length H) 
      | _ => 
         match goal with 
         | Eq: m = n |- _ => constr:(fresh_resize H _ (sym_eq Eq)) 
         | Eq: n = m |- _ => constr:(fresh_resize H _ Eq) 
         end
      end
  | fresh (?F \u ?G) ?m xs => 
     let H' :=
        match F with 
        | context [E] => constr:(fresh_union_r1 H)
        | _ => match G with 
          | context [E] => constr:(fresh_union_r2 H)
          | _ => fail 20
          end
        end in
     fresh_solve_target_from E n xs H' 
  end.

Ltac fresh_solve_target E n xs :=
  match goal with H: fresh ?L _ xs |- _ =>
    match L with context[E] =>
      let F := fresh_solve_target_from E n xs H in
      apply F 
    end
  end.

Ltac fresh_solve_one :=
  match goal with 
  | |- fresh ?E ?n ?xs =>   
    fresh_solve_target E n xs 
  | |- fresh \{} ?n ?xs =>
    match goal with H: fresh ?F ?m xs |- _ =>
      apply (fresh_empty H);
      fresh_solve_target F n xs 
    end
  end.

Ltac fresh_simpl :=
  try match goal with |- fresh (_ \u _) _ _ =>
    apply fresh_union_l; fresh_simpl end.

Ltac fresh_solve_by_notins :=
  simpl; splits; try notin_solve.

Ltac fresh_solve :=
  fresh_simpl; 
  first [ fresh_solve_one 
        | fresh_solve_by_notins 
        | idtac ].

Hint Extern 1 (fresh _ _ _) => fresh_solve.

(* LATER: more automation of fresh_length properties *)



