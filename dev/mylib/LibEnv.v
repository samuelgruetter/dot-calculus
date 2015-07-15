(**************************************************************************
* TLC: A library for Coq                                                  *
* Environments for metatheory                                             *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibOption LibList LibProd LibLogic LibReflect.
Require Export LibVar.
Generalizable Variable A.


(* ********************************************************************** *)
(** * Definition of environments and their basic operations *)
 
(** To avoid definitions being unfolded by [simpl] in an uncontrollable
    manner, we use a module signature to enforce abstraction *)

(* ---------------------------------------------------------------------- *)
(** ** Abstract definitions *)

Definition env (A:Type) := list (var * A).

Module Type EnvOpsSig.

Section Definitions.
Variable A B : Type.

Parameter empty : env A.
Parameter empty_def : empty = nil.

Parameter single : var -> A -> env A.
Parameter single_def : 
  single = fun x v => (x,v)::nil.

Parameter concat : env A -> env A -> env A.
Parameter concat_def :
  concat = fun E F => F ++ E.

Parameter singles : list var -> list A -> env A.
Parameter singles_def : 
  singles = fun xs vs =>
    fold_right (fun p acc => concat acc (single (fst p) (snd p))) empty (combine xs vs).

Parameter keys : env A -> list var.
Parameter keys_def : 
  keys = map fst.

Parameter values : env A -> list A.
Parameter values_def :
  values = map snd.

Parameter fold_vars : (A -> vars) -> env A -> vars.
Parameter fold_vars_defs : 
  fold_vars = fun fv E =>
    fold_right (fun v acc => fv v \u acc) \{} (values E).

Parameter dom : env A -> vars.
Parameter dom_def : 
  dom = fold_right (fun p E => \{fst p} \u E) \{}.

Parameter map : (A -> B) -> env A -> env B.
Parameter map_def : 
  map = fun f E => 
    LibList.map (fun p => (fst p, f (snd p))) E.

Parameter map_keys : (var -> var) -> env A -> env A.
Parameter map_keys_def : 
  map_keys = fun f E =>
    LibList.map (fun p => (f (fst p), snd p)) E.

Parameter get : var -> env A -> option A.
Fixpoint get_impl (k : var) (E : env A) {struct E} : option A :=
  match E with
  | nil => None
  | (x,v) :: E' => If k = x then Some v else get_impl k E'
  end.
Parameter get_def : 
  get = get_impl.

End Definitions.

Implicit Arguments empty [A].

End EnvOpsSig.


(* ---------------------------------------------------------------------- *)
(** ** Concrete definitions *)

Module Export EnvOps : EnvOpsSig.

Section Concrete.
Variable A B : Type.

Definition empty : env A := nil.
Lemma empty_def : empty = nil.
Proof. reflexivity. Qed.

Definition single x v : env A := (x,v)::nil.
Lemma single_def : 
  single = fun x v => (x,v)::nil.
Proof. reflexivity. Qed.

Definition concat (E F : env A) := F ++ E.
Lemma concat_def : 
  concat = fun E F => F ++ E.
Proof. reflexivity. Qed.

Definition singles (xs : list var) (vs : list A) : env A := 
  fold_right (fun p acc => concat acc (single (fst p) (snd p))) empty (combine xs vs).
Lemma singles_def : 
  singles = fun xs vs =>
   fold_right (fun p acc => concat acc (single (fst p) (snd p))) empty (combine xs vs).
Proof. reflexivity. Qed.

Definition keys : env A -> list var :=
  map fst.
Lemma keys_def : 
  keys = map fst.
Proof. reflexivity. Qed.

Definition values : env A -> list A :=
  map snd.
Lemma values_def : 
  values = map snd.
Proof. reflexivity. Qed.

Definition fold_vars (fv : A -> vars) (E : env A) :=
  fold_right (fun v acc => fv v \u acc) \{} (values E).
Lemma fold_vars_defs : 
  fold_vars = fun fv E => fold_right (fun v acc => fv v \u acc) \{} (values E).
Proof. reflexivity. Qed.

Definition map (f:A->B) (E:env A) :=
  LibList.map (fun p => (fst p, f (snd p))) E.
Lemma map_def : 
  map = fun f E => LibList.map (fun p => (fst p, f (snd p))) E.
Proof. reflexivity. Qed.

Definition map_keys (f:var->var) (E:env A) :=
  LibList.map (fun p => (f (fst p), snd p)) E.
Lemma map_keys_def : 
  map_keys = fun f E => LibList.map (fun p => (f (fst p), snd p)) E.
Proof. reflexivity. Qed.

Definition dom : env A -> vars :=  
  fold_right (fun p E => \{fst p} \u E) \{}.
Lemma dom_def : 
  dom = fold_right (fun p E => \{fst p} \u E) \{}.
Proof. reflexivity. Qed.

Fixpoint get_impl (k : var) (E : env A) {struct E} : option A :=
  match E with
  | nil => None
  | (x,v) :: E' => If k = x then Some v else get_impl k E'
  end.
Definition get := get_impl.
Lemma get_def : 
  get = get_impl.
Proof. reflexivity. Qed.

End Concrete.

Implicit Arguments empty [A].

End EnvOps.

(* ---------------------------------------------------------------------- *)
(** ** Notations *)

(** [x ~ a] is the notation for a singleton environment mapping x to a. *)

Notation "x ~ a" := (single x a)
  (at level 27, left associativity) : env_scope.

(** [xs ~* vs] is the notation for [single_iter xs vs]. *)

Notation "xs ~* vs" := (singles xs vs)
  (at level 27, left associativity) : env_scope.

(** [E & F] is the notation for concatenation of E and F. *)

Notation "E & F" := (concat E F) 
  (at level 28, left associativity) : env_scope.

(** [x # E] to be read x fresh from E captures the fact that 
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Bind Scope env_scope with env.
Delimit Scope env_scope with env.
Open Scope env_scope.

(* ---------------------------------------------------------------------- *)
(** ** Additional definitions *)

Section MoreDefinitions.
Variable A : Type.
Implicit Types E F : env A.

(** Well-formed environments contains no duplicate bindings. *)

Inductive ok : env A -> Prop :=
  | ok_empty :
      ok empty
  | ok_push : forall E x v,
      ok E -> x # E -> ok (E & x ~ v).

(** An environment contains a binding from x to a iff the most recent
  binding on x is mapped to a *)

Definition binds x v E := 
  get x E = Some v.

(** Read the value associated to a bound variable *)

Definition get_or_arbitrary `{Inhab A} x (E:env A) :=
  unsome (get x E).

(** Inclusion of an environment in another one. *)

Definition extends E F :=
  forall x v, binds x v E -> binds x v F.

(** Gathering free variables contained in the values of an environment *)

Definition fv_in_values (fv:A->vars) (E:env A) :=
  fold_right (fun v L => (fv v) \u L) \{} (values E).

End MoreDefinitions.


(* ---------------------------------------------------------------------- *)
(** ** Basic Properties *)

Hint Rewrite empty_def single_def concat_def singles_def keys_def values_def
  dom_def map_def map_keys_def get_def : env_defs.

Ltac rew_env_defs := autorewrite with env_defs in *.

Section Properties.

Variable A B : Type.
Implicit Types k x : var.
Implicit Types v : A.
Implicit Types E F G : env A.
Implicit Types f : A -> B.
Implicit Types r : var -> var.

Lemma cons_to_push : forall x v E,
  (x, v) :: E = E & x ~ v.
Proof. intros. rew_env_defs. rew_app~. Qed.

Lemma env_ind : forall (P : env A -> Prop),
  (P empty) ->
  (forall E x v, P E -> P (E & x ~ v)) ->
  (forall E, P E).
Proof.
  rew_env_defs. induction E as [|(x,v)].
  auto. forwards*: H0 IHE.
Qed.

Lemma map_empty : forall f,
  map f empty = empty.
Proof. intros. rew_env_defs. auto. Qed.
Lemma map_single : forall f x v,
  map f (x ~ v) = (x ~ f v).
Proof. intros. rew_env_defs. auto. Qed.
Lemma map_concat : forall f E F,
  map f (E & F) = map f E & map f F.
Proof.
  intros. rew_env_defs.
  gen E. induction F as [|(x,v)]; intros.
  rew_list~. 
  rew_list. fequals.
Qed.
Lemma map_push : forall f x v E,
  map f (E & x ~ v) = map f E & x ~ f v.
Proof. intros. rewrite map_concat, map_single. auto. Qed.

Lemma map_keys_empty : forall r,
  map_keys r (@empty A) = empty.
Proof. intros. rew_env_defs. auto. Qed.
Lemma map_keys_single : forall r x v,
  map_keys r (x ~ v) = (r x ~ v).
Proof. intros. rew_env_defs. auto. Qed.
Lemma map_keys_concat : forall r E F,
  map_keys r (E & F) = map_keys r E & map_keys r F.
Proof.
  intros. rew_env_defs.
  gen E. induction F as [|(x,v)]; intros.
  rew_list~.
  rew_list. fequals.
Qed.
Lemma map_keys_push : forall r x v E,
  map_keys r (E & x ~ v) = map_keys r E & r x ~ v.
Proof. intros. rewrite map_keys_concat, map_keys_single. auto. Qed.

Lemma get_empty : forall k,
  get k (@empty A) = None.
Proof. intros. rew_env_defs. auto. Qed.
Lemma get_single : forall k x v,
  get k (x ~ v) = If k = x 
                    then Some v 
                    else None.
Proof. intros. rew_env_defs. unfold get_impl. auto. Qed.
Lemma get_concat : forall k E F,
  get k (E & F) = match get k F with 
                  | None => get k E 
                  | Some v => Some v 
                  end.
Proof.
  intros. rew_env_defs. induction F as [|(x,v)].
  auto.
  simpl. case_if~.
Qed.

Lemma dom_empty :
  dom (@empty A) = \{}.
Proof. rew_env_defs. auto. Qed.
Lemma dom_single : forall x v,
  dom (x ~ v) = \{x}.
Proof.
  intros. rew_env_defs. 
  rew_list. rewrite~ union_empty_r. 
Qed.
Lemma dom_concat : forall E F,
  dom (E & F) = dom E \u dom F.
Proof. 
  intros. rew_env_defs. 
  gen E. induction F as [|(x,v)]; intros.
  rew_list. rewrite~ union_empty_r.
  rew_app. rewrite fold_right_cons. rewrite IHF.
   rewrite~ union_comm_assoc.
Qed.
Lemma dom_push : forall x v E,
  dom (E & x ~ v) = \{x} \u dom E.
Proof.  
  intros. rewrite dom_concat. rewrite dom_single.
  rewrite~ union_comm.
Qed.

End Properties.

Section SinglesProperties.
Variable A B : Type.
Implicit Types x : var. 
Implicit Types v : A. 
Implicit Types xs : list var.
Implicit Types vs : list A.
Implicit Types E F : env A.

Lemma singles_nil : 
  nil ~* nil = (@empty A).
Proof. intros. rew_env_defs. auto. Qed.

Lemma singles_cons : forall x v xs vs,
  (x::xs) ~* (v::vs) = (xs ~* vs) & (x ~ v).
Proof. intros. rew_env_defs. simpl. rew_env_defs. fequals. Qed.

Lemma singles_one : forall x v,
  (x::nil) ~* (v::nil) = (x ~ v).
Proof. intros. rew_env_defs. simpl. rew_env_defs. fequals. Qed.

Lemma singles_two : forall x1 x2 v1 v2,
  (x1::x2::nil) ~* (v1::v2::nil) = (x2 ~ v2 & x1 ~ v1).
Proof. intros. rew_env_defs. simpl. rew_env_defs. fequals. Qed.
 
Lemma keys_singles : forall xs vs,
  length xs = length vs ->
  keys (xs ~* vs) = xs.
Proof.
  intros. rew_env_defs. gen vs. induction xs; introv E.
  rew_list~.
  destruct vs. false. simpl. rew_env_defs. rew_list. fequals.
   rew_list in E. applys IHxs. inverts E. auto.
Qed.

Lemma values_singles : forall xs vs,
  length xs = length vs ->
  values (xs ~* vs) = vs.
Proof. 
  intros. rew_env_defs. gen vs.
  induction xs; destruct vs; introv E; tryfalse.
  auto.
  rew_list in E. simpl. rew_env_defs. rew_list. fequals.
   applys IHxs. inverts E. auto.
Qed.

Lemma dom_singles : forall xs vs,
  length xs = length vs ->
  dom (xs ~* vs) = from_list xs.
Proof. 
  intros. rew_env_defs. gen vs. 
  induction xs; destruct vs; introv E; tryfalse.
  simpl. rewrite~ from_list_nil.
  simpl. rew_env_defs. rew_list. rewrite from_list_cons. fequals.
   applys IHxs. inverts~ E.
Qed.

Lemma map_singles : forall (f : A -> B) xs vs,
  length xs = length vs ->
  map f (xs ~* vs) = xs ~* (LibList.map f vs).
Proof.
  intros. rew_env_defs. gen vs.
  induction xs; destruct vs; introv E; tryfalse.
  rew_list~.
  rew_list. simpl. rew_list. fequals~.
Qed.

Lemma map_keys_singles : forall f xs vs,
  length xs = length vs ->
  map_keys f (xs ~* vs) = (LibList.map f xs) ~* vs.
Proof.
  intros. rew_env_defs. gen vs.
  induction xs; destruct vs; introv E; tryfalse.
  rew_list~.
  rew_list. simpl. rew_list. fequals~.
Qed.

Lemma concat_singles : forall xs1 xs2 vs1 vs2,
  length xs1 = length vs1 ->
  length xs2 = length vs2 ->
  (xs2 ~* vs2) & (xs1 ~* vs1) = (xs1 ++ xs2) ~* (vs1 ++ vs2).
Proof.
  introv E1 E2. rew_env_defs. gen vs1.
  induction xs1; destruct vs1; intros; tryfalse.
  rew_list~.
  rew_list. simpl. rew_list. fequals~.
Qed.

Lemma singles_keys_values : forall E,
  E = keys E ~* values E.
Proof. 
  intros. rew_env_defs. induction E as [|[x v] E'].
  auto.
  rew_list. simpl. rew_env_defs. rew_list. fequals.
Qed.

End SinglesProperties.

(* ---------------------------------------------------------------------- *)
(** ** Structural properties *)

Section StructProperties.

Variable A : Type.
Implicit Types x : var.
Implicit Types v : A.
Implicit Types E F : env A.

Lemma env_case : forall E,
  E = empty \/ exists x v E', E = E' & x ~ v.
Proof. intros. induction E using env_ind; auto*. Qed.

Lemma concat_empty_r : forall E,
  E & empty = E.
Proof. intros. rew_env_defs. rew_app~. Qed.

Lemma concat_empty_l : forall E,
  empty & E = E.
Proof. intros. rew_env_defs. rew_app~. Qed.

Lemma concat_assoc : forall E F G,
  E & (F & G) = (E & F) & G.
Proof. intros. rew_env_defs. rew_app~. Qed.

Lemma empty_single_inv : forall x v,
  empty = x ~ v -> False.
Proof. introv H. rew_env_defs. inverts H. Qed.

Lemma empty_concat_inv : forall E F,
  empty = E & F -> empty = E /\ empty = F.
Proof. introv H. rew_env_defs. forwards*: nil_eq_app_inv H. Qed.

Lemma empty_push_inv : forall E x v,
  empty = E & x ~ v -> False.
Proof. introv H. rew_env_defs. inverts H. Qed.

Lemma empty_middle_inv : forall E F x v,
  empty = E & x ~ v & F -> False.
Proof. introv H. rew_env_defs. forwards* [_ ?]: nil_eq_app_inv H. false. Qed.

Lemma eq_single_inv : forall x1 x2 v1 v2,
  x1 ~ v1 = x2 ~ v2 ->
  x1 = x2 /\ v1 = v2.
Proof. introv H. rew_env_defs. inverts~ H. Qed.

Lemma eq_push_inv : forall x1 x2 v1 v2 E1 E2,
  E1 & x1 ~ v1 = E2 & x2 ~ v2 -> 
  x1 = x2 /\ v1 = v2 /\ E1 = E2.
Proof. introv H. rew_env_defs. inverts~ H. Qed.

End StructProperties.

(* ---------------------------------------------------------------------- *)
(** ** More properties *)

Section MoreProperties.

Variable A : Type.
Implicit Types x : var.
Implicit Types v : A.
Implicit Types E F : env A.

Lemma dom_map : forall (B:Type) (f:A->B) E,
  dom (map f E) = dom E.
Proof.
  induction E using env_ind.
  rewrite map_empty. do 2 rewrite dom_empty. auto.
  rewrite map_concat. rewrite map_single. 
  rewrite_all dom_concat. rewrite_all dom_single. congruence.
Qed.

Lemma concat_assoc_map_push : forall f E F x v,
  E & (map f (F & x ~ v)) = (E & map f F) & x ~ (f v).
Proof.
  intros. rewrite map_concat. rewrite map_single.
  rewrite~ concat_assoc.
Qed.

Lemma get_push : forall k x v E,
  get k (E & x ~ v) = 
    If k = x 
      then Some v 
      else get k E.
Proof.
  intros. rewrite get_concat. rewrite get_single. case_if~.
Qed.

Ltac simpl_dom :=
  rewrite_all dom_push in *;  
  rewrite_all dom_empty in *.

Lemma get_some : forall x E,
  x \in dom E -> exists v, get x E = Some v. 
(* i.e.  [x \in dom E -> exists v, binds x v E] *)
Proof. (* beautify *)
  unfold binds.
  introv H. rew_env_defs. induction E as [|[y v] E'].
  rew_list in H. rewrite* in_empty in H.
  unfold get_impl. case_if.
    eauto.
    rew_list in H. rewrite in_union in H. destruct H as [H|H].
     rewrite in_singleton in H. simpls. false.
     forwards* [v' ?]: IHE'.
Qed.

Lemma get_some_inv : forall x v E,
  get x E = Some v -> x \in dom E. 
(* i.e.  [binds x v E -> x \in dom E] *)
Proof. (* beautify *)
  unfold binds.
  introv H. rew_env_defs. unfolds get_impl. induction E as [|[y v'] E'].
  false.
  rew_list. rewrite in_union. simpl. case_if.
    inverts H. subst. left. rewrite~ in_singleton.
    forwards*: IHE'.
Qed.

Lemma get_none : forall x E,
  x # E -> get x E = None. 
Proof. 
  induction E using env_ind; introv In.
  rewrite~ get_empty.
  rewrite~ get_push. case_if.
    simpl_dom. subst. notin_false. 
    simpl_dom. auto.
Qed.

Lemma get_none_inv : forall x E,
  get x E = None -> x # E. 
Proof.
  induction E using env_ind; introv Eq.
  simpl_dom. auto.
  rewrite get_push in Eq. case_if~.
   simpl_dom. auto.
Qed.

End MoreProperties.

Lemma binds_get_or_arbitrary : forall `{Inhab A} x v (E:env A), 
  binds x v E -> get_or_arbitrary x E = v.
Proof. introv M. unfold get_or_arbitrary. rewrite~ M. Qed.

Definition indom_dec A (E:env A) x :=
  match get x E with None => false | Some _ => true end.
 
Global Instance indom_decidable : forall A (E:env A) x,
  Decidable (x \in dom E).
Proof.
  intros. applys decidable_make (indom_dec E x).
  unfold indom_dec. cases (get x E) as C.
    lets: (get_some_inv C). rewrite~ isTrue_true.
    lets: (get_none_inv C). rewrite~ isTrue_false.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Hints and rewriting tactics *)

Hint Constructors ok.

Hint Rewrite dom_empty dom_single dom_concat : rew_env_dom.
Hint Rewrite map_empty map_single map_concat : rew_env_map.
Hint Rewrite map_keys_empty map_keys_single 
 map_keys_concat : rew_env_map_keys.
Hint Rewrite get_empty get_single get_concat : rew_evn_get.

Hint Rewrite concat_empty_r concat_empty_l concat_assoc : rew_env_concat.

Tactic Notation "rew_env_concat" := 
  autorewrite with rew_env_concat.
Tactic Notation "rew_env_concat" "in" hyp(H) := 
  autorewrite with rew_env_concat in H.
Tactic Notation "rew_env_concat" "in" "*" := 
  autorewrite with rew_env_concat in *.

Ltac simpl_dom :=
  rewrite_all dom_map in *;
  rewrite_all dom_push in *;  
  rewrite_all dom_concat in *;  
  rewrite_all dom_single in *;
  rewrite_all dom_empty in *.

Hint Extern 1 (_ # _) => simpl_dom; notin_solve.

(* ---------------------------------------------------------------------- *)
(** ** Properties of well-formedness and freshness *)

Section OkProperties.

Variable A B : Type.
Implicit Types k x : var.
Implicit Types v : A.
Implicit Types E F : env A.

Lemma ok_push_inv : forall E x v,
  ok (E & x ~ v) -> ok E /\ x # E.
Proof.
  intros. inverts H as H1 H2.
  false (empty_push_inv H1).
  destructs 3 (eq_push_inv H). subst~.
Qed.

Lemma ok_push_inv_ok : forall E x v,
  ok (E & x ~ v) -> ok E.
Proof. introv H. destruct* (ok_push_inv H). Qed.

Lemma ok_concat_inv : forall E F,
  ok (E & F) -> ok E /\ ok F.
Proof.
  induction F using env_ind; rew_env_concat; introv Ok. auto.
  destruct (ok_push_inv Ok). destruct~ IHF.
Qed.

Lemma ok_concat_inv_l : forall E F,
  ok (E & F) -> ok E.
Proof. introv H. lets*: ok_concat_inv H. Qed.

Lemma ok_concat_inv_r : forall E F,
  ok (E & F) -> ok F.
Proof. introv H. lets*: ok_concat_inv H. Qed.

Lemma ok_middle_change : forall E F x v1 v2,
  ok (E & x ~ v1 & F) -> ok (E & x ~ v2 & F).
Proof.
  induction F using env_ind; introv; rew_env_concat; introv Ok.
  destruct* (ok_push_inv Ok).
  destruct* (ok_push_inv Ok).
Qed.

Lemma ok_middle_inv : forall E F x v,
  ok (E & x ~ v & F) -> x # E /\ x # F.
Proof.
  induction F using env_ind; introv; rew_env_concat; intros Ok;
   destruct (ok_push_inv Ok).
  split~.
  forwards~ [? ?]: IHF H.
Qed.

Lemma ok_middle_inv_l : forall E F x v,
  ok (E & x ~ v & F) -> x # E.
Proof. introv H. forwards~ [? _]: ok_middle_inv H. Qed. 

Lemma ok_middle_inv_r : forall E F x v,
  ok (E & x ~ v & F) -> x # F.
Proof. introv H. forwards~ [_ ?]: ok_middle_inv H. Qed. 
 
Lemma ok_remove : forall F E G,
  ok (E & F & G) -> ok (E & G).
Proof.
  induction G using env_ind; rew_env_concat; introv Ok.
  lets*: ok_concat_inv Ok.
  lets*: ok_push_inv Ok.
Qed.

Lemma ok_map : forall E (f : A -> B),
  ok E -> ok (map f E).
Proof. 
  induction E using env_ind; introv;
   autorewrite with rew_env_map; rew_env_concat; intros Ok.
  auto. destruct* (ok_push_inv Ok).
Qed.

Lemma ok_concat_map: forall E F (f : A -> A),
  ok (E & F) -> ok (E & map f F).
Proof.
  induction F using env_ind; introv;
   autorewrite with rew_env_map; rew_env_concat; intros Ok.
  auto. destruct* (ok_push_inv Ok).
Qed.

Lemma ok_singles : forall n E xs (vs:list A),
  fresh (dom E) n xs ->
  length xs = length vs ->
  ok E ->
  ok (E & xs ~* vs).
Proof.
  introv F EQ O. gen E n vs.
  induction xs; destruct vs; destruct n; intros; tryfalse.
  rewrite singles_nil. rewrite~ concat_empty_r.
  rew_length in EQ. inverts EQ.
   simpl in F. destruct F as [Fr F']. lets [? M]: (fresh_union_r F').
   rewrite singles_cons. rewrite concat_assoc. applys ok_push.
     applys~ IHxs n.
     simpl_dom. rewrite~ dom_singles. lets~: fresh_single_notin M.
Qed.

(* LATER: not used
Lemma singles_ok : forall xs vs E, 
  ok E ->
  fresh (dom E) (length xs) xs -> 
  ok (E & xs ~* vs).
Proof. ...
  induction xs; simpl; intros. auto.
  destruct H0. destruct Us; simpls. auto.
  rewrite iter_push_cons. rewrite* <- concat_assoc.
*)

(* LATER: not used;
   missing a precondition unless nil~*vs returns nil 
Lemma ok_concat_singles : forall n xs vs E,
  ok E ->
  fresh (dom E) n xs ->
  ok (E & xs ~* vs).
Proof.
  intros. rew_env_defs. gen vs n E.
  induction xs; introv Ok Fr; destruct n; tryfalse.
  auto.
  destruct vs. simpl.
  rew_list in Fr. destruct Fr as [F Fr'].
  applys_to Fr notin_union_r...
Qed.
*)

(* LATER: not used 
  Lemma ok_concat : forall E F,
    ok E -> ok F -> disjoint (dom E) (dom F) ->
    ok (E & F).
*)

End OkProperties.

Implicit Arguments ok_push_inv [A E x v].
Implicit Arguments ok_concat_inv [A E F].
Implicit Arguments ok_remove [A F E G].
Implicit Arguments ok_map [A E f].
Implicit Arguments ok_middle_inv_l [A E F x v].
Implicit Arguments ok_middle_inv_r [A E F x v].
Implicit Arguments ok_middle_inv [A E F x v].


(** Automation *)

Hint Resolve ok_middle_inv_l ok_map ok_concat_map ok_singles.

Hint Extern 1 (ok (?E & ?G)) =>
  match goal with H: ok (E & ?F & G) |- _ =>
    apply (ok_remove H) end.

Hint Extern 1 (ok (?E)) =>
  match goal with H: ok (E & _ ~ _) |- _ =>
    apply (ok_push_inv_ok H) end.

Hint Extern 1 (ok (?E)) =>
  match goal with H: ok (E & _) |- _ =>
    apply (ok_concat_inv_l H) end.

Hint Extern 1 (ok (?E)) =>
  match goal with H: ok (_ & E) |- _ =>
    apply (ok_concat_inv_r H) end.

(* not used 
Hint Extern 1 (ok (_ & ?xs ~* ?vs)) =>
  match goal with H: fresh _ ?n xs |- _ =>
  match type of vs with list ?A =>
    apply (@ok_concat_singles A n)
  end end.
*)


(* ---------------------------------------------------------------------- *)
(** ** Properties of the binds relation *)

Section BindsProperties.
Variable A B : Type.
Implicit Types E F : env A.
Implicit Types x : var.
Implicit Types v : A.

Lemma binds_get : forall x v E,
  binds x v E -> get x E = Some v.
Proof. auto. Qed.

(** Constructor forms *)

Lemma binds_empty_inv : forall x v,
  binds x v empty -> False.
Proof. 
  unfold binds. introv H. rewrite get_empty in H. false. 
Qed.

Lemma binds_single_eq : forall x v,
  binds x v (x ~ v).
Proof.
  intros. unfold binds. rewrite get_single. case_if~. 
Qed.

Lemma binds_single_inv : forall x1 x2 v1 v2,
  binds x1 v1 (x2 ~ v2) ->
  x1 = x2 /\ v1 = v2.
Proof.
  unfold binds. introv H. rewrite get_single in H.
  case_if; inversions~ H. 
Qed.

Lemma binds_push_inv : forall x1 v1 x2 v2 E,
  binds x1 v1 (E & x2 ~ v2) ->
     (x1 = x2 /\ v1 = v2)
  \/ (x1 <> x2 /\ binds x1 v1 E).
Proof.  
  introv H. unfolds binds. rewrite get_push in H. case_if.
  inverts~ H. auto.
Qed.

Lemma binds_push_eq : forall x v E,
  binds x v (E & x ~ v).
Proof. intros. unfolds binds. rewrite get_push. case_if~. Qed.

Lemma binds_push_eq_inv : forall x v1 v2 E,
  binds x v1 (E & x ~ v2) -> v1 = v2.
Proof.
  introv H. forwards [|]: binds_push_inv H. auto*. intros [? _]. false.
Qed.

Lemma binds_push_neq_inv : forall x1 x2 v1 v2 E,
  binds x1 v1 (E & x2 ~ v2) -> x1 <> x2 -> binds x1 v1 E.
Proof.
  introv H. forwards [|]: binds_push_inv H.
  intros [? ?] ?. false. auto*.
Qed.

Lemma binds_tail : forall x v E,
  binds x v (E & x ~ v).
Proof. intros. unfold binds. rewrite get_push. cases_if~. Qed.

Lemma binds_push_neq : forall x1 x2 v1 v2 E,
  binds x1 v1 E -> x1 <> x2 -> binds x1 v1 (E & x2 ~ v2).
Proof. 
  introv H N. unfolds binds. rewrite get_push. case_if~. 
Qed.

Lemma binds_concat_inv : forall x v E1 E2,
  binds x v (E1 & E2) ->
     (binds x v E2)
  \/ (x # E2 /\ binds x v E1).
Proof. 
  introv H. induction E2 using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H. 
   forwards [[? ?]|[? M]]: binds_push_inv H.
     subst. left. apply binds_tail.
     forwards [?|[? ?]]: IHE2 M.
       left. applys~ binds_push_neq.
       right~.
Qed.

Lemma binds_map : forall x v (f : A -> B) E,
  binds x v E -> binds x (f v) (map f E).
Proof. 
  introv H. unfolds binds. rew_env_defs.
  induction E as [|[x' v'] E']; simpls. 
  false.
  cases_if~. inverts~ H. 
Qed.

(** Basic forms *)

Lemma binds_func : forall x v1 v2 E,
  binds x v1 E -> binds x v2 E -> v1 = v2.
Proof.
  introv H1 H2. unfolds binds. 
  induction E as [|E' x' v'] using env_ind. 
  rewrite get_empty in H1. false.
  rewrite get_push in H1,H2. case_if~.
   inverts H1. inverts~ H2.
Qed.

Lemma binds_fresh_inv : forall x v E,
  binds x v E -> x # E -> False.
Proof.
  introv H F. unfolds binds. 
  induction E as [|E' x' v'] using env_ind.
  rewrite get_empty in H. false.
  rewrite get_push in H. case_if~. subst.
   simpl_dom; notin_false.
Qed.

(** Derived forms *)

Lemma binds_single_eq_inv : forall x v1 v2,
  binds x v1 (x ~ v2) ->
  v1 = v2.
Proof.
  introv H. unfolds binds. rewrite get_single in H.
  case_if. inverts~ H.
Qed.

Lemma binds_concat_left : forall x v E1 E2,
  binds x v E1 ->
  x # E2 ->
  binds x v (E1 & E2).
Proof. 
  introv H F. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc. applys~ binds_push_neq.
   simpl_dom. auto.
Qed.

Lemma binds_concat_left_ok : forall x v E1 E2,
  ok (E1 & E2) ->
  binds x v E1 ->
  binds x v (E1 & E2).
Proof. 
  introv O H. induction E2 using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc in O|-*. lets [_ ?]: ok_push_inv O.
  applys~ binds_push_neq. intro_subst. applys~ binds_fresh_inv H. 
Qed.

Lemma binds_concat_left_inv : forall x v E1 E2,
  binds x v (E1 & E2) ->
  x # E2 ->
  binds x v E1.
Proof. 
  introv H F. lets~ [M|[? ?]]: binds_concat_inv H.
    false. applys~ binds_fresh_inv M.
Qed.

Lemma binds_concat_right : forall x v E1 E2,
  binds x v E2 ->
  binds x v (E1 & E2).
Proof.
  introv H. induction E2 using env_ind.
  false. applys* binds_empty_inv.
  rewrite concat_assoc. lets [[? ?]|[? ?]]: binds_push_inv H.
    subst. applys binds_tail.
    applys~ binds_push_neq.
Qed.

Lemma binds_concat_right_inv : forall x v E1 E2,
  binds x v (E1 & E2) ->
  x # E1 ->
  binds x v E2.
Proof.
  introv H F. lets~ [?|[? M]]: binds_concat_inv H.
    false. applys~ binds_fresh_inv M.
Qed.

Lemma binds_middle_eq : forall x E1 E2 v,
  x # E2 ->
  binds x v (E1 & x ~ v & E2).
Proof. 
  introv F. applys~ binds_concat_left. applys binds_tail.
Qed.

(** Metatheory proof forms *)

(** Interaction between binds and the insertion of bindings.
  In theory we don't need this lemma since it would suffice
  to use the binds_cases tactics, but since weakening is a
  very common operation we provide a lemma for it. *)

Lemma binds_weaken : forall x a E F G,
  binds x a (E & G) -> ok (E & F & G) ->
  binds x a (E & F & G).
Proof.
  introv H O. lets [?|[? ?]]: binds_concat_inv H.
    applys~ binds_concat_right.
    applys~ binds_concat_left. applys~ binds_concat_left_ok.
Qed.

Lemma binds_remove : forall E2 E1 E3 x v,
  binds x v (E1 & E2 & E3) ->
  x # E2 ->
  binds x v (E1 & E3).
Proof. 
  introv H F. lets [?|[? M]]: binds_concat_inv H.
    applys~ binds_concat_right.
    forwards~: binds_concat_left_inv M. applys~ binds_concat_left.
Qed.

Lemma binds_subst : forall x2 v2 x1 v1 E1 E2,
  binds x1 v1 (E1 & x2 ~ v2 & E2) ->
  x1 <> x2 ->
  binds x1 v1 (E1 & E2).
Proof. introv H N. applys~ binds_remove H. Qed.

Lemma binds_middle_eq_inv : forall x E1 E2 v1 v2,
  binds x v1 (E1 & x ~ v2 & E2) ->
  ok (E1 & x ~ v2 & E2) ->
  v1 = v2.
Proof. 
  introv H O. lets [? ?]: ok_middle_inv O.
  forwards~ M: binds_concat_left_inv H.
  applys~ binds_push_eq_inv M.
Qed.

Lemma binds_middle_inv : forall x1 v1 x2 v2 E1 E2,
  binds x1 v1 (E1 & x2 ~ v2 & E2) -> 
     (binds x1 v1 E2)
  \/ (x1 # E2 /\ x1 = x2 /\ v1 = v2)
  \/ (x1 # E2 /\ x1 <> x2 /\ binds x1 v1 E1).
Proof. 
  introv H. lets [?|[? M]]: (binds_concat_inv H).
    left~.
    right. lets [N|[? N]]: (binds_concat_inv M).
      lets [? ?]: (binds_single_inv N). subst~.
      right. simpl_dom. split~.
Qed.

Lemma binds_not_middle_inv : forall x v E1 E2 E3,
  binds x v (E1 & E2 & E3) -> 
  x # E2 ->
     (binds x v E3)
  \/ (x # E3 /\ binds x v E1).
Proof.
  introv H F. lets [?|[? M]]: (binds_concat_inv H).
    left~.
    right. forwards~ N: (binds_concat_left_inv M).
Qed.

Lemma fv_in_values_binds : forall y fv x v E,
  binds x v E -> y \notin fv_in_values fv E -> y \notin fv v.
Proof.
  unfold fv_in_values. introv H. 
  induction E using env_ind; introv M.
  false. applys* binds_empty_inv.
  rewrite values_def in M,IHE.
  rewrite concat_def, single_def in M. rew_list in M. simpl in M.
  lets [[? ?]|[? ?]]: (binds_push_inv H); subst~.
Qed.

(* unused -- requires a precondition on f 
Lemma binds_keys : forall x v f E,
  binds x v E -> binds (f x) v (map_keys f E).
Proof. 
Qed.
*)

(* unused 
Lemma binds_concat_inv_ok : forall x v E1 E2,
  ok (E1 & E2) ->
  binds x v (E1 & E2) ->
     (x # E2 /\ binds x v E1)
  \/ (x # E1 /\ binds x v E2).
Proof. 
  introv O H. induction E2 using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in O,H. 
   forwards [[? ?]|[? M]]: binds_push_inv H.
     subst. left. apply conj_dup_r.
     split.
       apply binds_tail.
     forwards [?|[? ?]]: IHE2 M.
       left. applys~ binds_push_neq.
       right~....
Qed.
*)

End BindsProperties.

(* ---------------------------------------------------------------------- *)
(** ** Tactics *)

Hint Resolve binds_push_eq binds_push_neq
  binds_map binds_concat_left binds_concat_right.

Tactic Notation "binds_mid" :=
  match goal with H: binds ?x ?v1 (_ & ?x ~ ?v2 & _) |- _ =>
    asserts: (v1 = v2); [ apply (binds_middle_eq_inv H) | subst; clear H ] 
  end.
Tactic Notation "binds_mid" "~" :=
  binds_mid; auto_tilde.
Tactic Notation "binds_mid" "*" :=
  binds_mid; auto_star.

Tactic Notation "binds_push" constr(H) :=
  match type of H with binds ?x1 ?v1 (_ & ?x2 ~ ?v2) =>
    destruct (binds_push_inv H) as [[? ?]|[? ?]]; [ subst x2 v2 | ] 
  end.
Tactic Notation "binds_push" "~" constr(H) :=
  binds_push H; auto_tilde.
Tactic Notation "binds_push" "*" constr(H) :=
  binds_push H; auto_star.

(* ---------------------------------------------------------------------- *)
(** ** Properties of environment inclusion *)

Section ExtendsProperties.
Variable A : Type.
Implicit Types x : var.
Implicit Types v : A.
Implicit Types E F : env A.

Lemma extends_refl : forall E,
  extends E E.
Proof. intros_all~. Qed.

Lemma extends_push : forall E x v, 
  x # E -> extends E (E & x ~ v).
Proof.
  introv Fr. intros x' v' B. unfolds binds.
  rewrite get_push. case_if~.
  lets: get_none Fr. false.
Qed.

Lemma extends_concat_l : forall E F,
  extends F (E & F).
Proof.
  introv B. unfolds binds. 
  rewrite get_concat. rewrite~ B.
Qed.

Lemma extends_concat_r : forall E F,
  disjoint (dom E) (dom F) ->
  extends E (E & F).
Proof.
  introv D B. unfolds binds. 
  lets: get_some_inv A B. 
  forwards M: get_none A x F.
    applys~ disjoint_in_notin D.
  rewrite get_concat. rewrite~ M. 
Qed.

(* not used
Lemma extends_push_reoccur : forall E x v,
  binds x v E -> extends E (E & x ~ v).
*)

End ExtendsProperties.

Hint Resolve extends_refl extends_push.


(* ********************************************************************** *)
(** ** Tactics for case analysis on binding relations *)

(** [binds_get H as EQ] produces from an hypothesis [H] of
  the form [binds x a (E & x ~ b & F)] the equality [EQ: a = b]. *)

Ltac binds_get_nosubst_base H EQ :=
  match type of H with
  | binds ?x ?v1 (?E1 & ?x ~ ?v2 & ?E2) =>
    forwards EQ: (@binds_middle_eq_inv _ x E1 E2 v1 v2 H); [ auto | ] 
  (* | binds ?x1 ?v1 (?E1 & ?x2 ~ ?v2 & ?E2) =>
     forwards EQ: (@binds_middle_inv _ x1 v1 x2 v2 E1 E2); [ | auto ] *)
  end.

Tactic Notation "binds_get_nosubst" constr(H) "as" ident(EQ) :=
  binds_get_nosubst_base H EQ.
Tactic Notation "binds_get_nosubst" constr(H) :=
  let EQ := fresh "EQ" in binds_get_nosubst H as EQ.

(** [binds_get H] expects an hypothesis [H] of the form 
  [binds x a (E & x ~ b & F)] and substitute [a] for [b] in the goal. *)

Ltac binds_get H :=
  let EQ := fresh in binds_get_nosubst H as EQ;
  try match type of EQ with 
  | ?f _ = ?f _ => inversions EQ
  | ?x = ?y => subst x end.

(** [binds_single H] derives from an hypothesis [H] of the form 
  [binds x a (y ~ b)] the equalities [x = y] and [a = b], then
  it substitutes [x] for [y] in the goal or deduce a contradiction
  if [x <> y] can be found in the context. *)

Ltac binds_single H :=
  match type of H with binds ?x ?a (?y ~ ?b) =>
    let EQ := fresh "EQ" in
    destruct (binds_single_inv H) as [? EQ]; 
    try discriminate; try subst y; 
    try match goal with N: ?x <> ?x |- _ =>
      false; apply N; reflexivity end end.

(** [binds_case H as B1 B2] derives from an hypothesis [H] of the form 
  [binds x a (E & F)] two subcases: [B1: binds x a E] (with a freshness
  condition [x # F]) and [B2: binds x a F]. *)

Lemma binds_concat_inv' : forall A, forall x (v:A) E1 E2,
  binds x v (E1 & E2) ->
     (x # E2 /\ binds x v E1)
  \/ (binds x v E2).
Proof. intros. forwards K: binds_concat_inv A H. destruct* K. Qed.

Tactic Notation "binds_case" constr(H) "as" ident(B1) ident(B2) :=
   let Fr := fresh "Fr" in 
   destruct (binds_concat_inv' H) as [[Fr B1] | B2].

(** [binds_case H] makes a case analysis on an hypothesis [H] of the form 
  [binds x a E] where E can be constructed using concatenation and
  singletons. It calls [binds_single] when reaching a singleton. *)

Ltac binds_cases H :=
  let go B := clear H; 
    first [ binds_single B | binds_cases B | idtac ] in
  let B1 := fresh "B" in let B2 := fresh "B" in
  binds_case H as B1 B2; (*fix_env;*) [ go B1 | go B2 ].
  (* TODO: add support for binds_empty_inv *)

(* LATER: improve the above tactic using pattern matching
Ltac binds_cases_base H :=
  match H with
  | binds _ _ empty => false (binds_empty_inv H)
  | binds _ _ (_ & _) => 
     let H1 := fresh "B" in 
     destruct (binds_concat_inv H) as [H1|H1];
     clear H; binds_cases_base H1
  | binds _ _ (_ ~ _) =>
  | _ => idtac
  end.
*)



