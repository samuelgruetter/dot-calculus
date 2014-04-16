(**************************************************************************
* TLC: A library for Coq                                                  *
* Fixed-point combinator                                                  *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect LibEpsilon LibInt
  LibProd LibSum LibOperation LibRelation LibWf LibOrder.


(* ********************************************************************** *)
(** * Generalities *)

(* ---------------------------------------------------------------------- *)
(** ** Setting up of automation for the file *)

Ltac destruct_if_post ::= tryfalse~.

Hint Unfold pred_le pred_and.
Hint Unfold large empty.
Hint Resolve empty_wf.
Hint Resolve equiv_refl equiv_sym equiv_trans.

Ltac auto_tilde ::= 
  try solve [ auto | eauto | intros_all; subst_local; simpls; eauto ].

(* ---------------------------------------------------------------------- *)
(** ** Post-conditions for functions *)

Definition post_true {A B:Type} : A -> B -> Prop :=
  fun _ _ => True.

Definition post_false {A B:Type} : A -> B -> Prop :=
  fun _ _ => False.

Hint Unfold post_true post_false.

(* ---------------------------------------------------------------------- *)
(** ** Unique values satisfying a property upto equivalence *)

Definition unique_upto_st A (E:binary A) (P : A -> Prop) (x : A) :=
  P x /\ forall y, P y -> E y x.

(* ---------------------------------------------------------------------- *)
(** ** Facts about ordered sets *)

Definition lower_bound A (le:binary A) (E:A->Prop) (x:A) :=
  forall x', E x' -> le x x'.

Definition upper_bound A (le:binary A) (E:A->Prop) (x:A) :=
  forall x', E x' -> le x' x.

Definition smallest A (le:binary A) (E:A->Prop) (x:A) :=
  E x /\ lower_bound le E x. 

Definition greatest A (le:binary A) (E:A->Prop) (x:A) :=
  E x /\ upper_bound le E x.

Definition lub A (le:binary A) (E:A->Prop) (x:A) :=
  smallest le (upper_bound le E) x.

Definition glb A (le:binary A) (E:A->Prop) (x:A) :=
  smallest le (lower_bound le E) x.


(* ---------------------------------------------------------------------- *)
(** ** Properties of functions defined only on a domain *)

(** Two functions defined on a same domain [P] are equivalent 
    iff they are extensionally equivalent on their domain. *)

Definition pfunc_equiv A B (E:B->B->Prop) (P:A->Prop) (f f':A->B) := 
  forall x, P x -> E (f x) (f' x). 

Hint Unfold pfunc_equiv.

(** Same, but specialized to Leibnitz' equality *)

Definition pfunc_equal A B (P:A->Prop) (f f':A->B) := 
  pfunc_equiv (@eq B) P f f'.

Hint Unfold pfunc_equal.

(** [pfunc_equiv] is an equivalence relation. *)

Lemma pfunc_equiv_equiv : forall A B (E:binary B) (P:A->Prop),
  equiv E -> equiv (@pfunc_equiv A B E P).
Proof.
  introv [RE SE TE]. unfold pfunc_equiv. constructor; intros_all*.
Qed.

Hint Resolve pfunc_equiv_equiv. 


(* ---------------------------------------------------------------------- *)
(** ** Representation of partial functions *)

(** A partial function [f], of type [A-->B], consists of a pair of
    a total function [f], of type [A->B], and of a domain, of type
    [A -> Prop]. *)

Record partial (A B : Type) : Type := 
  { support :> A -> B;
    dom : A -> Prop }.

Notation "A --> B" := (partial A B) (right associativity, at level 55).

(** The type of partial functions is inhabited as soon as the
    return type is inhabited. *)

Instance partial_inhab : forall A B {I:Inhab B}, Inhab (A-->B). 
Proof. intros. apply (prove_Inhab (Build_partial arbitrary (fun _ => True))). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of partial functions *)

(** Two partial functions [f] and [f'] are equivalent
    modulo [E] iff they have the same domain and are
    equivalent modulo [E] on their domain. *)

Definition partial_equiv A B (E:binary B) (f f': A-->B) :=
  (dom f) = (dom f') /\ pfunc_equiv E (dom f) f f'.

(** [partial_equiv] is an equivalence relation. *)

Lemma partial_equiv_equiv : forall A B (E:binary B),
  equiv E -> equiv (@partial_equiv A B E).
Proof. 
  introv Equi. unfold partial_equiv. constructor.
  intros_all. split*.
  introv [D H]. rewrite D in *. splits*. 
  introv [D1 H1] [D2 H2]. rewrite D1,D2 in *. splits*. 
Qed.

(** A partial function [f'] defined on a domain [D'] 
    extends a partial function [f] defined on a domain [D]
    iff [D] is included in [D'] and if [f] and [f'] yield
    equivalent results on the domain [D]. *)

Definition extends A B (E:binary B) (f f': A-->B) :=
  pred_le (dom f) (dom f') /\ pfunc_equiv E (dom f) f f'.

(** [extends] is an order relation on the set of partial 
    fixed points (antisymmetry is modulo equiv). *)

Lemma extends_order : forall A B (E:binary B),
  equiv E -> order_wrt (partial_equiv E) (@extends A B E).
Proof.
  unfold extends. constructor.
   intros_all. split*. 
   introv [D1 H1] [D2 H2]. split~. unfolds* pfunc_equiv.
   introv [D1 H1] [D2 H2]. split~. apply* prop_ext_1.
Qed.

(** Two partial functions [f] and [f'] are consistent if
    they produce equivalent results on the intersection of
    their domains. *)

Definition consistent A B (E:binary B) (f f': A-->B) :=
  pfunc_equiv E (pred_and (dom f) (dom f')) f f'.


(* ---------------------------------------------------------------------- *)
(** ** Definition of fixed points and unique fixed points *)

(** A value [x] is a fixed point for a functional [F] modulo an
    equiv relation [E] iff [x] is equivalent to [F x], and
    moreover a similar equiv applies for any value [y] related
    to [x] modulo [E]. *)

Definition fixed_point A (E:binary A) (F:A->A) (x:A) :=
  forall y, E x y -> E y (F y).

(** An alternative equivalent definition of unique fixed point *)

Definition unique_fixed_point A (E:binary A) (F:A->A) :=
  unique_upto_st E (fixed_point E F).


(* ---------------------------------------------------------------------- *)
(** ** Representation of partial fixed points *)

(** In this section, we give two equivalent definitions of:
    "the partial function [f] of type [A-->B] is a fixed point
     of the functional [F] of type [(A->B)->(A->B)]". The first
     definition is stated in terms of the general definition
     [fixed_point], and the second one is stated directly as
     an equivalence between [f] and [F f] on the domain of [f]. *)

(** Given a functional [F] of type [(A->B)->(A->B)], we can define
    its counterpart as a combinator of partial functions, i.e. at 
    type [(A-->B)->(A-->B)]. When given a partial function [f] of type [A-->B]
    defined on a domain [P], we return the function [F f] restricted to
    the domain [P]. *)

Definition partialize A B (F:(A->B)->(A->B)) : (A-->B)->(A-->B) :=
  fun fp => let (f,P) := fp in Build_partial (F f) P.

(** We say that a partial function is a fixed point of a functional [F] 
    iff it is a fixed point for the functional [partialize F],
    with respect to the equiv relation between partial functions. *)

Definition partial_fixed_point' 
  A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B)
  := fixed_point (partial_equiv E) (partialize F) f.

(** An equivalent definition of a partial fixed point is the following:
    The partial function [f] is a fixed point of [F] modulo [E] iff
    for any partial function [f'] equal to [f] on the domain of [f], 
    [f'] is equivalent to [F f'] on the domain of [f]. *)

Definition partial_fixed_point 
  A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B) :=  
  forall (f':A-->B), pfunc_equiv E (dom f) f f' -> 
                     pfunc_equiv E (dom f) f' (F f').

(** Let us prove formally the equiv between the two definitions. 
    (Note: it is also possible to state the lemma in a way that does
     not require the subsequent use of propositional extensionality. *)

Lemma partial_fixed_point_definitions : 
  partial_fixed_point = partial_fixed_point'.
Proof. 
  applys prop_ext_5. intros A B E F f. 
  unfold partial_fixed_point, partial_fixed_point'. 
  destruct f as [f P]. simpl. iff H.
    intros [f' P'] [Eff' Pff']. simpls. subst.
     hnf. simpl. splits~. applys (H (Build_partial f' P') Pff').
    intros [f' P'] Eff'. simpls. forwards H1 H2: (H (Build_partial f' P)).
     hnf. simpl. splits~. apply H2.
Qed.

(** A lemma to exploit the property of being a partial fixed point *)

Lemma partial_fixed_point_elim : forall A B (P:A->Prop) F (f:A->B) (E:binary B),
  partial_fixed_point E F (Build_partial f P) ->
  fixed_point (pfunc_equiv E P) F f.
Proof. introv Fixf. intros f' Hff'. apply~ (Fixf (Build_partial f' P)). Qed.


(* *************************************************************** *)
(** * Theory of optimal fixed points *)

(* ---------------------------------------------------------------------- *)
(** ** Least-upper bound of a consistent set of fixed points *)

(** A consistent set of partial functions [S] is a set whose
    elements are pairwise consistent. *)

Definition consistent_set A B (E:binary B) (S:(A-->B)->Prop) :=
  forall f f', S f -> S f' -> consistent E f f'.

(** The following results shows that any consistent set of 
    partial fixed points admits a least upper bound with respect
    to the relation extends, and establishes that this upper bound
    is itself a partial fixed point. *)

Lemma lub_of_consistent_set : 
  forall A B {I:Inhab B} (E:binary B) (F:(A->B)->(A->B)) (S:(A-->B)->Prop),
  equiv E ->
  consistent_set E S -> 
  (forall fi, S fi -> partial_fixed_point E F fi) ->
  exists (f:A-->B), lub (extends E) S f /\ partial_fixed_point E F f.
Proof.
  introv I Equiv Cons Fixi.
  (* construct a function f *) 
  sets covers: (fun (x:A) (fi:A-->B) => S fi /\ (dom fi) x).
  sets D: (fun x => exists fi, covers x fi). 
  sets f: (fun x => if classicT (D x) then epsilon (covers x) x else arbitrary).
  exists (Build_partial f D). split. split.
  (* proof that f is an upper bound *)
  intros f' Sf'. split; simpl.
  intros x Dx. exists~ f'.
  intros x D'x. unfold f. destruct_if as Dx.
  spec_epsilon~ f' as fi [Si Domi]. apply~ Cons. 
  (* proof that f is the smallest upper bound *)
  intros f' Upper'. split; simpl.
  intros x (fi&Ci&Di). apply~ (Upper' fi Ci).
  intros x Dx. unfold f. destruct_if.
   spec_epsilon~ as fi [Si Domi]. apply~ (Upper' fi).
  (* proof that f is a fixed point *) 
  intros f' Eq'. simpls. intros x Dx. lets (fi&Ci&Di): Dx. 
  apply~ (Fixi _ Ci). intros y Diy. asserts~ Dy: (D y).
  apply~ (trans_elim (f y)). unfold f. destruct_if. 
  spec_epsilon~ as fj [Sj Domj]. apply~ Cons.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Existence of the optimal fixed point *)

(** A function [f] is a generally-consistent partial fixed point iff it 
   is a partial fixed point and it is consistent with all other partial
   fixed points. *)

Definition generally_consistent_partial_fixed_point
  A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B) :=
     partial_fixed_point E F f 
  /\ forall f', partial_fixed_point E F f' -> consistent E f f'. 

(** The optimal fixed point of a functional [F] is a function which
    is the greatest element of the set of generally-consistent partial
    fixed point. *)

Definition optimal_fixed_point A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B) :=
  greatest (extends E) (generally_consistent_partial_fixed_point E F) f.

(** The optimal fixed point, if it exists, is unique (up to equiv). *)

Lemma optimal_fixed_point_unique : forall A B (E:binary B) (F:(A->B)->(A->B)),
  equiv E -> at_most_one_upto (partial_equiv E) (optimal_fixed_point E F).
Proof.
  introv Equi [Fix1 Ge1] [Fix2 Ge2]. 
  apply~ (order_wrt_antisym (extends_order A Equi)).
Qed.

(** The following proofs shows that there exists an optimal fixed point. *)

Lemma optimal_fixed_point_exists : 
  forall A B {I:Inhab B} (E:binary B) (F:(A->B)->(A->B)),
  equiv E -> exists (f:A-->B), optimal_fixed_point E F f. 
Proof.
  introv I Equiv.
  (* there exists an optimal fixed point [f] *)
  sets S: (generally_consistent_partial_fixed_point E F).
  forwards~ (f&[Upf Lubf]&Fixf): (@lub_of_consistent_set _ _ _ E F S).
    intros f f' [Pf Cf] [Pf' Cf']. auto.
    intros f [Pf Cf]. auto.
  exists f. split~. split~.
  (* and it is generally consistent *)
  intros g Fixg. sets S': (fun x => S x \/ (x = g)).
  forwards~ (h&[Uph Lubh]&Fixh): (@lub_of_consistent_set _ _ _ E F S').
    intros f1 f2 [[Pf1 Cf1]|G1] [[Pf2 Cf2]|G2]; subst~.
      intros_all. apply~ sym_elim. apply~ Cf2. unfolds* pred_and.
      intros_all. apply~ refl_elim.
    intros f1 [[Pf1 Cf1]|G1]; subst~.
  asserts Dfh Efh: (extends E f h). apply Lubf. intros f' Sf'. apply~ Uph.
  asserts Dgh Egh: (extends E g h). apply~ Uph.
  intros x [Dfx Dgx]. apply~ (trans_sym_2 (h x)).
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Remark: another direct construction of the optimal fixed point 
       for functions (suggested by Georges Gonthier, in a unpublished
       note written prior to my work on the optimal fixed point combinator) *)

Section Another.
Context A B {IB:Inhab B} (E:binary B) (F:(A->B)->(A->B)).
Variable (HE: equiv E).

Definition optimal : A-->B :=
  epsilon (optimal_fixed_point E F).

(** Gonthier's construction does not construct the domain of the optimal
    fixed point, however it gives a function that evaluates just like
    the optimal fixed point on any point from the domain of the optimal
    fixed point. To compute the image of [x], one picks any function [f]
    that is a fixed point of [F] on any domain domain [D] containing [x],
    and then evaluates [f x]. *)

Definition gonthier : A --> B :=
  Build_partial 
   (fun x => 
    let f := epsilon (fun f:A->B => 
         exists D, D x /\
         partial_fixed_point E F (Build_partial f D))
    in f x)
   (fun x => True).

(** The function obtained by Gonthier's construction agrees with
    the optimal fixed point on the domain of the optimal fixed point. *)

Lemma inclusion_optimal_gonthier : 
  extends E optimal gonthier.
Proof.
  split; simpl. auto. introv Dx. unfold optimal in *.
  spec_epsilon in Dx as g ((Gp&Gc)&Gu).
    apply~ optimal_fixed_point_exists. clearbody g.
  match goal with |- context [epsilon ?P _] =>
    lets (D'&D'x&Gp'): (>> (@epsilon_spec_exists' _ P) __ __);
    [| sets g': (epsilon P) ] end. exists~ g (dom g). clearbody g'.
  applys~ (Gc (Build_partial g' D')).
Qed.

End Another.


(* ********************************************************************** *)
(** * Dependently-typed fixed-point combinator,
      used in the proof of the fixed point theorem for 
      complete ordered families *)

(** The well-founded recursion combinator *)

Definition fix_dep A B (R:binary A) 
  (F:forall x:A, (forall y:A, R y x -> B) -> B) (W:well_founded R) : A -> B :=
  fun x => Acc_rect _ (fun x _ H => F x H) (W x).

(** The associated fixed point equation *)

Lemma fix_dep_eq : forall A B (R:binary A) 
  (F:forall x:A, (forall y:A, R y x -> B) -> B) (W:wf R),
  (forall x f f', (forall y (S:R y x), f y S = f' y S) -> F x f = F x f') ->
  forall x, fix_dep F W x = F x (fun y _ => fix_dep F W y).
Proof.
  introv Cont. intros. unfold fix_dep.
  match goal with |- ?g x (W x) = _ => sets G: g end.
  asserts: (forall x (Ac1 Ac2:Acc R x), G x Ac1 = G x Ac2).
   clears x. intros x Ac1. induction Ac1 using Acc_inv_dep. 
   intros Ac2. dependent inversion Ac2. simpl. apply~ Cont.
  case (W x). intros. simpl. apply~ Cont.
Qed.

(** The same lemma, with a shorter proof using proof-irrelevance *)

Lemma fix_dep_eq_with_proof_irrelevance : forall A B (R:binary A) 
 (F:forall x:A, (forall y:A, R y x -> B) -> B) (W:wf R),
  (forall x f f', (forall y (S:R y x), f y S = f' y S) -> F x f = F x f') ->
  forall x, fix_dep F W x = F x (fun y _ => fix_dep F W y).
Proof.
  introv Cont. intros x. unfold fix_dep at 1. case (W x). intros K.
  simpl. apply Cont. intros. pi_rewrite* (K y S).
Qed.


(* ********************************************************************** *)
(** * Existence of fixed points based for functionals that are contractive 
      with respect to a complete ordered families of equivs (COFE) *)

(* ---------------------------------------------------------------------- *)
(** ** Families of binary relations *)

(** Families of binary relations on [A] indexed by an ordered set [I] *)

Record family (I A : Type) := {
  family_r : binary I;
  family_sim : I -> binary A }.

(** Two elements [x] and [y] of type [A] are similar iff
    they are similar at any level [i] *)

Definition similar I A (M:family I A) := 
  fun x y => forall i, family_sim M i x y.

(** A set of indices [K] is downward-closed iff for any element [x] in 
   [K], all the elements smaller than [x] also belong to [K]. *)

Definition downward_closed I A (M:family I A) (K:I->Prop) :=
  forall i j, K i -> family_r M j i -> K j.

(* ---------------------------------------------------------------------- *)
(** ** Ordered Families of Equivalences *)

(** An ordered family of equiv is a family such that:
    - the relation [R] is transitive and well-founded 
    - each relation [sim i] is an equivalence relation *)

Record OFE I A (M:family I A) := {
  ofe_wf : wf (family_r M);
  ofe_trans : trans (family_r M);
  ofe_equiv : forall i, equiv (family_sim M i) }.

(** The similarity relation induced by an OFE is an equiv. *)

Lemma similar_equiv : forall I A (M:family I A),
  OFE M -> equiv (similar M).
Proof.
  introv Ofe. lets: (ofe_equiv Ofe). constructor; intros_all.
  apply~ refl_elim. apply~ sym_elim. apply~ trans_elim.
Qed.

Hint Resolve similar_equiv.

(* ---------------------------------------------------------------------- *)
(** ** Complete Ordered Families of Equivalences *)

(** A sequence [u] indexed by [K] is "coherent" iff
    forall [i] and [j] from [K], [u j] is similar to [u i] at level [j].
    The notion of coherent sequence is analogous to that 
    of Cauchy sequences. *)

Definition coherent I A (M:family I A) (K:I->Prop) (u:I->A) :=
  forall i j, K i -> K j -> family_r M j i -> family_sim M j (u j) (u i).

(** A sequence [u] indexed by [K] admits [l] as "limit" iff
    forall [i] in [K], [u i] is similar to [l] at level [i] *)

Definition limit I A (M:family I A) (K:I->Prop) (u:I->A) (l:A) :=
  forall i, K i -> family_sim M i (u i) l.

(** Completeness describes the fact that every coherent sequence [u]
    indexed by a downward-closed set [K] admits a limit. *)

Definition complete I A (M:family I A) :=
  forall K u, 
  downward_closed M K ->
  coherent M K u -> 
  exists l, limit M K u l.

(** A complete ordered family of equiv is a OFE which is complete *)

Record COFE I A (M:family I A) := {
  cofe_ofe :> OFE M;
  cofe_complete : complete M }.


(* ---------------------------------------------------------------------- *)
(** ** Alternative definition of completeness *)

(** We prove that completeness is equivalent to the existence
    of "local"-limits and "global"-limits for every locally-coherent
    and globally-coherent sequences, respectively. *)
    
(** -------- Local completeness --------- *)

(** A sequence [u] is locally coherent up-to index [i] iff
    it is coherent on the set of indices [j] smaller than [i]. *)

Definition locally_coherent I A (M:family I A) (i:I) (u:I->A) :=
  coherent M (flip (family_r M) i) u.

(** A sequence [u] admits [l] as limit up-to index [i] iff
    for any [j] smaller than [i], [u j] is similar to [l] at level [j]. *)

Definition local_limit I A (M:family I A) (i:I) (u:I->A) (l:A) :=
  limit M (flip (family_r M) i) u l.

(** An ordered family of equiv is locally-complete iff
    for every [i], every sequence locally coherent upto index [i] 
    admits a limit upto the index [i] *)

Definition locally_complete I A (M:family I A) :=
  forall u i, locally_coherent M i u -> 
  exists l, local_limit M i u l.

(** -------- Global completeness --------- *)

(** A sequence [u] is globally coherent iff
    it is coherent on the set of all indices. *)

Definition globally_coherent I A (M:family I A) (u:I->A) :=
  coherent M pred_true u.

(** A sequence [u] admits [l] as global limit iff
    for any [i], the value [u i] is similar to [l] at level [i]. *)

Definition global_limit I A (M:family I A) (u:I->A) (l:A) :=
  limit M pred_true u l.

(** An ordered family of equiv is globally-complete iff
    for every [i], every globally-coherent sequence 
    admits a global limit *)

Definition globally_complete I A (M:family I A) :=
  forall u, globally_coherent M u -> 
  exists l, global_limit M u l.

(** -------- Hints for proofs --------- *)

Hint Resolve ofe_wf ofe_trans ofe_equiv.
Hint Resolve cofe_ofe cofe_complete.
Hint Unfold coherent globally_coherent locally_coherent.

Lemma ofe_sim_refl : forall I A (M:family I A) i,
  OFE M -> refl (family_sim M i).
Proof. intros. apply~ equiv_refl. Qed.

Lemma ofe_sim_trans : forall I A (M:family I A) i,
  OFE M -> trans (family_sim M i).
Proof. intros. apply~ equiv_trans. Qed.

Lemma ofe_sim_sym : forall I A (M:family I A) i,
  OFE M -> sym (family_sim M i).
Proof. intros. apply~ equiv_sym. Qed.

Hint Resolve ofe_sim_refl ofe_sim_trans ofe_sim_sym.


(** -------- Alternative definition of completeness --------- *)

(** An alternative definition of the completeness of [M]
    is the fact that [M] is both locally-complete and
    globally-complete. This alternative definition, despite
    the fact that it has two components, is often more convenient to
    exploit, both as a introduction rule or as an elimination rule. *)

Definition complete' I A (M:family I A) :=
  locally_complete M /\ globally_complete M.

(** Completness implies local completeness *)

Lemma complete_to_locally_complete : forall I A (M:family I A),
  OFE M -> complete M -> locally_complete M.
Proof.
  introv Ofem Comp Cohu. apply~ Comp. intros j' j. introv Rij' Rjj'.
  unfolds flip. applys* trans_elim.
Qed.

(** Completness implies global completeness *)

Lemma complete_to_globally_complete : forall I A (M:family I A),
  OFE M -> complete M -> globally_complete M.
Proof. introv Ofem Comp Cohu. apply~ Comp. Qed.

(** A more involved proof is required to prove completeness
    from local- and global- completeness. For this proof,
    and also for the proof of the fixed point theorem, we
    we need to define a sequence [v] where [v i] is defined
    in terms of the values of [v j] for [j] smaller than [i].
    For Coq to accept this definition, we rely on the dependendly-
    typed fixed point combinator [fix_dep]. Also, we rely on the
    following auxiliary definition which is used to pick the
    limit, if it exists, of a family [u] defined only on indices
    smaller than a given index [i]. This definition requires
    the type [A] to be inhabited. *)

Definition local_limit_dep I A {IA:Inhab A} (M:family I A)  
 (i:I) (u:forall j, family_r M j i -> A) :=
  epsilon (fun l =>
    forall j, match classicT (family_r M j i) with
              | left m => family_sim M j (u j m) l
              | right _ => True
              end).

(** The following lemma is used to show that when a sequence
    [v] (of type [I->A]) is locally-coherent upto index i
    with respect to a locally-complete family of equivs,
    then [local_limit_dep M i (fun j _ => v j)] returns a
    value [l] which is a local limit for [v] upto index [i].
    Remark: above, the unnamed argument has type [family_r M j i].
    Note: for the sake of convenience, the definiiton of 
    [local_limit] has been unfolded in the formal statement. *)

Lemma local_limit_dep_name : forall I A {IA:Inhab A}  
  (i:I) (v:I->A) (M:family I A),
  locally_complete M -> locally_coherent M i v -> exists l,
     local_limit_dep M i (fun j _ => v j) = l
  /\ (forall j, family_r M j i -> family_sim M j (v j) l).
Proof.
  introv Loca Cohi. esplit. split. reflexivity. 
  unfold local_limit_dep. spec_epsilon as l L.
  forwards~ [l L]: (Loca v i). exists l. intros k. destruct_if~.
  intros j Rji. specializes L j. rewrite~ (classicT_left Rji) in L.
Qed.

(** A corrolary of the above lemma used to prove similarity directly *)

Lemma local_limit_dep_elim : forall I A {IA:Inhab A}  
  (i j:I) (v:I->A) (M:family I A),
  locally_complete M -> locally_coherent M i v -> family_r M j i -> 
  family_sim M j (v j) (local_limit_dep M i (fun j _ => v j)).
Proof.
  intros. forwards~ (l&Eq&L): local_limit_dep_name. rewrite~ Eq.
Qed.

(** The proof that local- and global completeness suffice to
    derive completeness. Let [u] be a coherent sequence indexed by [K].
    The key idea to show that [u] admits a limit is to define a sequence [v]
    as follows: [v i] is equal to [u i] if [i] is in the set [K], and
    [v i] is equal to the limit of the values [v j] for [j] smaller than [i].
    We can show by induction on [i] that [v] is locally-coherent upto index
    [i], and then that [v] is globally-coherent. Finally, we show that
    the global limit of [v] is also a limit for [u]. *)

Lemma complete_from_locally_and_globally_complete :
  forall I A {IA:Inhab A} (M:family I A),
  OFE M -> locally_complete M -> globally_complete M -> complete M.
Proof.
  introv IA Ofem Loca Glob Down Cohu.
  (* definition of [v] and of its limit *)
  sets V: (fun i v' => if classicT (K i) then u i else local_limit_dep M i v').
  sets v: (fix_dep V (ofe_wf Ofem)). exists (epsilon (global_limit M v)). 
  (* fixed point equation used to unfold the definition of [v] *)
  asserts Fixv: (forall i, v i = V i (fun j _ => v j)).
    apply fix_dep_eq. intros x v1 v2 H. unfold V. destruct_if~.
    apply epsilon_eq. intros i. iff N; intros j; specializes N j;
     destruct_head_match; congruence.
  (* the sequence [v] is locally-coherent up to any index *)
  asserts LocCohv: (forall i, locally_coherent M i v).
    intros i. induction_wf: (ofe_wf Ofem) i.
    intros j' j Rij' Rij Rjj'. unfolds flip.
    destruct (classicT (K j')) as [Kj'|NKj']. 
      forwards~ Kj: (>> Down j' j).
      do 2 rewrite Fixv. unfold V. do 2 destruct_if~.
      rewrite (Fixv j'). unfold V. destruct_if~.
      apply~ local_limit_dep_elim.
  (* the sequence [v] is globally-coherent *)
  asserts GloCohv: (globally_coherent M v).
    intros i j _ _ Rji. rewrite (Fixv i). unfold V. destruct_if.
      forwards~ Kj: (>> Down i j). rewrite Fixv. unfold V. destruct_if~.
      apply~ local_limit_dep_elim.
  (* the global limit of [v] is also a limit for [u] *)
  spec_epsilon as l L. apply~ Glob.
  introv Ki. applys~ equiv_trans. rewrite Fixv. unfold V.
  destruct_if~. apply~ equiv_refl.
Qed.
    
(** Summary: the two definitions of completeness are equivalent *)

Lemma complete_iff_complete' : forall I A {IA:Inhab A} (M:family I A),
  OFE M -> (complete M <-> complete' M).
Proof.
  split. split.
    apply~ complete_to_locally_complete.
    apply~ complete_to_globally_complete.
  intros [H1 H2]. apply~ complete_from_locally_and_globally_complete.
Qed.

(** -------- A direct lemma to build COFE --------- *)

Lemma make_COFE : forall I A {IA:Inhab A} (M:family I A),
  wf (family_r M) ->
  trans (family_r M) ->
  (forall i, equiv (family_sim M i)) ->
  complete M ->
  COFE M.
Proof. intros. asserts: (OFE M). constructor~. constructor~. Qed. 

Hint Resolve complete_to_locally_complete 
             complete_to_globally_complete.


(* ---------------------------------------------------------------------- *)
(** ** Fixed-point theorem *)

(** -------- Definitions --------- *)

(** A relation [Q] is "continuous" if it remains true when
    taking the limit of its second argument. *)

Definition continuous I A (M:family I A) (Q:I->A->Prop) :=
  forall (K:I->Prop) (u:I->A) (l:A), 
  limit M K u l ->
  (forall i, K i -> Q i (u i)) ->
  (forall i, K i -> Q i l).

(** A functional [F] is contractive if [F x] is similar to [F y]
    at level [i] whenever [x] is similar to [y] at any level [j]
    smaller than [i]. *)

Definition contractive_noinv I A (M:family I A) (F:A->A) :=
  forall i x y, (forall j, family_r M j i -> family_sim M j x y) ->
  family_sim M i (F x) (F y).

(** A more general definition of contractive allows for an invariant
    [Q] to be assumed of [x] and [y] when trying to prove [F x] and [F y]
    similar. In exchange, one must establish that [Q] holds of [F x]. *)

Definition contractive I A (M:family I A) (F:A->A) (Q:I->A->Prop) :=
  forall i x y, 
  (forall j, family_r M j i -> family_sim M j x y /\ Q j x /\ Q j y) ->
  family_sim M i (F x) (F y) /\ Q i (F x).

(** The simple definition of contractive is in fact just an instance
    of the general contraction condition with [Q] instantiated as the
    predicate which always returns True. *)

Lemma contractive_noinv_to_contractive : forall I A (M:family I A) (F:A->A),
  contractive_noinv M F -> contractive M F (fun _ _ => True).
Proof.
  introv Cont. unfolds. intros. split~. apply Cont. intros. forwards*: H.
Qed.

(** A relation [Q] of type [I->A->Prop] is said to be an
    "invariant" of a functional [F] if [Q i (F x)] is derivable
    from the knowledge that [Q j x] holds for any [j] smaller than [i]. *)

Definition invariant I A (M:family I A) (F:A->A) (Q:I->A->Prop) :=
  forall i x, (forall j, family_r M j i -> Q j x) -> Q i (F x).

(** If [F] is contractive with respect to [Q], then
    [Q] is an invariant for [F]. *)

Lemma contractive_to_invariant : 
  forall I A (M:family I A) (F:A->A) (Q:I->A->Prop),
  OFE M -> contractive M F Q -> invariant M F Q.
Proof.
  introv Ofem Cont. intros_all. forwards~ [M1 M2]: (>> Cont i x x).  
  introv Rji. splits~. apply~ refl_elim.
Qed.

(** A continuous invariant for a functional [F] 
    holds of any fixed point of [F]. *)

Lemma invariant_on_fixed_point : 
  forall I A (M:family I A) (F:A->A) (Q:I->A->Prop) (x:A),
  OFE M -> continuous M Q -> invariant M F Q ->
  similar M x (F x) -> forall i, Q i x.
Proof.
  introv Cofe Cont Inv Fixx. intros i. induction_wf: (ofe_wf Cofe) i.
  applys~ (Cont (large (flip (family_r M)) i) (fun _:I => (F x))).
    intros_all. apply~ sym_elim.
    intros j Le. apply Inv. intros k Rkj.
     apply IH. destruct Le. apply~ trans_elim. subst~.
Qed.


(** -------- Theorem --------- *)

(** The general fixed point theorem states that, given a complete 
    ordered family of equivs, if [Q] is a continuous property
    and [F] is a functional contractive with respect to [Q],
    then [F] admits a unique fixed point (upto similarity),
    which satisfies all the predicates [Q i]. 

    The key idea of the proof is to define a sequence [v] such 
    that [v i] is equal to the application of [F] to the limit
    of the values [v j], for [j] smaller than [i]. We prove in
    the same time that [v] is locally-coherent upto index [i]
    and that [Q i (v i)] holds. We then show that [v] is 
    globally-coherent, and that its limit [l] is such that
    [Q i l] for any [i], using the continuity of [Q].
 
    Then, we show that [v] is similar to [F v], and that [v]
    is similar to any [x] such that [x] is similar to [F x]. 
    
 *)

Definition build_fixed_point I A {IA:Inhab A} (M:family I A) (F:A->A) (Cofe:COFE M) :=
  let V := fun i v' => F (local_limit_dep M i v') in
  let v := fix_dep V (ofe_wf Cofe) in
  epsilon (global_limit M v).

Theorem cofe_explicit_fixed_point : 
  forall I A {IA:Inhab A} (M:family I A) (F:A->A) (Q:I->A->Prop)
  (Cofe: COFE M), continuous M Q -> contractive M F Q ->
  let x := build_fixed_point F Cofe in
     unique_fixed_point (similar M) F x
  /\ (forall i, Q i x).
Proof.
  introv Conti Contr.
  sets predecessor: (flip (family_r M)).
  (* definition of the sequence [v] and of its limit *)
  unfold build_fixed_point.
  sets V: (fun i v' => F (local_limit_dep M i v')).
  sets v: (fix_dep V (ofe_wf Cofe)).
  (* fixed-point equation used to unfold the definition of [v] *)
  asserts Fixv: (forall i, v i = V i (fun j _ => v j)).  
    apply fix_dep_eq. intros x v1 v2 H. unfold V. fequals.
    apply epsilon_eq. intros i. iff N; intros j; specializes N j;
      destruct_head_match; congruence.
  (* a lemma to help establish coherence *)
  asserts Coh: (forall i j, family_r M j i ->  
     locally_coherent M i v -> locally_coherent M j v -> 
     (forall k, family_r M k i -> Q k (v k)) ->
     family_sim M j (v j) (v i)).
    intros i j Rji Cohi Cohj Qk. do 2 rewrite Fixv. unfold V.
    forwards* (l1&El1&L1): (>> (@local_limit_dep_name I) j).
    forwards* (l2&El2&L2): (>> (@local_limit_dep_name I) i). 
    rewrite El1. rewrite El2. clear El1 El2.
    apply (proj1 (proj_lemma_4 Contr)). intros k Rkj.
    asserts Rkj': (family_r M k i). apply* ofe_trans. splits.
     applys~ (trans_sym_1 (v k)). 
     applys~ (Conti (predecessor j) v). 
      intros. apply Qk. applys* trans_elim.
     applys~ (Conti (predecessor i) v).
  (* prove of local-coherence, together with the invariant *)
  asserts LocCohQv: (forall i, locally_coherent M i v /\ Q i (v i)).
    intros i. induction_wf: (ofe_wf Cofe) i.
    lets [IH1 IH2]: (proj_lemma_2 IH). clear IH. 
    logic (forall (U V : Prop), U -> (U -> V) -> U /\ V). 
    (* locally coherent *)
    intros j' j Rij' Rij Rjj'. unfolds flip.
    apply~ Coh. intros k Rkj'. apply IH2. apply* trans_elim.
    (* step the invariant *)
    introv Cohi. rewrite Fixv. unfold V.
    forwards* (l&El&L): (>> (@local_limit_dep_name I) i). 
    rewrite El. clear El. (* todo: limitation of forward *)
    applys~ (contractive_to_invariant Cofe Contr).
    introv Rji. applys~ (Conti (predecessor i) v).
  lets LocCohv Qv: (proj_lemma_1 LocCohQv). clear LocCohQv.
  (* global coherence of [v] *) 
  asserts Cohv: (globally_coherent M v). intros_all. apply~ Coh.
  (* prove the three conclusions *)    
  spec_epsilon as l L. apply~ cofe_complete. 
  split. unfolds. logic (forall P Q : Prop,
    P -> (P -> Q) -> P /\ Q).
  (* 1- fixed point *)
  intros l' Sim' i.
  applys~ (trans_sym l). applys~ (trans_sym_1 (v i)).
  rewrite Fixv. unfold V.
  applys (proj1 (proj_lemma_4 Contr)). intros j Rji. splits.
    applys~ (trans_sym_1 l). applys~ (trans_sym_1 (v j)).
     applys~ local_limit_dep_elim.
    forwards* (l1&El1&L1): (>> (@local_limit_dep_name I) i).
     rewrite El1. clear El1. applys~ (Conti (predecessor i) v).
    applys~ (Conti pred_true v). intros k _. applys~ (trans_elim l).
  (* 2- uniqueness *)
  intros Fixl l' Fixl'. unfold fixed_point in Fixl, Fixl'.
  specializes Fixl l __. intros j. apply~ refl_elim. apply~ sym_elim. 
  intros i. induction_wf: (ofe_wf Cofe) i.
  applys~ (@trans_elim _ (F l)). apply~ sym_elim.
  applys~ (@trans_sym_2 _ (F l')). apply Fixl'. intros j. apply* refl_elim.
  apply (proj1 (proj_lemma_4 Contr)). intros j Rji. splits.
    apply~ IH.
    applys~ (Conti pred_true v).  
    applys~ (Conti (predecessor i) v).
      intros k Rki. apply~ (@trans_elim _ l). 
  (* 3- invariant *)
  intros i. applys~ (Conti pred_true v). 
Qed.

Theorem cofe_fixed_point : 
  forall I A {IA:Inhab A} (M:family I A) (F:A->A) (Q:I->A->Prop),
  COFE M -> continuous M Q -> contractive M F Q ->
  exists x, unique_fixed_point (similar M) F x
         /\ (forall i, Q i x).
Proof. intros. forwards*: (@cofe_explicit_fixed_point I A IA M F Q H). Qed.



(* ********************************************************************** *)
(** * Particular COFEs *)

(* ---------------------------------------------------------------------- *)
(** ** COFE for (partial) recursive functions (on a quotient) *)

(** We define the family used to reason on partial functions, 
    taking the set of arguments (of type [A]) as set of indices,
    using the transitive closure of the termination relation R as
    relation between indices, and taking the similarity at level [x]
    between two functions [f1] and [f2] as the extensional equality
    between those functions on values smaller or equal to [x],
    and on the domain [P] of the function. *)

Definition rec_family A B (E:binary B) (P:A->Prop) (R:binary A)
  : family A (A->B) :=
  Build_family 
    (tclosure R)
    (fun x f1 f2 =>
       forall x', P x' -> large (tclosure R) x' x -> E (f1 x') (f2 x')).

(** We show that the family for partial recursive functions is a COFE *)

Lemma rec_cofe : 
  forall A B {IB:Inhab B} (E:binary B) (P:A->Prop) (R:binary A),
  equiv E -> wf R -> COFE (rec_family E P R).
Proof.
  introv IB Equiv WfR. apply make_COFE; simpl. 
  typeclass.
  apply~ tclosure_wf.
  apply tclosure_trans.
  destruct Equiv. constructor; intros_all*.
  intros K u Downk Cohu. hnf in Downk. hnf in Cohu. simpls. 
   exists (fun x => u x x). intros x Kx. simpl.
   intros x' Px' [Ex'x|x'x].
     apply equiv_sym; auto. apply* Cohu.
     subst. apply~ equiv_refl.
Qed.

(** In the following, we reformulate the fixed-point theorem for the 
    particular case of partial functions. First, we reformulate 
    the contraction condition. *)

Definition rec_contractive A B (E:binary B) (P:A->Prop) 
 (F:(A->B)->(A->B)) (R:binary A) (S:A->B->Prop) :=
  forall f1 f2 x, P x -> 
  (forall y, P y -> R y x -> E (f1 y) (f2 y) /\ S y (f1 y)) -> 
  E (F f1 x) (F f2 x) /\ S x (F f1 x).

(** And we also reformulate the simple case for non-nested recursion *)

Definition rec_contractive_noinv A B (E:binary B) (P:A->Prop) 
 (F:(A->B)->(A->B)) (R:binary A) :=
  forall f1 f2 x, P x -> 
  (forall y, P y -> R y x -> E (f1 y) (f2 y)) ->
   E (F f1 x) (F f2 x).

(** The later is a particular case of the former *)

Lemma rec_contractive_noinv_to_rec_contractive : 
  forall A B (E:binary B) (P:A->Prop)
    (F:(A->B)->(A->B)) (R:binary A),
  rec_contractive_noinv E P F R -> 
  rec_contractive E P F R post_true.
Proof.
  introv Cont. unfolds. intros. split~. 
  apply~ Cont. intros. forwards*: H0.
Qed.

Lemma rec_contractive_as_contractive :
  forall A B (E:binary B) (P:A->Prop) 
  (F:(A->B)->(A->B)) (R:binary A) (S:A->B->Prop),
  equiv E -> (forall x, pred_compatible E (S x)) ->
  wf R -> rec_contractive E P F R S ->
  contractive (rec_family E P R) F 
    (fun x f => P x -> S x (f x)).
Proof.
  introv Equiv Comp WfR Cont.
  sets Q: (fun x f => P x -> S x (f x)).
  intros x f1 f2. simpl. intros H. split.
    intros x' Px' Rx'x. apply~ Cont. intros y Py Ryx'. 
    forwards~ (M1&M2&M3): (H y). destruct Rx'x as [Rx'x|Ex'x]. 
      apply* tclosure_trans. apply~ tclosure_once.
      subst. apply~ tclosure_once.
    intros Px. forwards [M1 M2]: Cont f1 f1 Px.
      introv Py Ryx. forwards (M1&M2&M3): H y. apply~ tclosure_once.
       splits~. apply~ equiv_refl.
      apply M2.
Qed.

(** The fixed point theorem for partial functions states that the
    existence of a unique fixed point on the domain P as soon as
    [F] satisfies the contraction condition with respect to a well-founded
    relation R. The invariant [Q] used in the contraction condition 
    must respect equiv classes of the equiv relation [E]. *)

Theorem rec_fixed_point : forall A B {IB:Inhab B} 
 (F:(A->B)->(A->B)) (R:binary A) (P:A->Prop) (S:A->B->Prop) (E:binary B), 
  equiv E -> (forall x, pred_compatible E (S x)) ->
  wf R -> rec_contractive E P F R S ->
  exists (f:A->B), partial_fixed_point E F (Build_partial f P)
               /\ (forall x, P x -> S x (f x)).
Proof.
  introv IB Equiv Comp WfR Cont. sets M: (rec_family E P R).
  sets Q: (fun x f => P x -> S x (f x)). 
  forwards (f&Fixf&Qf): (>> cofe_fixed_point A (A->B) M F Q). 
  typeclass.
  apply~ rec_cofe.
  introv Limu Qiui Ki Pi. applys Comp. apply~ Qiui.
   apply~ equiv_sym. apply~ Limu.
  apply~ rec_contractive_as_contractive.
  asserts Equ: (pfunc_equiv E P = similar M).
    apply func_ext_2. intros f1 f2. unfold M, similar, pfunc_equiv.
    apply prop_ext. simpl. split~. 
  exists (Build_partial f P). destruct Fixf as [Fixf _]. split~. 
  unfolds in Fixf. intros [f' P']. simpls. rewrite~ Equ.    
Qed.

(** Moreover, we prove that such a unique fixed point is 
    always generally consistent. *)

Lemma rec_fixed_point_generally_consistent : forall A B {IB:Inhab B} 
 (F:(A->B)->(A->B)) (R:binary A) (P:A->Prop) (S:A->B->Prop) (E:binary B) f, 
  equiv E -> (forall x, pred_compatible E (S x)) ->
  wf R -> rec_contractive E P F R S ->
  fixed_point (pfunc_equiv E P) F f ->
  (forall x, P x -> S x (f x)) ->
  generally_consistent_partial_fixed_point E F (Build_partial f P).
Proof. 
  introv IB Equiv Comp Wf Cont Fixf Inva. split.   
  unfolds. simpl. intros [f' P'] N. simple~.
  intros [f' P'] Fixf'.
   sets f'': (fun x => if classicT (P' x) then f' x else f x).
   intros x [Px P'x]. simpls.
   cuts Ind: (forall x, P x -> E (f x) (f'' x)).
     apply~ (trans_elim (f'' x)). unfold f''. destruct_if. apply~ refl_elim.
   clears x. intros x. induction_wf: Wf x. intros Px. 
   destruct (classic (P' x)) as [P'x|NP'x];
     [| unfold f''; destruct_if; apply~ refl_elim ].
   apply~ (trans_sym_2 (F f'' x)). apply~ (trans_elim (F f x)).
     apply~ Fixf. apply~ equiv_refl.
     apply~ (proj1 (proj_lemma_5 Cont)).
     apply~ (Fixf' (Build_partial f'' P')). simpl.
      intros y P'y. unfold f''. destruct_if~. apply~ refl_elim.
Qed.

(** Alternative formulation *)

Definition rec_contractive' A B (E:binary B) (P:A->Prop) 
 (F:(A->B)->(A->B)) (R:binary A) (f:A->B) :=
  forall f' x, P x -> 
  (forall y, P y -> R y x -> E (f y) (f' y)) ->
   E (F f x) (F f' x).

Lemma rec_fixed_point_generally_consistent' : forall A B {IB:Inhab B} 
 (F:(A->B)->(A->B)) (R:binary A) (P:A->Prop) (E:binary B) f, 
  equiv E -> wf R -> rec_contractive' E P F R f ->
  fixed_point (pfunc_equiv E P) F f ->
  generally_consistent_partial_fixed_point E F (Build_partial f P).
Proof. 
  introv IB Equiv Wf Cont Fixf. split.   
  unfolds. simpl. intros [f' P'] N. simple~.
  intros [f' P'] Fixf'.
   sets f'': (fun x => if classicT (P' x) then f' x else f x).
   intros x [Px P'x]. simpls.
   cuts Ind: (forall x, P x -> E (f x) (f'' x)).
     apply~ (trans_elim (f'' x)). unfold f''. destruct_if. apply~ refl_elim.
   clears x. intros x. induction_wf: Wf x. intros Px. 
   destruct (classic (P' x)) as [P'x|NP'x];
     [| unfold f''; destruct_if; apply~ refl_elim ].
   apply~ (trans_sym_2 (F f'' x)). apply~ (trans_elim (F f x)).
     apply~ Fixf. apply~ equiv_refl.
     apply~ (Fixf' (Build_partial f'' P')). simpl.
      intros y P'y. unfold f''. destruct_if~. apply~ refl_elim.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** COFE for definitions functions mixing recursion and corecursion *)

Hint Unfold lexico2.

(** We define the family used to reason on partial functions mixing
    recursion and co-recursion. More precisely, given a COFE on values
    from the return type [B] indexed by values of type [I], and given a 
    well-founded relation [R] on arguments of type [A], we define a
    COFE for functions of type [A->B] indexed by pairs of type [I*A].
 
    The idea is to consider the lexicographical order build upon the
    order on [I] and the order on [A], and to consider that two functions
    [f1] and [f2] are similar at level [(i,x)] iff they are extensionnaly
    similar at level [i'] on arguments [x'] such that [i'] is smaller
    than [i] (for guarded recursive calls) or [i'] is equal to [i] and
    [x'] is smaller than [x] (for non-guarded recursive calls). *)

Definition corec_rec_family I A B 
  (M:family I B) (P:A->Prop) (R:binary A) : family (I*A) (A->B) :=
  let R' := lexico2 (family_r M) (tclosure R) in
  Build_family R'
    (fun p f1 f2 => let (i,x) := p : I*A in
      forall i' x', large R' (i',x') (i,x) -> P x' -> 
      family_sim M i' (f1 x') (f2 x')).

(** We show that this structure is a COFE *)

Lemma corec_rec_cofe : 
  forall I A B {IB:Inhab B} (M:family I B) (P:A->Prop) (R:binary A),
  COFE M -> wf R -> COFE (corec_rec_family M P R).
Proof.
  introv IB Cofe WfR. apply make_COFE; simpl.
  typeclass. 
  apply~ @lexico2_wf. apply~ tclosure_wf.
  apply~ lexico2_trans. apply tclosure_trans.
  intros [i x]. constructor.
    intros_all. destruct~ (ofe_equiv Cofe i').
    intros_all. destruct~ (ofe_equiv Cofe i').
    intros_all. destruct* (ofe_equiv Cofe i').
  intros K u Downk Cohu. hnf in Downk. hnf in Cohu. simpls. 
   exists (fun x => epsilon (limit M (fun i => K (i,x)) (fun i => u (i,x) x))).
   intros [i x] Kix. simpl. intros j x' LR' Px'.
   spec_epsilon as l L.
     apply (cofe_complete Cofe).
       introv H H'. hnf. applys~ Downk H.
       introv H H' H''. applys~ (>> Cohu H H').
   hnf in L. simpl in L. destruct LR' as [LR'|Ex'x].
     asserts Kjx': (K (j,x')). apply* Downk.
      apply~ trans_sym_1. applys~ (>> Cohu Kix Kjx' LR').
     inversion Ex'x. subst x. apply~ L.
Qed.

(** The similarity relation induced on the new COFE 
    corresponds to the pointwise similarity from the
    base COFE, on the domain. *)

Lemma corec_rec_similar : forall I A B 
  (M:family I B) (P:A->Prop) (R:binary A),
  similar (corec_rec_family M P R) = 
  (fun f1 f2 => forall x, P x -> similar M (f1 x) (f2 x)).
Proof.
  intros. apply prop_ext_2. intros f1 f2. 
  unfold similar. simpl. iff H.
  intros. apply~ (H (i,x)).
  intros [i x]. intros. apply~ H.
Qed. 

(** In the following, we reformulate the fixed-point theorem for the 
    particular case of partial functions. First, we reformulate 
    the contraction condition. *)

Definition mixed_contractive I A B (M:family I B) (P:A->Prop) 
 (F:(A->B)->(A->B)) (R:binary A) (S:I->A->B->Prop) :=
  forall i x f1 f2, P x -> 
  (forall y j, P y -> lexico2 (family_r M) R (j,y) (i,x) ->
     family_sim M j (f1 y) (f2 y) /\ S j y (f1 y) /\ S j y (f2 y)) -> 
  family_sim M i (F f1 x) (F f2 x) /\ S i x (F f1 x).

(** We show that the above is indeed a reformulation *)

Lemma mixed_contractive_as_contractive :
  forall I A B (M:family I B) (P:A->Prop) 
  (F:(A->B)->(A->B)) (R:binary A) (S:I->A->B->Prop),
  OFE M -> wf R -> 
  mixed_contractive M P F R S -> 
  contractive (corec_rec_family M P R) F 
    (fun p f => let (i,x) := p in P x -> S i x (f x)).
Proof.
  introv Ofe WfR Cont.
  sets Q: (fun p f => let (i,x) :=p:I*A in P x -> S i x (f x)).
  intros p f1 f2. induction_wf: (lexico2_wf (ofe_wf Ofe) (tclosure_wf WfR)) p.
  destruct p as [i x]. intros H.
  split.
  intros j y Le Px. destruct Le as [Le|Eq].
    destruct (IH (j,y)) as [K _]; auto~. (* TODO: bug forwards *)
      intros [k z] Le'. apply H. apply~ lexico2_trans. apply tclosure_trans. apply Le'.
   inversions Eq.
   forwards~ [K _]: (>> Cont i x f1 f2). intros y j Py Lt.
   forwards* (K1&K2&K3): (H (j,y)). 
     forwards*: (>> lexico2_incl I A (family_r M) (family_r M) R (tclosure R) (j,y) (i,x)).
  introv Px. forwards~ [_ K]: (>> Cont i x f1 f2).
   intros y j Py Lt. forwards* (K1&K2&K3): (H (j,y)).
     forwards*: (>> lexico2_incl I A (family_r M) (family_r M) R (tclosure R) (j,y) (i,x)).
Qed. (* TODO: clean up the lexico2_incl *)

(** The simple version of contraction *)

Definition mixed_contractive_noinv I A B (M:family I B) (P:A->Prop) 
 (F:(A->B)->(A->B)) (R:binary A) :=
  forall i x f1 f2, P x -> 
  (forall y j, P y -> lexico2 (family_r M) R (j,y) (i,x) ->
     family_sim M j (f1 y) (f2 y)) -> 
  family_sim M i (F f1 x) (F f2 x).

Lemma mixed_contractive_noinv_to_mixed_contractive : 
  forall I A B (M:family I B) (P:A->Prop) 
  (F:(A->B)->(A->B)) (R:binary A),
  mixed_contractive_noinv M P F R -> 
  mixed_contractive M P F R (fun _ => post_true).
Proof.
  introv Cont. unfolds. intros. split~. 
  apply~ Cont. intros. forwards*: H0.
Qed.

(** Similarly, we reformulate the definition of continuity. *)

Definition mixed_continuous I A B (M:family I B) (S:I->A->B->Prop) :=
  forall i x y1 y2, 
  S i x y1 ->
  (forall j, family_r M j i -> family_sim M j y1 y2) ->
  S i x y2.

(** We can now state and prove the fixed point theorem *)

Theorem mixed_fixed_point : 
  forall I A B {IB:Inhab B} (M:family I B) (E:binary B) (P:A->Prop) 
  (F:(A->B)->(A->B)) (R:binary A) (S:I->A->B->Prop),
  COFE M -> wf R -> E = similar M -> 
  mixed_continuous M S -> mixed_contractive M P F R S -> 
  exists (f:A->B), partial_fixed_point E F (Build_partial f P)
               /\ (forall i x, P x -> S i x (f x)).
Proof. 
  introv IB Cofe WfR SimE Conti Contr.
  forwards (f&Fixf&Qf): 
   (@cofe_fixed_point (I*A) (A->B) _ (corec_rec_family M P R) F 
      (fun p f => let (i,x) := p in P x -> S i x (f x))).
    apply~ corec_rec_cofe.
    introv Limu Qiui. unfolds in Limu. simpls. intros [i x] Kix Px.
     applys Conti. apply~ (Qiui (i,x)). intros j Rji.
     apply~ (>> Limu Kix j x).
    apply~ mixed_contractive_as_contractive.  
  exists (Build_partial f P). destruct Fixf as [Fixf _]. split. 
    unfolds in Fixf. rewrite corec_rec_similar in Fixf. rewrite SimE.
     intros [f' P']. simpls~.
    intros. apply~ (Qf (i,x)).
Qed.

(** General consistency of a fixed point *)

Lemma mixed_fixed_point_generally_consistent : 
  forall I A B {IB:Inhab B} (M:family I B) (E:binary B) (P:A->Prop)
  (R:binary A) (F:(A->B)->(A->B)) (S:I->A->B->Prop) (f:A->B),
  COFE M -> wf R -> E = similar M -> 
  mixed_continuous M S -> mixed_contractive M P F R S -> 
  fixed_point (pfunc_equiv E P) F f ->
  (forall i x, P x -> S i x (f x)) ->
  generally_consistent_partial_fixed_point E F (Build_partial f P).
Proof. 
  Hint Resolve pfunc_equiv_equiv similar_equiv.
  introv IB Cofe WfR SimE. introv Conti Contr Fixf Inva. 
  subst E. split. unfolds. simpl. intros [f' P'] N. simple~. 
  intros [f' P'] Fixf'.
   sets f'': (fun x => if classicT (P' x) then f' x else f x).
   intros x [Px P'x]. simpls.
   cuts Ind: (forall p, let (i,x) := p:I*A in P x -> family_sim M i (f x) (f'' x)).
     intros i. apply~ (trans_elim (f'' x)).
       apply~ (Ind (i,x)).
       unfold f''. destruct_if. apply~ refl_elim.
   clears x. intros p. induction_wf: (lexico2_wf (ofe_wf Cofe) (tclosure_wf WfR)) p. 
   destruct p as [i x]. intros Px. 
   destruct (classic (P' x)) as [P'x|NP'x];
     [| unfold f''; destruct_if; apply~ refl_elim ].
   apply~ (trans_sym_2 (F f'' x)). apply~ (trans_elim (F f x)).
     apply~ Fixf. apply~ equiv_refl.
     applys (proj1 (proj_lemma_6 Contr)) Px. intros y j Py Lt. splits.
       apply~ (IH (j,y)).
         forwards*: (>> lexico2_incl I A (family_r M) (family_r M) R (tclosure R) (j,y) (i,x)).
       auto. 
       applys~ Conti. intros k Rkj. applys (IH (k,y)) Py.   
        destruct Lt as [|[? ?]].
          left. apply~ (trans_elim j).
          subst~.
     apply~ (Fixf' (Build_partial f'' P)). simpl.
      intros y P'y. unfold f''. destruct_if~. apply~ refl_elim.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** COFE indexed with natural numbers *)

(** The contraction condition can be given a simpler statement
    in the particular case where indexes are instantiated as
    natural numbers ordered by relation [lt]. *)

(** First, we define the notion of nat-indexed family of
    equiv relations. *)

Definition nat_family A (sim:nat->binary A) : family nat A :=
  Build_family lt sim.

(** A sufficient condition for completeness is that for any 
    nat-indexed sequence [u], if forall [i], [u i] is similar
    at level [i] to [u (i+1)], then there exists a limit [l]
    to the sequence [u], that is, [u i] is similar to [l] at
    level [i], for any [i]. *)

Definition nat_complete A (sim:nat->binary A) :=
  forall (u:nat->A), 
  (forall i, sim i (u i) (u (S i))) -> 
  exists l, forall i, sim i (u i) l.

(** We can now reformulate conditions for a nat-indexed
    family of equiva lence to be a COFE *)

Lemma nat_cofe : forall A {IA:Inhab A} (sim:nat->binary A),
  (forall i, equiv (sim i)) ->
  nat_complete sim ->
  COFE (nat_family sim).
Proof.
  introv IA Equiv Comp.
  asserts Ofe: (OFE (nat_family sim)). constructor; simpl.
    apply lt_wf.
    intros_all~. nat_math.
    apply Equiv.
  constructor~. apply~ complete_from_locally_and_globally_complete.
  (* local completeness *)
  introv Cohu. sets v: (fun j => If j < i then u j else u (i-1)%nat).
  forwards [l L]: (Comp v). intros j. tests: (S j < i).
    unfold v. do 2 case_if; try math. apply Cohu; hnf; try math.
    unfold v. do 2 case_if; try math.
      math_rewrite ((i - 1)%nat = j). apply~ equiv_refl.
      apply~ equiv_refl.
  exists l. intros j Rji. unfolds flip. simpls.
  specializes L j. unfold v in L. case_if~; try false.
  (* global completeness *)
  introv Cohu. forwards [l L]: (Comp u). intros i.
  induction_wf: lt_wf i. apply~ Cohu. simpl. math.
  exists l. introv _. apply L.
Qed.

(** Another more relaxed definition of nat-completeness *)

Require LibNat.

Definition nat_complete' A (sim:nat->binary A) :=
  forall (u:nat->A), 
  (forall i j, i < j -> sim i (u i) (u j)) -> 
  exists l, forall i, sim i (u i) l.

(** We can now reformulate conditions for a nat-indexed
    family of equiva lence to be a COFE *)

Lemma nat_cofe' : forall A {IA:Inhab A} (sim:nat->binary A),
  (forall i, equiv (sim i)) ->
  nat_complete' sim ->
  COFE (nat_family sim).
Proof.
  introv IA Equiv Comp.
  asserts Ofe: (OFE (nat_family sim)). constructor; simpl.
    apply lt_wf.
    intros_all~. math.
    apply Equiv.
  constructor~. apply~ complete_from_locally_and_globally_complete.
  (* local completeness *)
  introv Cohu. sets v: (fun j => If j < i then u j else u (i-1)%nat).
  forwards [l L]: (Comp v). intros k j Rkj. tests: (S j < i).
    unfold v. do 2 case_if; try math. apply Cohu; hnf; math.
    unfold v. tests: (j < i).
      math_rewrite ((i - 1)%nat = j). case_if; try math. 
      apply Cohu; hnf; math.
      case_if. tests: (k = (i -1)%nat). 
          apply~ equiv_refl.
          apply Cohu; hnf; try math.
        apply~ equiv_refl.
  exists l. intros j Rji. unfolds flip. simpls.
  specializes L j. unfold v in L. case_if~; try false.
  (* global completeness *)
  introv Cohu. forwards [l L]: (Comp u). intros i.
  induction_wf: lt_wf i. intros. apply~ Cohu.
  exists l. introv _. apply L.
Qed.



(* ********************************************************************** *)
(** * COFE for products *)

Definition prod_family_sim I A1 A2 (R:binary I) (Sim1:I->binary A1) (Sim2:I->binary A2) :=
  Build_family R (fun i => prod2 (Sim1 i) (Sim2 i)).

Lemma prod_cofe_sim : forall I A1 A2 (R:binary I) (Sim1:I->binary A1) (Sim2:I->binary A2),
  COFE (Build_family R Sim1) -> COFE (Build_family R Sim2) ->
  COFE (prod_family_sim R Sim1 Sim2).
Proof.
  introv [[W1 T1 E1] C1] [[W2 T2 E2] C2]; simpls.
  constructor. constructor; simple~.
   intros. apply* prod2_equiv.
  intros K w Down Cohu. unfolds in Cohu. simpls. unfold prod2 in Cohu.
  forwards~ [l1 L1]: (C1 K (fun i => fst (w i))).
   intros_all. simpl. specializes Cohu i j. destruct (w j). destruct (w i). apply* Cohu.
  forwards~ [l2 L2]: (C2 K (fun i => snd (w i))).
   intros_all. simpl. specializes Cohu i j. destruct (w j). destruct (w i). apply* Cohu.
  exists (l1,l2). intros_all. unfolds limit. simpls. unfold prod2.
   specializes L1 i. specializes L2 i. destruct* (w i).
Qed.
  
Definition prod_family I A1 A2 (F1:family I A1) (F2:family I A2) :=
  prod_family_sim (family_r F1) (family_sim F1) (family_sim F2).

Lemma prod_cofe : forall I A1 A2 (F1:family I A1) (F2:family I A2),
  COFE F1 -> COFE F2 -> family_r F1 = family_r F2 ->
  COFE (prod_family F1 F2).   
Proof.
  introv Cofe1 Cofe2 Eqr. apply prod_cofe_sim. 
  destruct F1 as [R1 S1]. auto.
  destruct F2 as [R2 S2]. rewrite Eqr. auto.
Qed.

Lemma prod_similar : forall I A1 A2 (F1:family I A1) (F2:family I A2),
  prod2 (similar F1) (similar F2) = similar (prod_family F1 F2).
Proof.
  intros. unfold prod_family, prod_family_sim, similar. simpl.
  apply func_ext_2. intros [x1 x2] [y1 y2]. simpls.
  apply pred_conj_forall_distrib.
Qed.



(* ********************************************************************** *)
(** * Construction of fixed point combinators *)

(* ---------------------------------------------------------------------- *)
(** ** A generic fixed point combinator *)

(** [x] is a solution of the fixed point equation for [F], modulo [E],
    and is best fixed point with respect to the partial order [C]. *)

Definition Fix_prop A (E C:binary A) (F:A->A) (x:A) :=
  greatest C (fixed_point E F) x.

(** [Fix E C F] picks a fixed point, if it exists, for [F] *)

Definition Fix A {IA:Inhab A} (E C:binary A) (F:A->A) : A :=
  epsilon (Fix_prop E C F).

(** [Fix_prop E E F] is equivalent to [unique_fixed_point E F] *)

Lemma Fix_prop_iff_unique_fixed_point : forall A (E:binary A) (F:A->A) (x:A),
  (Fix_prop E E F x <-> unique_fixed_point E F x).
Proof.
  intros. iff [Fx Ux].
  split; intros y Hy. apply~ Fx. apply~ Ux.
  split; intros y Hy. apply~ Fx. apply~ Ux. 
Qed.

(** For partial functions, we use the following partial order *)

Definition lesser_fixed_point A B (E:binary B) (F:(A->B)->(A->B)) :=
  fun f g => 
      (generally_consistent_partial_fixed_point E F f -> extends E f g)
   /\ (consistent E g f).

(** The following lemmas prove the equiv between
    [optimal_fixed_point E F f] and
    [Fix_prop (partial_equiv E) (lesser_fixed_point E F) (partialize F) f]. *)

Lemma Fix_prop_from_optimal: 
  forall A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B),
  optimal_fixed_point E F f ->
  Fix_prop (partial_equiv E) (lesser_fixed_point E F) (partialize F) f.
Proof.
  introv [Gf Uf]. lets [Ff Cf]: Gf. split.
    rewrite~ partial_fixed_point_definitions in Ff.
    intros f' Ff'. split. intros Cf'. applys~ Uf. apply Gf.
     rewrite~ partial_fixed_point_definitions.
Qed.

Lemma Fix_prop_to_gc : 
  forall A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B),
  Fix_prop (partial_equiv E) (lesser_fixed_point E F) (partialize F) f ->
  generally_consistent_partial_fixed_point E F f.
Proof.
  introv [Ff Uf]. split.
    rewrite~ partial_fixed_point_definitions.
    intros f' Ff'. forwards~ [_ ?]: (Uf f').
     rewrite~ partial_fixed_point_definitions in Ff'.
Qed.

Lemma Fix_prop_to_optimal: 
  forall A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B),
  Fix_prop (partial_equiv E) (lesser_fixed_point E F) (partialize F) f ->
  optimal_fixed_point E F f.
Proof.
  introv Pf. lets [Ff Uf]: Pf. split.
    apply~ Fix_prop_to_gc.
    intros [f' P'] Gf'. apply~ Uf. destruct Gf' as [Ff' Cf'].
     rewrite~ partial_fixed_point_definitions in Ff'.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Specializations of the combinator *)

(** -------- Recursive values --------- *)

(** Pick a value [x] solution of [E x (F x)] *)

Definition FixValMod A {IA:Inhab A} (E:binary A) (F:A->A) : A :=
  Fix E E F.

(** Pick a value [x] solution of [x = (F x)] *)

Definition FixVal A {IA:Inhab A} (F:A->A) : A :=
  FixValMod eq F.

(** Pick a pair (x1,x2) solution of [x1 = F1 x1 X2] and [x2 = F2 x1 x2] *)

Definition mutualize2 A1 A2 
  (F1:A1->A2->A1) (F2:A1->A2->A2) : (A1*A2)->(A1*A2) :=
  fun (p:A1*A2) => let (x1,x2) := p in
  (F1 x1 x2, F2 x1 x2).

Definition FixValModMut2 A1 A2 {IA1:Inhab A1} {IA2:Inhab A2} 
 (E1:binary A1) (E2:binary A2) (F1:A1->A2->A1) (F2:A1->A2->A2) : A1*A2 := 
  FixValMod (prod2 E1 E2) (mutualize2 F1 F2).

(** -------- Recursive functions --------- *)

(** Pick a generally-consistent fixed point of the equation [E f (F f)] *)

Definition FixFunMod A B {IB:Inhab B} (E:binary B) (F:(A->B)->(A->B)) : A->B :=
  Fix (partial_equiv E) (lesser_fixed_point E F) (partialize F).

(** Pick a generally-consistent fixed point of the equation [f = (F f)]
    (note that we drop the domain of the domain of the solution,
    and keep only the support function). *)

Definition FixFun A B {IB:Inhab B} (F:(A->B)->(A->B)) : A->B :=
  FixFunMod eq F.

(** Functions of arity 2 *)

Definition FixFun2Mod B {IB:Inhab B} (E:binary B)
   A1 A2 (F:(A1->A2->B)->(A1->A2->B)) :=
  curry2 (FixFunMod E (fun f' => uncurry2 (F (curry2 f')))).

Definition FixFun2 B {IB:Inhab B} := FixFun2Mod eq.

(** Functions of arity 3 *)

Definition FixFun3Mod B {IB:Inhab B} (E:binary B)
  A1 A2 A3 (F:(A1->A2->A3->B)->(A1->A2->A3->B)) :=
  curry3 (FixFunMod E (fun f' => uncurry3 (F (curry3 f')))).

Definition FixFun3 B {IB:Inhab B} := FixFun3Mod eq.


(* ---------------------------------------------------------------------- *)
(** ** Fixed point equation for the combinators *)

(** -------- Recursive values --------- *)

(** To show that [FixVal E F] is a fixed point modulo [E]
    that satifies a continuous invariant [Q], it suffices to 
    find a complete ordered family of equiv [M] such that [F] 
    is contractive with the invariant [Q], and that the 
    equiv [E] is the same as the similarity relation induced
    by [M] (the intersection of the similarities at all level). *)

Lemma FixValMod_fix_inv : forall I A {IA:Inhab A} (M:family I A)
  (E:binary A) (F:A->A) (Q:I->A->Prop) (x:A),
  x = FixValMod E F -> E = similar M ->
  COFE M -> continuous M Q -> contractive M F Q ->
  E x (F x) /\ forall i, (Q i x).
Proof.
  introv Defx SimE Cofe Conti Contr.
  unfolds FixValMod, Fix. spec_epsilon as y [Fixy Uniy].
    forwards* (y&Fixy&Inv): cofe_fixed_point.
    exists y. apply <- Fix_prop_iff_unique_fixed_point.
     rewrite~ SimE.
  subst x. logic (forall U V:Prop,U->(U->V)->U/\V).
  apply Fixy. rewrite SimE. apply~ refl_elim. 
  intros Ey. applys~ (>> invariant_on_fixed_point I A M F).
    apply~ contractive_to_invariant.
    rewrite~ <- SimE.
Qed.

(** Same without invariant *)

Lemma FixValMod_fix : forall I A (M:family I A) 
  {IA:Inhab A} (E:binary A) (F:A->A) (x:A),
  x = FixValMod E F -> E = similar M ->
  COFE M -> contractive_noinv M F -> E x (F x).
Proof.
  intros. applys* (@FixValMod_fix_inv I A IA M E F post_true x).
  intros_all~. apply~ contractive_noinv_to_contractive.
Qed.

Implicit Arguments FixValMod_fix [I A [IA] E F x].

(** Same for Leibnitz equality *)

Lemma FixVal_fix_inv : forall I A {IA:Inhab A} (M:family I A)
  (E:binary A) (F:A->A) (Q:I->A->Prop) (x:A),
  x = FixVal F -> eq = similar M ->
  COFE M -> continuous M Q -> contractive M F Q ->
  x = F x /\ forall i, (Q i x).
Proof. intros. applys* FixValMod_fix_inv. Qed.

(** Same without invariant for Leibnitz equality *)

Lemma FixVal_fix : forall I A {IA:Inhab A} 
  (M:family I A) (E:binary A) (F:A->A) (x:A),
  x = FixVal F -> eq = similar M ->
  COFE M -> contractive_noinv M F ->
  x = F x.
Proof. intros. applys* (@FixValMod_fix _ _ M _ eq). Qed.


(** -------- Mutually-recursive values --------- *)

Definition valmut2_contractive I A1 A2 (M:family I (A1*A2)) 
  (F1:A1->A2->A1) (F2:A1->A2->A2) (Q:I->A1->A2->Prop) :=
  forall i x1 x2 y1 y2, 
  (forall j, family_r M j i -> 
    family_sim M j (x1,x2) (y1,y2) /\ Q j x1 x2 /\ Q j y1 y2) ->
  family_sim M i (F1 x1 x2, F2 x1 x2) (F1 y1 y2, F2 y1 y2) 
          /\ Q i (F1 x1 x2) (F2 x1 x2).

Definition valmut2_continuous I A1 A2 (M:family I (A1*A2)) (Q:I->A1->A2->Prop) :=
  forall (K:I->Prop) (u:I->A1*A2) (l1:A1) (l2:A2), 
  limit M K u (l1,l2) ->
  (forall i, K i -> let (x1,x2) := u i in Q i x1 x2) ->  
  forall i, K i -> Q i l1 l2.

Lemma FixValModMut2_fix_inv : forall I A1 A2 {IA1:Inhab A1} {IA2:Inhab A2}
  (M:family I (A1*A2)) (E1:binary A1) (E2:binary A2) (F1:A1->A2->A1) 
  (F2:A1->A2->A2) (Q:I->A1->A2->Prop) (x1:A1) (x2:A2),
  (x1,x2) = FixValModMut2 E1 E2 F1 F2 -> prod2 E1 E2 = similar M ->
  COFE M -> valmut2_continuous M Q -> valmut2_contractive M F1 F2 Q ->
  E1 x1 (F1 x1 x2) /\ E2 x2 (F2 x1 x2) /\ forall i, (Q i x1 x2).
Proof.
  introv Defx SimE Cofe Conti Contr.
  forwards~ [H1 H2]: (@FixValMod_fix_inv I (A1*A2) _ M (prod2 E1 E2) (mutualize2 F1 F2) 
    (fun i p => let (a1,a2) := p in Q i a1 a2) (x1,x2)).
  intros K u [l1 l2] L uQ i Ki. applys~ Conti.
  clears x1 x2. intros i [x1 x2] [y1 y2] H. simple~.
  inversion~ H1.
Qed.

Definition valmut2_contractive_noinv I A1 A2 (M:family I (A1*A2)) 
  (F1:A1->A2->A1) (F2:A1->A2->A2) :=
  forall i x1 x2 y1 y2, 
  (forall j, family_r M j i -> family_sim M j (x1,x2) (y1,y2)) ->
  family_sim M i (F1 x1 x2, F2 x1 x2) (F1 y1 y2, F2 y1 y2).

Lemma FixValModMut2_fix : forall I A1 A2 {IA1:Inhab A1} {IA2:Inhab A2}
  (M:family I (A1*A2)) (E1:binary A1) (E2:binary A2) (F1:A1->A2->A1) 
  (F2:A1->A2->A2) (x1:A1) (x2:A2),
  (x1,x2) = FixValModMut2 E1 E2 F1 F2 -> prod2 E1 E2 = similar M -> 
  COFE M -> valmut2_contractive_noinv M F1 F2 ->
  E1 x1 (F1 x1 x2) /\ E2 x2 (F2 x1 x2).
Proof.
  introv Defx SimE Cofe Contr.
  forwards~ (H1&H2&_): (@FixValModMut2_fix_inv I A1 A2 _ _ M E1 E2 F1 F2 (fun _ _ _ => True) x1 x2).
   intros_all. forwards~ Z: Contr. intros. forwards*: H.
Qed.

Implicit Arguments FixValModMut2_fix [I A1 A2 [IA1] [IA2] F1 F2 x1 x2].

(* todo: express continuity with two invariants *)

(** -------- Recursive functions --------- *)

(* todo: comment and use in the next proof *)

Lemma FixFunMod_elim : 
  forall A (P:A->Prop) B {IB:Inhab B} (F:(A->B)->(A->B)) (E:binary B) (f f':A->B), 
  f = FixFunMod E F -> equiv E ->
  generally_consistent_partial_fixed_point E F (Build_partial f' P) ->
  pfunc_equiv E P f' f.
Proof.
  introv Deff Equiv Gcf'. 
  unfolds FixFunMod, Fix. spec_epsilon as g [Fixg Bestg].
    forwards* [g Opt]: (@optimal_fixed_point_exists _ _ _ E F).
    exists g. apply~ Fix_prop_from_optimal.
  subst f.  
  lets Fixf: (proj1 Gcf'). lets Fixf': (partial_fixed_point_elim Fixf).
  rewrite partial_fixed_point_definitions in Fixf.
  lets [ED MG]: (Bestg _ Fixf). forwards~ [Dom Equ]: ED. 
Qed.

(** To show that [FixFun E F] is a fixed point modulo [E], on a domain [P],
    that satifies a invariant [S] (compatible with [E]), it suffices to 
    find a well-founded relation [R] such that [F] is a contractive 
    function with respect to [R] using the invariant [S]. *)

Lemma FixFunMod_fix_partial_inv : forall A (R:binary A) (P:A->Prop)
  B (S:A->B->Prop) {IB:Inhab B} (F:(A->B)->(A->B)) (E:binary B) (f:A->B), 
  f = FixFunMod E F -> equiv E -> (forall x, pred_compatible E (S x)) ->
  wf R -> rec_contractive E P F R S ->
  (forall x, P x -> E (f x) (F f x)) /\
  (forall x, P x -> S x (f x)).
Proof.
  introv Deff Equiv Comp Wfr Contr.
  unfolds FixFunMod, Fix. spec_epsilon as g [Fixg Bestg].
    forwards* [g Opt]: (@optimal_fixed_point_exists _ _ _ E F).
    exists g. apply~ Fix_prop_from_optimal.
  subst f.
  forwards~ (f&Fixf&Inv): (@rec_fixed_point _ _ _ F R P S E).
  lets Fixf': Fixf. rewrite partial_fixed_point_definitions in Fixf'.
  lets Fixf'': (partial_fixed_point_elim Fixf).
  lets [ED MG]: (Bestg _ Fixf').
  forwards [Dom Equ]: ED.
    eapply rec_fixed_point_generally_consistent with (R:=R); eauto.
    clear ED.
  simpls. split; introv Px. apply~ Fixf. apply* Comp.
Qed.

(** Same without invariant *)

Lemma FixFunMod_fix_partial : forall A (R:binary A) (P:A->Prop)
  B {IB:Inhab B} (F:(A->B)->(A->B)) (E:binary B) (f:A->B), 
  f = FixFunMod E F -> equiv E -> 
  wf R -> rec_contractive_noinv E P F R ->
  (forall x, P x -> E (f x) (F f x)).
Proof.
  introv Def Equiv Wf Cont.
  forwards~ [H _]: (@FixFunMod_fix_partial_inv A R P B post_true IB F E f Def).
  apply~ rec_contractive_noinv_to_rec_contractive.
Qed.

(** Same for Leibnitz' equality *)

Lemma FixFun_fix_partial_inv : forall A (R:binary A) (P:A->Prop) B 
  (S:A->B->Prop) {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B), 
  f = FixFun F -> wf R -> rec_contractive eq P F R S ->
  (forall x, P x -> f x = F f x) /\
  (forall x, P x -> S x (f x)).
Proof. intros. applys* (@FixFunMod_fix_partial_inv A R). intros_all. subst~. Qed.

Implicit Arguments FixFun_fix_partial_inv [A B [IB] F f].

Lemma FixFun_fix_inv : forall A (R:binary A) B 
  (S:A->B->Prop) {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B), 
  f = FixFun F -> wf R -> 
  (forall f1 f2 x, 
    (forall y, R y x -> (f1 y) = (f2 y) /\ S y (f1 y)) -> 
    (F f1 x) = (F f2 x) /\ S x (F f1 x)) ->
  (forall x, f x = F f x) /\
  (forall x, S x (f x)).
Proof. intros. forwards~ [K1 K2]: (FixFun_fix_partial_inv R pred_true S). subst~. Qed.

Implicit Arguments FixFun_fix_inv [A B [IB] F f].

Lemma FixFun_fix_partial : forall A (R:binary A) (P:A->Prop)
   B {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B), 
  f = FixFun F -> wf R -> rec_contractive_noinv eq P F R ->
  (forall x, P x -> f x = F f x).
Proof.
  introv Def Wf Cont. forwards~ [H _]: (@FixFun_fix_partial_inv A R P B post_true).
  apply~ rec_contractive_noinv_to_rec_contractive. subst~.
Qed.

Implicit Arguments FixFun_fix_partial [A B [IB] F f].

Lemma FixFun_fix : forall A (R:binary A) B {IB:Inhab B} (F:(A->B)->(A->B)) 
   (f:A->B), 
  f = FixFun F -> wf R -> 
  (forall f1 f2 x, 
    (forall y, R y x -> f1 y = f2 y) ->
    F f1 x = F f2 x) ->
  (forall x, f x = F f x).
Proof.
  intros. apply FixFun_fix_partial with (IB:=IB) (R:=R) (P:=pred_true); auto.
  hnf; auto*.
Qed. 

Implicit Arguments FixFun_fix [A B [IB] F f].

(* todo: comment *)

Lemma FixFun_fix_partial' : forall A (R:binary A) (P:A->Prop)
  B {IB:Inhab B} (F:(A->B)->(A->B)) (f' f:A->B), 
  f = FixFun F -> wf R -> rec_contractive' eq P F R f' ->
  fixed_point (pfunc_equal P) F f' ->
  (forall x, P x -> f x = F f x).
Proof.
  introv Df W Cont Fixf'. applys Fixf' (Build_partial f P). simpl.
  applys~ FixFunMod_elim F. applys~ rec_fixed_point_generally_consistent' R.
Qed.


(** -------- Mixed Corecursive and Recursive functions --------- *)

(** To show that [FixFun E F] is a fixed point modulo [E], on a domain [P],
    that satifies a invariant [S] (compatible with [E]), it suffices to 
    find a complete ordered family of equiv [M] such that [F] 
    is a contractive function using the invariant [S] with respect
    to a well-founded relation [R]. *)

Lemma FixFunMod_mixed_partial_inv : forall I A B  
  (M:family I B) (R:binary A) (P:A->Prop) (S:I->A->B->Prop)  
  (E:binary B) {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B),
  f = FixFunMod E F -> E = similar M -> 
  COFE M -> wf R -> 
  mixed_continuous M S -> mixed_contractive M P F R S -> 
  (forall x, P x -> E (f x) (F f x)) /\
  (forall x i, P x -> S i x (f x)).
Proof.
  introv Deff SimE Cofe Wrr Conti Contr.
  asserts Equiv: (equiv E). rewrite~ SimE.
  unfolds FixFunMod, Fix. spec_epsilon as g [Fixg Bestg].
    forwards* [g Opt]: (@optimal_fixed_point_exists _ _ _ E F).  
    exists g. apply~ Fix_prop_from_optimal.
  subst f.
  forwards~ (f&Fixf&Inv): (@mixed_fixed_point _ _ _ _ M E P F R S).
  lets Fixf': Fixf. rewrite partial_fixed_point_definitions in Fixf'.
  lets Fixf'': (partial_fixed_point_elim Fixf).
  lets [ED MG]: (Bestg _ Fixf').
  forwards [Dom Equ]: ED.
    eapply mixed_fixed_point_generally_consistent with (R:=R); eauto.
    clear ED.
  simpls. split; introv Px. apply~ Fixf. apply* Conti.
   introv Rji. rewrite SimE in Equ. apply~ Equ.
Qed.

Implicit Arguments FixFunMod_mixed_partial_inv [I A B [IB] F f].

Lemma FixFunMod_mixed_partial : forall I A B  
  (M:family I B) (R:binary A) (P:A->Prop)  
  (E:binary B) {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B),
  f = FixFunMod E F -> E = similar M -> 
  COFE M -> wf R -> 
  mixed_contractive_noinv M P F R -> 
  (forall x, P x -> E (f x) (F f x)).
Proof. 
  introv Def Equiv Cofe Wf Trans Cont.
  forwards~ [H _]: (@FixFunMod_mixed_partial_inv I A B M R P (fun _ _ _ => True) E IB F f Def).
  apply~ mixed_contractive_noinv_to_mixed_contractive.
Qed.

Implicit Arguments FixFunMod_mixed_partial [I A B [IB] F f].


(** -------- Corecursive functions --------- *)

(** Fixed point result for corecursive functions with invariants *)

Definition corec_contractive I A B (M:family I B) (P:A->Prop) 
 (F:(A->B)->(A->B)) (S:I->B->Prop) :=
  forall i x f1 f2, P x -> 
  (forall y j, P y -> family_r M j i ->
     family_sim M j (f1 y) (f2 y) /\ S j (f1 y) /\ S j (f2 y)) -> 
  family_sim M i (F f1 x) (F f2 x) /\ S i (F f1 x).

Lemma FixFunMod_corec_inv : forall I A B (M:family I B) 
  (P:A->Prop) (S:I->B->Prop) {IB:Inhab B} (E:binary B)  
  (F:(A->B)->(A->B)) (f:A->B),
  f = FixFunMod E F -> E = similar M -> COFE M -> 
  (forall i y1 y2, S i y1 ->
     (forall j, family_r M j i -> family_sim M j y1 y2) ->
     S i y2) ->
  corec_contractive M P F S -> 
  (forall x, P x -> E (f x) (F f x)) /\
  (forall x i, P x -> S i (f x)).
Proof.
  introv Deff SimE Cofe Conti Contr.
  eapply FixFunMod_mixed_partial_inv with (S:=fun i x y => S i y) (R:=@empty A); 
   auto~. 
Qed.

(** Without invariant *)

Definition corec_contractive_noinv I A B (M:family I B) (P:A->Prop) 
 (F:(A->B)->(A->B)) :=
  forall i x f1 f2, P x -> 
  (forall y j, P y -> family_r M j i -> family_sim M j (f1 y) (f2 y)) -> 
  family_sim M i (F f1 x) (F f2 x).

Lemma FixFunMod_corec : forall I A B (M:family I B) 
  (P:A->Prop) {IB:Inhab B} (E:binary B)  
  (F:(A->B)->(A->B)) (f:A->B),
  f = FixFunMod E F -> E = similar M -> COFE M -> 
  corec_contractive_noinv M P F -> 
  (forall x, P x -> E (f x) (F f x)).
Proof.
  introv Deff SimE Cofe Contr.
  forwards H _: (@FixFunMod_corec_inv I A B M P post_true _ E F); auto~.
  intros_all~. split~. applys* Contr f1 f2. intros. forwards*: H0.
  subst~.
Qed.

Implicit Arguments FixFunMod_corec [I A B [IB] E F f].

Lemma FixFunMod_corec_total : forall I A B (M:family I B) 
  {IB:Inhab B} (E:B->B->Prop)  
  (F:(A->B)->(A->B)) (f:A->B),
  f = FixFunMod E F -> E = similar M -> COFE M -> 
  (forall i x f1 f2, 
    (forall y j, family_r M j i -> family_sim M j (f1 y) (f2 y)) -> 
    family_sim M i (F f1 x) (F f2 x)) ->
  (forall x, E (f x) (F f x)).
Proof.
  intros. asserts~ K: (pred_true x). gen x. apply* FixFunMod_corec.
  intros_all~.
Qed.

Implicit Arguments FixFunMod_corec_total [I A B [IB] E F f].


(** -------- Recursive functions of arity 2 --------- *)

Lemma FixFun2Mod_fix_partial_inv : forall A1 A2 (R:binary (A1*A2)) (P:A1->A2->Prop)
  B {IB:Inhab B} (S:A1->A2->B->Prop) (E:binary B) F (f:A1->A2->B), 
  f = FixFun2Mod E F -> wf R -> equiv E ->
  (forall x1 x2, pred_compatible E (S x1 x2)) ->
  (forall x1 x2 f1 f2, P x1 x2 ->   
    (forall y1 y2, P y1 y2 -> R (y1,y2) (x1,x2) -> 
      E (f1 y1 y2) (f2 y1 y2) /\ S y1 y2 (f1 y1 y2)) ->
     E (F f1 x1 x2) (F f2 x1 x2) /\ S x1 x2 (F f1 x1 x2)) ->
  (forall x1 x2, P x1 x2 -> E (f x1 x2) (F f x1 x2)) /\ 
  (forall x1 x2, P x1 x2 -> S x1 x2 (f x1 x2)).
Proof.
  introv Eqf WfR Equiv Comp Cont. 
  sets F': (fun f' => uncurry2 (F (curry2 f'))).
  forwards~ [H1 H2]: (@FixFunMod_fix_partial_inv (A1*A2)%type R (fun p => P (fst p) (snd p)) B
    (fun p => S (fst p) (snd p)) IB F' E).
    intros f1 f2 [x1 x2] Px H. simpls. apply~ Cont.
    intros y1 y2 Py Ryx. apply~ (H (y1,y2)). 
  subst f. split. 
    intros x1 x2 Px. apply~ (H1 (x1,x2)).
    intros x1 x2 Px. apply~ (H2 (x1,x2)).
Qed.

Lemma FixFun2Mod_fix_partial : forall A1 A2 (R:binary (A1*A2)) (P:A1->A2->Prop)
  B {IB:Inhab B} (S:A1->A2->B->Prop) (E:binary B) F (f:A1->A2->B), 
  f = FixFun2Mod E F -> wf R -> equiv E ->
  (forall x1 x2, pred_compatible E (S x1 x2)) ->
  (forall x1 x2 f1 f2, P x1 x2 ->   
    (forall y1 y2, P y1 y2 -> R (y1,y2) (x1,x2) -> 
      E (f1 y1 y2) (f2 y1 y2) /\ S y1 y2 (f1 y1 y2)) ->
     E (F f1 x1 x2) (F f2 x1 x2) /\ S x1 x2 (F f1 x1 x2)) ->
  (forall x1 x2, P x1 x2 -> E (f x1 x2) (F f x1 x2)) /\ 
  (forall x1 x2, P x1 x2 -> S x1 x2 (f x1 x2)).
Proof.
  introv Eqf WfR Equiv Comp Cont. 
  sets F': (fun f' => uncurry2 (F (curry2 f'))).
  forwards~ [H1 H2]: (@FixFunMod_fix_partial_inv (A1*A2)%type R (fun p => P (fst p) (snd p)) B
    (fun p => S (fst p) (snd p)) IB F' E).
    intros f1 f2 [x1 x2] Px H. simpls. apply~ Cont.
    intros y1 y2 Py Ryx. apply~ (H (y1,y2)). 
  subst f. split. 
    intros x1 x2 Px. apply~ (H1 (x1,x2)).
    intros x1 x2 Px. apply~ (H2 (x1,x2)).
Qed.

Lemma FixFun2_fix_partial_inv : forall A1 A2 (R:binary (A1*A2)) (P:A1->A2->Prop)
  B (S:A1->A2->B->Prop) {IB:Inhab B} F (f:A1->A2->B), 
  f = FixFun2 F -> wf R -> 
  (forall x1 x2 f1 f2, P x1 x2 ->   
    (forall y1 y2, P y1 y2 -> R (y1,y2) (x1,x2) -> 
       f1 y1 y2 = f2 y1 y2 /\ S y1 y2 (f1 y1 y2)) ->
     F f1 x1 x2 = F f2 x1 x2 /\ S x1 x2 (F f1 x1 x2)) ->
  (forall x1 x2, P x1 x2 -> f x1 x2 = F f x1 x2) /\ 
  (forall x1 x2, P x1 x2 -> S x1 x2 (f x1 x2)).
Proof.
  intros. eapply FixFun2Mod_fix_partial with (E:=eq) (R:=R); auto~.
    intros_all. subst~.
Qed.

Lemma FixFun2_fix_partial : forall A1 A2 (R:binary (A1*A2)) (P:A1->A2->Prop)
  B {IB:Inhab B} F (f:A1->A2->B), 
  f = FixFun2 F -> wf R -> 
  (forall x1 x2 f1 f2, P x1 x2 ->   
    (forall y1 y2, P y1 y2 -> R (y1,y2) (x1,x2) -> f1 y1 y2 = f2 y1 y2) ->
     F f1 x1 x2 = F f2 x1 x2) ->
  (forall x1 x2, P x1 x2 -> f x1 x2 = F f x1 x2).
Proof.
  intros. forwards [K _]: (@FixFun2_fix_partial_inv A1 A2 R P B (fun _ _ _ => True) _ F); auto~.
  intros_all. split~. applys~ H1 f1 f2. intros. forwards*: H4.
  subst~. 
Qed.

Implicit Arguments FixFun2_fix_partial [A1 A2 B [IB] F f].

Lemma FixFun2_fix : forall A1 A2 (R:binary (A1*A2)) 
  B {IB:Inhab B} F (f:A1->A2->B), 
  f = FixFun2 F -> wf R -> 
  (forall x1 x2 f1 f2,
    (forall y1 y2, R (y1,y2) (x1,x2) -> f1 y1 y2 = f2 y1 y2) ->
     F f1 x1 x2 = F f2 x1 x2) ->
  (forall x1 x2, f x1 x2 = F f x1 x2).
Proof. intros. applys* (FixFun2_fix_partial R (fun _ _ => True)). Qed.

Implicit Arguments FixFun2_fix [A1 A2 B IB F f].

Lemma FixFun2Mod_corec : forall I A1 A2 B (M:family I B) {IB:Inhab B}
  (E:binary B) F (f:A1->A2->B), 
  f = FixFun2Mod E F -> E = similar M -> COFE M -> 
  (forall i x1 x2 f1 f2,
    (forall j y1 y2, family_r M j i ->
     family_sim M j (f1 y1 y2) (f2 y1 y2)) ->
     family_sim M i (F f1 x1 x2) (F f2 x1 x2)) ->
  forall x1 x2, E (f x1 x2) (F f x1 x2).
Proof.
  introv Eqf Esim Cofe Cont.
  sets F': (fun f' => uncurry2 (F (curry2 f'))).
  forwards~ [H1 H2]: (@FixFunMod_corec_inv I (A1*A2)%type B M  
    (fun _ => True) (fun _ _ => True) IB E F').
    intros i [x1 x2] f1 f2 Px H. simpls. split~. apply~ Cont.
    intros j y1 y2 Ryx. apply~ (H (y1,y2)). 
  subst f. intros x1 x2. apply~ (H1 (x1,x2)).
Qed.

Implicit Arguments FixFun2Mod_corec [I A1 A2 B [IB] E F f].

(** -------- Recursive functions of arity 3 --------- *)

(* TODO: complete *)

Lemma FixFun3_fix_partial : forall A1 A2 A3 (R:binary (A1*A2*A3)) (P:A1->A2->A3->Prop)
  B {IB:Inhab B} F (f:A1->A2->A3->B), 
  f = FixFun3 F -> wf R -> 
  (forall x1 x2 x3 f1 f2, P x1 x2 x3 ->   
    (forall y1 y2 y3, P y1 y2 y3 -> R (y1,y2,y3) (x1,x2,x3) -> f1 y1 y2 y3 = f2 y1 y2 y3) ->
     F f1 x1 x2 x3 = F f2 x1 x2 x3) ->
  (forall x1 x2 x3, P x1 x2 x3 -> f x1 x2 x3 = F f x1 x2 x3).
Admitted. (* TODO: copy-paste the above *)

Implicit Arguments FixFun3_fix_partial [A1 A2 A3 B IB F f].


(** -------- Induction principles --------- *)

(** Induction principle for recursive fixed points modulo *)

Lemma rec_ind : forall A B F (E:binary B) (P:A->Prop) (R:binary A) (f:A->B) (S:A->B->Prop),
  (forall x, P x -> E (f x) (F f x)) ->
  (forall x, pred_compatible E (S x)) ->
  wf R ->
  (forall x f', P x -> 
     (forall y, P y -> R y x -> S y (f' y)) ->
     S x (F f' x)) -> 
  forall x, P x -> S x (f x).
Proof.
  introv Eqf Comp WfR Red. intros x. induction_wf IH: WfR x.
  intros Px. eapply Comp. apply~ Red. apply~ Eqf.
Qed.

(** Induction principle for recursive fixed points *)

Lemma rec_eq_ind : forall A B F (P:A->Prop) (R:binary A) (f:A->B) (S:A->B->Prop),
  (forall x, P x -> f x = F f x) ->
  wf R ->
  (forall x f', P x -> 
     (forall y, P y -> R y x -> S y (f' y)) ->
     S x (F f' x)) -> 
  forall x, P x -> S x (f x).
Proof.
  introv Eqf WfR Red Px. applys~ (>> rec_ind A R Eqf __). 
    intros_all. subst~. 
Qed.

(** Induction principle for corecursive fixed points modulo *)

Lemma corec_ind : forall I A {IA:Inhab A} (E:binary A)
  (M:family I A) (F:A->A) (Q:I->A->Prop) (x:A),
  COFE M -> continuous M Q -> E x (F x) -> E = similar M ->
  (forall i, (forall j, family_r M j i -> Q j x) -> Q i (F x)) ->
  forall i, Q i x. 
Proof.
  introv IA Cofe Conti Eqf SimE Red. subst E.
  intros i. induction_wf IH: (ofe_wf Cofe) i.
  apply~ (Conti (large (flip (family_r M)) i) (fun _ => F x)).
    intros_all. apply~ equiv_sym.
    intros j Rji. apply Red. intros k Rkj.
     apply IH. destruct Rji as [Rji|Eq]. apply* (trans_elim j). subst~.
Qed.

(** Induction principle for mixed fixed points *)

Lemma mixed_ind : forall I A B (E:binary B)
  (M:family I B) (P:A->Prop) 
  (F:(A->B)->(A->B)) (R:binary A) (S:I->A->B->Prop) (f:A->B),
  (forall x, P x -> E (f x) (F f x)) -> E = similar M ->
  COFE M -> well_founded R -> mixed_continuous M S -> 
  (forall i x, (forall j y, P y -> lexico2 (family_r M) R (j,y) (i,x) -> S j y (f y)) -> S i x (F f x)) ->
  (forall i x, P x -> S i x (f x)).
Proof.
  introv Eqf Equiv Cofe Wfr Cont Inv. intros i x.
  sets_eq p: (i, x). gen i x.
  induction_wf: (lexico2_wf (ofe_wf Cofe) (tclosure_wf Wfr)) p. 
  intros i x Eix. destruct p. inversions Eix. intros Px.
  eapply Cont with (y1 := F f x). apply Inv. intros.
    apply* IH.
     forwards*: (>> lexico2_incl I A (family_r M) (family_r M) R (tclosure R) (j,y) (i,x)).
    intros. apply~ equiv_sym. apply~ Eqf.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Useful lemmas about c.o.f.e. *)

Lemma cofe_similar_modulo : forall I A (M:family I A) x y x' y' i,
  COFE M ->
  similar M x x' -> 
  similar M y y' -> 
  family_sim M i x' y' -> 
  family_sim M i x y.
Proof.
  intros. apply* (trans_elim x'). apply* (trans_sym_2 y').
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Extraction for Caml *)

Extraction Language Ocaml.

Extract Constant FixFunMod => 
  "(fun bigf -> let rec f x = bigf f x in f)".

Extract Constant FixValMod => 
  "(fun bigf -> let rec x = lazy (Lazy.force (bigf x)) in x)".

Extract Constant FixValModMut2 =>
 "(fun f1 f2 ->
  let rec x1 = lazy (Lazy.force (f1 x1 x2))  
      and x2 = lazy (Lazy.force (f2 x1 x2)) in 
  Pair (x1,x2))".

(* optional 
Extraction Inline FixFunMod.
Extraction Inline FixValMod.
Extraction Inline FixValModMut2.
*)

(* ---------------------------------------------------------------------- *)
(** ** Extraction for Haskell *)

Extraction Language Haskell.

Extract Constant Fix =>
  "(fun bigf => let x = bigf x in x)".


(* ---------------------------------------------------------------------- *)
(** ** Re-establish automation *)

Ltac auto_tilde ::= auto_tilde_default.
