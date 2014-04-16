(**************************************************************************
* TLC: A library for Coq                                                  *
* Shared definitions for containers                                       *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect 
  LibRelation LibOperation LibInt LibStruct.
Generalizable Variables A B K T.

(* ********************************************************************** *)
(** * Operators *)

(* ---------------------------------------------------------------------- *)
(** ** Definitions *)

Class BagEmpty T := { empty : T }.
Class BagSingle A T := { single : A -> T }.
Class BagSingleBind A B T := { single_bind : A -> B -> T }.
Class BagIn A T := { is_in : A -> T -> Prop }.
Class BagBinds A B T := { binds : T -> A -> B -> Prop }.
Class BagRead A B T := { read : T -> A -> B }. 
Class BagUpdate A B T := { update : T -> A -> B -> T }.
Class BagUnion T := { union : T -> T -> T }.
Class BagInter T := { inter : T -> T -> T }.
Class BagIncl T := { incl : binary T }.
Class BagDisjoint T := { disjoint : binary T }.
Class BagRestrict T K := { restrict : T -> K -> T }.
Class BagRemove T K := { remove : T -> K -> T }.
Class BagFold I F T := { fold : monoid_def I -> F -> T -> I }.
Class BagCard T := { card : T -> nat }.
Class BagDom T Ks := { dom : T -> Ks }.
Class BagIndex T A := { index : T -> A -> Prop }.

Definition notin `{BagIn A T} x m :=
  ~ (is_in x m).


(* ---------------------------------------------------------------------- *)
(** ** Notation *)

Notation "\{}" := (empty) 
  : container_scope.
Notation "\{ x }" := (single x) 
  : container_scope.
Notation "x '\in' m" := (is_in x m) 
  (at level 39) : container_scope.
Notation "x '\notin' E" := (notin x E) 
  (at level 39) : container_scope.
Notation "x \:= v" := (single_bind x v) 
  (at level 29) : container_scope.
Notation "m \( x )" := (read m x)
  (at level 33, format "m \( x )") : container_scope.
Notation "m \( x := v )" := (update m x v)
  (at level 33, format "m \( x := v )") : container_scope.
(* todo :
Notation "m \[ x ]" := (read m x)
  (at level 29) : container_scope.
Notation "m \[ x := v ]" := (update m x v)
  (at level 29) : container_scope.
*)

Notation "m1 '\c' m2" := (incl m1 m2)  
  (at level 38) : container_scope.
Notation "m1 '\u' m2" := (union m1 m2)
  (at level 37, right associativity) : container_scope.
Notation "m1 '\n' m2" := (inter m1 m2)
  (at level 36, right associativity) : container_scope.
Notation "m1 '\-' m2" := (remove m1 m2)
  (at level 35) : container_scope.
Notation "m1 '\|' m2" := (restrict m1 m2)
  (at level 34) : container_scope.
Notation "m1 '\#' m2" := (disjoint m1 m2)
  (at level 37, right associativity) : container_scope.

Open Scope container_scope.

(* todo: bug with spaces *)
Notation "''{' x '}'" := (single x) (format "''{' x '}'")
  : container_scope.

Notation "M \-- i" := (M \- \{i}) (at level 35) : container_scope.

(* ---------------------------------------------------------------------- *)
(** ** [forall x \in E, P x] notation *)

Notation "'forall_' x '\in' E ',' P" := 
  (forall x, x \in E -> P)
  (at level 200, x ident) : container_scope.
Notation "'forall_' x y '\in' E ',' P" := 
  (forall x y, x \in E -> y \in E -> P)
  (at level 200, x ident, y ident) : container_scope.
Notation "'forall_' x y z '\in' E ',' P" := 
  (forall x y z, x \in E -> y \in E -> z \in E -> P)
  (at level 200, x ident, y ident, z ident) : container_scope.

(* ---------------------------------------------------------------------- *)
(** ** [exists x \in E st P x] notation *)

Notation "'exists_' x '\in' E ',' P" := 
  (exists x, x \in E /\ P)
  (at level 200, x ident) : container_scope.
Notation "'exists_' x y '\in' E ',' P" := 
  (exists x, x \in E /\ y \in E /\ P)
  (at level 200, x ident, y ident) : container_scope.
Notation "'exists_' x y z '\in' E ',' P" := 
  (exists x, x \in E /\ y \in E /\ z \in E /\ P)
  (at level 200, x ident, y ident, z ident) : container_scope.

(* ---------------------------------------------------------------------- *)
(** ** Foreach *)

Definition foreach `{BagIn A T} (P:A->Prop) (E:T) :=
  forall x, x \in E -> P x.

(* ---------------------------------------------------------------------- *)
(** ** [index] for natural numbers *)


Instance int_index : BagIndex int int.
Proof. intros. constructor. exact (fun n (i:int) => 0 <= i < n). Defined.

Lemma int_index_def : forall (n i : int),
  index n i = (0 <= i < n).
Proof. auto. Qed. 

Global Opaque int_index.

Lemma int_index_le : forall i n m : int,
  index n i -> n <= m -> index m i.
Proof. introv. do 2 rewrite @int_index_def. math. Qed.

Lemma int_index_prove : forall (n i : int),
  0 <= i -> i < n -> index n i.
Proof. intros. rewrite~ int_index_def. Qed.

Lemma int_index_succ : forall n i, n >= 0 ->
  index (n + 1) i = (index n i \/ i = n).
Proof.
  introv P. do 2 rewrite int_index_def. extens. iff H.   
  apply classic_left. math.
  destruct H; math. 
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Derivable *)

(** Bag update can be defined as bag union with a singleton bag *)

Instance bag_update_as_union_single : forall A B T
  `{BagSingleBind A B T} `{BagUnion T},
  BagUpdate A B T.
  constructor. apply (fun m k v => m \u (k \:= v)). Defined.

Global Opaque bag_update_as_union_single.


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

(** Membership *)

Class In_empty_eq `{BagIn A T, BagEmpty T} :=
  { in_empty_eq : forall x, x \in \{} = False }.
Class In_empty `{BagIn A T, BagEmpty T} :=
  { in_empty : forall x, x \in \{} -> False }.

Implicit Arguments in_empty [[A] [T] [H] [H0] [In_empty]].

Class In_single_eq `{BagIn A T, BagSingle A T} :=
  { in_single_eq : forall x y, x \in \{y} = (x = y) }.
Class In_single `{BagIn A T, BagSingle A T} :=
  { in_single : forall x y, x \in \{y} -> x = y }.
Class In_single_self `{BagIn A T, BagSingle A T} :=
  { in_single_self : forall x, x \in \{x} }.

Implicit Arguments in_single_eq [[A] [T] [H] [H0] [In_single_eq]].
Implicit Arguments in_single [[A] [T] [H] [H0] [In_single] x y].
Implicit Arguments in_single_self [[A] [T] [H] [H0] [In_single_self]].

Class In_union_eq `{BagIn A T, BagUnion T} :=
  { in_union_eq : forall x (E F : T), x \in (E \u F) = (x \in E \/ x \in F) }.
Class In_union_l `{BagIn A T, BagUnion T} :=
  { in_union_l : forall x E F, x \in E -> x \in (E \u F) }.
Class In_union_r `{BagIn A T, BagUnion T} :=
  { in_union_r : forall x E F, x \in F -> x \in (E \u F) }.
Class In_union_inv `{BagIn A T, BagUnion T} :=
  { in_union_inv : forall x (E F : T), x \in (E \u F) -> (x \in E \/ x \in F) }.

Implicit Arguments in_union_eq [[A] [T] [H] [H0] [In_union_eq]].
Implicit Arguments in_union_l [[A] [T] [H] [H0] [In_union_l] x E F].
Implicit Arguments in_union_r [[A] [T] [H] [H0] [In_union_r] x E F].
Implicit Arguments in_union_inv [[A] [T] [H] [H0] [In_union_inv] x E F].

Class In_inter_eq `{BagIn A T, BagInter T} :=
  { in_inter_eq : forall x E F, x \in (E \n F) = (x \in E /\ x \in F) }.
Class In_inter `{BagIn A T, BagInter T} :=
  { in_inter : forall x E F, x \in E -> x \in F -> x \in (E \n F) }.
Class In_inter_inv `{BagIn A T, BagInter T} :=
  { in_inter_inv : forall x E F, x \in (E \n F) -> x \in E /\ x \in F }.

Implicit Arguments in_inter_eq [[A] [T] [H] [H0] [In_inter_eq]].
Implicit Arguments in_inter [[A] [T] [H] [H0] [In_inter] x E F].
Implicit Arguments in_inter_inv [[A] [T] [H] [H0] [In_inter_inv] x E F].

Class In_remove_eq `{BagIn A T, BagRemove T T} :=
  { in_remove_eq : forall x (E F : T), x \in (E \- F) = (x \in E /\ x \notin F) }.

Implicit Arguments in_remove_eq [[A] [T] [H] [H0] [In_remove_eq]].

Class In_double_eq `{BagIn A T} :=
  { in_double_eq : forall E F, (forall x, x \in E = x \in F) -> E = F }.
Class In_double `{BagIn A T} :=
  { in_double : forall E F, (forall x, x \in E <-> x \in F) -> E = F }.

Implicit Arguments in_double_eq [[A] [T] [H] [In_double_eq]].
Implicit Arguments in_double [[A] [T] [H] [In_double]].

Class Incl_in `{BagIn A T, BagIncl T} :=
  { incl_in : forall x E F, E \c F -> x \in E -> x \in F}.

Implicit Arguments incl_in [[A] [T] [H] [H0] [Incl_in] x E F].

Class Incl_refl `{BagIncl T} :=
  { incl_refl : refl incl }.
Class Incl_trans `{BagIncl T} :=
  { incl_trans : trans incl }. 
Class Double_incl `{BagIncl T} :=
  { double_incl : antisym incl }.
Class Incl_order `{BagIncl T} :=
  { incl_order : LibOrder.order incl }. 

Implicit Arguments incl_refl [[T] [H] [Incl_refl]].
Implicit Arguments incl_trans [[T] [H] [Incl_trans] x z].

(* todo: add implicit
Implicit Arguments double_incl [[T] [H] [Double_incl] x E F].
Implicit Arguments incl_order [[T] [H] [Incl_order] x E F].*)

Class Empty_incl `{BagEmpty T, BagIncl T} :=
  { empty_incl : forall E, \{} \c E }.
Class Incl_empty `{BagEmpty T, BagIncl T} :=
  { incl_empty : forall E, (E \c \{}) = (E = \{}) }.
Class Incl_empty_inv `{BagEmpty T, BagIncl T} :=
  { incl_empty_inv : forall E, E \c \{} -> E = \{} }.

Implicit Arguments empty_incl [[T] [H] [H0] [Empty_incl]].
Implicit Arguments incl_empty [[T] [H] [Incl_empty]].
Implicit Arguments incl_empty_inv [[T] [H] [Incl_empty_inv] E].

(* todo: add implicit arguments in the rest of the file *)

Class Single_incl `{BagSingle A T, BagIn A T, BagIncl T} :=
  { single_incl : forall x E, (\{x} \c E) = (x \in E) }.
Class Incl_single `{BagSingle A T, BagIn A T, BagIncl T, BagEmpty T} :=
  { incl_single : forall x E, (E \c \{x}) -> (E = \{} \/ E = \{x}) }.

Class Incl_union_l `{BagUnion T, BagIncl T} :=
  { incl_union_l : forall E F G, E \c F -> E \c (F \u G) }.
Class Incl_union_r `{BagUnion T, BagIncl T} :=
  { incl_union_r : forall E F G, E \c G -> E \c (F \u G) }.

Class Union_incl_eq `{BagUnion T, BagIncl T} :=
  { union_incl_eq : forall E F G, (E \u F) \c G = (E \c G /\ F \c G) }.
Class Union_incl `{BagUnion T, BagIncl T} :=
  { union_incl : forall E F G, E \c G -> F \c G -> (E \u F) \c G }.
Class Union_incl_inv `{BagUnion T, BagIncl T} :=
  { union_incl_inv : forall E F G, (E \u F) \c G -> E \c G /\ F \c G }.

Class Incl_inter_b `{BagInter T, BagIncl T} :=
  { incl_inter_b : forall E F G, E \c (F \n G) = (E \c F /\ E \c G) }.
Class Incl_inter `{BagInter T, BagIncl T} :=
  { incl_inter : forall E F G, E \c F -> E \c G -> E \c (F \n G) }.
Class Incl_inter_inv `{BagInter T, BagIncl T} :=
  { incl_inter_inv : forall E F G, E \c (F \n G) -> E \c F /\ E \c G }.

(** Union *)

Class Union_assoc `{BagUnion T} :=
  { union_assoc : assoc union }.
Class Union_comm `{BagUnion T} :=
  { union_comm : comm union }.
Class Union_comm_assoc `{BagUnion T} :=
  { union_comm_assoc : comm_assoc union }.
Class Union_empty_l `{BagUnion T, BagEmpty T} :=
  { union_empty_l : neutral_l union empty }.
Class Union_empty_r `{BagUnion T, BagEmpty T} :=
  { union_empty_r : neutral_r union empty }.
Class Union_empty_inv `{BagUnion T, BagEmpty T} :=
  { union_empty_inv : forall E F,
     E \u F = \{} -> E = \{} /\ F = \{} }.
Class Union_self `{BagUnion T} :=
  { union_self : idempotent2 union }.

(* todo: union_comm_monoid *)

(** Intersection *)

Class Inter_assoc `{BagInter T} :=
  { inter_assoc : assoc inter }.
Class Inter_comm `{BagInter T} :=
  { inter_comm : comm inter }.
Class Inter_empty_l `{BagInter T, BagEmpty T} :=
  { inter_empty_l : absorb_l inter empty }.
Class Inter_empty_r `{BagInter T, BagEmpty T} :=
  { inter_empty_r : absorb_r inter empty }.
Class Inter_self `{BagInter T} :=
  { inter_self : idempotent2 inter }.

(** Removal *)

(** Disjointness *)

(** Restriction *)

(** Cardinal *)

Class Card_empty `{BagEmpty T, BagCard T} :=
  { card_empty : card \{} = 0%nat }.
Class Card_single `{BagSingle A T, BagCard T} :=
  { card_single : forall X, card \{X} = 1%nat }.
Class Card_union `{BagUnion T, BagCard T} :=
  { card_union : forall E F, card (E \u F) = (card E + card F)%nat }.
Class Card_union_le `{BagUnion T, BagCard T} :=
  { card_union_le : forall E F, card (E \u F) <= (card E + card F)%nat }.

(* ---------------------------------------------------------------------- *)
(** ** Derived Properties *)

(** Membership *)

Instance in_empty_from_in_empty_eq : 
  forall `{BagIn A T, BagEmpty T},
  In_empty_eq -> In_empty.
Proof. constructor. introv I. rewrite~ in_empty_eq in I. Qed.

Instance in_single_from_in_single_eq : 
  forall `{BagSingle A T, BagIn A T},
  In_single_eq -> In_single.
Proof. constructor. introv I. rewrite~ in_single_eq in I. Qed.

Instance in_single_self_from_in_single_eq : 
  forall `{BagSingle A T, BagIn A T},
  In_single_eq -> In_single_self.
Proof. constructor. intros. rewrite~ in_single_eq. Qed.

Instance in_union_r_from_in_union_eq : 
  forall `{BagIn A T, BagUnion T},
  In_union_eq -> In_union_r.
Proof. constructor. introv I. rewrite in_union_eq. rew_reflect*. Qed.

Instance in_union_l_from_in_union_eq : 
  forall `{BagIn A T, BagUnion T},
  In_union_eq -> In_union_l.
Proof. constructor. introv I. rewrite in_union_eq. rew_reflect*. Qed.

Instance in_union_inv_from_in_union_eq : 
  forall `{BagIn A T, BagUnion T},
  In_union_eq -> In_union_inv.
Proof. constructor. introv I. rewrite~ @in_union_eq in I. Qed.

Instance in_inter_from_in_inter_eq : 
  forall `{BagIn A T, BagInter T},
  In_inter_eq -> In_inter.
Proof. constructor. introv I1 I2. rewrite in_inter_eq. rew_reflect*. Qed. 

(** Union *)

Instance union_empty_r_from_union_empty_l : 
  forall `{BagUnion T, BagEmpty T},
  Union_empty_l -> Union_comm -> Union_empty_r.
Proof. constructor. intros_all. rewrite union_comm. apply union_empty_l. Qed.

(** Intersection *)

Instance inter_empty_r_from_inter_empty_l : 
  forall `{BagInter T, BagEmpty T},
  Inter_empty_l -> Inter_comm -> Inter_empty_r.
Proof. constructor. intros_all. rewrite inter_comm. apply inter_empty_l. Qed.

(* Inclusion *)

Instance incl_refl_from_incl_order :
  forall `{BagIncl T},
  Incl_order -> Incl_refl.
Proof. constructor. apply order_refl. apply incl_order. Qed.

Instance incl_trans_from_incl_order :
  forall `{BagIncl T},
  Incl_order -> Incl_trans.
Proof. constructor. apply order_trans. apply incl_order. Qed.

Instance double_incl_from_incl_order :
  forall `{BagIncl T},
  Incl_order -> Double_incl.
Proof. constructor. apply order_antisym. apply incl_order. Qed.

Instance incl_empty_inv_from_incl_empty :
  forall `{BagEmpty T, BagIncl T},
  Incl_empty -> Incl_empty_inv.
Proof. constructor. introv I. rewrite~ incl_empty in I. Qed.

Instance incl_union_r_from_incl_union_l :
  forall `{BagUnion T, BagIncl T},
  Incl_union_l -> Union_comm -> Incl_union_r.
Proof. constructor. introv I. rewrite union_comm. apply~ incl_union_l. Qed.

Instance union_incl_from_union_incl_eq :
  forall `{BagUnion T, BagIncl T},
  Union_incl_eq -> Union_incl_eq.
Proof. constructor. intros_all. rewrite union_incl_eq. rew_reflect*. Qed.

Instance union_incl_inv_from_union_incl_eq :
  forall `{BagUnion T, BagIncl T},
  Union_incl_eq -> Union_incl_inv.
Proof. constructor. introv I. rewrite union_incl_eq in I. destruct* I. Qed.

Instance in_double_eq_from_in_double :
  forall `{BagIn A T},
  In_double -> In_double_eq.
Proof. constructor. introv I. apply in_double. intros. rewrite* I. Qed.

(** Union and inter from Extensionality *)

Hint Rewrite @in_union_eq @in_inter_eq 
  @in_empty_eq @in_single_eq : rew_in_eq. 

Tactic Notation "contain_by_in_double" :=
  intros_all; apply in_double; intros; 
  autorewrite with rew_in_eq; rew_reflect; 
  intuition (try solve [auto|eauto|auto_false|false]).

Section UnionDouble.
Context `{BagIn A T, BagUnion T}.

Global Instance union_assoc_from_in_union :
  In_double -> In_union_eq -> Union_assoc.
Proof. constructor. contain_by_in_double. Qed.

Global Instance union_comm_from_in_union :
  In_double -> In_union_eq -> Union_comm.
Proof. constructor. contain_by_in_double. Qed.

Global Instance union_empty_l_from_in_union : 
  forall `{BagEmpty T},
  In_double -> In_union_eq -> In_empty_eq -> Union_empty_l.
Proof. constructor. contain_by_in_double. Qed.

Global Instance union_self_from_in_union :
  In_double -> In_union_eq -> Union_self.
Proof. constructor. contain_by_in_double. Qed.

End UnionDouble.

Section InterDouble.
Context `{BagIn A T, BagInter T}.

Global Instance inter_assoc_from_in_inter :
  In_double -> In_inter_eq -> Inter_assoc.
Proof. constructor. contain_by_in_double. Qed.

Global Instance inter_comm_from_in_inter :
  In_double -> In_inter_eq -> Inter_comm.
Proof. constructor. contain_by_in_double. Qed.

Global Instance inter_empty_l_from_in_inter :
  forall `{BagEmpty T},
  In_double -> In_inter_eq -> In_empty_eq -> Inter_empty_l.
Proof. constructor. contain_by_in_double. Qed.

Global Instance inter_self_from_in_inter :
  In_double -> In_inter_eq -> Inter_self.
Proof. constructor. contain_by_in_double. Qed.

End InterDouble.

Instance union_comm_assoc_from_assoc_and_comm 
  `{Union_assoc} {UH: Union_comm} : Union_comm_assoc.
Proof. 
  constructor. intros_all. do 2 rewrite union_assoc. 
  rewrite (union_comm _ x). auto. 
Qed.

(* todo: comm_assoc_l and _r *)



