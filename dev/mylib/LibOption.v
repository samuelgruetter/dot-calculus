(**************************************************************************
* TLC: A library for Coq                                                  *
* Option data-structure                                              
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibReflect.
Generalizable Variables A.

(** Fixing implicit arguments *)

Implicit Arguments Some [[A]].
Implicit Arguments None [[A]].


(* ********************************************************************** *)
(** * Inhabited and comparable *)

Instance option_inhab : forall A, Inhab (option A).
Proof. intros. apply (prove_Inhab None). Qed.

Definition option_compare `{Comparable A} (o1 o2 : option A) :=
  match o1, o2 with
  | None, None => true
  | Some v1, Some v2 => decide (v1 = v2)
  | _, _ => false
  end.

Global Instance option_comparable : forall `{Comparable A}, 
  Comparable (option A).
Proof.
  intros.
  applys (comparable_beq option_compare).
  destruct x; destruct y; simpl; rew_refl; iff; auto_false*; congruence.
Qed.


(* ********************************************************************** *)
(** * Operations and their properties *)

(* ---------------------------------------------------------------------- *)
(** ** Definitions *)

(** [is_some o] holds when [o] is of the form [Some x] *)

Definition is_some A (o:option A) :=
  match o with 
  | None => false
  | Some _ => true
  end.

(** [unsome_default d o] returns the content of the option, and returns [d]
    in case the option in [None]. *)

Definition unsome_default A d (o:option A) :=
  match o with
  | None => d
  | Some x => x
  end.

(** [unsome o] returns the content of the option, and returns an arbitrary 
    value in case the option in [None]. *)

Definition unsome `{Inhab A} := 
  unsome_default arbitrary.

(** [map f o] takes an option and returns an option, and maps the function
    [f] to the content of the option if it has one. *)

Definition map A B (f : A -> B) o :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

(** [map_on o f] is the same as [map f o], only the arguments are swapped. *)

Definition map_on A B o (f : A -> B) := 
  map f o.

(** [apply f o] optionnaly applies a function of type [A -> option B] *)
(* --todo: find a more explicit name *)

Definition apply A B (f : A -> option B) o :=
  match o with
  | None => None
  | Some x => f x
  end.

(** [apply_on o f] is the same as [apply f o] *)

Definition apply_on A B o (f : A -> option B) :=
  apply f o.


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Lemma apply_on_inv : forall A B (f : A->option B) x y, 
  apply_on x f = Some y -> 
  exists z, x = Some z /\ f z = Some y.
Proof. destruct x; simpl; introv H; inverts* H. Qed.

Implicit Arguments apply_on_inv [A B f x y].

Lemma map_on_inv : forall A B (f : A->B) x y, 
  map_on x f = Some y -> 
  exists z, x = Some z /\ y = f z.
Proof. destruct x; simpl; introv H; inverts* H. Qed.

Implicit Arguments map_on_inv [A B f x y].











