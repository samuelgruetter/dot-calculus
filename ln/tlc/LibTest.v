(*** extracted from libtactics ***) 

Variable skip_axiom : False. 
Tactic Notation "skip" := 
  elimtype False; apply skip_axiom.

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.


Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with 
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

Ltac intro_until_mark :=
  match goal with 
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.

Ltac clears_or_generalizes_all_core :=
  repeat match goal with H: _ |- _ => 
           first [ clear H | revert H] end.

Tactic Notation "clears_all" :=
  generalize ltac_mark;
  clears_or_generalizes_all_core;
  intro_until_mark.


Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4)  :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) :=
  gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) :=
  gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) ident(X8) :=
  gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) ident(X8) ident(X9) :=
  gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) ident(X8) ident(X9) ident(X10) :=
  gen X10; gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.


Tactic Notation "clears" ident(X1) :=
  let rec doit _ :=
  match goal with 
  | H:context[X1] |- _ => clear H; try (doit tt)
  | _ => clear X1
  end in doit tt.
Tactic Notation "clears" ident(X1) ident(X2) :=
  clears X1; clears X2.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) :=
  clears X1; clears X2; clears X3.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) :=
  clears X1; clears X2; clears X3; clears X4.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) 
 ident(X5) :=
  clears X1; clears X2; clears X3; clears X4; clears X5.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
 ident(X5) ident(X6) :=
  clears X1; clears X2; clears X3; clears X4; clears X5; clears X6.



(*** new tactics ***) 

Ltac using_base cont :=
  generalize ltac_mark;
  cont tt; 
  clears_all;
  intro_until_mark.

Tactic Notation "using" :=
  using_base ltac:(fun _ => idtac).
Tactic Notation "using" ident(H1) :=
  using_base ltac:(fun _ => gen H1; clears H1).
Tactic Notation "using" ident(H1) ident(H2) :=
  using_base ltac:(fun _ => gen H1 H2; clears H1 H2).
Tactic Notation "using" ident(H1) ident(H2) ident(H3) :=
  using_base ltac:(fun _ => gen H1 H2 H3; clears H1 H2 H3).
Tactic Notation "using" ident(H1) ident(H2) ident(H3) ident(H4) :=
  using_base ltac:(fun _ => gen H1 H2 H3 H4; clears H1 H2 H3 H4).
Tactic Notation "using" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) :=
  using_base ltac:(fun _ => gen H1 H2 H3 H4 H5; clears H1 H2 H3 H4 H5).


(** demo *)

Section Sec.

Variables (A : Type).
Variables (H : forall x y : A, x = y).
Variables (H' : forall x : A, x <> x).

Lemma lem1 : forall x y : A, x = y.
Proof. apply H. Qed.

Lemma lem2 : forall x y : A, x = y.
Proof. apply H. Admitted.

(* version to be used in normal mode:
   starts the proof with using, whose effect
   is to keep only the section variables mentioned
   directly or indirectly via a dependency *)
Lemma lem3 : forall x y : A, x = y.
Proof. using H. apply H. Qed.

(* version to be used in precompilation mode:
   keeps only the "using" tactic and replace
   the rest of the proof with "skip". *)
Lemma lem4 : forall x y : A, x = y.
Proof. using H. skip. Qed.

Lemma lem5 : forall x y : A, x = y.
Proof. using. skip. Qed.

Lemma lem6 : forall x y : A, x = y.
Proof. using H H'. skip. Qed.

End Sec.

Check lem1. (* includes H *)
Check lem2. (* includes none *)
Check lem3. (* includes H *)
Check lem4. (* includes H *)
Check lem5. (* includes none *)
Check lem6. (* includes H and H' *)

Print lem1. (* includes H *)
Print lem2. (* includes none *)
Print lem3. (* includes H *)
Print lem4. (* includes H *)
Print lem5. (* includes none *)
Print lem6. (* includes H and H' *)

