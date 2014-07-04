
Require (*Export*) List.
Require Export Arith.Peano_dec.

(* List notation with head on the right *)
Notation "E '&' F" := (app F E) (at level 31, left associativity).
Notation " E  ;; x " := (cons x E) (at level 29, left associativity).
(* Testing the list notations: *)
Definition head(l: list nat) := match l with
| nil => 777
| cons x xs => x
end.
Eval compute in nil ;; 1 ;; 2 ;; 3.
Eval compute in head (nil ;; 1 ;; 2 ;; 3).
Eval compute in head ((nil ;; 1 ;; 2 ;; 3) & (nil ;; 4 ;; 5)).
Eval compute in nil ;; 1 ;; 2 & nil ;; 3 ;; 4 & nil ;; 5 ;; 6. 
(* Unset Printing Notations. (* or by CoqIDE menu *) *)
Check (nil ;; 0 & nil ;; 0 ;; 0 & nil ;; 0 ;; 0 ;; 0).

Definition var := nat.

(* If it's clear whether a field or method is meant, we use nat, if not, we use label: *)
Inductive label: Type :=
| label_fld: nat -> label
| label_mtd: nat -> label.

Lemma eq_label_dec: forall l1 l2: label, {l1 = l2} + {l1 <> l2}.
Proof.
  intros. 
  destruct l1 as [n1|n1]; destruct l2 as [n2|n2]; 
  destruct (eq_nat_dec n1 n2); solve [
     (left; f_equal; assumption) |
     (right; unfold not; intro H; inversion H; rewrite H1 in n; apply n; reflexivity)].
Qed.

Inductive avar : Type :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to tenv or venv *)

Inductive typ : Type :=
  | typ_rcd  : list ndec -> typ (* record type *)
with ndec : Type := (* named declaration *)
  | ndec_fld : nat -> typ -> ndec
  | ndec_mtd : nat -> typ -> typ -> ndec.
Inductive dec : Type := (* declaration without name *)
  | dec_fld  : typ -> dec
  | dec_mtd  : typ -> typ -> dec.

Inductive trm : Type :=
  | trm_var  : avar -> trm
  | trm_new  : list nini -> trm -> trm
  | trm_sel  : trm -> nat -> trm
  | trm_call : trm -> nat -> trm -> trm
with nini : Type :=
  | nini_fld : nat -> avar -> nini (* cannot have term here, need to assign first *)
  | nini_mtd : nat -> typ -> trm -> nini.
Inductive ini : Type :=
  | ini_fld : avar -> ini
  | ini_mtd : typ -> trm -> ini.

(* Syntactic sugar *)
Definition trm_fun(T: typ)(body: trm) := trm_new (nil ;; nini_mtd 0 T body)
                                                 (trm_var (avar_b 0)).
Definition trm_app(func arg: trm) := trm_call func 0 arg.
Definition trm_let(T: typ)(rhs body: trm) := trm_app (trm_fun T body) rhs.
Definition trm_upcast(T: typ)(e: trm) := trm_app (trm_fun T (trm_var (avar_b 0))) e.
Definition typ_arrow(T1 T2: typ) := typ_rcd (nil ;; ndec_mtd 0 T1 T2).

(* 
Environment requirements:
   * Want to use the same definitions and lemmas for
     - decs
     - inis
     - tenv
     - venv
   * Intersection of two dec lists must be total, i.e. if we have
     (m: T -> U) in ds1 and (m: T) in ds2,
     then (ds1 /\ ds2) must be defined and contain both declarations.
     This requires that method labels be distinct from field labels, or that
     the environment data structure allows two decs with the same name if they
     are of a different kind.
   * Want to have generic dec (dec_typ, dec_mtd, dec_fld), and treat dec lists as
     as mappings from dec name to dec, instead of having three separate lists.
Hopefully, this module system approach satisfies the requirements.
*)

Module Type EnvParams.
Parameter K : Type.
Parameter V : Type.
Parameter B : Type.
Parameter key: B -> K.
Parameter value: B -> V. 
Axiom eq_key_dec: forall k1 k2: K, {k1 = k2} + {k1 <> k2}.
End EnvParams.

(* General environment *)
Module Env (params: EnvParams).
Import params.
Definition t := list B.
Definition map: (B -> B) -> t -> t := (@List.map B B).
Fixpoint get(k: K)(E: t): option V := match E with
  | nil => None
  | bs ;; b => if eq_key_dec k (key b) then Some (value b) else get k bs
  end.
Definition binds(k: K)(v: V)(E: t): Prop := (get k E = Some v).
Definition unbound(k: K)(E: t): Prop := (get k E = None).
End Env.

(* Module decs: For lists of declarations: [list ndec] or [label => dec] *)
Module decsParams <: EnvParams.
Definition K := label.
Definition V := dec.
Definition B := ndec.
Definition key(d: ndec): label := match d with
| ndec_fld n T => label_fld n
| ndec_mtd n T U => label_mtd n
end.
Definition value(d: ndec): dec := match d with
| ndec_fld n T => dec_fld T
| ndec_mtd n T U => dec_mtd T U
end.
Definition eq_key_dec := eq_label_dec.
End decsParams.
Module decs := Env(decsParams).

(* Module inis: For lists of initialisations: [list nini] or [label => ini] *)
Module inisParams <: EnvParams.
Definition K := label.
Definition V := ini.
Definition B := nini.
Definition key(i: nini): label := match i with
| nini_fld n T => label_fld n
| nini_mtd n T e => label_mtd n
end.
Definition value(i: nini): ini := match i with
| nini_fld n T => ini_fld T
| nini_mtd n T e => ini_mtd T e
end.
Definition eq_key_dec := eq_label_dec.
End inisParams.
Module inis := Env(inisParams).

(* Module tenv: For type environments: [var => typ] *)
Module tenvParams <: EnvParams.
Definition K := var.
Definition V := typ.
Definition B := (var * typ)%type.
Definition key := @fst var typ.
Definition value := @snd var typ.
Definition eq_key_dec := eq_nat_dec.
End tenvParams.
Module tenv := Env(tenvParams).

(* Module venv: For value environments: [var => inis] *)
Module venvParams <: EnvParams.
Definition K := var.
Definition V := inis.t.
Definition B := (var * inis.t)%type.
Definition key := @fst var inis.t.
Definition value := @snd var inis.t.
Definition eq_key_dec := eq_nat_dec.
End venvParams.
Module venv := Env(venvParams).

(* ... opening ...
   replaces in some syntax a bound variable with dangling index (k) by a free variable x
*)

Fixpoint open_rec_avar (k: nat) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => if eq_nat_dec k i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

(* The only binders are trm_new and (n)ini_mtd, which cannot be inside a typ or
   inside a dec, so we don't need opening for typ and dec *)

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var  a     => trm_var (open_rec_avar k u a)
  | trm_new  is e  => trm_new (inis.map (open_rec_nini (S k) u) is) (open_rec_trm (S k) u e)
  | trm_sel  e n   => trm_sel (open_rec_trm k u e) n
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_nini (k: nat) (u: var) (i: nini) { struct i } : nini :=
  match i with
  | nini_fld n a   => nini_fld n (open_rec_avar k u a)
  | nini_mtd n T e => nini_mtd n T (open_rec_trm (S k) u e)
  end.

Definition open_avar u a := open_rec_avar 0 u a.
Definition open_trm  u e := open_rec_trm  0 u e.
Definition open_nini u i := open_rec_nini 0 u i.

Inductive fvar : avar -> Prop :=
  | fvar_f : forall x,
      fvar (avar_f x).

(** Operational Semantics **)
(* Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
   Whenever we introduce a new avar_f (only happens in red_new), we choose one
   which is not in the store, so we never have name clashes. *) 
Inductive red : venv.t -> trm -> venv.t -> trm -> Prop :=
  (* computation rules *)
  | red_call : forall (s: venv.t) (x y: var) (m: nat) (T: typ) (is: inis.t) (body: trm),
      venv.binds x is s ->
      inis.binds (label_mtd m) (ini_mtd T body) is ->
      red s (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) 
          s (open_trm y body)
  | red_sel : forall (s: venv.t) (x: var) (y: avar) (l: nat) (is: inis.t),
      venv.binds x is s ->
      inis.binds (label_fld l) (ini_fld y) is ->
      red s (trm_sel (trm_var (avar_f x)) l) s 
            (trm_var y)
  | red_new : forall (s: venv.t) (is: inis.t) (e: trm) (x: var),
      venv.unbound x s ->
      red s (trm_new is e)
          (s ;; (x, is)) (open_trm x e)
  (* congruence rules *)
  | red_call1 : forall s o m a s' o',
      red s o s' o' ->
      red s  (trm_call o  m a) 
          s' (trm_call o' m a)
  | red_call2 : forall s x m a s' a',
      red s a s' a' ->
      red s  (trm_call (trm_var (avar_f x)) m a ) 
          s' (trm_call (trm_var (avar_f x)) m a')
  | red_sel1 : forall s o l s' o',
      red s o s' o' ->
      red s  (trm_sel o  l)
          s' (trm_sel o' l).


(* garbage .............. *)


(*
what's below is not needed because simpler:
assign everything first to a var -> no need to evaluate fields of record
and one type for record construction / fully evaluated record
*)

(* Value (: [list nslot] or [label => slot] *)
Module val <: env.
Definition K := loc.
Definition V := slot.
Definition B := nslot.
Definition t := list nslot.
Definition key(s: nslot): loc := match s with
| nslot_fld n lo => label_fld n
| nslot_mtd n T e => label_mtd n
end.
Definition value(s: nslot): slot := match s with
| nslot_fld n lo => slot_fld lo
| nslot_mtd n T e => slot_mtd T e
end.
End val.

(* fully evaluated record member *)
Inductive slot : Type :=
  | slot_fld : loc -> slot
  | slot_mtd : typ -> trm -> slot.

(* named slot *)
Inductive nslot : Type :=
  | nslot_fld : nat -> loc -> nslot
  | nslot_mtd : nat -> typ -> trm -> nslot.

(* Import List.ListNotations. *)

(*
theories/Lists/List, Module ListNotations:
Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

theories/Init/Datatypes:
Infix "++" := app (right associativity, at level 60) : list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
*)

