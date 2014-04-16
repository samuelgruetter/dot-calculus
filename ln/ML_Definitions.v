(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Definitions                *
* Arthur Charguéraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
Require List.
Require Export LibLogic LibList LibLN.

(* ********************************************************************** *)
(** ** Description of types *)

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_unit  : typ
  | typ_nat   : typ
  | typ_prod  : typ -> typ -> typ
  | typ_sum   : typ -> typ -> typ
  | typ_ref   : typ -> typ.

(** [typ] is inhabited *)

Definition typ_def := typ_unit.
Instance typ_inhab : Inhab typ.
Proof. intros. apply (prove_Inhab typ_unit). Defined.

(** Computing free variables of a type.
    Needed to say that typ_exn is closed
    and that typing of store is done with ground terms *)

Fixpoint typ_fv (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar i      => \{}
  | typ_fvar x      => \{x}
  | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2)
  | typ_unit        => \{}  
  | typ_nat         => \{}  
  | typ_prod T1 T2  => (typ_fv T1) \u (typ_fv T2)
  | typ_sum T1 T2   => (typ_fv T1) \u (typ_fv T2)
  | typ_ref T1      => (typ_fv T1)
  end.

(** Exceptions is an abstract typ. typ_unit can be a naive implementation
    of exceptions, but to be able to pattern match on exceptions one may
    rather consider defining exception as a sum of types.
    The exception type must be ground (no free type variable). *)

Parameter typ_exn : typ. 
Parameter typ_exn_fresh : typ_fv typ_exn = \{}.

(** Type schemes. *)

Record sch : Set := Sch { 
  sch_arity : nat ; 
  sch_type  : typ }.

(** Opening body of type schemes. *)

Fixpoint typ_open (T : typ) (Vs : list typ) {struct T} : typ :=
  match T with
  | typ_bvar i      => List.nth i Vs typ_def
  | typ_fvar x      => typ_fvar x 
  | typ_arrow T1 T2 => typ_arrow (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_unit        => typ_unit  
  | typ_nat         => typ_nat  
  | typ_prod T1 T2  => typ_prod (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_sum T1 T2   => typ_sum (typ_open T1 Vs) (typ_open T2 Vs)
  | typ_ref T1      => typ_ref (typ_open T1 Vs)
  end.

(** Opening body of type schemes with variables *)

Definition typ_fvars := 
  LibList.map typ_fvar.

Definition typ_open_vars T Xs := 
  typ_open T (typ_fvars Xs).

(** Instanciation of a type scheme *)

Definition sch_open M := 
  typ_open (sch_type M).

Definition sch_open_vars M := 
  typ_open_vars (sch_type M).
  
Notation "M ^^ Vs" := (sch_open M Vs) 
  (at level 67, only parsing) : typ_scope.
Notation "M ^ Xs" := 
  (sch_open_vars M Xs) (only parsing) : typ_scope.

Bind Scope typ_scope with typ.
Open Scope typ_scope.

(** Locally closed types *)

Inductive type : typ -> Prop :=
  | type_fvar : forall X, 
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_arrow T1 T2)
  | type_unit : 
      type (typ_unit)
  | type_nat : 
      type (typ_nat)
  | type_prod : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_prod T1 T2)
  | type_sum : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (typ_sum T1 T2)
  | type_ref : forall T1,
      type T1 -> 
      type (typ_ref T1).

(** List of n locally closed types *)

Definition types := list_for_n type.

(** Body of a scheme *)

Definition typ_body n T :=
  exists L, forall Xs, 
  fresh L n Xs ->
  type (typ_open_vars T Xs).

(** Definition of a well-formed scheme *)

Definition scheme M :=
   typ_body (sch_arity M) (sch_type M).


(* ********************************************************************** *)
(** ** Description of terms *)

(** Definition of locations. *)

Definition loc := var.

(** Grammar of patterns. *)

Inductive pat : Set :=
  | pat_bvar : pat
  | pat_wild : pat
  | pat_unit : pat
  | pat_pair : pat -> pat -> pat
  | pat_inj1 : pat -> pat
  | pat_inj2 : pat -> pat.

(** Grammar of terms. *)

Inductive trm : Set :=
  | trm_bvar  : nat -> nat -> trm
  | trm_fvar  : var -> trm
  | trm_abs   : trm -> trm
  | trm_fix   : trm -> trm
  | trm_let   : trm -> trm -> trm
  | trm_match : trm -> pat -> trm -> trm -> trm
  | trm_app   : trm -> trm -> trm
  | trm_unit  : trm
  | trm_nat   : nat -> trm
  | trm_add  : trm
  | trm_pair  : trm -> trm -> trm
  | trm_inj1  : trm -> trm
  | trm_inj2  : trm -> trm
  | trm_loc   : loc -> trm
  | trm_ref   : trm -> trm
  | trm_get   : trm -> trm
  | trm_set   : trm -> trm -> trm
  | trm_raise : trm -> trm
  | trm_catch : trm -> trm -> trm.

(** [trm] is inhabited *)

Definition trm_def := trm_unit.
Instance trm_inhab : Inhab trm.
Proof. intros. apply (prove_Inhab trm_unit). Defined.

(** Arity of a pattern. *)

Fixpoint pat_arity (p : pat) : nat :=
  match p with
  | pat_bvar       => 1
  | pat_wild       => 0
  | pat_unit       => 0
  | pat_pair p1 p2 => (pat_arity p1) + (pat_arity p2)
  | pat_inj1 p1    => (pat_arity p1)
  | pat_inj2 p1    => (pat_arity p1)
  end. 

(** Pattern matching. *)

Fixpoint pat_match (p : pat) (t : trm) {struct p} : option (list trm) :=
  match p, t with
  | pat_bvar      , t1             => Some (t1::nil)
  | pat_wild      , t1             => Some nil
  | pat_unit      , trm_unit       => Some nil
  | pat_pair p1 p2, trm_pair t1 t2 => match (pat_match p1 t1), (pat_match p2 t2) with
                                      | Some r1, Some r2 => Some (r1 ++ r2)
                                      | _      , _       => None end
  | pat_inj1 p1   , trm_inj1 t1    => (pat_match p1 t1) 
  | pat_inj2 p1   , trm_inj2 t1    => (pat_match p1 t1)
  | _             , _              => None
  end.

(** nth function on term lists *)

Definition trm_nth n (ts : list trm) := List.nth n ts trm_def.

(** Opening up abstractions *)

Fixpoint opens_rec (k : nat) (us : list trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i j  => If k = i then (trm_nth j us) else (trm_bvar i j)
  | trm_fvar x    => trm_fvar x
  | trm_abs t1    => trm_abs (opens_rec (S k) us t1)
  | trm_fix t1    => trm_fix (opens_rec (S k) us t1)
  | trm_let t1 t2 => trm_let (opens_rec k us t1) (opens_rec (S k) us t2)
  | trm_match t1 p1 b t2 => trm_match (opens_rec k us t1) p1 
                               (opens_rec (S k) us b)
                               (opens_rec (S k) us t2)
  | trm_app t1 t2 => trm_app (opens_rec k us t1) (opens_rec k us t2)
  | trm_unit      => trm_unit
  | trm_nat n     => trm_nat n
  | trm_add       => trm_add
  | trm_pair t1 t2 => trm_pair (opens_rec k us t1) (opens_rec k us t2)
  | trm_inj1 t1   => trm_inj1 (opens_rec k us t1) 
  | trm_inj2 t1   => trm_inj2 (opens_rec k us t1) 
  | trm_loc l     => trm_loc l
  | trm_ref t1    => trm_ref (opens_rec k us t1)
  | trm_get t1    => trm_get (opens_rec k us t1)
  | trm_set t1 t2 => trm_set (opens_rec k us t1) (opens_rec k us t2)
  | trm_raise t1    => trm_raise (opens_rec k us t1)
  | trm_catch t1 t2 => trm_catch (opens_rec k us t1) (opens_rec k us t2)
  end.

Definition opens t us := opens_rec 0 us t.
Definition open t u := opens t (u::nil).
Definition trm_fvars := LibList.map trm_fvar.

Notation "{ k ~> u } t" := (opens_rec k u t) (at level 67).
Notation "t ^^ us" := (opens t us) (at level 67).
Notation "t ^ xs" := (opens t (trm_fvars xs)).

(** Terms are locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, fresh L 1 (x::nil) -> 
        term (t1 ^ (x::nil))) ->
      term (trm_abs t1)
  | term_fix : forall L t1,
      (forall f x, fresh L 2 (x::f::nil) -> 
        term (t1 ^ (x::f::nil))) ->
      term (trm_fix t1)
  | term_let : forall L t1 t2,
      term t1 ->
      (forall x, fresh L 1 (x::nil) -> 
        term (t2 ^ (x::nil))) ->
      term (trm_let t1 t2)
  | term_match : forall L t1 p b t2,
      term t1 -> 
      (forall xs, fresh L (pat_arity p) xs -> term (b ^ xs)) ->
      term t2 ->
      term (trm_match t1 p b t2)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_unit : 
      term (trm_unit)
  | term_nat : forall n,
      term (trm_nat n)
  | term_add : 
      term (trm_add)
  | term_pair : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_pair t1 t2)
  | term_inj1 : forall t1,
      term t1 -> 
      term (trm_inj1 t1)
  | term_inj2 : forall t1,
      term t1 -> 
      term (trm_inj2 t1)
  | term_loc : forall l,
      term (trm_loc l)
  | term_new : forall t1,
      term t1 ->
      term (trm_ref t1)
  | term_get : forall t1,
      term t1 ->
      term (trm_get t1)
  | term_set : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_set t1 t2)
  | term_raise : forall t1,
      term t1 ->
      term (trm_raise t1)
  | term_catch : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_catch t1 t2).

(** Definition of [bodys n t] as [t ^ xs] is a term when [|xs|=n] *)
  
Definition bodys n t :=
  exists L, forall xs,
  fresh L n xs -> term (t ^ xs).



(* ********************************************************************** *)
(** ** Semantics *)

(** Representation of the store and its well-formedness judgment *)

Definition sto := LibEnv.env trm.

Inductive sto_ok : sto -> Prop :=
  | sto_ok_empty : sto_ok empty
  | sto_ok_push : forall mu l t,
      sto_ok mu -> term t -> 
      sto_ok (mu & l ~ t).

(** Grammar of values *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1, term (trm_abs t1) -> value (trm_abs t1)
  | value_fix : forall t1, term (trm_fix t1) -> value (trm_fix t1)
  | value_nat : forall n, value (trm_nat n)
  | value_add : value trm_add
  | value_add_1 : forall n, value (trm_app trm_add (trm_nat n))
  | value_pair : forall v1 v2, value v1 -> value v2 -> value (trm_pair v1 v2)
  | value_inj1 : forall v1, value v1 -> value (trm_inj1 v1)
  | value_inj2 : forall v1, value v1 -> value (trm_inj2 v1)
  | value_unit : value trm_unit
  | value_loc : forall l, value (trm_loc l).

(** Raising of Exceptions *)

Inductive fails : trm -> trm -> Prop :=
  | fails_raise_val : forall t1,
      value t1 ->
      fails (trm_raise t1) t1
  | fails_app_1 : forall t1 t2 e,
      term t2 ->
      fails t1 e ->
      fails (trm_app t1 t2) e
  | fails_app_2 : forall t1 t2 e,
      value t1 ->
      fails t2 e ->
      fails (trm_app t1 t2) e
  | fails_let_1 : forall t1 t2 e, 
      bodys 1 t2 ->
      fails t1 e ->
      fails (trm_let t1 t2) e
  | fails_pair_1 : forall t1 t2 e,
      term t2 ->
      fails t1 e ->
      fails (trm_pair t1 t2) e
  | fails_pair_2 : forall t1 t2 e, 
      value t1 -> 
      fails t2 e ->
      fails (trm_pair t1 t2) e
  | fails_inj_1 : forall t1 e,
      fails t1 e ->
      fails (trm_inj1 t1) e
  | fails_inj_2 : forall t1 e,
      fails t1 e ->
      fails (trm_inj2 t1) e
  | fails_mat_1 : forall t1 p b t2 e,
      bodys (pat_arity p) b ->
      term t2 ->
      fails t1 e ->
      fails (trm_match t1 p b t2) e
  | fails_new_1 : forall t1 e,
      fails t1 e ->
      fails (trm_ref t1) e
  | fails_get_1 : forall t1 e,
      fails t1 e ->
      fails (trm_get t1) e
  | fails_set_1 : forall t1 t2 e,
      fails t1 e ->
      term t2 ->
      fails (trm_set t1 t2) e
  | fails_set_2 : forall t1 t2 e,
      value t1 ->
      fails t2 e ->
      fails (trm_set t1 t2) e
  | fails_raise_1 : forall t1 e,
      fails t1 e ->
      fails (trm_raise t1) e.

(** Reduction rules *)

Definition conf := (trm * sto)%type.

Inductive red : conf -> conf -> Prop :=

  (* -- reduction with substitution -- *)

  | red_beta : forall mu t1 t2,
      sto_ok mu ->
      term (trm_abs t1) -> 
      value t2 ->
      red (trm_app (trm_abs t1) t2, mu) (t1 ^^ (t2::nil), mu)
  | red_fix : forall mu t1 t2,
      sto_ok mu ->
      term (trm_fix t1) -> 
      value t2 ->
      red (trm_app (trm_fix t1) t2, mu) 
          (t1 ^^ (t2::(trm_fix t1)::nil), mu)
  | red_let : forall mu t1 t2, 
      sto_ok mu ->
      term (trm_let t1 t2) ->
      value t1 -> 
      red (trm_let t1 t2, mu) (t2 ^^ (t1::nil), mu)
  | red_match_some : forall ts mu t1 p b t2,
      sto_ok mu ->
      value t1 ->
      bodys (pat_arity p) b ->
      term t2 ->
      pat_match p t1 = Some ts ->
      red (trm_match t1 p b t2, mu) (b ^^ ts, mu)
  | red_match_none : forall mu t1 p b t2,
      sto_ok mu ->
      value t1 ->
      bodys (pat_arity p) b ->
      term t2 ->
      pat_match p t1 = None ->
      red (trm_match t1 p b t2, mu) (t2, mu)

  (* -- reduction of primitives -- *)

  | red_add : forall mu n1 n2, 
      sto_ok mu ->
      red (trm_app (trm_app trm_add (trm_nat n1)) (trm_nat n2), mu)
          (trm_nat (n1 + n2), mu)
  | red_new : forall mu t1 l,
      sto_ok mu ->
      value t1 ->
      l # mu ->
      red (trm_ref t1, mu) (trm_loc l, (mu & l ~ t1))
  | red_get : forall mu l t,
      sto_ok mu ->
      binds l t mu ->
      red (trm_get (trm_loc l), mu) (t, mu)
  | red_set : forall mu l t2,
      sto_ok mu ->
      value t2 ->
      red (trm_set (trm_loc l) t2, mu) (trm_unit, mu & l ~ t2)  
  | red_catch_val : forall mu t1 t2,
      sto_ok mu ->
      term t1 ->
      value t2 ->
      red (trm_catch t1 t2, mu) (t2, mu)
  | red_catch_exn : forall mu t1 t2 e,
      sto_ok mu ->
      term t1 ->
      fails t2 e ->
      red (trm_catch t1 t2, mu) (trm_app t1 e, mu)

  (* -- reduction under context -- *)

  | red_app_1 : forall mu mu' t1 t1' t2,
      term t2 ->
      red (t1, mu) (t1', mu') ->
      red (trm_app t1 t2, mu) (trm_app t1' t2, mu')
  | red_app_2 : forall mu mu' t1 t2 t2',
      value t1 ->
      red (t2, mu) (t2', mu') ->
      red (trm_app t1 t2, mu) (trm_app t1 t2', mu')
  | red_match_1 : forall mu mu' t1 t1' p b t2, 
      term t2 ->
      bodys (pat_arity p) b ->
      red (t1, mu) (t1', mu') ->
      red (trm_match t1 p b t2, mu) (trm_match t1' p b t2, mu')
  | red_pair_1 : forall mu mu' t1 t1' t2,
      term t2 ->
      red (t1, mu) (t1', mu') ->
      red (trm_pair t1 t2, mu) (trm_pair t1' t2, mu')
  | red_pair_2 : forall mu mu' t1 t2 t2', 
      value t1 -> 
      red (t2, mu) (t2', mu') ->
      red (trm_pair t1 t2, mu) (trm_pair t1 t2', mu')
  | red_inj1_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_inj1 t1, mu) (trm_inj1 t1', mu')
  | red_inj2_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_inj2 t1, mu) (trm_inj2 t1', mu')
  | red_new_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_ref t1, mu) (trm_ref t1', mu')
  | red_get_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_get t1, mu) (trm_get t1', mu')
  | red_set_1 : forall mu mu' t1 t1' t2,
      red (t1, mu) (t1', mu') ->
      term t2 ->
      red (trm_set t1 t2, mu) (trm_set t1' t2, mu')
  | red_set_2 : forall mu mu' t1 t2 t2',
      value t1 ->
      red (t2, mu) (t2', mu') ->
      red (trm_set t1 t2, mu) (trm_set t1 t2', mu')

  | red_catch_2 : forall mu mu' t1 t2 t2',
      term t1 ->
      red (t2, mu) (t2', mu') ->
      red (trm_catch t1 t2, mu) (trm_catch t1 t2', mu')
  | red_raise_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_raise t1, mu) (trm_raise t1', mu').

Notation "c --> c'" := (red c c') (at level 68).


(* ********************************************************************** *)
(** ** Typing *)

(** Typing environments mapping variable to type schemes *)

Definition env := LibEnv.env sch.

(** Typing environments mapping locations to types 
    and its well-formedness judgment *)

Definition phi := LibEnv.env typ.

Inductive phi_ok : phi -> Prop :=
  | phi_ok_empty : phi_ok empty
  | phi_ok_push : forall P l T,
      phi_ok P -> type T -> (*  typ_fv T = \{} -> *)
      phi_ok (P & l ~T).


(** Typing relation for patterns: if Us are the types of the
    bound variables in the pattern p, then the pattern p matches
    values of type T. *)

Reserved Notation "Us \= p ~: T" (at level 69).

Inductive pat_typing : list typ -> pat -> typ -> Prop := 
  | pat_typing_bvar : forall T,
     (T::nil) \= pat_bvar ~: T
  | pat_typing_wild : forall T,
     nil \= pat_wild ~: T
  | pat_typing_unit :
     nil \= pat_unit ~: typ_unit 
  | pat_typing_pair : forall p1 p2 T1 T2 Us1 Us2,
     Us1 \= p1 ~: T1 ->
     Us2 \= p2 ~: T2 ->
     (Us1 ++ Us2) \= (pat_pair p1 p2) ~: (typ_prod T1 T2)
  | pat_typing_inj1 : forall T2 p1 T1 Us1,
     Us1 \= p1 ~: T1 ->
     Us1 \= (pat_inj1 p1) ~: (typ_sum T1 T2)
  | pat_typing_inj2 : forall T2 p1 T1 Us1,
     Us1 \= p1 ~: T2 ->
     Us1 \= (pat_inj2 p1) ~: (typ_sum T1 T2)

where "Ts \= p ~: T" := (pat_typing Ts p T).


(** The typing judgment for terms *)

Reserved Notation "E ! P |= t ~: T" (at level 69).

Inductive typing : env -> phi -> trm -> typ -> Prop :=
  | typing_var : forall E P x M Us, 
      ok E -> phi_ok P ->
      binds x M E -> 
      types (sch_arity M) Us ->
      scheme M ->
      E ! P |= (trm_fvar x) ~: (M ^^ Us)
  | typing_abs : forall L E P U T t1,
      type U -> 
      (forall x, fresh L 1 (x::nil) -> 
       (E & x ~ Sch 0 U) ! P |= t1 ^ (x::nil) ~: T) ->
      E ! P |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_fix : forall L E P U T t1,
      type U -> 
      (forall f x, fresh L 2 (x::f::nil) -> 
        (E & f ~ Sch 0 (typ_arrow U T) & x ~ Sch 0 U) ! P |= t1 ^ (x::f::nil) ~: T) ->
      E ! P |= (trm_fix t1) ~: (typ_arrow U T)
  | typing_let : forall M L1 L2 E P T2 t1 t2, 
      value t1 -> 
      scheme M ->
      (forall Xs, fresh L1 (sch_arity M) Xs ->
         E ! P |= t1 ~: (M ^ Xs)) ->
      (forall x, fresh L2 1 (x::nil) -> 
         (E & x ~ M) ! P |= (t2 ^ (x::nil)) ~: T2) -> 
      E ! P |= (trm_let t1 t2) ~: T2
  | typing_match : forall T Us L R E P t1 p b t2,
      E ! P |= t1 ~: T ->
      Us \= p ~: T ->
      (forall xs, fresh L (pat_arity p) xs -> 
        (E & (xs ~* (LibList.map (Sch 0) Us))) ! P |= (b ^ xs) ~: R) ->
      E ! P |= t2 ~: R -> 
      E ! P |= (trm_match t1 p b t2) ~: R
  | typing_app : forall E P S T t1 t2, 
      E ! P |= t1 ~: (typ_arrow S T) ->
      E ! P |= t2 ~: S ->   
      E ! P |= (trm_app t1 t2) ~: T
  | typing_unit : forall E P,
      ok E -> phi_ok P ->
      E ! P |= (trm_unit) ~: (typ_unit)
  | typing_nat : forall E P n,
      ok E -> phi_ok P ->
      E ! P |= (trm_nat n) ~: (typ_nat)
  | typing_add : forall E P,
      ok E -> phi_ok P ->
      E ! P |= trm_add ~: (typ_arrow typ_nat (typ_arrow typ_nat typ_nat))
  | typing_pair : forall E P t1 t2 T1 T2,
      E ! P |= t1 ~: T1 -> 
      E ! P |= t2 ~: T2 ->
      E ! P |= (trm_pair t1 t2) ~: (typ_prod T1 T2)
  | typing_inj1 : forall T2 E P t1 T1,
      type T2 ->
      E ! P |= t1 ~: T1 -> 
      E ! P |= (trm_inj1 t1) ~: (typ_sum T1 T2)
  | typing_inj2 : forall T1 E P t1 T2,
      type T1 ->
      E ! P |= t1 ~: T2 -> 
      E ! P |= (trm_inj2 t1) ~: (typ_sum T1 T2)
  | typing_loc : forall E P l T,
      ok E -> phi_ok P -> 
      binds l T P ->
      E ! P |= (trm_loc l) ~: (typ_ref T)
  | typing_ref : forall E P t1 T,
      E ! P |= t1 ~: T ->
      E ! P |= (trm_ref t1) ~: (typ_ref T)
  | typing_get : forall E P t1 T,
      E ! P |= t1 ~: (typ_ref T) ->
      E ! P |= (trm_get t1) ~: T
  | typing_set : forall E P t1 t2 T,
      E ! P |= t1 ~: (typ_ref T) ->
      E ! P |= t2 ~: T ->
      E ! P |= (trm_set t1 t2) ~: typ_unit
  | typing_raise : forall E P t1 T,
      type T ->
      E ! P |= t1 ~: typ_exn ->
      E ! P |= (trm_raise t1) ~: T
  | typing_catch : forall E P t1 t2 T,
      E ! P |= t1 ~: (typ_arrow typ_exn T) ->
      E ! P |= t2 ~: T ->
      E ! P |= (trm_catch t1 t2) ~: T

where "E ! P |= t ~: T" := (typing E P t T).

(** Typing store *)

Definition sto_typing P mu :=
     phi_ok P
  /\ sto_ok mu 
  /\ (forall l, l # mu -> l # P)
  /\ (forall l T, binds l T P -> 
        exists t, binds l t mu
               /\ empty ! P |= t ~: T).

Notation "P |== mu" := (sto_typing P mu) (at level 68).


(* ********************************************************************** *)
(** ** Theorems *)

(** Preservation: if t has type T in the empty context and under
    P typing the store mu, and if t reduces to t' by updating
    the context to mu', then there exists a extended relation P'
    typing the new store mu', such that t' has its typed preserved
    under P'. *)

Definition preservation := forall P t t' mu mu' T,
  empty ! P |= t ~: T ->
  (t,mu) --> (t',mu') ->
  P |== mu ->
  exists P', 
     extends P P'
  /\ empty ! P' |= t' ~: T
  /\ P' |== mu'.

(** Progress: If a term t has type T in the empty environment and
    under P typing the store mu, then three cases are possibles:
    (1) t is a value, (2) t raises an exception e, or (3) there
    exists a term t' and a store mu' such that the configuration
    (t,mu) reduces to the configuration (t',mu'). *)

Definition progress := forall P t mu T, 
  empty ! P |= t ~: T ->
  P |== mu ->
     value t 
  \/ (exists e, fails t e)
  \/ (exists t', exists mu', (t,mu) --> (t',mu')).

