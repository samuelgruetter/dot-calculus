
Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.


(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter mtd_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_mtd: mtd_label -> label.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* { D } *)
  | typ_sel  : avar -> typ_label -> typ (* x.L *)
  | typ_and  : typ -> typ -> typ
  | typ_or   : typ -> typ -> typ
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* L: S..U *)
  | dec_mtd  : mtd_label -> typ -> typ -> dec (* m: S->U *).

Inductive trm: Set :=
  | trm_var : avar -> trm
  | trm_new : defs -> trm -> trm (* val x = new {...} in t *)
  | trm_call: trm -> mtd_label -> trm -> trm (* t1.m(t2) *)
with def : Set :=
  | def_typ : typ_label -> typ -> typ -> def (* same as dec_typ *)
  | def_mtd : mtd_label -> typ -> typ -> trm -> def (* one nameless argument *)
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env defs.

(** *** TODO Syntactic sugar *)


(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ _ => label_typ L
| def_mtd m _ _ _ => label_mtd m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_mtd m _ _ => label_mtd m
end.

Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of_def d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of_def d) ds = Some d.
Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.


(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k) 
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_or  T1 T2  => typ_or  (open_rec_typ k u T1) (open_rec_typ k u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_mtd m T U => dec_mtd m (open_rec_typ k u T) (open_rec_typ k u U)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  | trm_new ds t   => trm_new (open_rec_defs (S k) u ds) (* self ref *)
                              (open_rec_trm (S k) u t)
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L Lo Hi => def_typ L (open_rec_typ k u Lo) (open_rec_typ k u Hi)
  | def_mtd m T1 T2 e => def_mtd m (open_rec_typ k u T1) (open_rec_typ k u T2)
                         (open_rec_trm (S k) u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u D := open_rec_dec   0 u D.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.


(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar) : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => (fv_dec D)
  | typ_sel x L    => (fv_avar x)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_or  T U    => (fv_typ T) \u (fv_typ U)
  end
with fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_mtd m T U => (fv_typ T) \u (fv_typ U)
  end.

(* Since we define defs ourselves instead of using [list def], we don't have any
   termination proof problems: *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var x        => (fv_avar x)
  | trm_new ds t     => (fv_defs ds) \u (fv_trm t)
  | trm_call t1 m t2 => (fv_trm t1) \u (fv_trm t2)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T U   => (fv_typ T) \u (fv_typ U)
  | def_mtd _ T U u => (fv_typ T) \u (fv_typ U) \u (fv_trm u)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).


(* ###################################################################### *)
(** ** Operational Semantics *)

(** Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
    Whenever we introduce a new avar_f (only happens in red_new), we choose one
    which is not in the store, so we never have name clashes. *)
Inductive red : trm -> sto -> trm -> sto -> Prop :=
  (* computation rules *)
  | red_call: forall s x y m T U ds body,
      binds x ds s ->
      defs_has ds (def_mtd m T U body) ->
      red (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) s
          (open_trm y body) s
  | red_new: forall s ds t x,
      x # s ->
      red (trm_new ds t) s
          (open_trm x t) (s & x ~ (open_defs x ds))
  (* congruence rules *)
  | red_call1 : forall s o m a s' o',
      red o s o' s' ->
      red (trm_call o  m a) s
          (trm_call o' m a) s'
  | red_call2 : forall s x m a s' a',
      red a s a' s' ->
      red (trm_call (trm_var (avar_f x)) m a ) s
          (trm_call (trm_var (avar_f x)) m a') s'.


(* ###################################################################### *)
(** ** Typing *)

(* "optimization" of typ_and (makes some proofs simpler, but others more
    complicated!!).
   If intersect_dec and thus typ_has uses intersect_typ instead of typ_and, 
   we know that if a decl returned by typ_has is "equivalent" to a bottom-decl,
   it's actually also structurally equal.
   Or in other words: Instead of returning (dec_fld l (typ_and typ_bot T)),
   typ_has will return just (dec_fld l typ_bot).
Definition intersect_typ(T1 T2: typ): typ := If T1 = T2 then T1 else
match T1, T2 with
| typ_top, _ => T2
| _, typ_top => T1
| typ_bot, _ => typ_bot
| _, typ_bot => typ_bot
| _, _       => typ_and T1 T2
end.

Definition union_typ(T1 T2: typ): typ := If T1 = T2 then T1 else
match T1, T2 with
| typ_top, _ => typ_top
| _, typ_top => typ_top
| typ_bot, _ => T2
| _, typ_bot => T1
| _, _       => typ_or T1 T2
end.
*)

(* returns (option dec) because it's not total. *)
Definition intersect_dec(D1 D2: dec): option dec :=
  If label_of_dec D1 = label_of_dec D2 then
    match D1, D2 with
    | (dec_typ L S1 U1), (dec_typ _ S2 U2)
      => Some (dec_typ L (typ_or S1 S2) (typ_and U1 U2))
    | (dec_mtd m S1 U1), (dec_mtd _ S2 U2)
      => Some (dec_mtd m (typ_or S1 S2) (typ_and U1 U2))
    | _, _ => None
    end
  else
    None.

Definition union_dec(D1 D2: dec): option dec :=
  If label_of_dec D1 = label_of_dec D2 then
    match D1, D2 with
    | (dec_typ L S1 U1), (dec_typ _ S2 U2)
      => Some (dec_typ L (typ_and S1 S2) (typ_or U1 U2))
    | (dec_mtd m S1 U1), (dec_mtd _ S2 U2)
      => Some (dec_mtd m (typ_and S1 S2) (typ_or U1 U2))
    | _, _ => None
    end
  else
    None.

(*
Definition intersect_dec(D1 D2: dec): option dec :=
  If label_of_dec D1 = label_of_dec D2 then
    match D1, D2 with
    | (dec_typ L S1 U1), (dec_typ _ S2 U2)
      => Some (dec_typ L (union_typ S1 S2) (intersect_typ U1 U2))
    | (dec_mtd m S1 U1), (dec_mtd _ S2 U2)
      => Some (dec_mtd m (union_typ S1 S2) (intersect_typ U1 U2))
    | _, _ => None
    end
  else
    None.

Definition union_dec(D1 D2: dec): option dec :=
  If label_of_dec D1 = label_of_dec D2 then
    match D1, D2 with
    | (dec_typ L S1 U1), (dec_typ _ S2 U2)
      => Some (dec_typ L (intersect_typ S1 S2) (union_typ U1 U2))
    | (dec_mtd m S1 U1), (dec_mtd _ S2 U2)
      => Some (dec_mtd m (intersect_typ S1 S2) (union_typ U1 U2))
    | _, _ => None
    end
  else
    None.
*)

Notation "D1 && D2 == D3" := (intersect_dec D1 D2 = Some D3) (at level 40).
Notation "D1 || D2 == D3" := (union_dec D1 D2 = Some D3) (at level 40).

Definition dec_bot(l: label): dec := match l with
  | label_typ L => dec_typ L typ_top typ_bot
  | label_mtd m => dec_mtd m typ_top typ_bot
end.

(*
Definition dec_top(l: label): dec := match l with
  | label_typ L => dec_typ L typ_bot typ_top
  | label_mtd m => dec_mtd m typ_bot typ_top
end.
*)

Inductive typ_has: ctx -> typ -> dec -> Prop :=
(*| typ_top_has: typ_top has nothing *)
  | typ_bot_has: forall G l,
      typ_has G typ_bot (dec_bot l)
  | typ_rcd_has: forall G D,
      typ_has G (typ_rcd D) D
  | typ_sel_has: forall G x T L Lo Hi D,
      binds x T G ->
      typ_has  G T (dec_typ L Lo Hi) ->
      typ_has  G Hi D ->
      typ_has G (typ_sel (avar_f x) L) D
  | typ_and_has_1: forall G T1 T2 D,
      typ_has G T1 D ->
      typ_hasnt G T2 (label_of_dec D) ->
      typ_has G (typ_and T1 T2) D
  | typ_and_has_2: forall G T1 T2 D,
      typ_hasnt G T1 (label_of_dec D) ->
      typ_has G T2 D ->
      typ_has G (typ_and T1 T2) D
  | typ_and_has_12: forall G T1 T2 D1 D2 D3,
      typ_has G T1 D1 ->
      typ_has G T2 D2 ->
      D1 && D2 == D3 ->
      typ_has G (typ_and T1 T2) D3
  | typ_or_has: forall G T1 T2 D1 D2 D3,
      typ_has G T1 D1 ->
      typ_has G T2 D2 ->
      D1 || D2 == D3 ->
      typ_has G (typ_or T1 T2) D3
with typ_hasnt: ctx -> typ -> label -> Prop :=
  | typ_top_hasnt: forall G l,
      typ_hasnt G typ_top l
(*| typ_bot_hasnt: There's no label that typ_bot hasn't. *)
  | typ_rcd_hasnt: forall G D l,
      l <> label_of_dec D ->
      typ_hasnt G (typ_rcd D) l
  | typ_sel_hasnt: forall G x T L Lo Hi l,
      binds x T G ->
      typ_has    G T (dec_typ L Lo Hi) ->
      typ_hasnt  G Hi l ->
      typ_hasnt G (typ_sel (avar_f x) L) l
  | typ_and_hasnt: forall G T1 T2 l, 
      typ_hasnt G T1 l ->
      typ_hasnt G T2 l ->
      typ_hasnt G (typ_and T1 T2) l
(* could also just have two typ_or_hasnt rules, which only explore 1 type, but for
   the proofs, it's better to always explore both types *)
  | typ_or_hasnt_1: forall G T1 T2 D,
      typ_hasnt G T1 (label_of_dec D) ->
      typ_has G T2 D ->
      typ_hasnt G (typ_or T1 T2) (label_of_dec D)
  | typ_or_hasnt_2: forall G T1 T2 D,
      typ_has G T1 D ->
      typ_hasnt G T2 (label_of_dec D) ->
      typ_hasnt G (typ_or T1 T2) (label_of_dec D)
  | typ_or_hasnt_12: forall G T1 T2 l,
      typ_hasnt G T1 l ->
      typ_hasnt G T2 l ->
      typ_hasnt G (typ_or T1 T2) l.
 
(* [stable_typ T] means that T's members don't change under narrowing.
   TODO this can be extended to include "class types", and aliases to stable types. *)
Inductive stable_typ: typ -> Prop :=
| stable_top: stable_typ typ_top
| stable_bot: stable_typ typ_bot
| stable_rcd: forall D, stable_typ (typ_rcd D)
(* Note: typ_sel is not stable (that's the whole point) *)
| stable_and: forall T1 T2, stable_typ T1 -> stable_typ T2 -> stable_typ (typ_and T1 T2)
| stable_or : forall T1 T2, stable_typ T1 -> stable_typ T2 -> stable_typ (typ_or  T1 T2).

(* wf means "well-formed", not "well-founded" ;-)
   G; A |- T wf       G: context
                      A: assumptions (set of types assumed to be wf)
                      T: type to check

Let's distinguish between "computational types" and "non-expansive types" the same
way as Julien Cretin does in his thesis:
Computational types are those which have a corresponding constructor on term level,
i.e. only typ_rcd.
Non-expansive types are those which are just "aliases" [in a broad sense ;-)],
i.e. bounds of path types and/or-types.
Since we only want to allow guarded recursion, only the rules for compuational types
add the type being checked to the assumptions (i.e. only wf_rcd). *)
Inductive wf_typ_impl: ctx -> fset typ -> typ -> Prop :=
  | wf_top: forall G A,
      wf_typ_impl G A typ_top
  | wf_bot: forall G A,
      wf_typ_impl G A typ_bot
  | wf_hyp: forall G A T,
      T \in A ->
      wf_typ_impl G A T
  | wf_rcd: forall G A D,
      wf_dec_impl G (A \u \{(typ_rcd D)}) D ->
      wf_typ_impl G A (typ_rcd D)
  | wf_sel: forall G A x X L T U,
      binds x X G ->
      stable_typ X -> (* <-- important restriction *)
      typ_has G X (dec_typ L T U) ->
      wf_typ_impl G A X ->
      wf_typ_impl G A T ->
      wf_typ_impl G A U ->
      wf_typ_impl G A (typ_sel (avar_f x) L)
  | wf_and: forall G A T1 T2,
      wf_typ_impl G A T1 ->
      wf_typ_impl G A T2 ->
      wf_typ_impl G A (typ_and T1 T2)
  | wf_or: forall G A T1 T2,
      wf_typ_impl G A T1 ->
      wf_typ_impl G A T2 ->
      wf_typ_impl G A (typ_or T1 T2)
with wf_dec_impl: ctx -> fset typ -> dec -> Prop :=
  | wf_tmem: forall G A L Lo Hi,
      wf_typ_impl G A Lo ->
      wf_typ_impl G A Hi ->
      wf_dec_impl G A (dec_typ L Lo Hi)
  | wf_mtd: forall G A m U V,
      wf_typ_impl G A U ->
      wf_typ_impl G A V ->
      wf_dec_impl G A (dec_mtd m U V).

Notation wf_typ G T := (wf_typ_impl G \{} T).
Notation wf_dec G D := (wf_dec_impl G \{} D).

Inductive subtyp: ctx -> typ -> typ -> Prop :=
  | subtyp_refl: forall G T,
      wf_typ G T ->
      subtyp G T T
  | subtyp_top: forall G T,
      wf_typ G T ->
      subtyp G T typ_top
  | subtyp_bot: forall G T,
      wf_typ G T ->
      subtyp G typ_bot T
  | subtyp_rcd: forall G D1 D2,
      subdec G D1 D2 ->
      subtyp G (typ_rcd D1) (typ_rcd D2)
  | subtyp_sel_l: forall G x X L T U,
      binds x X G ->
      wf_typ G X ->
      stable_typ X -> (* <-- important restriction *)
      typ_has G X (dec_typ L T U) ->
      subtyp G T U -> (* <-- probably not needed, but keep for symmetry with subtyp_sel_r *)
      subtyp G (typ_sel (avar_f x) L) U
  | subtyp_sel_r: forall G x X L T U,
      binds x X G ->
      wf_typ G X ->
      stable_typ X -> (* <-- important restriction *)
      typ_has G X (dec_typ L T U) ->
      subtyp G T U -> (* <-- makes proofs a lot easier!! *)
      subtyp G T (typ_sel (avar_f x) L)
  | subtyp_and: forall G T U1 U2,
      subtyp G T U1 ->
      subtyp G T U2 ->
      subtyp G T (typ_and U1 U2)
  | subtyp_and_l: forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp G (typ_and T1 T2) T1
  | subtyp_and_r: forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp G (typ_and T1 T2) T2
  | subtyp_or: forall G T1 T2 U,
      subtyp G T1 U ->
      subtyp G T2 U ->
      subtyp G (typ_or T1 T2) U
  | subtyp_or_l: forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp G T1 (typ_or T1 T2)
  | subtyp_or_r: forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp G T2 (typ_or T1 T2)
  | subtyp_trans: forall G T1 T2 T3,
      subtyp G T1 T2 ->
      subtyp G T2 T3 ->
      subtyp G T1 T3
(* Error: Non strictly positive occurrence of "subtyp"
   --> define the whole subtyping function as a Fixpoint with fuel?
   --> or put the assumption in ty_trm? *)
(*| subtyp_hyp: forall x X G L Lo Hi T1 T2,
      binds x X G ->
      typ_has G X (dec_typ L Lo Hi) ->
      (subtyp G Lo Hi -> subtyp G T1 T2) ->
      subtyp G T1 T2
*)
with subdec: ctx -> dec -> dec -> Prop :=
  | subdec_typ: forall G L Lo1 Hi1 Lo2 Hi2,
      subtyp G Lo2 Lo1 ->
      subtyp G Hi1 Hi2 ->
      subdec G (dec_typ L Lo1 Hi1) (dec_typ L Lo2 Hi2)
  | subdec_mtd: forall m G S1 T1 S2 T2,
      subtyp G S2 S1 ->
      subtyp G T1 T2 ->
      subdec G (dec_mtd m S1 T1) (dec_mtd m S2 T2).

Definition good_bounds_typ(G: ctx)(T: typ) :=
  wf_typ G T /\ (forall L Lo Hi, typ_has G T (dec_typ L Lo Hi) -> subtyp G Lo Hi).

Definition good_bounds_old(G: ctx) :=
  forall x X, binds x X G -> good_bounds_typ G X.

Inductive good_bounds: ctx -> Prop :=
  | good_bounds_empty:
      good_bounds empty
  | good_bounds_push: forall G x T,
      good_bounds G ->
      good_bounds_typ (G & x ~ T) T ->
      good_bounds (G & x ~ T).

(** 
Can we avoid shrink_good_bounds?
Or defer it until we have a wf_sto and only shrink to a prefix?

ty_hyp hyp can pick any subenv --> weakening should work
 --> but inversion lemmas need to shrink good env before giving it to hyp of ty_hyp 
but since ty_hyp has a subenv hyp, we and
  subenv G1 G2 /\ good_bounds G2 -> good_bounds G1
we're fine there.
But if we have this, we can also leave things as is and just apply this implication in
weakening.

Because really, this one:
  subenv G1 G2 /\ good_bounds G2 -> good_bounds G1
is the hard part --> approx the same as shrink_good_bounds:

  ok (G1 & G2 & G3) ->
  (forall x X, binds x X (G1 & G3) -> wf_typ (G1 & G3) X) ->
  good_bounds (G1 & G2 & G3) ->
  good_bounds (G1 &      G3).

Q: What kinds of env shrinking are allowed?
Only at the end --> can shrink wf_sto in inversion lemmas

Instead of encoding the dependency structure in the subenv judgment (or good_bounds),
already encode it in the env itself
==--> unique destruction of the env into smaller, consistent sub-envs
==   (which is a desirable property)

-----

closed_env which can insert in the middle, and good_bounds, and subenv following
 the same structure?

*)

(* ###################################################################### *)
(** ** Closed *)

Inductive closed_typ: ctx -> typ -> Prop :=
  | closed_top: forall G,
      closed_typ G typ_top
  | closed_bot: forall G,
      closed_typ G typ_bot
  | closed_rcd: forall G D,
      closed_dec G D ->
      closed_typ G (typ_rcd D)
  | closed_sel: forall G x X L,
      binds x X G ->
      closed_typ G (typ_sel (avar_f x) L)
  | closed_and: forall G T1 T2,
      closed_typ G T1 ->
      closed_typ G T2 ->
      closed_typ G (typ_and T1 T2)
  | closed_or: forall G T1 T2,
      closed_typ G T1 ->
      closed_typ G T2 ->
      closed_typ G (typ_or T1 T2)
with closed_dec: ctx -> dec -> Prop :=
  | closed_tmem: forall G L Lo Hi,
      closed_typ G Lo ->
      closed_typ G Hi ->
      closed_dec G (dec_typ L Lo Hi)
  | closed_mtd: forall G m U V,
      closed_typ G U ->
      closed_typ G V ->
      closed_dec G (dec_mtd m U V).

Inductive closed_env: ctx -> Prop :=
  | closed_empty: closed_env empty
  | closed_insert: forall G1 G2 x T,
      closed_env G1 ->
      closed_env G2 ->
      x # G1 ->
      x # G2 ->
      closed_typ (G1 & x ~ T) T ->
      closed_env (G1 & x ~ T & G2).

(*
Goal: all valid weakening steps (defined by a subenv relation)
must be such that going from good_bounds on the bigger env
to good_bounds on the smaller env is easy.

------

weakening axiom (rule)?

--> inversion lemmas will "push-back" weakening axiom (for ty_trm/def/defs judgments they
return) or apply the weakening lemmas before returning (for has/subtyp judgments).
BUT in order to apply their IH, they'll have to shrink the good_bounds hyp!

-------

weakening / ty_mdef will suppose good bounds for 
 G1 & G2 & G3 & x ~ T
(because of T which might have bad bounds now)

but IH wants good bounds on (if good_bounds is a hyp of weakening)
G1 & G3 & x ~ T

-------


Prove permutation lemmas (should be easy),
then only prove weakening for appending at the end,
and ty_hyp supposes good_bounds on a closed prefix of env.
Weakening on ty_hyp will still be easy, because if
G1 is a closed prefix of G2, it's also a closed prefix of (G2 & G3).
In the inversion lemmas, we'll have to provide a good_bounds hyp to ty_hyp, but
we can get that for all prefixes of G because wf_sto is defined "step-by-step".

BUT how will the permutation lemma deal with ty_hyp? "being prefix" is not preserved
by permutation!

-----

Next try:

Prove permutation lemmas (should be easy),
then only prove weakening for appending at the end,
and ty_hyp supposes good_bounds on a the same of env as in its conclusion.
Weakening on ty_hyp will need to shrink good_bounds (G1 & G2) to good_bounds G1,
which is also hard. Except if we define good_bounds step-wise, but then the
permutation lemma won't work any more, because it would have to permute good_bounds.



*)
(*
Inductive subenv: ctx -> ctx -> Prop :=
(*| subenv_refl: forall G,
      subenv G G not needed because subenv_sub with subtyp_refl yield this *)
  | subenv_sub: forall G1 x S1 S2 G2,
      stable_typ S1 ->
      subtyp (G1 & x ~ S1) S1 S2 ->
      subenv (G1 & x ~ S1 & G2) (G1 & x ~ S2 & G2)
  | subenv_trans: forall G1 G2 G3,
      subenv G1 G2 ->
      subenv G2 G3 ->
      subenv G1 G3.
*)

Inductive subenv: ctx -> ctx -> Prop :=
  | subenv_empty:
      subenv empty empty
  | subenv_sub: forall G1 G2 x T1 T2,
      subenv G1 G2 ->
      stable_typ T1 ->
      subtyp (G1 & x ~ T1) T1 T2 ->
      subenv (G1 & x ~ T1) (G2 & x ~ T2)
  | subenv_push: forall G1 G2 x T,
      (* here we don't require T to be stable *)
      subenv G1 G2 ->
      subenv (G1 & x ~ T) (G2 & x ~ T).

(* typing on term level is always imprecise (can use subsumption) *)
Inductive ty_trm: ctx -> trm -> typ -> Prop :=
  | ty_var: forall G x T,
      binds x T G ->
      wf_typ G T ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_call: forall G t T m U V u,
      ty_trm G t T ->
      typ_has G T (dec_mtd m U V) ->
      ty_trm G u U -> (* <-- allows subsumption *)
      wf_typ G V ->
      ty_trm G (trm_call t m u) V
  | ty_new: forall L G1 G2 ds T u U,
      (forall x, x \notin L ->
         ty_defs (G1 & x ~ (open_typ x T) (*& G2*)) (open_defs x ds) (open_typ x T)) ->
   (* not & G2 because otherwise we'll have to strengthen good_bounds_typ *)
      (forall x, x \notin L ->
         ty_trm (G1 & x ~ (open_typ x T) (*& G2*)) (open_trm x u) U) ->
      wf_typ G1 U -> (* <-- even stronger than x \notin fv_typ U *)
      ty_trm (G1 & G2) (trm_new ds u) U
  (* If you want to suppose good bounds, you must prove the typing derivation not just
     for G, but for all subenvs of G, because otherwise narrowing needs un-narrowing *)
  | ty_hyp: forall G t T,
      wf_typ G T ->
      (forall G', subenv G' G -> good_bounds G' -> ty_trm G' t T) ->
      ty_trm G t T
  (* Ideally, this rule would already be in subtyp, but it can't be there because
      of Coq's strict positivity restriction.
  | ty_hyp: forall G t T,
      wf_typ G T ->
      (good_bounds G -> ty_trm G t T) ->
      ty_trm G t T *)
(* imprecise typing: subsumption allowed *)
  | ty_sbsm: forall G t T1 T2,
      ty_trm G t T1 ->
      subtyp G T1 T2 ->
      ty_trm G t T2
with ty_def: ctx -> def -> dec -> Prop :=
  | ty_tdef: forall G L T U,
      subtyp G T U -> (* <-- only allow realizable bounds *)
      ty_def G (def_typ L T U) (dec_typ L T U)
  | ty_mdef: forall L m G1 G2 T U u,
      (* These wf checks ensure that x does not appear in T and U.
         But note that it is allowed to occur in the precise type of u. *)
      wf_typ G1 T ->
      wf_typ G1 U ->
      (forall x, x \notin L ->
         ty_trm (G1 & x ~ T (*& G2*)) (open_trm x u) U) -> (* <-- allows subsumption *)
      ty_def (G1 & G2) (def_mtd m T U u) (dec_mtd m T U)
(*
  | ty_def_hyp: forall G d D,
      wf_dec G D ->
      label_of_def d = label_of_dec D ->
      (forall G', subenv G' G -> good_bounds G' -> ty_def G' d D) ->
      ty_def G d D
*)
with ty_defs: ctx -> defs -> typ -> Prop :=
  | ty_defs_nil: forall G,
      ty_defs G defs_nil typ_top
  | ty_defs_cons: forall G ds d T D,
      ty_defs G ds T ->
      ty_def G d D ->
      defs_hasnt ds (label_of_def d) -> (* <-- no duplicates *)
      ty_defs G (defs_cons ds d) (typ_and T (typ_rcd D)).

(** *** Well-formed store *)
Inductive wf_sto: sto -> ctx -> Prop :=
  | wf_sto_empty: wf_sto empty empty
  | wf_sto_push: forall s G x ds T,
      wf_sto s G ->
      x # s ->
      x # G ->
      (* Note that ds and T were already opened with x. *)
      ty_defs (G & x ~ T) ds T ->
      wf_sto (s & x ~ ds) (G & x ~ T).


(* ###################################################################### *)
(** ** Statements we want to prove *)

Definition progress := forall s G e T,
  wf_sto s G ->
  ty_trm G e T -> 
  (
    (* can step *)
    (exists e' s', red e s e' s') \/
    (* or is a value *)
    (exists x o, e = (trm_var (avar_f x)) /\ binds x o s)
  ).

Definition preservation := forall s G e T e' s',
  wf_sto s G -> ty_trm G e T -> red e s e' s' ->
  (exists G', wf_sto s' (G & G') /\ ty_trm (G & G') e' T).


(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme typ_mut := Induction for typ Sort Prop
with   dec_mut := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme trm_mut  := Induction for trm  Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, def_mut, defs_mut.

Scheme typ_has_mut := Induction for typ_has Sort Prop
with typ_hasnt_mut := Induction for typ_hasnt Sort Prop.
Combined Scheme typ_has_mutind from typ_has_mut, typ_hasnt_mut.

Scheme wf_typ_mut := Induction for wf_typ_impl Sort Prop
with   wf_dec_mut := Induction for wf_dec_impl Sort Prop.
Combined Scheme wf_mutind from wf_typ_mut, wf_dec_mut.

Scheme subtyp_mut := Induction for subtyp Sort Prop
with   subdec_mut := Induction for subdec Sort Prop.
Combined Scheme subtyp_mutind from subtyp_mut, subdec_mut.

Scheme ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop.
Combined Scheme ty_mutind from ty_trm_mut, ty_def_mut, ty_defs_mut.


(* ###################################################################### *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x         ) in
  let B := gather_vars_with (fun x : var       => \{ x }    ) in
  let C := gather_vars_with (fun x : ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x : sto       => dom x     ) in
  let E := gather_vars_with (fun x : avar      => fv_avar  x) in
  let F := gather_vars_with (fun x : trm       => fv_trm   x) in
  let G := gather_vars_with (fun x : def       => fv_def   x) in
  let H := gather_vars_with (fun x : defs      => fv_defs  x) in
  let I := gather_vars_with (fun x : typ       => fv_typ   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac in_empty_contradiction :=
  solve [match goal with
  | H: _ \in \{} |- _ => rewrite in_empty in H; exfalso; exact H
  end].

Ltac eq_specialize :=
  repeat match goal with
  | H:                 _ = _ -> _ |- _ => specialize (H         eq_refl)
  | H: forall _      , _ = _ -> _ |- _ => specialize (H _       eq_refl)
  | H: forall _ _    , _ = _ -> _ |- _ => specialize (H _ _     eq_refl)
  | H: forall _ _ _  , _ = _ -> _ |- _ => specialize (H _ _ _   eq_refl)
  | H: forall _ _ _ _, _ = _ -> _ |- _ => specialize (H _ _ _ _ eq_refl)
  end.

Ltac crush := eq_specialize; eauto.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors
  stable_typ
  typ_has typ_hasnt
  wf_typ_impl wf_dec_impl
  subtyp subdec
  ty_trm ty_def ty_defs.
Hint Constructors wf_sto.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.

(** *** Tactics for the examples *)

Ltac do_open :=
  repeat match goal with
  | _: _ |- context[open_avar _ _] => unfold open_avar; simpl
  | _: _ |- context[open_typ  _ _] => unfold open_typ ; simpl
  | _: _ |- context[open_dec  _ _] => unfold open_dec ; simpl
  | _: _ |- context[open_trm  _ _] => unfold open_trm ; simpl
  | _: _ |- context[open_def  _ _] => unfold open_def ; simpl
  | _: _ |- context[open_defs _ _] => unfold open_defs; simpl
  | _: _ |- context[(If _ = _ then _ else _)] => case_if; simpl
  end.

Ltac prove_defs_hasnt := solve [
  repeat match goal with
  | _: _ |- defs_hasnt _ _ => unfold defs_hasnt; simpl; auto
  | _: _ |- context[(If _ = _ then _ else _)] => case_if; simpl; auto
  end].

Ltac split_ty_defs :=
  repeat (prove_defs_hasnt || apply ty_defs_cons || apply ty_defs_nil).

Ltac prove_binds := solve [
  unfold binds; rewrite EnvOps.get_def; unfold get_impl;
  repeat (rewrite <- cons_to_push || case_if); auto].

Ltac prove_in_fset := solve [
  repeat rewrite in_union;
  repeat rewrite in_singleton;
  auto 10].


(* ###################################################################### *)
(** ** Examples *)

(*
val glob = new {
  E: Top..Top,
  Stream: Bot..{head: Top -> glob.E} /\ {tail: Top -> glob.Stream}
};
val unit = new {};
val stream = new { head(x: Top): glob.E = unit, tail(x: Top): glob.Stream = stream };
stream.tail(unit).tail(unit).head(unit)
*)

Module Examples1.

Parameter E: typ_label.
Parameter Stream: typ_label.
Axiom E_ne_Stream: E <> Stream.
Parameter head: mtd_label.
Parameter tail: mtd_label.
Axiom head_ne_tail: head <> tail.

Definition ex1: trm :=
trm_new (defs_cons (defs_cons defs_nil
  (def_typ E typ_top typ_top))
  (def_typ Stream typ_bot (typ_and
       (typ_rcd (dec_mtd head typ_top (typ_sel (avar_b 0) E)))
       (typ_rcd (dec_mtd tail typ_top (typ_sel (avar_b 0) Stream)))))
)
(trm_new defs_nil
(trm_var (avar_b 0))).

Fact tc1: ty_trm empty ex1 typ_top.
Proof.
  assert (ne1: label_typ E <> label_typ Stream). {
    intro. inversions H. apply E_ne_Stream. assumption.
  }
  assert (ne2: label_mtd head <> label_mtd tail). {
    intro. inversions H. apply head_ne_tail. assumption.
  }
  unfold ex1.
  rewrite <- (concat_empty_r empty).
  apply ty_new with \{} (typ_and (typ_and typ_top
    (typ_rcd (dec_typ E typ_top typ_top)))
    (typ_rcd (dec_typ Stream typ_bot (typ_and
       (typ_rcd (dec_mtd head typ_top (typ_sel (avar_b 0) E)))
       (typ_rcd (dec_mtd tail typ_top (typ_sel (avar_b 0) Stream))))))).
  { intros glob _. do_open.
    remember (typ_and
               (typ_rcd (dec_mtd head typ_top (typ_sel (avar_f glob) E)))
               (typ_rcd (dec_mtd tail typ_top (typ_sel (avar_f glob) Stream))))
    as TStream eqn: EqTStream.
    split_ty_defs.
    { auto. }
    { apply ty_tdef. apply subtyp_bot.
      rewrite concat_empty_l in *.
      (*rewrite concat_empty_r in *.*)
      rewrite EqTStream at 2.
      apply wf_and.
      { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
        eapply (wf_sel ((binds_single_eq _ _))).
        { eauto. }
        { eauto. }
        { repeat apply wf_and.
          { apply wf_top. }
          { auto. }
          { apply wf_rcd. apply wf_tmem.
            { apply wf_bot. }
            { rewrite EqTStream at 3.
              apply wf_and.
              { apply wf_hyp. prove_in_fset. }
              { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                eapply (wf_sel ((binds_single_eq _ _))).
                { eauto. }
                { eauto. }
                { repeat apply wf_and.
                  { apply wf_top. }
                  { auto. }
                  { apply wf_rcd. apply wf_tmem.
                    { apply wf_bot. }
                    { rewrite EqTStream at 4.
                      apply wf_and.
                      { apply wf_hyp. prove_in_fset. }
                      { apply wf_hyp. prove_in_fset. }
                    }
                  }
                }
                { apply wf_bot. }
                { rewrite EqTStream at 3.
                  apply wf_and.
                  { apply wf_hyp. prove_in_fset. }
                  { apply wf_hyp. prove_in_fset. }
                }
              }
            }
          }
        }
        { eauto. }
        { apply wf_top. }
      }
      { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
        eapply (wf_sel ((binds_single_eq _ _))).
        { eauto. }
        { eauto. }
        { repeat apply wf_and.
          { apply wf_top. }
          { auto. }
          { apply wf_rcd. apply wf_tmem.
            { apply wf_bot. }
            { rewrite EqTStream at 3.
              apply wf_and.
              { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                eapply (wf_sel ((binds_single_eq _ _))).
                { eauto. }
                { eauto. }
                { repeat apply wf_and.
                  { apply wf_top. }
                  { auto. }
                  { apply wf_rcd. apply wf_tmem.
                    { apply wf_bot. }
                    { rewrite EqTStream at 4.
                      apply wf_and.
                      { apply wf_hyp. prove_in_fset. }
                      { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                        eapply (wf_sel ((binds_single_eq _ _))).
                        { eauto. }
                        { eauto. }
                        { repeat apply wf_and.
                          { apply wf_top. }
                          { auto. }
                          { apply wf_rcd. apply wf_tmem.
                            { apply wf_bot. }
                            { rewrite EqTStream at 5.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { apply wf_bot. }
                        { rewrite EqTStream at 4.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_hyp. prove_in_fset. }
                        }
                      }
                    }
                  }
                }
                { apply wf_top. }
                { apply wf_top. }
              }
              { apply wf_hyp. prove_in_fset. }
            }
          }
        }
        { apply wf_bot. }
        { rewrite EqTStream at 2.
          apply wf_and.
          { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
            eapply (wf_sel ((binds_single_eq _ _))).
            { eauto. }
            { eauto. }
            { repeat apply wf_and.
              { apply wf_top. }
              { auto. }
              { apply wf_rcd. apply wf_tmem.
                { apply wf_bot. }
                { rewrite EqTStream at 3.
                  apply wf_and.
                  { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                    eapply (wf_sel ((binds_single_eq _ _))).
                    { eauto. }
                    { eauto. }
                    { repeat apply wf_and.
                      { apply wf_top. }
                      { auto. }
                      { apply wf_rcd. apply wf_tmem.
                        { apply wf_bot. }
                        { rewrite EqTStream at 4.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                            eapply (wf_sel ((binds_single_eq _ _))).
                            { eauto. }
                            { eauto. }
                            { repeat apply wf_and.
                              { apply wf_top. }
                              { auto. }
                              { apply wf_rcd. apply wf_tmem.
                                { apply wf_bot. }
                                { rewrite EqTStream at 5.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { apply wf_bot. }
                            { rewrite EqTStream at 4.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                      }
                    }
                    { apply wf_top. }
                    { apply wf_top. }
                  }
                  { apply wf_hyp. prove_in_fset. }
                }
              }
            }
            { apply wf_top. }
            { apply wf_top. }
          }
          { apply wf_hyp. prove_in_fset. }
        }
      }
    }
  }
  { intros glob _. do_open. apply ty_new with \{ glob } typ_top.
    { intros unit N. split_ty_defs. }
    { intros unit N. do_open. (*rewrite concat_empty_l, concat_empty_r.*) apply ty_var.
      { prove_binds. }
      { apply wf_top. }
    }
    { apply wf_top. }
   }
  { apply wf_top. }
Qed.

Print Assumptions tc1.

End Examples1.


(* ###################################################################### *)
(** ** Definition of var-by-var substitution *)

(** Note that substitution is not part of the definitions, because for the
    definitions, opening is sufficient. For the proofs, however, we also
    need substitution, but only var-by-var substitution, not var-by-term
    substitution. That's why we don't need a judgment asserting that a term
    is locally closed. *)

Definition subst_avar (z: var) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => avar_b i
  | avar_f x => If x = z then (avar_f u) else (avar_f x)
  end.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_sel x L    => typ_sel (subst_avar z u x) L
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_or  T1 T2  => typ_or  (subst_typ z u T1) (subst_typ z u T2)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_mtd m T U => dec_mtd m (subst_typ z u T) (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_new ds t     => trm_new (subst_defs z u ds) (subst_trm z u t)
  | trm_call t1 m t2 => trm_call (subst_trm z u t1) m (subst_trm z u t2)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ L T1 T2   => def_typ L (subst_typ z u T1) (subst_typ z u T2)
  | def_mtd m T1 T2 b => def_mtd m (subst_typ z u T1) (subst_typ z u T2) (subst_trm z u b)
  end
with subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.

Definition subst_ctx (z: var) (u: var) (G: ctx) : ctx := map (subst_typ z u) G.


(* ###################################################################### *)
(** ** Lemmas for var-by-var substitution *)

Lemma subst_fresh_avar: forall x y,
  (forall a: avar, x \notin fv_avar a -> subst_avar x y a = a).
Proof.
  intros. destruct* a. simpl. case_var*. simpls. notin_false.
Qed.

Lemma subst_fresh_typ_dec: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall D : dec , x \notin fv_dec  D  -> subst_dec  x y D  = D ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_avar.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec x y).
Definition subst_fresh_dec(x y: var) := proj2 (subst_fresh_typ_dec x y).

Lemma subst_fresh_trm_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec).
Qed.

Lemma invert_fv_ctx_types_push: forall x z T G,
  x \notin fv_ctx_types (G & z ~ T) -> x \notin fv_typ T /\ x \notin (fv_ctx_types G).
Proof.
  introv N.
  unfold fv_ctx_types in *.
  unfold fv_in_values in *.
  rewrite <- cons_to_push in *.
  rewrite values_def in *.
  unfold LibList.map in *.
  do 2 rewrite LibList.fold_right_cons in *.
  simpl in *.
  apply notin_union in N. exact N.
Qed.

Lemma subst_fresh_ctx: forall x y G,
  x \notin fv_ctx_types G -> subst_ctx x y G = G.
Proof.
  intros x y.
  apply (env_ind (fun G => x \notin fv_ctx_types G -> subst_ctx x y G = G)).
  + intro N. unfold subst_ctx. apply map_empty.
  + intros G z T IH N.
    apply invert_fv_ctx_types_push in N. destruct N as [N1 N2].
    unfold subst_ctx in *. rewrite map_push.
    rewrite (IH N2).
    rewrite ((proj1 (subst_fresh_typ_dec _ _)) _ N1).
    reflexivity.
Qed.

Definition subst_fvar(x y z: var): var := If z = x then y else z.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a) 
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall D : dec, forall n: nat,
     subst_dec x y (open_rec_dec n u D)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y D)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_avar.
Qed.

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec.
Qed.

Lemma subst_open_commute_dec: forall x y u D,
  subst_dec x y (open_dec u D) = open_dec (subst_fvar x y u) (subst_dec x y D).
Proof.
  intros. apply* subst_open_commute_typ_dec.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_trm_def_defs: forall x y u,
  (forall t : trm, forall n: Datatypes.nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall d : def , forall n: Datatypes.nat, 
     subst_def x y (open_rec_def n u d)
     = open_rec_def n (subst_fvar x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: Datatypes.nat, 
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*;
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ_dec).
Qed.

Lemma subst_open_commute_trm: forall x y u t,
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t).
Proof.
  intros. apply* subst_open_commute_trm_def_defs.
Qed.

Lemma subst_open_commute_defs: forall x y u ds,
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds).
Proof.
  intros. apply* subst_open_commute_trm_def_defs.
Qed.

(* "Introduce a substitution after open": Opening a term t with a var u is the
   same as opening t with x and then replacing x by u. *)
Lemma subst_intro_trm: forall x u t, x \notin (fv_trm t) ->
  open_trm u t = subst_trm x u (open_trm x t).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_trm.
  destruct (@subst_fresh_trm_def_defs x u) as [Q _]. rewrite* (Q t).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_defs: forall x u ds, x \notin (fv_defs ds) ->
  open_defs u ds = subst_defs x u (open_defs x ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_defs.
  destruct (@subst_fresh_trm_def_defs x u) as [_ [_ Q]]. rewrite* (Q ds).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_typ: forall x u T, x \notin (fv_typ T) ->
  open_typ u T = subst_typ x u (open_typ x T).
Proof.
  introv Fr. unfold open_typ. rewrite* subst_open_commute_typ.
  destruct (@subst_fresh_typ_dec x u) as [Q _]. rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_dec: forall x u D, x \notin (fv_dec D) ->
  open_dec u D = subst_dec x u (open_dec x D).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_dec.
  destruct (@subst_fresh_typ_dec x u) as [_ Q]. rewrite* (Q D).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_undo_avar: forall x y,
  (forall a, y \notin fv_avar a -> (subst_avar y x (subst_avar x y a)) = a).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + unfold fv_avar in H. assert (y <> v) by auto. repeat case_if; reflexivity.
Qed.

Lemma subst_undo_typ_dec: forall x y,
   (forall T , y \notin fv_typ  T  -> (subst_typ  y x (subst_typ  x y T )) = T )
/\ (forall D , y \notin fv_dec  D  -> (subst_dec  y x (subst_dec  x y D )) = D ).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*.
  apply* subst_undo_avar.
Qed.

Lemma subst_undo_trm_def_defs: forall x y,
   (forall t , y \notin fv_trm  t  -> (subst_trm  y x (subst_trm  x y t )) = t )
/\ (forall d , y \notin fv_def  d  -> (subst_def  y x (subst_def  x y d )) = d )
/\ (forall ds, y \notin fv_defs ds -> (subst_defs y x (subst_defs x y ds)) = ds).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_def, fv_defs in *; f_equal*;
    (apply* subst_undo_avar || apply* subst_undo_typ_dec).
Qed.

Lemma subst_typ_undo: forall x y T,
  y \notin fv_typ T -> (subst_typ y x (subst_typ x y T)) = T.
Proof.
  apply* subst_undo_typ_dec.
Qed.

Lemma subst_trm_undo: forall x y t,
  y \notin fv_trm t -> (subst_trm y x (subst_trm x y t)) = t.
Proof.
  apply* subst_undo_trm_def_defs.
Qed.

Lemma subst_idempotent_avar: forall x y,
  (forall a, (subst_avar x y (subst_avar x y a)) = (subst_avar x y a)).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + repeat case_if; reflexivity.
Qed.

Lemma subst_idempotent_typ_dec: forall x y,
   (forall T, subst_typ x y (subst_typ x y T) = subst_typ x y T)
/\ (forall D, subst_dec x y (subst_dec x y D) = subst_dec x y D).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*.
  apply* subst_idempotent_avar.
Qed.

Lemma subst_idempotent_trm_def_defs: forall x y,
   (forall t , subst_trm  x y (subst_trm  x y t ) = (subst_trm  x y t ))
/\ (forall d , subst_def  x y (subst_def  x y d ) = (subst_def  x y d ))
/\ (forall ds, subst_defs x y (subst_defs x y ds) = (subst_defs x y ds)).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_def, fv_defs in *; f_equal*;
    (apply* subst_idempotent_avar || apply* subst_idempotent_typ_dec).
Qed.

Lemma subst_typ_idempotent: forall x y T,
  subst_typ x y (subst_typ x y T) = subst_typ x y T.
Proof.
  apply* subst_idempotent_typ_dec.
Qed.

Lemma subst_trm_idempotent: forall x y t,
  subst_trm x y (subst_trm x y t) = subst_trm x y t.
Proof.
  apply* subst_idempotent_trm_def_defs.
Qed.


(* ###################################################################### *)
(** ** Growing and shrinking the assumptions of wf *)

Lemma add_hyps_to_wf: forall A2,
   (forall G A1 T, wf_typ_impl G A1 T -> wf_typ_impl G (A1 \u A2) T) 
/\ (forall G A1 D, wf_dec_impl G A1 D -> wf_dec_impl G (A1 \u A2) D).
Proof.
  intro A2. apply wf_mutind; eauto.
  + (* case wf_hyp *)
    intros. apply wf_hyp. rewrite in_union. auto.
  + (* case wf_rcd *)
    intros G A1 D WfD IH.
    rewrite <- union_assoc in *.
    rewrite (union_comm \{ typ_rcd D } A2) in *.
    rewrite union_assoc in *.
    eauto.
Qed.

Definition add_hyps_to_wf_typ(G: ctx)(A1 A2: fset typ) := (proj1 (add_hyps_to_wf A2)) G A1.
Definition add_hyps_to_wf_dec(G: ctx)(A1 A2: fset typ) := (proj2 (add_hyps_to_wf A2)) G A1.

Lemma remove_hyp_from_wf: forall G A0 U, wf_typ_impl G A0 U ->
   (forall G' A T, wf_typ_impl G' A T -> G' = G -> wf_typ_impl G (A0 \u (A \- \{ U })) T) 
/\ (forall G' A D, wf_dec_impl G' A D -> G' = G -> wf_dec_impl G (A0 \u (A \- \{ U })) D).
Proof.
  introv WfU. apply wf_mutind; eauto.
  + (* case wf_hyp *)
    introv In Eq. subst G0.
    destruct (classicT (T = U)) as [Eq | Ne].
    - subst T. rewrite <- (union_empty_l (A \- \{ U })). apply add_hyps_to_wf. exact WfU.
    - apply wf_hyp. rewrite in_union. right. rewrite in_remove.
      apply (conj In). rewrite notin_singleton. exact Ne.
  + (* case wf_rcd *)
    introv WfD IH Eq. subst G0. eq_specialize.
    destruct (classicT (typ_rcd D = U)) as [Eq | Ne].
    - rewrite <- (union_empty_l (A \- \{ U })). subst U. apply add_hyps_to_wf. exact WfU.
    - assert (Eq: (A \u \{ typ_rcd D }) \- \{ U} = (A \- \{ U } \u \{ typ_rcd D})). {
        apply fset_extens; unfold subset; intros X H;
        repeat (rewrite in_remove in * || rewrite in_union in * ).
        + auto_star.
        + destruct H as [[H1 H2] | H].
          - auto.
          - rewrite in_singleton in H. subst X. split.
            * right. rewrite in_singleton. reflexivity.
            * rewrite notin_singleton. exact Ne.
      }
      rewrite Eq in IH.
      rewrite union_assoc in IH.
      apply (wf_rcd IH).
  + (* case wf_sel *)
    intros G0 A x X L Lo Hi Bi Sb XHas WfX IHX WfLo IHLo WfHi IHHi Eq. subst G0. eauto.
Qed.

Print Assumptions remove_hyp_from_wf.

Lemma singleton_remove: forall (T: Type) (v: T),
  \{ v } \- \{ v } = \{}.
Proof.
  intros. apply fset_extens; unfold subset; intros.
  - rewrite in_remove in H. destruct H as [H1 H2]. rewrite in_singleton in H1. subst.
    exfalso. rewrite notin_singleton in H2. apply H2. reflexivity.
  - exfalso. apply (notin_empty H).
Qed.

Lemma empty_remove: forall (T: Type) (v: T),
  \{} \- \{ v } = \{}.
Proof.
  intros. apply fset_extens; unfold subset; intros; rewrite in_remove in *.
  - exfalso. apply (in_empty_elim (proj1 H)).
  - exfalso. apply (in_empty_elim H).
Qed.

Lemma remove_notin: forall (T: Type) (A: fset T) (v: T),
  v \notin A -> A \- \{ v } = A.
Proof.
  intros. apply fset_extens; unfold subset; intros.
  - rewrite in_remove in H0. destruct H0. auto. 
  - rewrite in_remove. apply (conj H0). rewrite notin_singleton.
    intro. subst. apply H. assumption.
Qed.

Lemma remove_own_hyp_from_wf_dec: forall G A D,
  wf_dec_impl G (A \u \{ typ_rcd D }) D ->
  wf_dec_impl G (A \- \{ typ_rcd D }) D.
Proof.
  introv Wf1.
  assert (Eq: A \u \{ typ_rcd D } = (A \- \{ typ_rcd D }) \u \{ typ_rcd D }). {
    apply fset_extens; unfold subset; intros; rewrite in_union in *.
    + rewrite in_singleton in *. destruct (classicT (x = typ_rcd D)) as [Eq | Ne].
      - subst. auto.
      - left. rewrite in_remove. rewrite notin_singleton. destruct H.
        * auto.
        * exfalso. subst. auto.
    + rewrite in_singleton in *. destruct (classicT (x = typ_rcd D)) as [Eq | Ne].
      - subst. auto.
      - left. rewrite in_remove in H. rewrite notin_singleton in H. repeat destruct H.
        * auto.
        * exfalso. auto.
  }
  rewrite Eq in Wf1.
  lets Wf2: (wf_rcd Wf1).
  lets P: (proj2 (remove_hyp_from_wf Wf2)).
  specialize (P _ _ _ Wf1 eq_refl).
  rewrite <- union_remove in P. rewrite <- Eq in P. rewrite union_assoc in P.
  rewrite union_same in P. rewrite union_remove in P. rewrite singleton_remove in P.
  rewrite union_empty_r in P.
  exact P.
Qed.

Print Assumptions remove_own_hyp_from_wf_dec.

Lemma weak_remove_own_hyp_from_wf_dec: forall G A D,
  wf_dec_impl G (A \u \{ typ_rcd D }) D ->
  wf_dec_impl G A D.
Proof.
  introv Wf.
  destruct (classicT ((typ_rcd D) \in A)) as [In | Ni].
  * assert (Eq: (A \u \{ typ_rcd D}) = A). {
      apply fset_extens; unfold subset; intros.
      - rewrite in_union, in_singleton in H. destruct H; subst; auto.
      - rewrite in_union. auto.
    }
    rewrite Eq in Wf. exact Wf.
  * assert (Eq: A = (A \u \{ typ_rcd D}) \- \{ typ_rcd D }). {
      rewrite union_remove. rewrite singleton_remove. rewrite union_empty_r.
      rewrite (remove_notin Ni). reflexivity.
    }
    rewrite Eq.
    apply remove_own_hyp_from_wf_dec.
    rewrite <- union_assoc. rewrite union_same.
    exact Wf.
Qed.

Lemma invert_wf_rcd: forall G D,
  wf_typ G (typ_rcd D) ->
  wf_dec G D.
Proof.
  introv Wf. inversion Wf; subst.
  - in_empty_contradiction.
  - lets P: (remove_own_hyp_from_wf_dec H2). rewrite union_empty_l in *.
    rewrite empty_remove in P. exact P.
Qed.

Lemma invert_wf_and: forall G T1 T2,
  wf_typ G (typ_and T1 T2) ->
  wf_typ G T1 /\ wf_typ G T2.
Proof.
  introv Wf. inversions Wf.
  - in_empty_contradiction.
  - eauto.
Qed.

Lemma invert_wf_or: forall G T1 T2,
  wf_typ G (typ_or T1 T2) ->
  wf_typ G T1 /\ wf_typ G T2.
Proof.
  introv Wf. inversions Wf.
  - in_empty_contradiction.
  - eauto.
Qed.

Lemma invert_wf_sel: forall G x L,
  wf_typ G (typ_sel (avar_f x) L) ->
  exists X T U,
    binds x X G /\
    typ_has G X (dec_typ L T U) /\
    wf_typ G X /\
    wf_typ G T /\
    wf_typ G U.
Proof.
  intros. inversions H.
  - in_empty_contradiction.
  - exists X T U. eauto.
Qed.

Lemma invert_wf_sel_2: forall G a L,
  wf_typ G (typ_sel a L) ->
  exists x X T U,
    a = avar_f x /\
    binds x X G /\
    typ_has G X (dec_typ L T U) /\
    wf_typ G X /\
    wf_typ G T /\
    wf_typ G U.
Proof.
  intros. inversions H.
  - in_empty_contradiction.
  - exists x X T U. eauto 10.
Qed.

Ltac destruct_wf :=
  repeat match goal with
  | W: wf_dec _ (dec_typ _ _ _)         |- _ => inversions W
  | W: wf_dec _ (dec_mtd _ _ _)         |- _ => inversions W
  | W: wf_typ _ (typ_rcd _)             |- _ => apply invert_wf_rcd in W
  | W: wf_typ _ (typ_sel (avar_f _) _)  |- _ => apply invert_wf_sel in W;
                                                destruct W as [? [? [? [? [? [? [? ?]]]]]]]
  | W: wf_typ _ (typ_and _ _)           |- _ => apply invert_wf_and in W
  | W: wf_typ _ (typ_or _ _)            |- _ => apply invert_wf_or in W
  | H: wf_typ _ _ /\ wf_typ _ _         |- _ => destruct H
  | H: wf_dec _ _ /\ wf_dec _ _         |- _ => destruct H
  end.


(* ###################################################################### *)
(** ** Weakening for typ_has and wf *)

Lemma weaken_has:
   (forall G T D, typ_has G T D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    typ_has (G1 & G2 & G3) T D)
/\ (forall G T l, typ_hasnt G T l -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    typ_hasnt (G1 & G2 & G3) T l).
Proof.
  apply typ_has_mutind.
  + (* case typ_bot_has *) eauto.
  + (* case typ_rcd_has *) eauto.
  + (* case typ_sel_has *)
    introv Bi THas IH1 HiHas IH2 Eq Ok. subst. lets Bi': (binds_weaken Bi Ok). eauto.
  + (* case typ_and_has_1 *) eauto.
  + (* case typ_and_has_2 *) eauto.
  + (* case typ_and_has_12 *) eauto.
  + (* case typ_or_has *) eauto.
  + (* case typ_top_hasnt *) eauto.
  + (* case typ_rcd_hasnt *) eauto.
  + (* case typ_sel_hasnt *)
    introv Bi THas IH1 HiHasnt IH2 Eq Ok. subst. lets Bi': (binds_weaken Bi Ok). eauto.
  + (* case typ_and_hasnt *) eauto.
  + (* case typ_or_hasnt_1 *) eauto.
  + (* case typ_or_hasnt_2 *) eauto.
  + (* case typ_or_hasnt_12 *) eauto.
Qed.

Lemma weaken_has_middle: forall G1 G2 G3 T D,
  typ_has (G1 & G3) T D ->
  ok (G1 & G2 & G3) ->
  typ_has (G1 & G2 & G3) T D.
Proof.
  introv Has Ok. eapply (proj1 weaken_has); eauto.
Qed.

Lemma weaken_typ_has_end: forall G1 G2 T D,
  ok (G1 & G2) -> typ_has G1 T D -> typ_has (G1 & G2) T D.
Proof.
  introv Ok Has. destruct weaken_has as [P _].
  specialize (P G1 _ _ Has G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.

Lemma weaken_hasnt_middle: forall G1 G2 G3 T l,
  typ_hasnt (G1 & G3) T l ->
  ok (G1 & G2 & G3) ->
  typ_hasnt (G1 & G2 & G3) T l.
Proof.
  introv Hasnt Ok. eapply (proj2 weaken_has); eauto.
Qed.

Lemma weaken_wf:
   (forall G A T, wf_typ_impl G A T -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      wf_typ_impl (G1 & G2 & G3) A T)
/\ (forall G A D, wf_dec_impl G A D -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      wf_dec_impl (G1 & G2 & G3) A D).
Proof.
  apply wf_mutind; eauto.
  (* case wf_sel *)
  introv Bi Sb XHas WfX IHX WfT IHT WFU IHU. introv Eq Ok. subst G.
  lets Bi': (binds_weaken Bi Ok).
  lets XHas': ((proj1 weaken_has) _ _ _ XHas _ _ _ eq_refl Ok).
  repeat split; repeat eexists; eauto.
Qed.

Lemma weaken_wf_typ_middle: forall G1 G2 G3 T,
  wf_typ (G1 & G3) T ->
  ok (G1 & G2 & G3) ->
  wf_typ (G1 & G2 & G3) T.
Proof.
  introv Wf Ok. eapply (proj1 weaken_wf); eauto.
Qed.

Print Assumptions weaken_wf_typ_middle.

Lemma weaken_wf_typ_end: forall G1 G2 T,
  wf_typ G1 T ->
  ok (G1 & G2) ->
  wf_typ (G1 & G2) T.
Proof.
  intros.
  assert (Eq1: G1 & G2 = G1 & G2 & empty) by (rewrite concat_empty_r; reflexivity).
  assert (Eq2: G1 = G1 & empty) by (rewrite concat_empty_r; reflexivity).
  rewrite Eq1 in *. rewrite Eq2 in H.
  apply* weaken_wf_typ_middle.
Qed.

Lemma weaken_wf_dec_middle: forall G1 G2 G3 D,
  wf_dec (G1 & G3) D ->
  ok (G1 & G2 & G3) ->
  wf_dec (G1 & G2 & G3) D.
Proof.
  introv Wf Ok. eapply (proj2 weaken_wf); eauto.
Qed.

Lemma weaken_wf_dec_end: forall G1 G2 D,
  wf_dec G1 D ->
  ok (G1 & G2) ->
  wf_dec (G1 & G2) D.
Proof.
  introv Wf Ok.
  lets P: (@weaken_wf_dec_middle G1 G2 empty). repeat rewrite concat_empty_r in P.
  apply* P.
Qed.

Axiom okadmit: forall (G: ctx), ok G.


(* ###################################################################### *)
(** ** Regularity of Typing *)

(* If a type is involved in a subtyping judgment, it is (deeply) well-formed. *)
Lemma subtyping_regular:
   (forall G T1 T2, subtyp G T1 T2 -> wf_typ G T1 /\ wf_typ G T2)
/\ (forall G D1 D2, subdec G D1 D2 -> wf_dec G D1 /\ wf_dec G D2).
Proof.
  apply subtyp_mutind; try solve [intros; split; subst; destruct_wf; eauto].
  (* case subtyp_rcd *)
  introv Sd Wf. destruct Wf as [Wf1 Wf2].
  split; apply wf_rcd; apply add_hyps_to_wf_dec; assumption.
Qed.

Definition subtyp_regular := proj1 subtyping_regular.
Definition subdec_regular := proj2 subtyping_regular.

Definition subtyp_regular_1(G: ctx)(T1 T2: typ)(St: subtyp G T1 T2) :=
  (proj1 (subtyp_regular St)).
Definition subtyp_regular_2(G: ctx)(T1 T2: typ)(St: subtyp G T1 T2) :=
  (proj2 (subtyp_regular St)).
Definition subdec_regular_1(G: ctx)(D1 D2: dec)(Sd: subdec G D1 D2) :=
  (proj1 (subdec_regular Sd)).
Definition subdec_regular_2(G: ctx)(D1 D2: dec)(Sd: subdec G D1 D2) :=
  (proj2 (subdec_regular Sd)).

Hint Resolve subtyp_regular_1 subtyp_regular_2 subdec_regular_1 subdec_regular_2.

Lemma typing_regular:
   (forall G t T, ty_trm G t T ->
      wf_typ G T)
/\ (forall G d D, ty_def G d D ->
      wf_dec G D)
/\ (forall G ds T, ty_defs G ds T ->
      wf_typ G T).
Proof.
  apply ty_mutind;
  try solve [
    intros; subst;
    repeat match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: wf_dec _ (dec_typ _ _ _) |- _ => inversions H
    | H: wf_dec _ (dec_mtd _ _ _) |- _ => inversions H
    | H: subtyp _ _ _ |- _ => apply subtyp_regular in H
    end;
    eauto
  ].
  (* case ty_new *)
  introv Tyds IH1 Tyu IH2 Wf.
  refine (weaken_wf_typ_end _ (okadmit _)).
  assumption.
  (* case ty_mtd *)
  introv WfT WfU Tyu IH.
  refine (weaken_wf_dec_end _ (okadmit _)).
  auto.
  (* case ty_defs_cons *)
  introv Tyds WfT TyD WfD Hasnt.
  apply (wf_and WfT). apply wf_rcd. apply add_hyps_to_wf_dec; assumption.
Qed.

Definition ty_trm_regular  := proj31 typing_regular.
Definition ty_def_regular  := proj32 typing_regular.
Definition ty_defs_regular := proj33 typing_regular.

Hint Resolve ty_trm_regular ty_def_regular ty_defs_regular.


(* ###################################################################### *)
(** ** Looks like rules, but follows from the rules *)

(* take subtyp_and/or rules and replace "and" by "intersect", "or" by "union":

Lemma subtyp_intersect : forall (G : ctx) (S T1 T2 : typ),
  subtyp G S T1 -> subtyp G S T2 -> subtyp G S (intersect_typ T1 T2).
Proof.
  intros. destruct T1; destruct T2; unfold intersect_typ; case_if; simpl; auto.
Qed.

(*
Lemma subtyp_intersect_l : forall (G : ctx) (T1 T2 S : typ),
  subtyp G T1 S ->
  subtyp G (intersect_typ T1 T2) S.
Proof.
  intros. destruct (subtyp_regular H) as [WfT1 WfS].
  destruct T1; destruct T2; destruct S; simpl; unfold intersect_typ; case_if; auto.
  refine (subtyp_trans (subtyp_top _) H); auto.
Qed.

Lemma subtyp_intersect_r : forall (G : ctx) (T1 T2 S : typ),
  subtyp G T2 S -> subtyp G (intersect_typ T1 T2) S.
Proof.
  intros.
  destruct T1; destruct T2; destruct S; simpl; auto;
  apply (subtyp_trans (subtyp_top _ _) H).
Qed.
*)

Lemma subtyp_union : forall (G : ctx) (T1 T2 S : typ),
  subtyp G T1 S -> subtyp G T2 S -> subtyp G (union_typ T1 T2) S.
Proof.
  intros.
  destruct T1; destruct T2; destruct S; unfold union_typ; case_if; simpl; auto.
Qed.

(*
Lemma subtyp_union_l : forall (G : ctx) (S T1 T2 : typ),
  subtyp G S T1 -> subtyp G S (union_typ T1 T2).
Proof.
  intros.
  destruct T1; destruct T2; destruct S; simpl; auto;
  apply (subtyp_trans H (subtyp_bot _ _)).
Qed.

Lemma subtyp_union_r: forall (G : ctx) (S T1 T2 : typ),
  subtyp G S T2 -> subtyp G S (union_typ T1 T2).
Proof.
  intros.
  destruct T1; destruct T2; destruct S; simpl; auto;
  apply (subtyp_trans H (subtyp_bot _ _)).
Qed.

Hint Resolve subtyp_intersect subtyp_intersect_l subtyp_intersect_r
             subtyp_union     subtyp_union_l     subtyp_union_r.
*)

Hint Resolve subtyp_intersect subtyp_union.
*)

Lemma subdec_refl: forall G D,
  wf_dec G D ->
  subdec G D D.
Proof.
  introv Wf. inversions Wf; eauto.
Qed.

Lemma subdec_bot: forall G D,
  wf_dec G D ->
  subdec G (dec_bot (label_of_dec D)) D.
Proof.
  introv Wf. inversions Wf; simpl; eauto.
Qed.

Hint Resolve subdec_refl subdec_bot.

Lemma subdec_intersect: forall G D0 D1 D2 D12,
  subdec G D0 D1 ->
  subdec G D0 D2 ->
  D1 && D2 == D12 ->
  subdec G D0 D12.
Proof.
  introv Sd01 Sd02 I. inversions Sd01; inversions Sd02;
  unfold intersect_dec in I; case_if; inversions I; auto.
Qed.

Lemma subdec_union: forall G D D1 D2 D12,
  subdec G D1 D ->
  subdec G D2 D ->
  D1 || D2 == D12 ->
  subdec G D12 D.
Proof.
  introv Sd01 Sd02 I. inversions Sd01; inversions Sd02;
  unfold union_dec in I; case_if; inversions I; auto.
Qed.

Lemma subdec_intersect_l: forall G D1 D2 D12,
  D1 && D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec G D12 D1.
Proof.
  introv Eq WfD1 WfD2. unfold intersect_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  destruct_wf;
  try in_empty_contradiction;
  eauto.
Qed.

Lemma subdec_intersect_r: forall G D1 D2 D12,
  D1 && D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec G D12 D2.
Proof.
  introv Eq WfD1 WfD2. unfold intersect_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  inversions H;
  destruct_wf;
  try in_empty_contradiction;
  eauto.
Qed.

Lemma subdec_union_l: forall G D1 D2 D12,
  D1 || D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec G D1 D12.
Proof.
  introv Eq Wf1 Wf2. unfold union_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  inversions H;
  destruct_wf;
  eauto.
Qed.

Lemma subdec_union_r: forall G D1 D2 D12,
  D1 || D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec G D2 D12.
Proof.
  introv Eq Wf1 Wf2. unfold union_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  inversions H;
  destruct_wf;
  eauto.
Qed.


(* ###################################################################### *)
(** ** Properties of declaration intersection/union *)

Lemma intersect_dec_total: forall D1 D2,
  label_of_dec D1 = label_of_dec D2 ->
  exists D12, D1 && D2 == D12.
Proof.
  introv Eq.
  destruct D1; destruct D2; inversions Eq; unfold intersect_dec; simpl; case_if; eauto.
Qed.

Lemma union_dec_total: forall D1 D2,
  label_of_dec D1 = label_of_dec D2 ->
  exists D12, D1 || D2 == D12.
Proof.
  introv Eq.
  destruct D1; destruct D2; inversions Eq; unfold union_dec; simpl; case_if; eauto.
Qed.

Lemma intersect_dec_label_eq: forall D1 D2 D12,
  D1 && D2 == D12 ->
  label_of_dec D1 = label_of_dec D2 /\
  label_of_dec D1 = label_of_dec D12 /\
  label_of_dec D2 = label_of_dec D12.
Proof.
  intros. destruct D1; destruct D2; unfold intersect_dec in H; simpl; case_if; 
  inversions H; auto.
Qed.

Lemma union_dec_label_eq: forall D1 D2 D12,
  D1 || D2 == D12 ->
  label_of_dec D1 = label_of_dec D2 /\
  label_of_dec D1 = label_of_dec D12 /\
  label_of_dec D2 = label_of_dec D12.
Proof.
  intros. destruct D1; destruct D2; unfold union_dec in H; simpl; case_if; 
  inversions H; auto.
Qed.

Lemma subdec_to_label_of_dec_eq: forall G D1 D2,
  subdec G D1 D2 -> label_of_dec D1 = label_of_dec D2.
Proof.
  introv Sd. inversions Sd; reflexivity.
Qed.

Lemma invert_subdec_typ_sync_left: forall G D L Lo2 Hi2,
   subdec G D (dec_typ L Lo2 Hi2) ->
   exists Lo1 Hi1, D = (dec_typ L Lo1 Hi1) /\
                   subtyp G Lo2 Lo1 /\
                   subtyp G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. exists Lo1 Hi1. auto.
Qed.

Lemma invert_subdec_mtd_sync_left: forall G D m T2 U2,
   subdec G D (dec_mtd m T2 U2) ->
   exists T1 U1, D = (dec_mtd m T1 U1) /\
                 subtyp G T2 T1 /\
                 subtyp G U1 U2.
Proof.
  introv Sd. inversions Sd. exists S1 T1. auto.
Qed.

Lemma intersect_dec_preserves_wf: forall G D1 D2 D3,
  D1 && D2 == D3 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  wf_dec G D3.
Proof.
  introv Eq Wf1 Wf2. unfold intersect_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  inversions Wf1; inversions Wf2;
  eauto.
Qed.

Lemma union_dec_preserves_wf: forall G D1 D2 D3,
  D1 || D2 == D3 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  wf_dec G D3.
Proof.
  introv Eq Wf1 Wf2. unfold union_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  inversions Wf1; inversions Wf2;
  eauto.
Qed.

Lemma subdec_trans: forall G D1 D2 D3,
  subdec G D1 D2 -> subdec G D2 D3 -> subdec G D1 D3.
Proof.
  introv H12 H23. inversions H12; inversions H23; constructor;
  solve [ assumption | (eapply subtyp_trans; eassumption)].
Qed.


(* ###################################################################### *)
(** ** Properties of typ_has/hasnt: total, unique, preserves wf *)

Lemma typ_has_total_impl: forall G A T, wf_typ_impl G A T -> A = \{} ->
  forall l, typ_hasnt G T l \/ exists D, l = label_of_dec D /\ typ_has G T D.
Proof.
  introv Wf. induction Wf; intros Eq l; subst.
  + (* case wf_top *)
    left. apply typ_top_hasnt.
  + (* case wf_bot *)
    right. exists (dec_bot l). split.
    - destruct l; reflexivity.
    - apply typ_bot_has.
  + (* case wf_hyp *)
    in_empty_contradiction.
  + (* case wf_rcd *)
    destruct (classicT (l = label_of_dec D)) as [Eq | Ne].
    - right. exists D. split.
      * apply Eq.
      * apply typ_rcd_has.
    - left. apply (typ_rcd_hasnt _ _ Ne).
  + (* case wf_sel *)
    specialize (IHWf3 eq_refl l). destruct IHWf3 as [UHasnt | [D [Eq UHas]]].
    - left. apply (typ_sel_hasnt H H1 UHasnt).
    - right. exists D. split.
      * apply Eq.
      * apply (typ_sel_has H H1 UHas).
  + (* case wf_and *)
    specialize (IHWf1 eq_refl l). specialize (IHWf2 eq_refl l).
    destruct IHWf1 as [T1Hasnt | [D1 [Eq1 T1Has]]];
    destruct IHWf2 as [T2Hasnt | [D2 [Eq2 T2Has]]].
    - left. apply (typ_and_hasnt T1Hasnt T2Hasnt).
    - right. exists D2. apply (conj Eq2).
      rewrite Eq2 in T1Hasnt. apply (typ_and_has_2 T1Hasnt T2Has).
    - right. exists D1. apply (conj Eq1).
      rewrite Eq1 in T2Hasnt. apply (typ_and_has_1 T1Has T2Hasnt).
    - right.
      lets Eq12: Eq2. rewrite Eq1 in Eq12.
      destruct (intersect_dec_total D1 D2 Eq12) as [D12 Eq].
      exists D12. rewrite Eq1.
      apply (conj (proj32 (intersect_dec_label_eq _ _ Eq))).
      apply (typ_and_has_12 T1Has T2Has Eq).
  + (* case wf_or *)
    specialize (IHWf1 eq_refl l). specialize (IHWf2 eq_refl l).
    destruct IHWf1 as [T1Hasnt | [D1 [Eq1 T1Has]]];
    destruct IHWf2 as [T2Hasnt | [D2 [Eq2 T2Has]]].
    - left. apply (typ_or_hasnt_12 T1Hasnt T2Hasnt).
    - left. subst. apply (typ_or_hasnt_1 T1Hasnt T2Has).
    - left. subst. apply (typ_or_hasnt_2 T1Has T2Hasnt).
    - right.
      lets Eq12: Eq2. rewrite Eq1 in Eq12.
      destruct (union_dec_total D1 D2 Eq12) as [D12 Eq].
      exists D12. rewrite Eq1.
      apply (conj (proj32 (union_dec_label_eq _ _ Eq))).
      apply (typ_or_has T1Has T2Has Eq).
Qed.

Lemma typ_has_total: forall G T, wf_typ G T ->
  forall l, typ_hasnt G T l \/ exists D, l = label_of_dec D /\ typ_has G T D.
Proof.
  intros. apply* typ_has_total_impl.
Qed.

Print Assumptions typ_has_total.

Lemma intersect_dec_unique: forall D1 D2 D3 D4,
  D1 && D2 == D3 ->
  D1 && D2 == D4 ->
  D3 = D4.
Proof.
  introv Eq3 Eq4. rewrite Eq3 in Eq4. inversions Eq4. reflexivity.
Qed.

Lemma union_dec_unique: forall D1 D2 D3 D4,
  D1 || D2 == D3 ->
  D1 || D2 == D4 ->
  D3 = D4.
Proof.
  introv Eq3 Eq4. rewrite Eq3 in Eq4. inversions Eq4. reflexivity.
Qed.

(* need to prove the same things several times to make sure we always have an IH *)
Lemma typ_has_unique_and_not_hasnt:
   (forall G T D1, typ_has G T D1 ->
        (forall D2, typ_has G T D2 -> label_of_dec D1 = label_of_dec D2 -> D1 = D2)
     /\ (typ_hasnt G T (label_of_dec D1) -> False))
/\ (forall G T l, typ_hasnt G T l ->
      forall D, l = label_of_dec D -> typ_has G T D -> False).
Proof.
  apply typ_has_mutind; try split.
  + (* case typ_bot_has *)
    introv Has Eq. inversions Has; simpl in Eq; try discriminate.
    destruct l; destruct l0; simpl in *; inversions Eq; reflexivity.
  + (* case typ_bot_has *)
    introv Hasnt. inversions Hasnt.
  + (* case typ_rcd_has *)
    introv Has Eq. inversions Has. reflexivity.
  + (* case typ_rcd_has *)
    introv Hasnt. inversions Hasnt. apply H1. reflexivity.
  + (* case typ_sel_has *)
    rename b into Bi, t into THas, H into IH1, t0 into HiHas, H0 into IH2.
    introv Has' Eq.
    inversions Has'. rename T0 into T', H1 into Bi', H3 into THas', H5 into HiHas'.
    lets EqT: (binds_func Bi' Bi). subst T'. clear Bi'.
    destruct IH1 as [IH1 _]. destruct IH2 as [IH2 _].
    specialize (IH1 _ THas' eq_refl). symmetry in IH1. inversions IH1.
    apply (IH2 _ HiHas' Eq).
  + (* case typ_sel_has *)
    rename b into Bi, t into THas, H into IH1, t0 into HiHas, H0 into IH2.
    introv Hasnt.
    destruct IH2 as [_ IH2]. inversions Hasnt.
    rename T0 into T', H1 into Bi', H3 into THas', H5 into HiHasnt.
    lets EqT: (binds_func Bi' Bi). subst T'. clear Bi'.
    destruct IH1 as [IH1 _]. specialize (IH1 _ THas' eq_refl).
    symmetry in IH1. inversions IH1. apply (IH2 HiHasnt).
  + (* case typ_and_has_1 *)
    rename t into T1Has, H into IH1, t0 into T2Hasnt, H0 into IH2.
    introv Has' Eq. destruct IH1 as [IH1 _].
    inversions Has'.
    - eauto.
    - exfalso. apply (IH2 _ Eq H4).
    - exfalso. refine (IH2 _ _ H3).
      rewrite Eq. symmetry. apply (proj33 (intersect_dec_label_eq _ _ H5)).
  + (* case typ_and_has_1 *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Hasnt. inversions T12Hasnt. destruct IH1 as [_ IH1]. apply (IH1 H2).
  + (* case typ_and_has_2 *)
    rename t into T1Hasnt, H into IH1, t0 into T2Has, H0 into IH2.
    introv Has' Eq. destruct IH2 as [IH2 _].
    inversions Has'.
    - exfalso. refine (IH1 _ Eq H2).
    - eauto.
    - exfalso. refine (IH1 _ _ H1).
      rewrite Eq. symmetry. apply (proj32 (intersect_dec_label_eq _ _ H5)).
  + (* case typ_and_has_2 *)
    rename t into T1Hasnt, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Hasnt. inversions T12Hasnt. destruct IH2 as [_ IH2]. apply (IH2 H4).
  + (* case typ_and_has_12 *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv Has' Eq.
    remember (label_of_dec D0) as l eqn: Eq0.
    symmetry in Eq. rename Eq into Eq3.
    destruct (intersect_dec_label_eq _ _ e) as [Eq12 [Eq13 Eq23]].
    rewrite <- Eq3 in Eq23. symmetry in Eq23; rename Eq23 into Eq2.
    rewrite <- Eq3 in Eq13. symmetry in Eq13; rename Eq13 into Eq1. clear Eq12.
    lets Eq: (conj Eq0 (conj Eq1 (conj Eq2 Eq3))). clear Eq0 Eq1 Eq2 Eq3.
    inversions Has'.
    - exfalso. rewrite <- (proj41 Eq) in H4. rewrite (proj43 Eq) in H4.
      destruct IH2 as [_ IH2]. apply (IH2 H4).
    - exfalso. rewrite <- (proj41 Eq) in H2. rewrite (proj42 Eq) in H2.
      destruct IH1 as [_ IH1]. apply (IH1 H2).
    - destruct (intersect_dec_label_eq _ _ H5) as [Eq45 [Eq40 Eq50]].
      destruct IH1 as [IH1 _]. specialize (IH1 D4).
      rewrite Eq40 in IH1. rewrite <- (proj41 Eq) in IH1. rewrite <- (proj42 Eq) in IH1.
      specialize (IH1 H1 eq_refl). subst D4.
      destruct IH2 as [IH2 _]. specialize (IH2 D5).
      rewrite Eq50 in IH2. rewrite <- (proj41 Eq) in IH2. rewrite <- (proj43 Eq) in IH2.
      specialize (IH2 H3 eq_refl). subst D5.
      apply (intersect_dec_unique _ _ e H5).
  + (* case typ_and_has_12 *)
    rename t into T1Hasnt, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Hasnt. inversions T12Hasnt. destruct IH2 as [_ IH2].
    destruct (intersect_dec_label_eq _ _ e) as [Eq12 [Eq13 Eq23]].
    rewrite Eq23 in IH2. apply (IH2 H4).
  + (* case typ_or_has *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Has Eq. inversions T12Has.
    remember (label_of_dec D0) as l eqn: Eq0.
    symmetry in Eq. rename Eq into Eq3.
    destruct (union_dec_label_eq _ _ e) as [Eq12 [Eq13 Eq23]].
    destruct (union_dec_label_eq _ _ H5) as [Eq45 [Eq40 Eq50]].
    destruct IH1 as [IH1 _]. specialize (IH1 D4).
    rewrite Eq40 in IH1. rewrite <- Eq0 in IH1. rewrite Eq3 in IH1.
    specialize (IH1 H1 Eq13). subst D4.
    destruct IH2 as [IH2 _]. specialize (IH2 D5).
    rewrite Eq50 in IH2. rewrite <- Eq0 in IH2. rewrite Eq3 in IH2.
    specialize (IH2 H3 Eq23). subst D5.
    apply (union_dec_unique _ _ e H5).
  + (* case typ_or_has *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    destruct (union_dec_label_eq _ _ e) as [Eq12 [Eq13 Eq23]].
    introv T12Hasnt. inversions T12Hasnt.
    - destruct IH1 as [_ IH1].
      rewrite Eq13 in IH1. rewrite H2 in H3. apply (IH1 H3).
    - destruct IH2 as [_ IH2].
      rewrite Eq23 in IH2. rewrite H2 in H4. apply (IH2 H4).
    - destruct IH1 as [_ IH1].
      rewrite Eq13 in IH1. apply (IH1 H2).
  + (* case typ_top_hasnt *)
    introv Eq Has. inversions Has.
  + (* case typ_rcd_hasnt *)
    introv Ne Eq Has. inversions Has. apply Ne. reflexivity.
  + (* case typ_sel_hasnt *)
    introv Bi THas IH1 HiHasnt IH2 Eq Has'.
    inversions Has'. rename T0 into T', H1 into Bi', H3 into THas', H5 into HiHas.
    lets EqT: (binds_func Bi' Bi). subst T'. clear Bi'.
    destruct IH1 as [IH1 _]. specialize (IH1 _ THas' eq_refl).
    symmetry in IH1. inversions IH1. apply (IH2 _ eq_refl HiHas).
  + (* case typ_and_hasnt *)
    introv T1Hasnt IH1 T2Hasnt IH2 Eq Has'.
    inversions Has'.
    - eauto.
    - eauto.
    - destruct (intersect_dec_label_eq _ _ H5) as [Eq12 [Eq1 Eq2]].
      rewrite <- Eq1 in *. apply (IH1 _ eq_refl H1).
  + (* case typ_or_hasnt_1 *)
    introv T1Hasnt IH1 T2Has IH2 Eq Has'. inversions Has'.
    destruct (union_dec_label_eq _ _ H5) as [Eq12 [Eq1 Eq2]].
    rewrite <- Eq1 in *. apply (IH1 _ Eq H1).
  + (* case typ_or_hasnt_2 *)
    introv T1Has IH1 T2Hasnt IH2 Eq Has'. inversions Has'.
    destruct (union_dec_label_eq _ _ H5) as [Eq12 [Eq1 Eq2]].
    rewrite <- Eq1 in *. refine (IH2 _ _ H3). rewrite Eq. exact Eq12.
  + (* case typ_or_hasnt_12 *)
    introv T1Hasnt IH1 T2Hasnt IH2 Eq Has'. inversions Has'.
    destruct (union_dec_label_eq _ _ H5) as [Eq12 [Eq1 Eq2]].
    rewrite <- Eq2 in *. refine (IH2 _ eq_refl H3).
Qed.

Print Assumptions typ_has_unique_and_not_hasnt.

Lemma typ_has_unique: forall G T D1 D2,
  typ_has G T D1 ->
  typ_has G T D2 ->
  label_of_dec D1 = label_of_dec D2 ->
  D1 = D2.
Proof.
  introv H1 H2 Eq.
  destruct typ_has_unique_and_not_hasnt as [P _].
  specialize (P G T D1 H1). destruct P as [P _]. apply (P _ H2 Eq).
Qed.

Lemma not_typ_has_and_hasnt: forall G T D,
  typ_has G T D -> typ_hasnt G T (label_of_dec D) -> False.
Proof.
  introv Has Hasnt.
  destruct typ_has_unique_and_not_hasnt as [_ P].
  apply (P G T (label_of_dec D) Hasnt D eq_refl Has).
Qed.

Lemma typ_has_preserves_wf: forall G T D,
  typ_has G T D ->
  wf_typ G T ->
  wf_dec G D.
Proof.
  introv Has. induction Has; introv Wf.
  + (* case typ_bot_has *)
    destruct l; simpl; eauto.
  + (* case typ_rcd_has *)
    apply (invert_wf_rcd Wf). (* <--- uses remove_hyp_from_wf_dec ! *)
  + (* case typ_sel_has *)
    inversions Wf. (* <-- gives us full wf-ness of bounds, wouldn't be possible
      without the assumption-set-based wf-judgment because it would require infinite
      proof trees for recursive types. *)
    - in_empty_contradiction.
    - lets Eq: (binds_func H H2). subst T.
      lets Eq: (typ_has_unique H4 Has1 eq_refl). inversions Eq.
      apply IHHas2. assumption.
  + (* case typ_and_has_1 *)
    inversions Wf.
    - in_empty_contradiction.
    - eauto.
  + (* case typ_and_has_2 *)
    inversions Wf.
    - in_empty_contradiction.
    - eauto.
  + (* case typ_and_has_12 *)
    inversions Wf.
    - in_empty_contradiction.
    - apply (intersect_dec_preserves_wf H); auto.
  + (* case typ_or_has *)
    inversions Wf.
    - in_empty_contradiction.
    - apply (union_dec_preserves_wf H); auto.
Qed.

Print Assumptions typ_has_preserves_wf.


(* ###################################################################### *)
(** ** Some inversion lemmas *)

Lemma invert_typ_and_has: forall G T1 T2 D,
   typ_has G (typ_and T1 T2) D ->
   (typ_has G T1 D /\ typ_hasnt G T2 (label_of_dec D))
\/ (typ_has G T2 D /\ typ_hasnt G T1 (label_of_dec D))
\/ exists D1 D2, D1 && D2 == D /\ typ_has G T1 D1 /\ typ_has G T2 D2.
Proof.
  intros. inversions H; eauto 10.
Qed.

Lemma ty_def_to_label_eq: forall G d D,
  ty_def G d D ->
  label_of_def d = label_of_dec D.
Proof.
  intros. inversions H; simpl; auto.
Qed.

Lemma not_defs_has_and_hasnt: forall ds d,
  defs_has ds d -> defs_hasnt ds (label_of_def d) -> False.
Proof.
  intro ds. induction ds.
  - introv nilHas. inversions nilHas. (* contradiction *)
  - introv dsHas dsHasnt. inversions dsHas; inversions dsHasnt. case_if.
Qed.

Lemma invert_ty_defs: forall G ds T D,
  ty_defs G ds T ->
  typ_has G T D ->
  exists d, defs_has ds d /\ ty_def G d D.
Proof.
  introv Tyds. gen D. induction Tyds.
  + introv THas. inversions THas.
  + rename H into Tyd0, D into D0, d into d0, H0 into Hasnt.
    introv THas.
    apply invert_typ_and_has in THas.
    destruct THas as [[THas D0Hasnt] | [[D0Has THasnt] | [D1 [D2 [Eq [THas D0Has]]]]]].
    - (* case lhs has *)
      inversions D0Hasnt.
      specialize (IHTyds D THas). destruct IHTyds as [d [dsHas Tyd]].
      exists d. refine (conj _ Tyd). unfold defs_has, get_def.
      lets Eql1: (ty_def_to_label_eq Tyd0). case_if. apply dsHas.
    - (* case rhs has *)
      inversions D0Has.
      exists d0. refine (conj _ Tyd0). unfold defs_has, get_def. case_if. reflexivity.
    - (* case both have *)
      inversions D0Has.
      specialize (IHTyds D1 THas). destruct IHTyds as [d [dsHas Tyd]].
      destruct (intersect_dec_label_eq _ _ Eq) as [Eq12 [Eq1 Eq2]].
      lets Eql3: (ty_def_to_label_eq Tyd).
      lets Eql4: (ty_def_to_label_eq Tyd0).
      rewrite Eql4 in Hasnt. rewrite <- Eq12 in Hasnt. rewrite <- Eql3 in Hasnt.
      exfalso. apply (not_defs_has_and_hasnt dsHas Hasnt).
Qed.

Lemma defs_has_unique: forall ds d1 d2,
  label_of_def d1 = label_of_def d2 ->
  defs_has ds d1 ->
  defs_has ds d2 ->
  d1 = d2.
Proof.
  intro ds. induction ds; introv Eq dsHas1 dsHas2.
  + inversions dsHas1. (* contradiction *)
  + inversions dsHas1; inversions dsHas2. do 2 case_if.
    - inversions H1. inversions H0. reflexivity.
    - eauto.
Qed.


(* ###################################################################### *)
(** ** Weakening for subtyping *)

Lemma weaken_subtyp_subdec:
   (forall G T1 T2, subtyp G T1 T2 -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp (G1 & G2 & G3) T1 T2)
/\ (forall G D1 D2, subdec G D1 D2 -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subdec (G1 & G2 & G3) D1 D2).
Proof.
  destruct weaken_has as [WHas WHasnt].
  destruct weaken_wf as [WWfTyp WWfDec].
  apply subtyp_mutind.
  + (* case subtyp_refl  *) eauto.
  + (* case subtyp_top   *) eauto.
  + (* case subtyp_bot   *) eauto.
  + (* case subtyp_rcd   *) eauto.
  + (* case subtyp_sel_l *)
    introv Bix WfX Sb XHas St IH Eq Ok. subst. apply subtyp_sel_l with X T; eauto.
    apply (binds_weaken Bix Ok).
  + (* case subtyp_sel_r *)
    introv Bix WfX Sb XHas St IH Eq Ok. subst. apply subtyp_sel_r with X U; eauto.
    apply (binds_weaken Bix Ok).
  + (* case subtyp_and   *) eauto.
  + (* case subtyp_and_l *) eauto.
  + (* case subtyp_and_r *) eauto.
  + (* case subtyp_or    *) eauto.
  + (* case subtyp_or_l  *) eauto.
  + (* case subtyp_or_r  *) eauto.
  + (* case subtyp_trans *) eauto.
  + (* case subdec_typ   *) eauto.
  + (* case subdec_mtd   *) eauto.
Qed.

Lemma weaken_subtyp_middle: forall G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp (G1 &     G3) S U ->
  subtyp (G1 & G2 & G3) S U.
Proof.
  introv Ok St. destruct weaken_subtyp_subdec as [P _]. apply* P.
Qed.

Lemma weaken_subtyp_end: forall G1 G2 S U,
  ok (G1 & G2) -> 
  subtyp G1        S U ->
  subtyp (G1 & G2) S U.
Proof.
  introv Ok St. destruct weaken_subtyp_subdec as [P _].
  specialize (P G1 S U St G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.


(* ###################################################################### *)
(** ** subenv *)

Lemma subenv_refl: forall G,
  subenv G G.
Admitted.

Lemma subenv_trans: forall G1 G2 G3,
  subenv G1 G2 -> subenv G2 G3 -> subenv G1 G3.
Admitted.


(* ###################################################################### *)
(** ** Strengthening *)

Lemma ty_defs_to_good_bounds_typ: forall G ds T,
  ty_defs G ds T ->
  good_bounds_typ G T.
Proof.
  unfold good_bounds_typ. introv Tyds. split; [eauto | idtac].
  introv THas.
  destruct (invert_ty_defs Tyds THas) as [d [dsHas Tyd]].
  inversions Tyd. assumption.
Qed.

(*
Lemma ty_defs_to_good_bounds_typ: forall G ds x T,
  good_bounds G ->
  ty_defs (G & x ~ T) ds T ->
  good_bounds_typ (G & x ~ T) T.
Proof.
  unfold good_bounds_typ. introv Gb Tyds. split; [eauto | idtac].
  introv THas.
  destruct (invert_ty_defs Tyds THas) as [d [dsHas Tyd]].
  gen_eq D: (dec_typ L Lo Hi). gen_eq G0: (G & x ~ T).
  induction Tyd; intros Eq1 Eq2; inversions Eq2.
  - assumption.
  - refine (H2 _ (subenv_refl _) _ _ _ _ eq_refl eq_refl).
Qed.

Lemma ty_defs_to_good_bounds_typ: forall G ds T,
  good_bounds G ->
  ty_defs G ds T ->
  good_bounds_typ G T.
Proof.
  unfold good_bounds_typ. introv Gb Tyds. split; [eauto | idtac].
  introv THas.
  destruct (invert_ty_defs Tyds THas) as [d [dsHas Tyd]].
  gen_eq D: (dec_typ L Lo Hi). induction Tyd; intro Eq; inversions Eq.
  - assumption.
  - refine (H2 G (subenv_refl _) Gb Gb Tyds THas dsHas eq_refl).
Qed.
*)

(* omg...

Lemma ok_binds_concat_inv: forall (T: Type) G1 G2 x (X: T),
  ok (G1 & G2) ->
  binds x X (G1 & G2) ->
  binds x X G1 /\ x # G2 \/ binds x X G2 /\ x # G1.
Proof.
  introv Ok. gen G2 x X. apply (env_ind (fun G2 =>
    ok (G1 & G2) ->
    forall (x : var) (X : T),
    binds x X (G1 & G2) -> binds x X G1 /\ x # G2 \/ binds x X G2 /\ x # G1)).
  - introv Ok Bi. rewrite concat_empty_r in Bi. left. auto.
  - introv IH Ok Bi. rewrite concat_assoc in *. apply binds_push_inv in Bi.
    + destruct Bi as [[Eq1 Eq2] | [Ne Bi2]].
      * subst. right. split; auto. intro H. apply get_some in H.
        destruct H as [X Bi]. apply ok_concat_inv_l in Ok.
        specialize (IH Ok x X). unfold binds in IH at 1. rewrite get_concat in IH.
        destruct (get x E) as [X' | ] eqn: Eq.
get
        binds _concat_l

Qed.

Lemma ok_concat_both_inv: forall (T: Type) G1 G2 x (X1 X2: T),
  ok (G1 & G2) ->
  binds x X1 G1 ->
  binds x X2 G2 ->
  False.
Proof.
  introv Ok Bi1 Bi2.
  apply get_some_inv in Bi1.
  apply get_some_inv in Bi2.
binds_concat_inv'
binds_concat_inv':
  forall (A : Type) (x : var) (v : A) (E1 E2 : env A),
  binds x v (E1 & E2) -> x # E2 /\ binds x v E1 \/ binds x v E2
binds
dom

  introv Ok. gen G2 x X1 X2. apply (env_ind (fun G2 =>
    ok (G1 & G2) ->
    forall (x : var) (X1 X2 : T), binds x X1 G1 -> binds x X2 G2 -> False)).
  - introv Ok Bi1 Bi2. apply (binds_empty_inv Bi2).
  - introv IH Ok Bi1 Bi2. apply binds_push_inv in Bi2.
    + destruct Bi2 as [[Eq1 Eq2] | [Ne Bi2]].
      * subst. get
Qed.
*)

Lemma strengthened_binds_unique: forall (T: Type) G1 G2 G3 x (X X': T),
  ok (G1 & G2 & G3) ->
  binds x X (G1 & G2 & G3) ->
  binds x X' (G1 & G3) ->
  X = X'.
Proof.
(*
  introv Ok Bi Bi'.
  destruct (binds_concat_inv Bi) as [Bi3 | [xG3 Bi12]].
  - destruct (binds_concat_inv Bi') as [Bi3' | [xG3 Bi1]].
    * apply (binds_func Bi3 Bi3').
    * exfalso. apply (binds_fresh_inv Bi3 xG3).
  - destruct (binds_concat_inv Bi') as [Bi3' | [xG3' Bi1]].
    * exfalso. apply (binds_fresh_inv Bi3' xG3).
    * destruct (binds_concat_inv Bi12) as [Bi2 | [xG2 Bi1']].
      + apply ok_concat_inv_l in Ok. ok
assert (x \in (dom G2)) by auto.

  - destruct (binds_concat_inv Bi') as [Bi3' | [xG3' Bi1]].
    * exfalso. apply (binds_fresh_inv Bi3' xG3).
    * 

 apply (binds_func Bi3 Bi3').
    * exfalso. apply (binds_fresh_inv Bi3 xG3).


*)
  introv Ok Bi Bi'.
  assert (xG2: x # G2). {
    destruct (binds_concat_inv Bi) as [Bi3 | [xG3 Bi12]].
    - admit.
    - admit.
  }
  lets Bi'': (binds_remove Bi xG2).
  apply (binds_func Bi'' Bi').
Qed.

Lemma strengthen_has:
   (forall G T D, typ_has G T D -> forall G1 G2 G3,
    G = G1 & G2 & G3 ->
    ok (G1 & G2 & G3) ->
    wf_typ (G1 & G3) T ->
    typ_has (G1 & G3) T D)
/\ (forall G T l, typ_hasnt G T l -> forall G1 G2 G3,
    G = G1 & G2 & G3 ->
    ok (G1 & G2 & G3) ->
    wf_typ (G1 & G3) T ->
    typ_hasnt (G1 & G3) T l).
Proof.
  apply typ_has_mutind; try solve [intros; subst; destruct_wf; eauto].
  + (* case typ_sel_has *)
    introv Bi THas IH1 HiHas IH2 Eq Ok Wf. subst. eq_specialize.
    apply invert_wf_sel in Wf.
    destruct Wf as [T' [Lo' [Hi' [Bi' [THas' [WfT [WfLo WfHi]]]]]]].
    lets Eq: (strengthened_binds_unique Ok Bi Bi'). subst T'.
    specialize (IH1 Ok WfT).
    lets Eq: (typ_has_unique THas' IH1 eq_refl). inversions Eq.
    specialize (IH2 Ok WfHi).
    apply (typ_sel_has Bi' THas' IH2).
  + (* case typ_sel_hasnt *)
    introv Bi THas IH1 HiHasnt IH2 Eq Ok Wf. subst. eq_specialize.
    apply invert_wf_sel in Wf.
    destruct Wf as [T' [Lo' [Hi' [Bi' [THas' [WfT [WfLo WfHi]]]]]]].
    lets Eq: (strengthened_binds_unique Ok Bi Bi'). subst T'.
    specialize (IH1 Ok WfT).
    lets Eq: (typ_has_unique THas' IH1 eq_refl). inversions Eq.
    specialize (IH2 Ok WfHi).
    apply (typ_sel_hasnt Bi' THas' IH2).
Qed.

Print Assumptions strengthen_has.

Lemma strengthen_has_end: forall G1 G2 T D,
  ok (G1 & G2) ->
  wf_typ G1 T ->
  typ_has (G1 & G2) T D ->
  typ_has G1 T D.
Proof.
  introv Ok Wf Has.
  rewrite <- (concat_empty_r G1).
  rewrite <- (concat_empty_r G1) in Wf.
  rewrite <- (concat_empty_r (G1 & G2)) in Has, Ok.
  apply ((proj1 strengthen_has) _ _ _ Has G1 G2 empty eq_refl Ok Wf).
Qed.

Lemma weaken_good_bounds_typ_middle: forall G1 G2 G3 T,
  ok (G1 & G2 & G3) ->
  good_bounds_typ (G1 &      G3) T ->
  good_bounds_typ (G1 & G2 & G3) T.
Proof.
  unfold good_bounds_typ. introv Ok Gb. destruct Gb as [Wf Gb].
  lets Wf': (weaken_wf_typ_middle Wf Ok). apply (conj Wf').
  introv Has. apply (weaken_subtyp_middle Ok). apply (Gb L).
  refine ((proj1 strengthen_has) _ _ _ Has _ _ _ eq_refl Ok Wf).
Qed.

Print Assumptions weaken_good_bounds_typ_middle.

Lemma weaken_good_bounds_typ_end: forall G1 G2 T,
  ok (G1 & G2) ->
  good_bounds_typ G1 T ->
  good_bounds_typ (G1 & G2) T.
Proof.
  unfold good_bounds_typ. introv Ok Gb. destruct Gb as [Wf Gb].
  lets Wf': (weaken_wf_typ_end Wf Ok). apply (conj Wf').
  introv Has. apply (weaken_subtyp_end Ok). apply (Gb L).
  apply (strengthen_has_end Ok Wf Has).
Qed.

(*
Lemma good_bounds_push_ty_defs: forall G y ds T,
  good_bounds G ->
  ty_defs (G & y ~ T) ds T ->
  ok (G & y ~ T) ->
  good_bounds (G & y ~ T).
Proof.
  introv Gb Tyds Ok. unfold good_bounds in *. introv Bix.
  apply binds_push_inv in Bix. destruct Bix as [[Eq1 Eq2] | [Ne Bix]].
  - subst. unfold good_bounds_typ. split.
    * apply (ty_defs_regular Tyds).
    * introv THas. destruct (invert_ty_defs Tyds THas) as [d [dsHas Tyd]].
      inversions Tyd. assumption.
  - specialize (Gb x X Bix). apply (weaken_good_bounds_typ_end Ok Gb).
Qed.

Print Assumptions good_bounds_push_ty_defs.

Axiom strengthen_subtyp_trans: forall G1 G2 G3 T1 T2 T3,
  subtyp (G1 & G2 & G3) T1 T2 ->
  subtyp (G1 & G2 & G3) T2 T3 ->
  wf_typ (G1 & G3) T1 ->
  wf_typ (G1 & G3) T3 ->
  subtyp (G1 & G3) T1 T3.

Lemma strengthen_subtyp_subdec:
   (forall G T1 T2, subtyp G T1 T2 -> forall G1 G2 G3,
    G = G1 & G2 & G3 ->
    ok (G1 & G2 & G3) ->
    wf_typ (G1 & G3) T1 ->
    wf_typ (G1 & G3) T2 ->
    subtyp (G1 & G3) T1 T2)
/\ (forall G D1 D2, subdec G D1 D2 -> forall G1 G2 G3,
    G = G1 & G2 & G3 ->
    ok (G1 & G2 & G3) ->
    wf_dec (G1 & G3) D1 ->
    wf_dec (G1 & G3) D2 ->
    subdec (G1 & G3) D1 D2).
Proof.
  apply subtyp_mutind.
  + (* case subtyp_refl  *) eauto.
  + (* case subtyp_top   *) eauto.
  + (* case subtyp_bot   *) eauto.
  + (* case subtyp_rcd   *)
    introv Sd IH Eq Ok Wf1 Wf2. subst.
    apply invert_wf_rcd in Wf1.
    apply invert_wf_rcd in Wf2.
    eauto.
  + (* case subtyp_sel_l *)
    introv Bix WfX Sb XHas St IH Eq Ok Wf1 WfU. subst.
    apply invert_wf_sel in Wf1.
    destruct Wf1 as [X' [T' [U' [Bix' [XHas' [WfX' [WfT' WfU']]]]]]].
    lets Eq: (strengthened_binds_unique Ok Bix Bix'). subst X'.
    lets XHas'': ((proj1 strengthen_has) _ _ _ XHas _ _ _ eq_refl Ok WfX').
    lets Eq: (typ_has_unique XHas' XHas'' eq_refl). inversions Eq.
    apply (subtyp_sel_l Bix' WfX' Sb XHas').
    apply* IH.
  + (* case subtyp_sel_r *)
    introv Bix WfX Sb XHas St IH Eq Ok WfT Wf1. subst.
    apply invert_wf_sel in Wf1.
    destruct Wf1 as [X' [T' [U' [Bix' [XHas' [WfX' [WfT' WfU']]]]]]].
    lets Eq: (strengthened_binds_unique Ok Bix Bix'). subst X'.
    lets XHas'': ((proj1 strengthen_has) _ _ _ XHas _ _ _ eq_refl Ok WfX').
    lets Eq: (typ_has_unique XHas' XHas'' eq_refl). inversions Eq.
    apply (subtyp_sel_r Bix' WfX' Sb XHas').
    apply* IH.
  + (* case subtyp_and   *)
    introv St1 IH1 St2 IH2 Eq OK WfT Wf. apply invert_wf_and in Wf. destruct Wf. eauto.
  + (* case subtyp_and_l *)
    introv Wf1 Wf2 Eq Ok Wf Wf1'. apply invert_wf_and in Wf. destruct Wf. eauto.
  + (* case subtyp_and_r *)
    introv Wf1 Wf2 Eq Ok Wf Wf1'. apply invert_wf_and in Wf. destruct Wf. eauto.
  + (* case subtyp_or    *)
    introv St1 IH1 St2 IH2 Eq OK Wf WfU. apply invert_wf_or in Wf. destruct Wf. eauto.
  + (* case subtyp_or_l  *)
    introv Wf1 Wf2 Eq Ok Wf1' Wf. apply invert_wf_or in Wf. destruct Wf. eauto.
  + (* case subtyp_or_r  *)
    introv Wf1 Wf2 Eq Ok Wf1' Wf. apply invert_wf_or in Wf. destruct Wf. eauto.
  + (* case subtyp_trans *)
    introv St1 IH1 St2 IH2 Eq Ok Wf1 Wf3. subst.
    lets Wf2: (proj1 (subtyp_regular St2)).
    (* Problem: We might not be able to strengthen Wf2, i.e. wf_typ (G1 & & G3) T2 might
       not hold.
       But still, I believe that the conclusion always holds, but how to prove it? *)
    apply (strengthen_subtyp_trans St1 St2 Wf1 Wf3).
    (* probably not like this:
    gen_eq G: (G1 & G2 & G3). gen_eq A: (@FsetImpl.empty typ).
    induction Wf2; intros Eq1 Eq2; subst.
    - (* case wf_top *)
      eapply (@subtyp_trans _ _ typ_top _); eauto.
    - (* case wf_bot *)
      eapply (@subtyp_trans _ _ typ_bot _); eauto.
    - (* case wf_hyp *)
      in_empty_contradiction.
    - (* case wf_rcd *)
      admit. (* No chance: D might contain stuff defined only in G2! *)
    - (* case wf_sel *)
      specialize (IHWf2_3 Ok Wf1 Wf3). (* refine (IHWf2_3 _ _ _ _ eq_refl eq_refl). *)
      admit.
    - (* case wf_and *)
      admit.
    - (* case wf_or *)
      admit.
    *)
  + (* case subdec_typ   *)
    introv StLo IH1 StHi IH2 Eq Ok Wf1 Wf2. subst. destruct_wf. eauto.
  + (* case subdec_mtd   *)
    introv StLo IH1 StHi IH2 Eq Ok Wf1 Wf2. subst. destruct_wf. eauto.
Qed.

Print Assumptions strengthen_subtyp_subdec.

Lemma good_bounds_push: forall G y T,
  ok (G & y ~ T) ->
  good_bounds G ->
  good_bounds_typ G T ->
  good_bounds (G & y ~ T).
Proof.
  unfold good_bounds, good_bounds_typ. introv Ok Gb GbT Bi.
  apply binds_push_inv in Bi. destruct Bi as [[Eq1 Eq2] | [Ne Bi]].
  - subst. split.
    * refine (weaken_wf_typ_end _ Ok). apply (proj1 GbT).
    * destruct GbT as [WfT GbT]. intros.
      apply (weaken_subtyp_end Ok). apply (GbT L).
      apply (strengthen_has_end Ok WfT H).
  - specialize (Gb x X Bi). apply (weaken_good_bounds_typ_end Ok Gb).
Qed.

Lemma shrink_good_bounds: forall G1 G2 G3,
  ok (G1 & G2 & G3) ->
  (forall x X, binds x X (G1 & G3) -> wf_typ (G1 & G3) X) ->
  good_bounds (G1 & G2 & G3) ->
  good_bounds (G1 &      G3).
Proof.
  unfold good_bounds, good_bounds_typ. introv Ok Wf Gb Bi.
  assert (Bi': binds x X (G1 & G2 & G3)) by admit.
  specialize (Gb _ _ Bi'). 
  destruct Gb as [WfX Gb].
  specialize (Wf _ _ Bi).
  split.
  - exact Wf.
  - introv XHas.
    lets WfD: (typ_has_preserves_wf XHas Wf). inversions WfD.
    refine ((proj1 strengthen_subtyp_subdec) _ _ _ _ G1 G2 G3 eq_refl Ok H3 H5).
    apply (Gb _ _ _ (weaken_has_middle XHas Ok)).
Qed.

Print Assumptions shrink_good_bounds.
*)

(* ###################################################################### *)
(** ** Weakening on term level *)

(* TODO these should follow from ty_hyp, or if they don't, add them as rules as well
  But note: only used in narrow_ty
Lemma ty_def_hyp: forall G d D,
  wf_dec G D ->
  (good_bounds G -> ty_def G d D) ->
  ty_def G d D.
Admitted.
*)

(* Note: Takes good_bound hyp, which is quite strong, but thanks to this, we don't
   need any shrink_good_bounds and strengthen_subtyp stuff
Lemma weaken_ty:
   (forall G t T, ty_trm G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    good_bounds (G1 & G3) ->
    ok (G1 & G2 & G3) ->
    ty_trm (G1 & G2 & G3) t T)
/\ (forall G t T, ty_imp G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    good_bounds (G1 & G3) ->
    ok (G1 & G2 & G3) ->
    ty_imp (G1 & G2 & G3) t T)
/\ (forall G d D, ty_def G d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    good_bounds (G1 & G3) ->
    ok (G1 & G2 & G3) ->
    ty_def (G1 & G2 & G3) d D)
/\ (forall G ds T, ty_defs G ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    good_bounds (G1 & G3) ->
    ok (G1 & G2 & G3) ->
    ty_defs (G1 & G2 & G3) ds T).
Proof.
  destruct weaken_has as [WHas WHasnt].
  destruct weaken_wf as [WWfTyp WWfDec].
  destruct weaken_subtyp_subdec as [WSt WSd].
  apply ty_mutind.
  + (* case ty_var *)
    introv Bix WfT Eq Gb Ok. subst. apply ty_var; eauto.
    apply (binds_weaken Bix Ok).
  + (* case ty_call *)
    introv Tyt IH1 THas Tyu IH2 WfV Eq Gb Ok. subst.
    eapply ty_call.
    - apply* IH1.
    - eauto.
    - apply* IH2.
    - eauto.
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Eq Gb Ok. subst.
    apply_fresh ty_new as x'; try assert (x'L: x' \notin L) by auto.
    - specialize (IH1 x' x'L G1 G2 (G3 & x' ~ open_typ x' T)).
      repeat rewrite concat_assoc in IH1.
      specialize (Tyds x' x'L).
      assert (Ok': ok (G1 & G3 & x' ~ open_typ x' T)) by auto.
      lets Gb2: (good_bounds_push_ty_defs Gb Tyds Ok').
      apply* IH1.
    - specialize (IH2 x' x'L G1 G2 (G3 & x' ~ open_typ x' T)).
      repeat rewrite concat_assoc in IH2.
      specialize (Tyds x' x'L).
      assert (Ok': ok (G1 & G3 & x' ~ open_typ x' T)) by auto.
      lets Gb2: (good_bounds_push_ty_defs Gb Tyds Ok').
      apply* IH2.
    - eauto.
  + (* case ty_hyp *)
    introv WfT Ty IH Eq Gb Ok. subst.
    apply (ty_hyp (weaken_wf_typ_middle WfT Ok)).
    intro Gb'. apply (IH Gb _ _ _ eq_refl Gb Ok).
  + (* case ty_sbsm *)
    introv Ty IH St Eq Gb Ok. apply* ty_sbsm.
  + (* case ty_tdef *) eauto.
  + (* case ty_mdef *)
    introv WfT WfU2 Tyu IH Eq Gb Ok. subst.
    apply_fresh ty_mdef as x'; [eauto | eauto | idtac].
    assert (x'L: x' \notin L) by auto.
    specialize (IH x' x'L G1 G2 (G3 & x' ~ T)).
    repeat rewrite concat_assoc in IH.
    assert (Ok': ok (G1 & G2 & G3 & x' ~ T)) by auto.
    apply ty_imp_hyp.
    - refine (weaken_wf_typ_end _ Ok'). apply (weaken_wf_typ_middle WfU2 Ok).
    - intro Gb'. apply* IH.
      rewrite <- concat_assoc in *.
      refine (shrink_good_bounds _ _ Gb'); rewrite concat_assoc in *; auto.
             (******************)
      introv Bi. apply weaken_wf_typ_end; auto.
      apply binds_push_inv in Bi. destruct Bi as [[Eq1 Eq2] | [Ne Bi]].
      * subst. exact WfT.
      * specialize (Gb _ _ Bi). apply (proj1 Gb).
  + (* case ty_defs_nil *) eauto.
  + (* case ty_defs_cons *) eauto.
Qed.

Print Assumptions weaken_ty.
*)

(* Note: this is only so simple because good_bounds is defined "step-wise" from left to
   the right. *)
Lemma shrink_good_bounds: forall G1 G2,
  good_bounds (G1 & G2) ->
  good_bounds G1.
Proof.
  intros. gen_eq G: (G1 & G2). gen G1 G2. induction H; introv Eq; subst.
  - apply empty_concat_inv in Eq. destruct Eq. subst. constructor.
  - destruct (env_case G2) as [Eq2 | [x' [T' [G2' Eq2]]]].
    * subst G2. rewrite concat_empty_r in Eq. subst G1. apply (good_bounds_push H H0).
    * subst G2. rewrite concat_assoc in Eq.
      apply eq_push_inv in Eq. destruct Eq as [Eq1 [Eq2 Eq3]]. subst x' T' G.
      apply (IHgood_bounds _ _ eq_refl).
Qed.

Axiom subenv_concat_inv: forall F G1 G2,
  subenv F (G1 & G2) ->
  exists F1 F2, F = F1 & F2 /\ subenv F1 G1.

Lemma weaken_ty_end_only:
   (forall G t T, ty_trm G t T -> forall G',
    ok (G & G') ->
    ty_trm (G & G') t T)
/\ (forall G d D, ty_def G d D -> forall G',
    ok (G & G') ->
    ty_def (G & G') d D)
/\ (forall G ds T, ty_defs G ds T -> forall G',
    ok (G & G') ->
    ty_defs (G & G') ds T).
Proof.
  apply ty_mutind.
  + (* case ty_var *)
    introv Bix WfT Ok. apply ty_var.
    - apply (binds_concat_left_ok Ok Bix).
    - apply (weaken_wf_typ_end WfT Ok).
  + (* case ty_call *)
    introv Tyt IH1 THas Tyu IH2 WfV Ok. subst.
    eapply ty_call.
    - eauto.
    - apply* weaken_typ_has_end.
    - apply* IH2.
    - apply* weaken_wf_typ_end.
(*
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Ok. subst.
    rewrite <- concat_assoc.
    apply_fresh ty_new as x';
    try assert (x'L: x' \notin L) by auto; try rewrite concat_assoc.
    - apply* IH1. apply okadmit.
    - apply* IH2. apply okadmit.
    - eauto.
*)
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Ok. subst.
    rewrite <- concat_assoc.
    (* No need for IHs because ty_new has a built-in weaken_end axiom *)
    apply_fresh ty_new as x'; try assert (x'L: x' \notin L) by auto.
    - apply* Tyds.
    - apply* Tyu.
    - eauto.
  + (* case ty_hyp *)
    introv WfT Ty IH Ok. subst.
    apply (ty_hyp (weaken_wf_typ_end WfT Ok)).
    intros G0 Se Gb.
    lets P: (subenv_concat_inv Se). destruct P as [G01 [G02 [Eq Se0]]]. subst.
    apply shrink_good_bounds in Gb.
    apply (IH _ Se0 Gb). apply okadmit.
  + (* case ty_sbsm *)
    introv Ty IH St Ok. eapply ty_sbsm.
    - apply* IH.
    - apply (weaken_subtyp_end Ok St).
  + (* case ty_tdef *)
    introv St Ok. apply ty_tdef. apply (weaken_subtyp_end Ok St).
(*
  + (* case ty_mdef *)
    introv WfT WfU2 Tyu IH Ok. subst.
    rewrite <- concat_assoc.
    apply_fresh ty_mdef as x'; [assumption | assumption | idtac].
    rewrite concat_assoc. apply* IH. apply okadmit.
*)
  + (* case ty_mdef *)
    introv WfT WfU2 Tyu IH Ok. subst.
    rewrite <- concat_assoc.
    apply_fresh ty_mdef as x'; [assumption | assumption | idtac].
    apply* Tyu. (* no need for IH because ty_mdef has built-in weaken_end axiom *)
  (*
  + (* case ty_def_hyp *)
    introv Wf Eq Tyd IH Ok.
    apply (ty_def_hyp (weaken_wf_dec_end Wf Ok) Eq).
    intros G0 Se Gb.
    lets P: (subenv_concat_inv Se). destruct P as [G01 [G02 [Eq' Se0]]]. subst.
    apply shrink_good_bounds in Gb.
    apply (IH _ Se0 Gb). apply okadmit.
  *)
  + (* case ty_defs_nil *) eauto.
  + (* case ty_defs_cons *) eauto.
Qed.

Print Assumptions weaken_ty_end_only.

Definition weaken_ty_trm_end  := proj31 weaken_ty_end_only.
Definition weaken_ty_def_end  := proj32 weaken_ty_end_only.
Definition weaken_ty_defs_end := proj33 weaken_ty_end_only.

(*
Lemma weaken_ty_without_good_bounds:
   (forall G t T, ty_trm G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_trm (G1 & G2 & G3) t T)
/\ (forall G t T, ty_imp G t T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_imp (G1 & G2 & G3) t T)
/\ (forall G d D, ty_def G d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_def (G1 & G2 & G3) d D)
/\ (forall G ds T, ty_defs G ds T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    ty_defs (G1 & G2 & G3) ds T).
Proof.
  destruct weaken_has as [WHas WHasnt].
  destruct weaken_wf as [WWfTyp WWfDec].
  destruct weaken_subtyp_subdec as [WSt WSd].
  apply ty_mutind.
  + (* case ty_var *)
    introv Bix WfT Eq Ok. subst. apply ty_var; eauto.
    apply (binds_weaken Bix Ok).
  + (* case ty_call *)
    introv Tyt IH1 THas Tyu IH2 WfV Eq Ok. subst.
    eapply ty_call; eauto.
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Eq Ok. subst.
    apply_fresh ty_new as x'; try assert (x'L: x' \notin L) by auto.
    - specialize (IH1 x' x'L G1 G2 (G3 & x' ~ open_typ x' T)).
      repeat rewrite concat_assoc in IH1. apply* IH1.
    - specialize (IH2 x' x'L G1 G2 (G3 & x' ~ open_typ x' T)).
      repeat rewrite concat_assoc in IH2. apply* IH2.
    - eauto.
  + (* case ty_hyp *)
    introv WfT Ty IH Eq Ok. subst.
    apply (ty_hyp (weaken_wf_typ_middle WfT Ok)).
    intro Gb. refine (IH _ _ _ _ eq_refl Ok).
    refine (shrink_good_bounds Ok _ Gb).
           (******************)
    admit. (* <--- that's why we don't use this lemma as such *)
  + (* case ty_sbsm *)
    introv Ty IH St Eq Ok. apply* ty_sbsm.
  + (* case ty_tdef *) eauto.
  + (* case ty_mdef *)
    introv WfT WfU2 Tyu IH Eq Ok. subst.
    apply_fresh ty_mdef as x'; [eauto | eauto | idtac].
    assert (x'L: x' \notin L) by auto.
    specialize (IH x' x'L G1 G2 (G3 & x' ~ T)).
    repeat rewrite concat_assoc in IH. apply* IH.
  + (* case ty_defs_nil *) eauto.
  + (* case ty_defs_cons *) eauto.
Qed.
*)

Lemma weaken_ty_trm_middle: forall G1 G2 G3 t T,
  good_bounds (G1 & G3) ->
  ok (G1 & G2 & G3) -> ty_trm (G1 & G3) t T -> ty_trm (G1 & G2 & G3) t T.
Proof.
Admitted.
 (* doesn't really hold because it would need to shrink good_bounds in the middle
  introv Gb Ok Ty. apply* weaken_ty.
Qed.

Lemma weaken_ty_trm_end: forall G1 G2 t T,
  ok (G1 & G2) -> 
  good_bounds G1 ->
  ty_trm G1        t T ->
  ty_trm (G1 & G2) t T.
Proof.
  introv Gb Ok Ty. destruct weaken_ty as [P _].
  specialize (P G1 _ _ Ty G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.

Lemma weaken_ty_imp_end: forall G1 G2 t T,
  ok (G1 & G2) -> 
  good_bounds G1 ->
  ty_imp G1        t T ->
  ty_imp (G1 & G2) t T.
Proof.
  introv Gb Ok Ty. destruct weaken_ty as [_ [P _]].
  specialize (P G1 _ _ Ty G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.
*)

Lemma weaken_ty_defs_middle: forall G1 G2 G3 ds T,
  good_bounds (G1 & G3) ->
  ok (G1 & G2 & G3) -> ty_defs (G1 & G3) ds T -> ty_defs (G1 & G2 & G3) ds T.
Proof.
Admitted. (* doesn't really hold because it would need to shrink good_bounds in the middle
  introv Gb Ok Ty. apply* weaken_ty.
Qed.

Lemma weaken_ty_defs_end: forall G1 G2 ds T,
  good_bounds G1 ->
  ok (G1 & G2) -> ty_defs G1 ds T -> ty_defs (G1 & G2) ds T.
Proof.
  introv Gb Ok Ty. destruct weaken_ty as [_ [_ [_ P]]].
  specialize (P G1 _ _ Ty G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.

Lemma weaken_ty_trm_middle: forall G1 G2 G3 t T,
  ok (G1 & G2 & G3) -> ty_trm (G1 & G3) t T -> ty_trm (G1 & G2 & G3) t T.
Proof.
  introv Ok Ty. apply* weaken_ty.
Qed.

Lemma weaken_ty_trm_end: forall G1 G2 t T,
  ok (G1 & G2) -> 
  ty_trm G1        t T ->
  ty_trm (G1 & G2) t T.
Proof.
  introv Ok Ty. destruct weaken_ty as [P _].
  specialize (P G1 _ _ Ty G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.

Lemma weaken_ty_imp_end: forall G1 G2 t T,
  ok (G1 & G2) -> 
  ty_imp G1        t T ->
  ty_imp (G1 & G2) t T.
Proof.
  introv Ok Ty. destruct weaken_ty as [_ [P _]].
  specialize (P G1 _ _ Ty G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.

Lemma weaken_ty_defs_middle: forall G1 G2 G3 ds T,
  ok (G1 & G2 & G3) -> ty_defs (G1 & G3) ds T -> ty_defs (G1 & G2 & G3) ds T.
Proof.
  introv Ok Ty. apply* weaken_ty.
Qed.

Lemma weaken_ty_defs_end: forall G1 G2 ds T,
  ok (G1 & G2) -> ty_defs G1 ds T -> ty_defs (G1 & G2) ds T.
Proof.
  introv Ok Ty. destruct weaken_ty as [_ [_ [_ P]]].
  specialize (P G1 _ _ Ty G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.
*)

(* ###################################################################### *)
(** ** Well-formed context *)

(* Note that T may contain variables defined anywhere in G, not just those
   defined before. 
Definition wf_ctx(G: ctx) := ok G /\ forall x T, binds x T G -> wf_typ G T. *)

Lemma wf_sto_to_ok_s: forall s G,
  wf_sto s G -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto s G -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds_raw: forall s G x T,
  wf_sto s G ->
  binds x T G ->
  exists G1 G2 ds, G = G1 & G2 /\ binds x ds s /\ ty_defs G1 ds T.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists (G & (x ~ T0)) (@empty typ) ds.
      rewrite concat_empty_r. auto.
    - specialize (IHWf _ _ Bi). destruct IHWf as [G1 [G2 [ds' [Eq [Bi' Tyds]]]]].
      subst. exists G1 (G2 & x ~ T) ds'. rewrite concat_assoc. auto.
Qed.

Lemma wf_sto_to_good_bounds: forall s G, wf_sto s G -> good_bounds G.
Proof.
  introv Wf. induction Wf.
  - apply good_bounds_empty.
  - apply (good_bounds_push IHWf). apply (ty_defs_to_good_bounds_typ H1).
Qed.

(*
Lemma wf_sto_to_good_bounds: forall s G, wf_sto s G -> good_bounds G.
Proof.
  unfold good_bounds. introv Wf BiG.
  destruct (ctx_binds_to_sto_binds_raw Wf BiG) as [G1 [G2 [ds [Eq [Bis Tyds]]]]]. subst.
  lets Gb: (ty_defs_to_good_bounds_typ Tyds).
  refine (weaken_good_bounds_typ_end _ Gb).
  apply (wf_sto_to_ok_G Wf).
Qed.

Lemma wf_ctx_push: forall G x T,
  wf_ctx G ->
  x # G ->
  wf_typ (G & x ~ T) T ->
  wf_ctx (G & x ~ T).
Proof.
  introv WfG WfT. unfold wf_ctx in *. destruct WfG as [Ok WfG]. split.
  - auto.
  - introv Bi. apply binds_push_inv in Bi. destruct Bi as [[Eq1 Eq2] | [Ne Bi]].
    * subst. assumption.
    * apply weaken_wf_typ_end; eauto.
Qed.
*)

Lemma invert_wf_sto_concat: forall s G1 G2,
  wf_sto s (G1 & G2) ->
  exists s1 s2, s = s1 & s2 /\ wf_sto s1 G1.
Proof.
  introv Wf. gen_eq G: (G1 & G2). gen G1 G2. induction Wf; introv Eq; subst.
  - do 2 exists (@empty defs). rewrite concat_empty_r. 
    apply empty_concat_inv in Eq. destruct Eq. subst. auto.
  - destruct (env_case G2) as [Eq1 | [x' [T' [G2' Eq1]]]].
    * subst G2. rewrite concat_empty_r in Eq. subst G1.
      exists (s & x ~ ds) (@empty defs). rewrite concat_empty_r. auto.
    * subst G2. rewrite concat_assoc in Eq. apply eq_push_inv in Eq.
      destruct Eq as [? [? ?]]. subst x' T' G. specialize (IHWf G1 G2' eq_refl).
      destruct IHWf as [s1 [s2 [Eq Wf']]]. subst.
      exists s1 (s2 & x ~ ds). rewrite concat_assoc. auto.
Qed.

Lemma ctx_binds_to_sto_binds: forall s G x T,
  wf_sto s G ->
  binds x T G ->
  exists ds, binds x ds s /\ ty_defs G ds T.
Proof.
  introv Wf Bi.
  lets P: (ctx_binds_to_sto_binds_raw Wf Bi).
  destruct P as [G1 [G2 [ds [Eq [Bis Tyds]]]]]. subst.
  exists ds. apply (conj Bis). refine (weaken_ty_defs_end Tyds _).
  (*
  - apply invert_wf_sto_concat in Wf. destruct Wf as [s1 [s2 [Eq Wf]]]. subst.
    apply (wf_sto_to_good_bounds Wf).
  *)
  - apply (wf_sto_to_ok_G Wf).
Qed.

Lemma sto_binds_to_ctx_binds: forall s G x ds,
  wf_sto s G ->
  binds x ds s ->
  exists T, binds x T G /\ ty_defs G ds T.
Proof.
  introv Wf Bi. gen x Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists T. auto.
    - specialize (IHWf _ Bi). destruct IHWf as [U [Bi' Tyds]].
      exists U. apply (conj Bi'). refine (weaken_ty_defs_end Tyds _).
      (* apply (wf_sto_to_good_bounds Wf). *)
      * apply wf_sto_to_ok_G in Wf. auto.
Qed.

Lemma sto_unbound_to_ctx_unbound: forall s G x,
  wf_sto s G ->
  x # s ->
  x # G.
Proof.
  introv Wf Ub_s.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub_s). 
    - auto.
Qed.

Lemma ctx_unbound_to_sto_unbound: forall s G x,
  wf_sto s G ->
  x # G ->
  x # s.
Proof.
  introv Wf Ub.
  induction Wf.
  + auto.
  + destruct (classicT (x0 = x)) as [Eq | Ne].
    - subst. false (fresh_push_eq_inv Ub). 
    - auto.
Qed.

(*
Lemma wf_sto_to_wf_ctx: forall s G,
  wf_sto s G -> wf_ctx G.
Proof.
  introv Wf. induction Wf; unfold wf_ctx in *.
  - split; auto. intros. exfalso. apply (binds_empty_inv H).
  - destruct IHWf as [Ok IH]. split; auto.
    intros. apply binds_push_inv in H2. destruct H2 as [[Eq1 Eq2] | [Ne Bi]].
    + subst. apply (ty_defs_regular H1).
    + apply weaken_wf_typ_end.
      * apply (IH _ _ Bi).
      * refine (ok_push _ Ok H0).
Qed.
*)

Lemma typ_has_to_defs_has: forall G T D x ds s,
  wf_sto s G ->
  typ_has G T D ->
  binds x ds s ->
  binds x T G ->
  exists d, defs_has ds d /\ ty_def G d D.
Proof.
  introv Wf THas Bis BiG.
  lets P: (sto_binds_to_ctx_binds Wf Bis). destruct P as [T' [Bi' Tyds]].
  apply (binds_func BiG) in Bi'. subst T'.
  apply (invert_ty_defs Tyds THas).
Qed.


(* ###################################################################### *)
(** ** subtyp-and-then-lookup to lookup-and-then-subdec *)

Lemma swap_sub_and_typ_has: forall G T1 T2 D2,
  subtyp G T1 T2 ->
  typ_has G T2 D2 ->
  exists D1,
    typ_has G T1 D1 /\
    subdec G D1 D2.
Proof.
  introv St. gen D2. induction St; introv T2Has.
  + (* case subtyp_refl *)
    eexists. apply (conj T2Has). apply subdec_refl.
    apply (typ_has_preserves_wf T2Has H).
  + (* case subtyp_top *)
    inversions T2Has.
  + (* case subtyp_bot *)
    rename T into T2.
    exists (dec_bot (label_of_dec D2)). split.
    - auto.
    - apply subdec_bot. apply (typ_has_preserves_wf T2Has H).
  + (* case subtyp_rcd *)
    inversions T2Has. rename D0 into D2. exists D1. auto.
  + (* case subtyp_sel_l *)
    rename H into Bi, H0 into XHas.
    exists D2. split.
    - eauto.
    - apply subdec_refl. apply (typ_has_preserves_wf T2Has).
      apply (proj2 (subtyp_regular St)).
  + (* case subtyp_sel_r *)
    rename H into Bi, H0 into Sb, H1 into WfX, H2 into XHas.
    inversions T2Has.
    lets Eq: (binds_func H1 Bi). subst T0.
    apply IHSt. clear IHSt.
    lets Eq: (typ_has_unique H3 XHas eq_refl). inversions Eq.
    exact H5.
  + (* case subtyp_and *)
    inversions T2Has.
    - eauto.
    - eauto.
    - rename H1 into U1Has, H3 into U2Has, H5 into Eq, D1 into DU1, D0 into DU2.
      specialize (IHSt1 _ U1Has). destruct IHSt1 as [D1 [THas Sd1]].
      specialize (IHSt2 _ U2Has). destruct IHSt2 as [D1' [THas' Sd2]].
      destruct (intersect_dec_label_eq _ _ Eq) as [Eq1 _].
      lets Eql1: (subdec_to_label_of_dec_eq Sd1).
      lets Eql2: (subdec_to_label_of_dec_eq Sd2).
      rewrite <- Eq1 in Eql2. rewrite <- Eql1 in Eql2.
      lets Eq': (typ_has_unique THas' THas Eql2). subst D1'. clear THas'.
      exists D1. apply (conj THas).
      apply (subdec_intersect Sd1 Sd2 Eq).
  + (* case subtyp_and_l *)
    rename T2Has into T1Has, D2 into D1, H into WfT1, H0 into WfT2.
    lets T2Has: (typ_has_total WfT2). specialize (T2Has (label_of_dec D1)).
                (*************)
    destruct T2Has as [T2Hasnt | [D2 [Eq T2Has]]].
    - exists D1. split.
      * auto.
      * apply subdec_refl. apply (typ_has_preserves_wf T1Has WfT1).
    - destruct (intersect_dec_total _ _ Eq) as [D12 Eq12]. exists D12. split.
      * eauto.
      * lets WfD1: (typ_has_preserves_wf T1Has WfT1).
        lets WfD2: (typ_has_preserves_wf T2Has WfT2).
        apply (subdec_intersect_l Eq12 WfD1 WfD2).
  + (* case subtyp_and_r *)
    rename H into WfT1, H0 into WfT2.
    lets T1Has: (typ_has_total WfT1). specialize (T1Has (label_of_dec D2)).
                (*************)
    destruct T1Has as [T1Hasnt | [D1 [Eq T1Has]]].
    - exists D2. split.
      * auto.
      * apply subdec_refl. apply (typ_has_preserves_wf T2Has WfT2).
    - symmetry in Eq.
      destruct (intersect_dec_total _ _ Eq) as [D12 Eq12]. exists D12. split.
      * eauto.
      * lets WfD1: (typ_has_preserves_wf T1Has WfT1).
        lets WfD2: (typ_has_preserves_wf T2Has WfT2).
        apply (subdec_intersect_r Eq12 WfD1 WfD2).
  + (* case subtyp_or *)
    rename T2Has into UHas.
    specialize (IHSt1 _ UHas). destruct IHSt1 as [D01 [T1Has Sd1]].
    specialize (IHSt2 _ UHas). destruct IHSt2 as [D02 [T2Has Sd2]].
    lets Eql1: (subdec_to_label_of_dec_eq Sd1).
    lets Eql2: (subdec_to_label_of_dec_eq Sd2).
    rewrite <- Eql2 in Eql1.
    destruct (union_dec_total _ _ Eql1) as [D12 Eq12]. exists D12. split.
    - apply (typ_or_has T1Has T2Has Eq12).
    - apply (subdec_union Sd1 Sd2 Eq12).
  + (* case subtyp_or_l *)
    inversions T2Has. rename H3 into T1Has, H5 into T2Has, D2 into D12, D0 into D2.
    exists D1. apply (conj T1Has). apply (subdec_union_l H7).
    - apply (typ_has_preserves_wf T1Has H).
    - apply (typ_has_preserves_wf T2Has H0).
  + (* case subtyp_or_r *)
    inversions T2Has. rename H3 into T1Has, H5 into T2Has, D2 into D12, D0 into D2.
    exists D2. apply (conj T2Has). apply (subdec_union_r H7).
    - apply (typ_has_preserves_wf T1Has H).
    - apply (typ_has_preserves_wf T2Has H0).
  + (* case subtyp_trans *)
    rename D2 into D3, T2Has into T3Has.
    specialize (IHSt2 _ T3Has).
    destruct IHSt2 as [D2 [T2Has Sd23]].
    specialize (IHSt1 _ T2Has).
    destruct IHSt1 as [D1 [T1Has Sd12]].
    exists D1. apply (conj T1Has). apply (subdec_trans Sd12 Sd23).
Qed.

Print Assumptions swap_sub_and_typ_has.


(* ###################################################################### *)
(** ** Properties of good_bounds *)

Lemma distribute_and: forall (P1 P2 Q1 Q2: Prop),
  (P1 /\ P2 -> Q1 /\ Q2) -> ((P1 /\ P2 -> Q1) /\ (P1 /\ P2 -> Q2)).
Proof.
  intros. split; intro H0; specialize (H H0); destruct H; auto.
Qed.

Lemma supertyp_has_good_bounds: forall G T1 T2,
  subtyp G T1 T2 ->
  good_bounds_typ G T1 ->
  good_bounds_typ G T2.
Proof.
  introv St. unfold good_bounds_typ.
  induction St; introv Gb; destruct Gb as [Wf Gb];
  repeat match goal with
  | H: _ /\ _ -> _ /\ _ |- _ => apply distribute_and in H; apply proj2 in H
  end;
  try (split; [(solve [eauto 4]) | introv T2Has]).
  + (* case subtyp_refl *)
    eauto.
  + (* case subtyp_top *)
    inversions T2Has.
  + (* case subtyp_bot *)
    specialize (Gb L typ_top typ_bot (typ_bot_has G (label_typ L))).
    lets WfD: (typ_has_preserves_wf T2Has H). inversions WfD.
    refine (subtyp_trans (subtyp_top H4) _).
    refine (subtyp_trans _ (subtyp_bot H6)).
    exact Gb.
  + (* case subtyp_rcd *)
    inversions T2Has.
    apply invert_subdec_typ_sync_left in H. destruct H as [Lo' [Hi' [Eq [StLo StHi]]]].
    subst. eauto.
  + (* case subtyp_sel_l *)
    eauto.
  + (* case subtyp_sel_r *)
    inversions T2Has.
    lets Eq: (binds_func H5 H). subst T0.
    lets Eq: (typ_has_unique H7 H2 eq_refl). inversions Eq.
    eauto.
  + (* case subtyp_and *)
    inversions T2Has.
    - eauto.
    - eauto.
    - destruct D1 as [L1 Lo1 Hi1 | ]; destruct D2 as [L2 Lo2 Hi2 | ];
      unfold intersect_dec in H5; simpl in H5; case_if; inversions H5.
      symmetry in H. inversions H.
      specialize (IHSt1 (conj Wf Gb) _ _ _ H1).
      specialize (IHSt2 (conj Wf Gb) _ _ _ H3).
      lets P: (swap_sub_and_typ_has St1 H1). destruct P as [D1 [THas Sd]].
              (********************)
      apply invert_subdec_typ_sync_left in Sd.
      destruct Sd as [Lo0 [Hi0 [Eq [StLo1 StHi1]]]]. subst.
      lets P: (swap_sub_and_typ_has St2 H3). destruct P as [D1 [THas' Sd]].
              (********************)
      apply invert_subdec_typ_sync_left in Sd.
      destruct Sd as [Lo0' [Hi0' [Eq [StLo2 StHi2]]]]. subst.
      lets Eq: (typ_has_unique THas' THas eq_refl). inversions Eq. clear THas'.
      specialize (Gb _ _ _ THas).
      apply subtyp_and; apply subtyp_or.
      * exact IHSt1.
      * apply (subtyp_trans StLo2 (subtyp_trans Gb StHi1)).
      * apply (subtyp_trans StLo1 (subtyp_trans Gb StHi2)).
      * exact IHSt2.
  + (* case subtyp_and_l *)
    rename T2Has into T1Has, Lo into Lo1, Hi into Hi1.
    destruct (typ_has_total H0 (label_typ L)) as [T2Hasnt | [D2 [Eq T2Has]]].
    - eauto.
    - symmetry in Eq. destruct D2 as [L' Lo2 Hi2 | ]; inversions Eq.
      specialize (Gb L (typ_or Lo1 Lo2) (typ_and Hi1 Hi2)).
      lets Wf1: (typ_has_preserves_wf T1Has H). inversions Wf1.
      lets Wf2: (typ_has_preserves_wf T2Has H0). inversions Wf2.
      refine (subtyp_trans _ (subtyp_and_l H7 H9)).
      refine (subtyp_trans (subtyp_or_l H5 H6) _).
      apply Gb.
      apply (typ_and_has_12 T1Has T2Has). unfold intersect_dec. simpl. case_if. reflexivity.
  + (* case subtyp_and_r *)
    rename Lo into Lo2, Hi into Hi2.
    destruct (typ_has_total H (label_typ L)) as [T1Hasnt | [D1 [Eq T1Has]]].
    - eauto.
    - symmetry in Eq. destruct D1 as [L' Lo1 Hi1 | ]; inversions Eq.
      specialize (Gb L (typ_or Lo1 Lo2) (typ_and Hi1 Hi2)).
      lets Wf1: (typ_has_preserves_wf T1Has H). inversions Wf1.
      lets Wf2: (typ_has_preserves_wf T2Has H0). inversions Wf2.
      refine (subtyp_trans _ (subtyp_and_r H7 H9)).
      refine (subtyp_trans (subtyp_or_r H5 H6) _).
      apply Gb.
      apply (typ_and_has_12 T1Has T2Has). unfold intersect_dec. simpl. case_if. reflexivity.
  + (* case subtyp_or *)
    rename T2Has into UHas.
    lets P: (swap_sub_and_typ_has St1 UHas). destruct P as [D1 [T1Has Sd]].
            (********************)
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo1 StHi1]]]]. subst.
    lets P: (swap_sub_and_typ_has St2 UHas). destruct P as [D2 [T2Has Sd]].
            (********************)
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo2 [Hi2 [Eq [StLo2 StHi2]]]]. subst.
    refine (subtyp_trans _ (subtyp_or StHi1 StHi2)).
    refine (subtyp_trans (subtyp_and StLo1 StLo2) _).
    apply Gb with L. apply (typ_or_has T1Has T2Has).
    unfold union_dec. simpl. case_if. reflexivity.
  + (* case subtyp_or_l *)
    inversions T2Has.
    destruct D1 as [L1 Lo1 Hi1 | ]; destruct D2 as [L2 Lo2 Hi2 | ];
    unfold union_dec in H7; simpl in H7; case_if; inversions H7.
    symmetry in H1. inversions H1.
    specialize (Gb _ _ _ H3).
    lets Wf1: (typ_has_preserves_wf H3 H). inversions Wf1.
    lets Wf2: (typ_has_preserves_wf H5 H0). inversions Wf2.
    refine (subtyp_trans (subtyp_and_l H7 H8) _).
    refine (subtyp_trans _ (subtyp_or_l H9 H11)).
    exact Gb.
  + (* case subtyp_or_r *)
    inversions T2Has.
    destruct D1 as [L1 Lo1 Hi1 | ]; destruct D2 as [L2 Lo2 Hi2 | ];
    unfold union_dec in H7; simpl in H7; case_if; inversions H7.
    symmetry in H1. inversions H1.
    specialize (Gb _ _ _ H5).
    lets Wf1: (typ_has_preserves_wf H3 H). inversions Wf1.
    lets Wf2: (typ_has_preserves_wf H5 H0). inversions Wf2.
    refine (subtyp_trans (subtyp_and_r H7 H8) _).
    refine (subtyp_trans _ (subtyp_or_r H9 H11)).
    exact Gb.
  + (* case subtyp_trans *)
    destruct (subtyp_regular St1) as [Wf1 Wf2].
    destruct (subtyp_regular St2) as [_ Wf3].
    eauto.
Qed.

Print Assumptions supertyp_has_good_bounds.


(* ###################################################################### *)
(** ** The substitution principle *)

Lemma subst_label_of_dec: forall x y D,
  label_of_dec D = label_of_dec (subst_dec x y D).
Proof.
  intros. destruct D; simpl; reflexivity.
Qed.

Lemma subst_label_of_def: forall x y d,
  label_of_def d = label_of_def (subst_def x y d).
Proof.
  intros. destruct d; simpl; reflexivity.
Qed.

Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_defs x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - simpl. reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if. apply (IHds Eq).
Qed.

Lemma subst_binds_0: forall x y v T G,
  binds v T G ->
  binds v (subst_typ x y T) (subst_ctx x y G).
Proof.
  introv Bi. unfold subst_ctx. apply binds_map. exact Bi.
Qed.

Lemma subst_binds: forall G1 x S G2 z Z y,
  binds z Z (G1 & x ~ S & G2) ->
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  binds (subst_fvar x y z) (subst_typ x y Z) (subst_ctx x y (G1 & G2)).
Proof.
  introv Biz Ok Biy. unfold subst_fvar. case_if.
  - (* case x = z *)
    lets Eq: (binds_middle_eq_inv Biz Ok). subst.
    lets P: (subst_binds_0 x y Biy). rewrite subst_typ_idempotent in P. exact P.
  - (* case x <> z *)
    apply subst_binds_0. apply (binds_subst Biz). auto.
Qed.

Lemma subst_binds_end_only: forall G1 x S z Z y,
  binds z Z (G1 & x ~ S) ->
  ok (G1 & x ~ S) ->
  binds y (subst_typ x y S) G1 ->
  binds (subst_fvar x y z) (subst_typ x y Z) (subst_ctx x y G1).
Proof.
  introv Biz Ok Biy. unfold subst_fvar. case_if.
  - (* case x = z *)
    lets Eq: (binds_push_eq_inv Biz). subst.
    lets P: (subst_binds_0 x y Biy). rewrite subst_typ_idempotent in P. exact P.
  - (* case x <> z *)
    apply subst_binds_0. apply (binds_push_neq_inv Biz). auto.
Qed.

Lemma subst_narrow_binds_end_only: forall G1 x S z Z y,
  binds z Z (G1 & x ~ S) ->
  ok (G1 & x ~ S) ->
  binds y (subst_typ x y S) G1 ->
  binds (subst_fvar x y z) (subst_typ x y Z) (subst_ctx x y G1).
Proof.
  introv Biz Ok Biy. unfold subst_fvar. case_if.
  - (* case x = z *)
    lets Eq: (binds_push_eq_inv Biz). subst.
    lets P: (subst_binds_0 x y Biy). rewrite subst_typ_idempotent in P. exact P.
  - (* case x <> z *)
    apply subst_binds_0. apply (binds_push_neq_inv Biz). auto.
Qed.

Lemma subst_intersect_dec: forall x y D1 D2 D3,
  D1 && D2 == D3 ->
  subst_dec x y D1 && subst_dec x y D2 == subst_dec x y D3.
Proof.
  introv Eq. unfold intersect_dec in *. case_if.
  + do 2 rewrite <- subst_label_of_dec in H. case_if.
    destruct D1; destruct D2; destruct D3; try discriminate;
    simpl; inversions Eq; reflexivity.
  + do 2 rewrite <- subst_label_of_dec in H. case_if.
Qed.

Lemma subst_union_dec: forall x y D1 D2 D3,
  D1 || D2 == D3 ->
  subst_dec x y D1 || subst_dec x y D2 == subst_dec x y D3.
Proof.
  introv Eq. unfold union_dec in *. case_if.
  + do 2 rewrite <- subst_label_of_dec in H. case_if.
    destruct D1; destruct D2; destruct D3; try discriminate;
    simpl; inversions Eq; reflexivity.
  + do 2 rewrite <- subst_label_of_dec in H. case_if.
Qed.

Lemma if_hoist: forall (A B: Type) (C: Prop) (f: A -> B) (e1 e2: A),
  (If C then f e1 else f e2) = f (If C then e1 else e2).
Proof.
  intros. case_if*.
Qed.

Lemma subst_stable_typ: forall x y T, stable_typ T -> stable_typ (subst_typ x y T).
Proof.
  intros x y T. induction T; intro S; simpl; inversions S; auto.
Qed.

Lemma subst_has_hasnt: forall y S,
   (forall G T D, typ_has G T D -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    typ_has (subst_ctx x y (G1 & G2)) (subst_typ x y T) (subst_dec x y D))
/\ (forall G T l, typ_hasnt G T l -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    typ_hasnt (subst_ctx x y (G1 & G2)) (subst_typ x y T) l).
Proof.
  intros y S. apply typ_has_mutind.
  + (* case typ_bot_has *)
    intros. subst.
    lets P: (typ_bot_has (subst_ctx x y (G1 & G2)) l). destruct l; eauto.
  + (* case typ_rcd_has *)
    intros. subst. apply typ_rcd_has.
  + (* case typ_sel_has *)
    introv Bix THas IH1 HiHas IH2 Eq Ok Biy. subst. eq_specialize.
    specialize (IH1 Ok Biy).
    specialize (IH2 Ok Biy).
    lets Bix': (subst_binds Bix Ok Biy).
    simpl. rewrite if_hoist. apply* typ_sel_has.
  + (* case typ_and_has_1 *)
    intros. subst. apply typ_and_has_1.
    - eauto.
    - rewrite <- subst_label_of_dec. eauto.
  + (* case typ_and_has_2 *)
    intros. subst. apply typ_and_has_2.
    - rewrite <- subst_label_of_dec. eauto.
    - eauto.
  + (* case typ_and_has_12 *)
    intros. subst. eapply typ_and_has_12; eauto.
    apply subst_intersect_dec. assumption.
  + (* case typ_or_has *)
    intros. subst. eapply typ_or_has; eauto.
    apply subst_union_dec. assumption.
  + (* case typ_top_hasnt *)
    eauto.
  + (* case typ_rcd_hasnt *)
    intros. subst. apply typ_rcd_hasnt.
    rewrite <- subst_label_of_dec. assumption.
  + (* case typ_sel_hasnt *)
    introv Bix THas IH1 HiHasnt IH2 Eq Ok Biy. subst. eq_specialize.
    specialize (IH1 Ok Biy).
    specialize (IH2 Ok Biy).
    lets Bix': (subst_binds Bix Ok Biy).
    simpl. rewrite if_hoist. apply* typ_sel_hasnt.
  + (* case typ_and_hasnt *)
    intros. subst. apply typ_and_hasnt; eauto.
  + (* case typ_or_hasnt_1 *)
    intros. subst. rewrite (subst_label_of_dec x y D) in *.
    apply typ_or_hasnt_1; eauto.
  + (* case typ_or_hasnt_2 *)
    intros. subst. rewrite (subst_label_of_dec x y D) in *.
    apply typ_or_hasnt_2; eauto.
  + (* case typ_or_hasnt_12 *)
    intros. subst. apply typ_or_hasnt_12; eauto.
Qed.

Print Assumptions subst_has_hasnt.

Lemma subst_has: forall G1 x y S G2 T D,
  typ_has (G1 & x ~ S & G2) T D ->
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  typ_has (subst_ctx x y (G1 & G2)) (subst_typ x y T) (subst_dec x y D).
Proof.
  intros. apply* subst_has_hasnt.
Qed.

Lemma subst_hasnt: forall G1 x y S G2 T l,
  typ_hasnt (G1 & x ~ S & G2) T l ->
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  typ_hasnt (subst_ctx x y (G1 & G2)) (subst_typ x y T) l.
Proof.
  intros. apply* subst_has_hasnt.
Qed.

Definition subst_assumptions(x y: var)(A1 A2: fset typ) :=
   (forall T1, T1 \in A1 -> (subst_typ x y T1) \in A2)
/\ (forall T2, T2 \in A2 -> exists T1, T1 \in A1 /\ (subst_typ x y T1) = T2).

Lemma subst_wf: forall y S,
   (forall G A1 T, wf_typ_impl G A1 T -> forall G1 G2 x A2,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    subst_assumptions x y A1 A2 ->
    wf_typ_impl (subst_ctx x y (G1 & G2)) A2 (subst_typ x y T))
/\ (forall G A1 D, wf_dec_impl G A1 D -> forall G1 G2 x A2,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    subst_assumptions x y A1 A2 ->
    wf_dec_impl (subst_ctx x y (G1 & G2)) A2 (subst_dec x y D)).
Proof.
  intros y S.
  apply wf_mutind.
  + (* case wf_top *) eauto.
  + (* case wf_bot *) eauto.
  + (* case wf_hyp *)
    intros. subst. apply wf_hyp.
    destruct H2 as [Incl _]. apply* Incl.
  + (* case wf_rcd *)
    intros. subst. apply wf_rcd. fold subst_dec.
    refine (H _ _ _ _ eq_refl H1 H2 _).
    unfold subst_assumptions in *.
    destruct H3 as [Incl1 Incl2].
    split; introv In.
    - rewrite in_union in *. destruct In as [In | In].
      * left. apply (Incl1 _ In).
      * right. rewrite in_singleton in *. subst T1. reflexivity.
    - rewrite in_union in *. destruct In as [In | In].
      * specialize (Incl2 T2 In). destruct Incl2 as [T1 [T1A Eq]].
        eexists. rewrite in_union. eauto.
      * rewrite in_singleton in In. subst T2. exists (typ_rcd D).
        rewrite in_union. rewrite in_singleton. auto.
  + (* case wf_sel *)
    intros G A1 x X L Lo Hi Bix Sb XHas WfX IHX WfLo IHLo WfHi IHHi.
    intros G1 G2 x0 A2 Eq Ok Biy Su.
    subst.
    specialize (IHX  _ _ _ _ eq_refl Ok Biy Su).
    specialize (IHLo _ _ _ _ eq_refl Ok Biy Su).
    specialize (IHHi _ _ _ _ eq_refl Ok Biy Su).
    destruct (subst_has_hasnt y S) as [SubstHas SubstHasnt].
    lets Bix': (subst_binds Bix Ok Biy).
    simpl. rewrite if_hoist.
    refine (wf_sel Bix' _ _ IHX IHLo IHHi).
    - apply (subst_stable_typ _ _ Sb).
    - apply (SubstHas _ _ _ XHas _ _ _ eq_refl Ok Biy).
  + (* case wf_and *)
    intros. subst. apply wf_and; eauto.
  + (* case wf_or *)
    intros. subst. apply wf_or; eauto.
  + (* case wf_tmem *)
    intros. subst. apply wf_tmem; eauto.
  + (* case wf_mtd *) eauto.
    intros. subst. apply wf_mtd; eauto.
Qed.

Lemma subst_wf_typ: forall G1 x y S G2 T,
  wf_typ (G1 & x ~ S & G2) T ->
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  wf_typ (subst_ctx x y (G1 & G2)) (subst_typ x y T).
Proof.
  introv Wf Ok Biy. destruct (subst_wf y S) as [P _].
  apply (P _ \{} _ Wf _ _ _ \{} eq_refl Ok Biy).
  split; introv Ie; rewrite in_empty in Ie; exfalso; exact Ie.
Qed.

Lemma subst_wf_dec: forall G1 x y S G2 D,
  wf_dec (G1 & x ~ S & G2) D ->
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  wf_dec (subst_ctx x y (G1 & G2)) (subst_dec x y D).
Proof.
  introv Wf Ok Biy. destruct (subst_wf y S) as [_ P].
  apply (P _ \{} _ Wf _ _ _ \{} eq_refl Ok Biy).
  split; introv Ie; rewrite in_empty in Ie; exfalso; exact Ie.
Qed.

Hint Resolve subst_has subst_hasnt subst_wf_typ subst_wf_dec.

Lemma subst_subtyp_subdec: forall y S,
   (forall G T1 T2, subtyp G T1 T2 -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    subtyp (subst_ctx x y (G1 & G2)) (subst_typ x y T1) (subst_typ x y T2))
/\ (forall G D1 D2, subdec G D1 D2 -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    subdec (subst_ctx x y (G1 & G2)) (subst_dec x y D1) (subst_dec x y D2)).
Proof.
  intros y S. apply subtyp_mutind.
  + (* case subtyp_refl *)
    intros. subst. eauto.
  + (* case subtyp_top *)
    intros. subst. eauto.
  + (* case subtyp_bot *)
    intros. subst. eauto.
  + (* case subtyp_rcd *)
    introv Sd IH Eq Ok Biy. subst. apply subtyp_rcd. eauto.
  + (* case subtyp_sel_l *)
    introv Bix WfX Sb XHas St IH Eq Ok Biy. subst. eq_specialize.
    specialize (IH Ok Biy).
    lets Bix': (subst_binds Bix Ok Biy).
    simpl. rewrite if_hoist.
    apply subtyp_sel_l with (subst_typ x0 y X) (subst_typ x0 y T).
    * apply Bix'.
    * eauto.
    * apply (subst_stable_typ _ _ Sb).
    * apply (subst_has XHas Ok Biy).
    * apply IH.
  + (* case subtyp_sel_r *)
    introv Bix WfX Sb XHas St IH Eq Ok Biy. subst. eq_specialize.
    specialize (IH Ok Biy).
    lets Bix': (subst_binds Bix Ok Biy).
    simpl. rewrite if_hoist.
    apply subtyp_sel_r with (subst_typ x0 y X) (subst_typ x0 y U).
    * apply Bix'.
    * eauto.
    * apply (subst_stable_typ _ _ Sb).
    * apply (subst_has XHas Ok Biy).
    * apply IH.
  + (* case subtyp_and *)
    introv St1 IH1 St2 IH2 Eq Ok Biy. subst. eq_specialize.
    specialize (IH1 Ok Biy).
    specialize (IH2 Ok Biy).
    apply subtyp_and; eauto.
  + (* case subtyp_and_l *)
    introv Wf1 Wf2 Eq Ok Biy. subst. apply subtyp_and_l; eauto.
  + (* case subtyp_and_r *)
    introv Wf1 Wf2 Eq Ok Biy. subst. apply subtyp_and_r; eauto.
  + (* case subtyp_or *)
    intros. subst. eq_specialize. apply subtyp_or; eauto.
  + (* case subtyp_or_l *)
    intros. subst. eq_specialize. apply subtyp_or_l; eauto.
  + (* case subtyp_or_r *)
    intros. subst. eq_specialize. apply subtyp_or_r; eauto.
  + (* case subtyp_trans *)
    introv St12 IH12 St23 IH23 Eq Ok Biy. subst. eq_specialize.
    specialize (IH12 Ok Biy).
    specialize (IH23 Ok Biy).
    apply subtyp_trans with (subst_typ x y T2); eauto.
  + (* case subdec_typ *)
    intros. subst. eq_specialize. apply subdec_typ; eauto.
  + (* case subdec_mtd *)
    intros. subst. eq_specialize. apply subdec_mtd; eauto.
Qed.

Lemma subst_subtyp: forall G1 x y S G2 T1 T2,
  subtyp (G1 & x ~ S & G2) T1 T2 ->
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  subtyp (subst_ctx x y (G1 & G2)) (subst_typ x y T1) (subst_typ x y T2).
Proof.
  intros. apply* subst_subtyp_subdec.
Qed.

Lemma subtyp_subst_principle: forall G x y S T1 T2,
  subtyp (G & x ~ S) T1 T2 ->
  ok (G & x ~ S) ->
  binds y (subst_typ x y S) G ->
  subtyp (subst_ctx x y G) (subst_typ x y T1) (subst_typ x y T2).
Proof.
  introv St Ok Biy.
  destruct (subst_subtyp_subdec y S) as [P _].
  specialize (P _ _ _ St G empty x). repeat rewrite concat_empty_r in P.
  apply (P eq_refl Ok Biy).
Qed.

(* undo what the substitution lemma did: *)
Lemma undo_subst_good_bounds: forall G1 x S G2 y,
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  good_bounds (subst_ctx x y (G1 & G2)) ->
  good_bounds (G1 & x ~ S & G2).
Abort.

Lemma subst_has_end: forall G1 x y S T D,
  typ_has (G1 & x ~ S) T D ->
  ok (G1 & x ~ S) ->
  binds y (subst_typ x y S) G1 ->
  typ_has (subst_ctx x y G1) (subst_typ x y T) (subst_dec x y D).
Proof.
Admitted. (*
  intros. apply* subst_has_hasnt.
Qed.*)

Lemma subst_hasnt_end: forall G1 x y S T l,
  typ_hasnt (G1 & x ~ S) T l ->
  ok (G1 & x ~ S) ->
  binds y (subst_typ x y S) G1 ->
  typ_hasnt (subst_ctx x y G1) (subst_typ x y T) l.
Proof.
Admitted. (*
  intros. apply* subst_has_hasnt.
Qed.*)

Lemma subst_wf_typ_end: forall G1 x y S T,
  wf_typ (G1 & x ~ S) T ->
  ok (G1 & x ~ S) ->
  binds y (subst_typ x y S) G1 ->
  wf_typ (subst_ctx x y G1) (subst_typ x y T).
Proof.
  introv Wf Ok Biy. destruct (subst_wf y S) as [P _].
  rewrite <- (concat_empty_r G1).
  rewrite <- (concat_empty_r (G1 & x ~ S)) in Ok, Wf.
  rewrite <- (concat_empty_r G1) in Biy.
  apply (P _ \{} _ Wf _ _ _ \{} eq_refl Ok Biy).
  split; introv Ie; rewrite in_empty in Ie; exfalso; exact Ie.
Qed.

Lemma subst_wf_dec_end: forall G1 x y S D,
  wf_dec (G1 & x ~ S) D ->
  ok (G1 & x ~ S) ->
  binds y (subst_typ x y S) G1 ->
  wf_dec (subst_ctx x y G1) (subst_dec x y D).
Proof.
  introv Wf Ok Biy. destruct (subst_wf y S) as [_ P].
Admitted.
(*
  apply (P _ \{} _ Wf _ _ _ \{} eq_refl Ok Biy).
  split; introv Ie; rewrite in_empty in Ie; exfalso; exact Ie.
Qed.
*)

Hint Resolve subst_has_end subst_hasnt_end subst_wf_typ_end subst_wf_dec_end.

(*

Lemma subst_narrow_ty_end: forall y S,
   (forall G t T, ty_trm G t T -> forall G' G1 x,
    G = G1 & x ~ S ->
    ok (G1 & x ~ S) ->
    subenv G' G ->
    ty_trm G' (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_trm G' (subst_trm x y t) (subst_typ x y T))
/\ (forall G d D, ty_def G d D -> forall G' G1 x,
    G = G1 & x ~ S ->
    ok (G1 & x ~ S) ->
    subenv G' G ->
    ty_trm G' (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_def (subst_ctx x y G1) (subst_def x y d) (subst_dec x y D))
/\ (forall G ds T, ty_defs G ds T -> forall G' G1 x,
    G = G1 & x ~ S ->
    ok (G1 & x ~ S) ->
    subenv G' G ->
    ty_trm G' (trm_var (avar_f y)) (subst_typ x y S) ->
    ty_defs (subst_ctx x y G1) (subst_defs x y ds) (subst_typ x y T)).
*)

Lemma subst_narrow_binds_end: forall G G' x y S1 S2 z Z2,
  ok (G & x ~ S2) ->
  subenv G' G ->
  binds y S1 G' ->
  subtyp G' S1 (subst_typ x y S2) ->
  binds z Z2 (G & x ~ S2) ->
  exists Z1, binds (subst_fvar x y z) Z1 G' /\ subtyp G' Z1 (subst_typ x y Z2).
Admitted.

(* On type level, we only need subst_narrow for stable types: *)
Lemma subst_narrow_has_hasnt_stable_end: forall y S2,
   (forall G T D, typ_has G T D -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    stable_typ T ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    typ_has G' (subst_typ x y T) (subst_dec x y D))
/\ (forall G T l, typ_hasnt G T l -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    stable_typ T ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    typ_hasnt G' (subst_typ x y T) l).
Proof.
  intros y S. apply typ_has_mutind.
  + (* case typ_bot_has *)
    intros. subst.
    lets P: (typ_bot_has G' l). destruct l; simpl; eauto.
  + (* case typ_rcd_has *)
    intros. subst. apply typ_rcd_has.
  + (* case typ_sel_has *)
    intros. inversions H3.
  + (* case typ_and_has_1 *)
    intros. subst. simpl. inversions H3. apply typ_and_has_1.
    - eauto.
    - rewrite <- subst_label_of_dec. eauto.
  + (* case typ_and_has_2 *) eauto.
    intros. subst. simpl. inversions H3. apply typ_and_has_2.
    - rewrite <- subst_label_of_dec. eauto.
    - eauto.
  + (* case typ_and_has_12 *)
    intros. subst. inversions H3. eapply typ_and_has_12; eauto.
    apply subst_intersect_dec. assumption.
  + (* case typ_or_has *)
    intros. subst. inversions H3. eapply typ_or_has; eauto.
    apply subst_union_dec. assumption.
  + (* case typ_top_hasnt *)
    eauto.
  + (* case typ_rcd_hasnt *)
    intros. subst. apply typ_rcd_hasnt.
    rewrite <- subst_label_of_dec. assumption.
  + (* case typ_sel_hasnt *)
    intros. inversions H3.
  + (* case typ_and_hasnt *)
    intros. inversions H3. subst. apply typ_and_hasnt; eauto.
  + (* case typ_or_hasnt_1 *)
    intros. subst. inversions H3. rewrite (subst_label_of_dec x y D) in *.
    apply typ_or_hasnt_1; eauto.
  + (* case typ_or_hasnt_2 *)
    intros. subst. inversions H3. rewrite (subst_label_of_dec x y D) in *.
    apply typ_or_hasnt_2; eauto.
  + (* case typ_or_hasnt_12 *)
    intros. subst. inversions H3. apply typ_or_hasnt_12; eauto.
Qed.

Print Assumptions subst_narrow_has_hasnt_stable_end.

(*
Lemma subst_narrow_has_stable_end: forall T D G' G1 x y S1 S2,
  typ_has (G1 & x ~ S2) T D ->
  ok (G1 & x ~ S2) ->
  stable_typ T ->
  subenv G' G1 ->
  binds y S1 G' ->
  subtyp G' S1 (subst_typ x y S2) ->
  typ_has G' (subst_typ x y T) (subst_dec x y D).

Lemma subst_narrow_hasnt_stable_end
/\ (forall G T l, typ_hasnt G T l -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    stable_typ T ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    typ_hasnt G' (subst_typ x y T) l).
Proof.
*)

(* On term level, we also need subst_narrow for non-stable types.
   Since we already proved it for stable types, we now have subst_narrow_wf available
   (which depends on subst_narrow_has_stable). *)   
Lemma subst_narrow_has_hasnt_end: forall y S2,
   (forall G T D2, typ_has G T D2 -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    exists D1, typ_has G' (subst_typ x y T) D1 /\ subdec G' D1 (subst_dec x y D2))
/\ (forall G T l, typ_hasnt G T l -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    typ_hasnt G' (subst_typ x y T) l).
Proof.
  intros y S. apply typ_has_mutind.
  + (* case typ_bot_has *)
    intros. subst. exists (dec_bot l).
    lets P: (typ_bot_has G' l). destruct l; simpl; eauto.
  + (* case typ_rcd_has *)
    intros. subst. exists (subst_dec x y D). split.
    - apply typ_rcd_has.
    - admit. (* wf-ness!!! *)
  + (* case typ_sel_has *)
    introv Bix THas IH1 HiHas IH2. introv Eq Ok Se Biy StS. subst. eq_specialize.
    specialize (IH1 _ _ _ S1 eq_refl Ok Se Biy StS).
    specialize (IH2 _ _ _ S1 eq_refl Ok Se Biy StS).
    simpl. rewrite if_hoist.
    lets Bix': (subst_narrow_binds_end Ok Se Biy StS Bix).
    destruct Bix' as [T' [Bix' St]].
(*
    lets P: (swap_sub_and_typ_has St IH1). destruct P as [D1 [T'Has Sd]].
    simpl in Sd. apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo' [Hi' [? [StLo StHi]]]]. subst D1.
    apply (typ_sel_has Bix' T'Has). IH2). eauto.
*)
Admitted.

Lemma subst_narrow_ty_end: forall y S2,
   (forall G t T, ty_trm G t T -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    ty_trm G' (subst_trm x y t) (subst_typ x y T))
/\ (forall G d D, ty_def G d D -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    ty_def (subst_ctx x y G1) (subst_def x y d) (subst_dec x y D))
/\ (forall G ds T, ty_defs G ds T -> forall G' G1 x S1,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S2) ->
    subenv G' G1 ->
    binds y S1 G' ->
    subtyp G' S1 (subst_typ x y S2) ->
    ty_defs (subst_ctx x y G1) (subst_defs x y ds) (subst_typ x y T)).
Proof.
  intros y S2. apply ty_mutind.
  + (* case ty_var *)
    introv Bix WfT Eq Ok Se Biy StS. subst.
    simpl. rewrite if_hoist.
    lets Bix': (subst_narrow_binds_end Ok Se Biy StS Bix).
    destruct Bix' as [T' [Bix' St]].
    refine (ty_sbsm _ St).
    apply (ty_var Bix'). eauto.
  + (* case ty_call *)
    introv Tyt IH1 THas Tyu IH2. introv WfV Eq Ok Se Biy StS.
    lets P: ((proj1 (subst_narrow_has_hasnt_end y S2)) _ _ _ THas _ _ _ _ Eq Ok Se Biy StS).
    destruct P as [D1 [THas' Sd]]. simpl in Sd. apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [U' [V' [? [StU StV]]]]. subst. simpl.
    refine (ty_sbsm _ StV).
    apply ty_call with (subst_typ x y T) U'; eauto.
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU. introv Eq Ok Se Biy StS. subst.
    destruct (env_case G2) as [Eq1 | [x' [S2' Eq1]]].
    - subst. rewrite concat_empty_r in Eq. subst.
      (* IH is useless!! *)
Abort.
 (*
 subst.
    apply_fresh ty_new as x'; fold subst_defs subst_trm.
    - assert (x'L: x' \notin L) by auto. clear IH2.
      specialize (IH1 _ x'L G1 (G2 & x' ~ open_typ x' T) x).
      repeat rewrite concat_assoc in IH1.
      assert (Ok': ok (G1 & x ~ S & G2 & x' ~ open_typ x' T)) by auto.
      specialize (IH1 eq_refl Ok').
      assert (Eqz: subst_fvar x y x' = x') by (unfold subst_fvar; case_var* ).
      unfold subst_ctx in IH1. rewrite map_push in IH1.
      lets P: (@subst_open_commute_typ x y x' T). rewrite Eqz in P.
      rewrite P in IH1. clear P.
      lets P: (@subst_open_commute_defs x y x' ds). rewrite Eqz in P.
      rewrite P in IH1. clear P.
      apply IH1. apply (binds_push_neq _ Biy). auto.
    - assert (x'L: x' \notin L) by auto. clear IH1.
      specialize (IH2 _ x'L G1 (G2 & x' ~ open_typ x' T) x).
      repeat rewrite concat_assoc in IH2.
      assert (Ok': ok (G1 & x ~ S & G2 & x' ~ open_typ x' T)) by auto.
      specialize (IH2 eq_refl Ok').
      assert (Eqz: subst_fvar x y x' = x') by (unfold subst_fvar; case_var* ).
      unfold subst_ctx in IH2. rewrite map_push in IH2.
      lets P: (@subst_open_commute_typ x y x' T). rewrite Eqz in P.
      rewrite P in IH2. clear P.
      lets P: (@subst_open_commute_trm x y x' u). rewrite Eqz in P.
      rewrite P in IH2. clear P.
      apply IH2. apply (binds_push_neq _ Biy). auto.
    - apply (subst_wf_typ WfU Ok Biy).
  + (* case ty_hyp *)
    introv WfT Ty IH Eq Ok Biy. subst.
    apply ty_hyp; eauto.
    introv Gb.
    refine (IH _ _ _ _ eq_refl Ok Biy).
    apply (undo_subst_good_bounds Ok Biy Gb).
  + (* case ty_sbsm *)
    introv Ty IH St Eq Ok Biy. subst.
    lets St': (subst_subtyp St Ok Biy). apply ty_sbsm with (subst_typ x y T1); eauto.
  + (* case ty_tdef *)
    introv St Eq Ok Biy. subst.
    lets St': (subst_subtyp St Ok Biy).
    apply ty_tdef; eauto.
  + (* case ty_mdef *)
    introv WfT WfU2 Tyu IH Eq Ok Biy. subst.
    apply_fresh ty_mdef as x'.
    - eauto.
    - eauto.
    - fold subst_trm.
      assert (x'L: x' \notin L) by auto.
      specialize (IH x' x'L G1 (G2 & x' ~ T) x).
      repeat rewrite concat_assoc in IH.
      assert (Ok': ok (G1 & x ~ S & G2 & x' ~ T)) by auto.
      specialize (IH eq_refl Ok').
      assert (Eqz: subst_fvar x y x' = x') by (unfold subst_fvar; case_var* ).
      unfold subst_ctx in IH. rewrite map_push in IH.
      lets P: (@subst_open_commute_trm x y x' u). rewrite Eqz in P.
      rewrite P in IH. clear P.
      apply IH. apply (binds_push_neq _ Biy). auto.
  + (* case ty_defs_nil *)
    eauto.
  + (* case ty_defs_cons *)
    intros. subst.
    lets Hasnt: (subst_defs_hasnt x y d0).
    rewrite (subst_label_of_def x y d) in Hasnt.
    apply ty_defs_cons; fold subst_defs subst_def; eauto.
*)
Qed.

Lemma subst_ty: forall y S,
   (forall G t T, ty_trm G t T -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    ty_trm (subst_ctx x y (G1 & G2)) (subst_trm x y t) (subst_typ x y T))
/\ (forall G t T, ty_imp G t T -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    ty_imp (subst_ctx x y (G1 & G2)) (subst_trm x y t) (subst_typ x y T))
/\ (forall G d D, ty_def G d D -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    ty_def (subst_ctx x y (G1 & G2)) (subst_def x y d) (subst_dec x y D))
/\ (forall G ds T, ty_defs G ds T -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    ty_defs (subst_ctx x y (G1 & G2)) (subst_defs x y ds) (subst_typ x y T)).
Proof.
  intros y S. apply ty_mutind.
  + (* case ty_var *)
    introv Bix WfT Eq Ok Biy. subst.
    lets Bix': (subst_binds Bix Ok Biy).
    simpl. rewrite if_hoist.
    apply (ty_var Bix'). eauto.
  + (* case ty_call *)
    introv Tyt IH1 THas Tyu IH2 WfV Eq Ok Biy. subst.
    lets THas': (subst_has THas Ok Biy).
    apply ty_call with (subst_typ x y T) (subst_typ x y U); eauto.
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Eq Ok Biy. subst.
    apply_fresh ty_new as x'; fold subst_defs subst_trm.
    - assert (x'L: x' \notin L) by auto. clear IH2.
      specialize (IH1 _ x'L G1 (G2 & x' ~ open_typ x' T) x).
      repeat rewrite concat_assoc in IH1.
      assert (Ok': ok (G1 & x ~ S & G2 & x' ~ open_typ x' T)) by auto.
      specialize (IH1 eq_refl Ok').
      assert (Eqz: subst_fvar x y x' = x') by (unfold subst_fvar; case_var* ).
      unfold subst_ctx in IH1. rewrite map_push in IH1.
      lets P: (@subst_open_commute_typ x y x' T). rewrite Eqz in P.
      rewrite P in IH1. clear P.
      lets P: (@subst_open_commute_defs x y x' ds). rewrite Eqz in P.
      rewrite P in IH1. clear P.
      apply IH1. apply (binds_push_neq _ Biy). auto.
    - assert (x'L: x' \notin L) by auto. clear IH1.
      specialize (IH2 _ x'L G1 (G2 & x' ~ open_typ x' T) x).
      repeat rewrite concat_assoc in IH2.
      assert (Ok': ok (G1 & x ~ S & G2 & x' ~ open_typ x' T)) by auto.
      specialize (IH2 eq_refl Ok').
      assert (Eqz: subst_fvar x y x' = x') by (unfold subst_fvar; case_var* ).
      unfold subst_ctx in IH2. rewrite map_push in IH2.
      lets P: (@subst_open_commute_typ x y x' T). rewrite Eqz in P.
      rewrite P in IH2. clear P.
      lets P: (@subst_open_commute_trm x y x' u). rewrite Eqz in P.
      rewrite P in IH2. clear P.
      apply IH2. apply (binds_push_neq _ Biy). auto.
    - apply (subst_wf_typ WfU Ok Biy).
  + (* case ty_hyp *)
    introv WfT Ty IH Eq Ok Biy. subst.
    apply ty_hyp; eauto.
    introv Gb.
    refine (IH _ _ _ _ eq_refl Ok Biy).
    apply (undo_subst_good_bounds Ok Biy Gb).
  + (* case ty_sbsm *)
    introv Ty IH St Eq Ok Biy. subst.
    lets St': (subst_subtyp St Ok Biy). apply ty_sbsm with (subst_typ x y T1); eauto.
  + (* case ty_tdef *)
    introv St Eq Ok Biy. subst.
    lets St': (subst_subtyp St Ok Biy).
    apply ty_tdef; eauto.
  + (* case ty_mdef *)
    introv WfT WfU2 Tyu IH Eq Ok Biy. subst.
    apply_fresh ty_mdef as x'.
    - eauto.
    - eauto.
    - fold subst_trm.
      assert (x'L: x' \notin L) by auto.
      specialize (IH x' x'L G1 (G2 & x' ~ T) x).
      repeat rewrite concat_assoc in IH.
      assert (Ok': ok (G1 & x ~ S & G2 & x' ~ T)) by auto.
      specialize (IH eq_refl Ok').
      assert (Eqz: subst_fvar x y x' = x') by (unfold subst_fvar; case_var* ).
      unfold subst_ctx in IH. rewrite map_push in IH.
      lets P: (@subst_open_commute_trm x y x' u). rewrite Eqz in P.
      rewrite P in IH. clear P.
      apply IH. apply (binds_push_neq _ Biy). auto.
  + (* case ty_defs_nil *)
    eauto.
  + (* case ty_defs_cons *)
    intros. subst.
    lets Hasnt: (subst_defs_hasnt x y d0).
    rewrite (subst_label_of_def x y d) in Hasnt.
    apply ty_defs_cons; fold subst_defs subst_def; eauto.
Qed.
*)

Lemma trm_subst_principle: forall G x y t S T,
  ty_trm (G & x ~ S) t T ->
  ok (G & x ~ S) ->
  binds y (subst_typ x y S) G ->
  ty_trm (subst_ctx x y G) (subst_trm x y t) (subst_typ x y T).
Proof.
Admitted. (*
  introv Ty Ok Biy.
  destruct (subst_ty y S) as [P _].
  specialize (P _ _ _ Ty G empty x). repeat rewrite concat_empty_r in P.
  apply (P eq_refl Ok Biy).
Qed.*)

Lemma trm_subst_principle_imp: forall G x y t S T,
  ty_trm (G & x ~ S) t T ->
  ok (G & x ~ S) ->
  binds y (subst_typ x y S) G ->
  ty_trm (subst_ctx x y G) (subst_trm x y t) (subst_typ x y T).
Proof.
Admitted. (*
  introv Ty Ok Biy.
  destruct (subst_ty y S) as [_ [P _]].
  specialize (P _ _ _ Ty G empty x). repeat rewrite concat_empty_r in P.
  apply (P eq_refl Ok Biy).
Qed.
*)

Lemma defs_subst_principle: forall G x y ds S T,
  ty_defs (G & x ~ S) ds T ->
  ok (G & x ~ S) ->
  binds y (subst_typ x y S) G ->
  ty_defs (subst_ctx x y G) (subst_defs x y ds) (subst_typ x y T).
Proof.
Admitted. (*
  introv Ty Ok Biy.
  destruct (subst_ty y S) as [_ [_ [_ P]]].
  specialize (P _ _ _ Ty G empty x). repeat rewrite concat_empty_r in P.
  apply (P eq_refl Ok Biy).
Qed.
*)

(* ###################################################################### *)
(** ** Narrowing *)

Lemma narrow_binds_raw: forall G1 x0 S1 S2 G2 x T2,
  binds x T2 (G1 & x0 ~ S2 & G2) ->
  subtyp (G1 & x0 ~ S1 & G2) S1 S2 ->
  binds x T2 (G1 & x0 ~ S1 & G2) \/ x0 = x /\ T2 = S2 /\ binds x S1 (G1 & x ~ S1 & G2).
Proof.
  introv Bi StS.
  apply binds_middle_inv in Bi.
  destruct Bi as [Bi | [[xG2 [Eq1 Eq2]]|[xG2 [Ne Bi]]]].
  - (* case x in G2 *)
    apply (binds_concat_right (G1 & x0 ~ S1)) in Bi.
    auto.
  - (* case x = x0 *)
    auto.
  - (* case x in G1 *)
    auto.
Qed.

(*
Lemma narrow_binds_old: forall G1 x0 S1 S2 G2 x T2,
  wf_ctx (G1 & x0 ~ S1 & G2) ->
  binds x T2 (G1 & x0 ~ S2 & G2) ->
  subtyp (G1 & x0 ~ S1 & G2) S1 S2 ->
  exists T1,
    binds x T1 (G1 & x0 ~ S1 & G2) /\
    subtyp (G1 & x0 ~ S1 & G2) T1 T2.
Proof.
  introv Wf Bi StS. destruct Wf as [Ok Wf].
  apply binds_middle_inv in Bi.
  destruct Bi as [Bi | [[xG2 [Eq1 Eq2]]|[xG2 [Ne Bi]]]].
  - (* case x in G2 *)
    apply (binds_concat_right (G1 & x0 ~ S1)) in Bi.
    exists T2.
    specialize (Wf _ _ Bi). auto.
  - (* case x = x0 *)
    subst x0 T2. exists S1.
    apply (conj (binds_middle_eq _ _ xG2)).
    apply StS.
  - (* case x in G1 *)
    assert (xx0: x # (x0 ~ S1)) by auto.
    lets Bi': (binds_concat_left (binds_concat_left Bi xx0) xG2).
    exists T2. apply (conj Bi').
    apply subtyp_refl. apply (Wf _ _ Bi').
Qed.
*)

Lemma narrow_binds: forall G1 x0 S1 S2 G2 x T2,
  wf_typ (G1 & x0 ~ S1 & G2) T2 ->
  binds x T2 (G1 & x0 ~ S2 & G2) ->
  subtyp (G1 & x0 ~ S1 & G2) S1 S2 ->
  exists T1,
    binds x T1 (G1 & x0 ~ S1 & G2) /\
    subtyp (G1 & x0 ~ S1 & G2) T1 T2.
Proof.
  introv Wf Bi StS.
  apply binds_middle_inv in Bi.
  destruct Bi as [Bi | [[xG2 [Eq1 Eq2]]|[xG2 [Ne Bi]]]].
  - (* case x in G2 *)
    apply (binds_concat_right (G1 & x0 ~ S1)) in Bi.
    exists T2. auto.
  - (* case x = x0 *)
    subst x0 T2. exists S1.
    apply (conj (binds_middle_eq _ _ xG2)).
    apply StS.
  - (* case x in G1 *)
    assert (xx0: x # (x0 ~ S1)) by auto.
    lets Bi': (binds_concat_left (binds_concat_left Bi xx0) xG2).
    exists T2. apply (conj Bi'). auto.
Qed.

Print Assumptions narrow_binds.

Lemma narrow_binds_end: forall G1 x0 S1 S2 x T2,
  wf_typ (G1 & x0 ~ S1) T2 ->
  binds x T2 (G1 & x0 ~ S2) ->
  subtyp (G1 & x0 ~ S1) S1 S2 ->
  exists T1,
    binds x T1 (G1 & x0 ~ S1) /\
    subtyp (G1 & x0 ~ S1) T1 T2.
Proof.
  introv Wf Bi StS.
  rewrite <- (concat_empty_r (G1 & x0 ~ S1)).
  rewrite <- (concat_empty_r (G1 & x0 ~ S1)) in Wf, StS.
  rewrite <- (concat_empty_r (G1 & x0 ~ S2)) in Bi.
  apply* narrow_binds.
Qed.

Lemma narrow_binds_2: forall G1 x0 S1 S2 G2 x T1 T2,
  wf_typ (G1 & x0 ~ S1 & G2) T1 ->
  binds x T2 (G1 & x0 ~ S2 & G2) ->
  binds x T1 (G1 & x0 ~ S1 & G2) ->
  subtyp (G1 & x0 ~ S1 & G2) S1 S2 ->
  subtyp (G1 & x0 ~ S1 & G2) T1 T2.
Proof.
  introv Wf Bi2 Bi1 StS.
  apply binds_middle_inv in Bi2.
  destruct Bi2 as [Bi2 | [[xG2 [Eq1 Eq2]]|[xG2 [Ne Bi2]]]].
  - (* case x in G2 *)
    lets Bi1': (binds_concat_right (G1 & x0 ~ S1) Bi2).
    lets Eq: (binds_func Bi1' Bi1). subst T2.
    auto.
  - (* case x = x0 *)
    subst x0 T2.
    lets Bi1': (binds_concat_left_inv Bi1 xG2).
    lets Eq: (binds_push_eq_inv Bi1'). subst T1.
    exact StS.
  - (* case x in G1 *)
    assert (xx0: x # (x0 ~ S1)) by auto.
    lets Bi1': (binds_concat_left (binds_concat_left Bi2 xx0) xG2).
    lets Eq: (binds_func Bi1' Bi1). subst T2.
    auto.
Qed.

(*
Lemma subdec2_to_label_of_dec_eq: forall G D1 D2, 
  subdec G D1 D2 \/ D1 = D2 -> label_of_dec D1 = label_of_dec D2.
Proof.
  introv Sd. destruct Sd as [Sd | Eq].
  - apply (subdec_to_label_of_dec_eq Sd).
  - subst. reflexivity.
Qed.
*)

Lemma narrow_has_stable:
   (forall G T D, typ_has G T D -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ T ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    typ_has (G1 & x ~ S1 & G2) T D)
/\ (forall G T l, typ_hasnt G T l -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ T ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    typ_hasnt (G1 & x ~ S1 & G2) T l).
Proof.
  apply typ_has_mutind; intros; subst;
  match goal with
  | H: stable_typ _ |- _ => inversions H
  end;
  eauto.
Qed.

Lemma narrow_has:
   (forall G T D2, typ_has G T D2 -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    wf_typ (G1 & x ~ S1 & G2) T ->  (* <-- S1! *)
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    exists D1,
      typ_has (G1 & x ~ S1 & G2) T D1 /\
      subdec (G1 & x ~ S1 & G2) D1 D2)
/\ (forall G T l, typ_hasnt G T l -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    wf_typ (G1 & x ~ S1 & G2) T ->  (* <-- S1! *)
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    typ_hasnt (G1 & x ~ S1 & G2) T l 
    \/ exists D, label_of_dec D = l /\ typ_has (G1 & x ~ S1 & G2) T D).
Proof.
  apply typ_has_mutind.
  + (* case typ_bot_has *)
    intros. exists (dec_bot l). split; [eauto | destruct l; simpl; eauto].
  + (* case typ_rcd_has *)
    intros. subst. apply invert_wf_rcd in H0. exists D. eauto.
  + (* case typ_sel_has *)
    intros G x X2 L Lo2 Hi2 D2 Bix2 _ IH1 _ IH2 G1 x0 S1 S2 G2 Eq Wf St. subst.
    apply invert_wf_sel in Wf. destruct Wf as [X1 [T [U [Bix1 [X1Has [WfX1 [WfT WfU]]]]]]].
    lets StX: (narrow_binds_2 WfX1 Bix2 Bix1 St).
    lets WfX2: (proj2 (subtyp_regular StX)).
    specialize (IH1 _ _ _ _ _ eq_refl WfX2 St). destruct IH1 as [D0 [X2Has Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo1 [Hi1 [Eq [StLo12 StHi12]]]]. subst D0.
    lets WfHi2: (proj2 (subtyp_regular StHi12)).
    specialize (IH2 _ _ _ _ _ eq_refl WfHi2 St). destruct IH2 as [D1 [Hi2Has Sd12]].
    lets P: (swap_sub_and_typ_has StX X2Has).
            (********************)
    destruct P as [D0 [X1Has' Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo0 [Hi0 [Eq [StLo01 StHi01]]]]. subst D0.
    lets StLo: (subtyp_trans StLo12 StLo01).
    lets StHi: (subtyp_trans StHi01 StHi12).
    lets P: (swap_sub_and_typ_has StHi Hi2Has).
            (********************)
    destruct P as [D0 [Hi0Has Sd01]].
    exists D0. split.
    - apply (typ_sel_has Bix1 X1Has' Hi0Has).
    - apply (subdec_trans Sd01 Sd12).
  + (* case typ_and_has_1 *)
    introv _ IH1 _ IH2 Eq Wf St. subst. rename D into D1.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH1 as [D1' [T1Has Sd1]].
    lets Eql1: (subdec_to_label_of_dec_eq Sd1).
    destruct IH2 as [T2Hasnt | [D2 [Eql2 T2Has]]].
    - exists D1'.
      rewrite <- Eql1 in T2Hasnt.
      split.
      * apply (typ_and_has_1 T1Has T2Hasnt).
      * exact Sd1.
    - rewrite <- Eql2 in Eql1. destruct (intersect_dec_total _ _ Eql1) as [D12 Eq].
      exists D12. split.
      * apply (typ_and_has_12 T1Has T2Has Eq).
      * refine (subdec_trans _ Sd1).
        lets WfD1: (typ_has_preserves_wf T1Has Wf1).
        lets WfD2: (typ_has_preserves_wf T2Has Wf2).
                   (********************)
        apply (subdec_intersect_l Eq WfD1 WfD2).
  + (* case typ_and_has_2 *)
    introv _ IH1 _ IH2 Eq Wf St. subst. rename D into D1.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH2 as [D2 [T2Has Sd2]].
    lets Eql1: (subdec_to_label_of_dec_eq Sd2).
    destruct IH1 as [T1Hasnt | [D1' [Eql2 T1Has]]].
    - exists D2.
      rewrite <- Eql1 in T1Hasnt.
      split.
      * apply (typ_and_has_2 T1Hasnt T2Has).
      * exact Sd2.
    - rewrite <- Eql2 in Eql1.
      symmetry in Eql1. destruct (intersect_dec_total _ _ Eql1) as [D12 Eq].
      exists D12. split.
      * apply (typ_and_has_12 T1Has T2Has Eq).
      * refine (subdec_trans _ Sd2).
        lets WfD1: (typ_has_preserves_wf T1Has Wf1).
        lets WfD2: (typ_has_preserves_wf T2Has Wf2).
                   (********************)
        apply (subdec_intersect_r Eq WfD1 WfD2).
  + (* case typ_and_has_12 *)
    introv _ IH1 _ IH2 Eq Eq2 Wf St. subst.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH1 as [D1' [T1Has Sd1]].
    destruct IH2 as [D2' [T2Has Sd2]].
    lets Eql1: (subdec_to_label_of_dec_eq Sd1).
    lets Eql2: (subdec_to_label_of_dec_eq Sd2).
    destruct (intersect_dec_label_eq _ _ Eq) as [Eql12 [Eql13 Eql23]].
    rewrite Eql12 in Eql1. rewrite <- Eql2 in Eql1.
    destruct (intersect_dec_total _ _ Eql1) as [D12' Eq'].
    exists D12'. split.
    - apply (typ_and_has_12 T1Has T2Has Eq').
    - lets WfD1': (proj1 (subdec_regular Sd1)).
      lets WfD2': (proj1 (subdec_regular Sd2)).
      refine (subdec_intersect _ _ Eq).
      * refine (subdec_trans _ Sd1). apply (subdec_intersect_l Eq' WfD1' WfD2').
      * refine (subdec_trans _ Sd2). apply (subdec_intersect_r Eq' WfD1' WfD2').
  + (* case typ_or_has *)
    introv _ IH1 _ IH2 Eq Eq2 Wf St. subst.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH1 as [D1' [T1Has Sd1]].
    destruct IH2 as [D2' [T2Has Sd2]].
    lets Eql1: (subdec_to_label_of_dec_eq Sd1).
    lets Eql2: (subdec_to_label_of_dec_eq Sd2).
    destruct (union_dec_label_eq _ _ Eq) as [Eql12 [Eql13 Eql23]].
    rewrite Eql12 in Eql1. rewrite <- Eql2 in Eql1.
    destruct (union_dec_total _ _ Eql1) as [D12' Eq'].
    exists D12'. split.
    - apply (typ_or_has T1Has T2Has Eq').
    - lets WfD1: (proj2 (subdec_regular Sd1)).
      lets WfD2: (proj2 (subdec_regular Sd2)).
      refine (subdec_union _ _ Eq').
      * refine (subdec_trans Sd1 _). apply (subdec_union_l Eq WfD1 WfD2).
      * refine (subdec_trans Sd2 _). apply (subdec_union_r Eq WfD1 WfD2).
  + (* case typ_top_hasnt *)
    eauto.
  + (* case typ_rcd_hasnt *)
    eauto.
  + (* case typ_sel_hasnt *)
    intros G x X2 L Lo2 Hi2 l Bix2 X2Has' IH1 Hi2Hasnt' IH2 G1 x0 S1 S2 G2 Eq Wf St.
    subst.
    apply invert_wf_sel in Wf. destruct Wf as [X1 [T [U [Bix1 [X1Has [WfX1 [WfT WfU]]]]]]].
    lets StX: (narrow_binds_2 WfX1 Bix2 Bix1 St).
    lets WfX2: (proj2 (subtyp_regular StX)).
    specialize (IH1 _ _ _ _ _ eq_refl WfX2 St). destruct IH1 as [D0 [X2Has Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo1 [Hi1 [Eq [StLo12 StHi12]]]]. subst D0.
    lets P: (swap_sub_and_typ_has StX X2Has).
            (********************)
    destruct P as [D0 [X1Has' Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo0 [Hi0 [Eq [StLo01 StHi01]]]]. subst D0.
    lets StLo: (subtyp_trans StLo12 StLo01).
    lets StHi: (subtyp_trans StHi01 StHi12).
    destruct (subtyp_regular StHi) as [WfHi0 _].
             (**************)
    lets P: (typ_has_total WfHi0 l). destruct P as [Hasnt | Has].
    - left. apply (typ_sel_hasnt Bix1 X1Has' Hasnt).
    - right. destruct Has as [D [Eq Has]]. exists D. eauto.
  + (* case typ_and_hasnt *)
    introv _ IH1 _ IH2 Eq Wf St. subst G.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH1 as [T1Hasnt | [D1 [Eq1 T1Has]]];
    destruct IH2 as [T2Hasnt | [D2 [Eq2 T2Has]]]; subst.
    - eauto.
    - right. exists D2. apply (conj eq_refl). apply (typ_and_has_2 T1Hasnt T2Has).
    - right. exists D1. apply (conj eq_refl). apply (typ_and_has_1 T1Has T2Hasnt).
    - right. symmetry in Eq2. destruct (intersect_dec_total _ _ Eq2) as [D12 Eq].
      exists D12. split.
      * destruct (intersect_dec_label_eq _ _ Eq) as [Eq12 [Eq112 Eq212]].
        symmetry. assumption.
      * apply (typ_and_has_12 T1Has T2Has Eq).
  + (* case typ_or_hasnt_1 *)
    introv Hasnt1 IH1 Has2 IH2 Eq Wf St. subst.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH2 as [D2 [T2Has Sd]].
    lets Eq: (subdec_to_label_of_dec_eq Sd).
    destruct IH1 as [T1Hasnt | [D1 [Eq1 T1Has]]].
    - left.
      rewrite <- Eq. refine (typ_or_hasnt_1 _ T2Has).
      rewrite Eq. apply T1Hasnt.
    - right. rewrite <- Eq in Eq1. destruct (union_dec_total _ _ Eq1) as [D12 EqD].
      exists D12. destruct (union_dec_label_eq _ _ EqD) as [Eql1 [Eql2 Eql3]].
      split.
      * rewrite <- Eql3. apply Eq.
      * apply (typ_or_has T1Has T2Has EqD).
  + (* case typ_or_hasnt_2 *)
    introv Has1 IH1 Hasnt2 IH2 Eq Wf St. subst.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH1 as [D1 [T1Has Sd]].
    lets Eq: (subdec_to_label_of_dec_eq Sd).
    destruct IH2 as [T2Hasnt | [D2 [Eq2 T2Has]]].
    - left.
      rewrite <- Eq. refine (typ_or_hasnt_2 T1Has _).
      rewrite Eq. apply T2Hasnt.
    - right. rewrite <- Eq2 in Eq. destruct (union_dec_total _ _ Eq) as [D12 EqD].
      exists D12. destruct (union_dec_label_eq _ _ EqD) as [Eql1 [Eql2 Eql3]].
      split.
      * rewrite <- Eql2. rewrite Eq. apply Eq2.
      * apply (typ_or_has T1Has T2Has EqD).
  + (* case typ_or_hasnt_12 *)
    introv _ IH1 _ IH2 Eq Wf St. subst.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Wf2 St).
    destruct IH1 as [T1Hasnt | [D1 [Eq1 T1Has]]];
    destruct IH2 as [T2Hasnt | [D2 [Eq2 T2Has]]].
    - eauto.
    - rewrite <- Eq2 in *. eauto.
    - rewrite <- Eq1 in *. eauto.
    - right. rewrite <- Eq2 in Eq1. destruct (union_dec_total _ _ Eq1) as [D12 EqD].
      exists D12. destruct (union_dec_label_eq _ _ EqD) as [Eql1 [Eql2 Eql3]].
      split.
      * rewrite <- Eql2. rewrite Eq1. apply Eq2.
      * apply (typ_or_has T1Has T2Has EqD).
Qed.

Print Assumptions narrow_has.

Lemma narrow_has_middle: forall G1 x S1 S2 G2 T D2,
  typ_has (G1 & x ~ S2 & G2) T D2 ->
  wf_typ  (G1 & x ~ S1 & G2) T ->  (* <-- quite strong *)
  subtyp  (G1 & x ~ S1 & G2) S1 S2 ->
  exists D1,
    typ_has (G1 & x ~ S1 & G2) T D1 /\
    subdec  (G1 & x ~ S1 & G2) D1 D2.
Proof.
  introv Has Wf St. apply* narrow_has.
Qed.

Lemma narrow_has_end: forall G1 x S1 S2 T D2,
  typ_has (G1 & x ~ S2) T D2 ->
  wf_typ  (G1 & x ~ S1) T ->  (* <-- quite strong *)
  subtyp  (G1 & x ~ S1) S1 S2 ->
  exists D1,
    typ_has (G1 & x ~ S1) T D1 /\
    subdec  (G1 & x ~ S1) D1 D2.
Proof.
  introv Has Wf St.
  rewrite <- (concat_empty_r (G1 & x ~ S2)) in Has.
  rewrite <- (concat_empty_r (G1 & x ~ S1)) in St, Wf.
  rewrite <- (concat_empty_r (G1 & x ~ S1)).
  apply* narrow_has_middle.
Qed.

Inductive valid_history: ctx -> fset typ -> Prop :=
| vh_empty: forall G, 
    valid_history G \{}
| vh_push: forall G A D,
    valid_history G A ->
    wf_typ_impl G A (typ_rcd D) ->
    valid_history G (A \u \{ typ_rcd D }).

Lemma invert_valid_history: forall G A T,
  valid_history G A ->
  T \in A ->
  wf_typ_impl G (A \- \{ T}) T.
Proof.
  introv Vh. induction Vh; intro In.
  - exfalso. apply (in_empty_elim In).
  - rename H into WfD.
    rewrite in_union in In. rewrite in_singleton in In. destruct In as [In | Eq].
    * specialize (IHVh In).
      rewrite union_remove. apply (add_hyps_to_wf_typ _ IHVh).
    * subst. rewrite union_remove. rewrite singleton_remove. rewrite union_empty_r.
      inversions WfD.
      { apply (IHVh H). }
      { apply wf_rcd. apply (add_hyps_to_wf_dec \{ typ_rcd D }).
        apply (remove_own_hyp_from_wf_dec H2). }
Qed.

Lemma shrink_wf_typ_history: forall G A T,
  wf_typ_impl G A T ->
  valid_history G A ->
  forall U, U \in A -> wf_typ_impl G (A \- \{ U }) T.
Proof.
  introv WfT Vh In.
  lets WfU: (invert_valid_history Vh In).
  lets WfT': ((proj1 (remove_hyp_from_wf WfU)) _ _ _ WfT eq_refl).
  rewrite <- union_remove in WfT'.
  rewrite union_same in WfT'.
  exact WfT'.
Qed.

Lemma remove_valid_history: forall G A T,
  wf_typ_impl G A T ->
  valid_history G A ->
  wf_typ G T.
Proof.
  introv Wf Vh. gen T. induction Vh.
  - intros. auto.
  - rename H into WfD.
    introv WfT. apply IHVh.
    destruct (classicT ((typ_rcd D) \in A)) as [In | Ni].
    * assert (Eq: (A \u \{ typ_rcd D}) = A). {
        apply fset_extens; unfold subset; intros.
        - rewrite in_union, in_singleton in H. destruct H; subst; auto.
        - rewrite in_union. auto.
      }
      rewrite Eq in WfT. exact WfT.
    * assert (Eq: A = (A \u \{ typ_rcd D}) \- \{ typ_rcd D }). {
        rewrite union_remove. rewrite singleton_remove. rewrite union_empty_r.
        rewrite (remove_notin Ni). reflexivity.
      }
      rewrite Eq.
      refine (shrink_wf_typ_history WfT _ _).
      + apply (vh_push Vh WfD).
      + rewrite in_union, in_singleton. auto.
Qed.

Print Assumptions remove_valid_history.

Lemma narrow_wf:
   (forall G A T, wf_typ_impl G A T -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ S1 ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    wf_typ_impl (G1 & x ~ S1 & G2) A T)
/\ (forall G A D, wf_dec_impl G A D -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ S1 ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    wf_dec_impl (G1 & x ~ S1 & G2) A D).
Proof.
  apply wf_mutind.
  + (* case wf_top *) eauto.
  + (* case wf_bot *) eauto.
  + (* case wf_hyp *) eauto.
  + (* case wf_rcd *) eauto.
  + (* case wf_sel *)
    introv Bix SbX XHas WfX IHX WfT IHT WfU IHU. introv Eq SbS1 St. subst.
    lets XHas': ((proj1 narrow_has_stable) _ _ _ XHas _ _ _ _ _ eq_refl SbX St).
    specialize (IHX _ _ _ _ _ eq_refl SbS1 St).
    specialize (IHT _ _ _ _ _ eq_refl SbS1 St).
    specialize (IHU _ _ _ _ _ eq_refl SbS1 St).
    destruct (narrow_binds_raw Bix St) as [Bix' | [Eq1 [Eq2 Bix']]].
    - (* case "type of x remained unchanged" *)
      apply (wf_sel Bix' SbX XHas' IHX IHT IHU).
    - (* case "x = x0, so type of x changed from S2 to S1" *)
      subst.
      lets P: (swap_sub_and_typ_has St XHas'). destruct P as [D1 [S1Has Sd]].
              (********************)
      apply invert_subdec_typ_sync_left in Sd. destruct Sd as [T' [U' [Eq [StT2 StU2]]]].
      subst D1.
      apply (wf_sel Bix' SbS1 S1Has);
      rewrite <- (union_empty_l A); apply add_hyps_to_wf_typ.
      * apply (proj1 (subtyp_regular St)).
      * apply (proj2 (subtyp_regular StT2)).
      * apply (proj1 (subtyp_regular StU2)).
  + (* case wf_and  *) eauto.
  + (* case wf_or   *) eauto.
  + (* case wf_tmem *) eauto.
  + (* case wf_mtd  *) eauto.
Qed.

Print Assumptions narrow_wf.

Lemma narrow_wf_typ_middle: forall G1 x S1 S2 G2 T,
  wf_typ (G1 & x ~ S2 & G2) T ->
  stable_typ S1 ->
  subtyp (G1 & x ~ S1 & G2) S1 S2 ->
  wf_typ (G1 & x ~ S1 & G2) T.
Proof.
  introv WfT St. apply* narrow_wf.
Qed.

Lemma narrow_wf_typ_end: forall G1 x S1 S2 T,
  wf_typ (G1 & x ~ S2) T ->
  stable_typ S1 ->
  subtyp (G1 & x ~ S1) S1 S2 ->
  wf_typ (G1 & x ~ S1) T.
Proof.
  introv WfT Sb St.
  rewrite <- (concat_empty_r (G1 & x ~ S2)) in WfT.
  rewrite <- (concat_empty_r (G1 & x ~ S1)) in St.
  rewrite <- (concat_empty_r (G1 & x ~ S1)).
  apply* narrow_wf.
Qed.

Lemma narrow_wf_dec_middle: forall G1 x S1 S2 G2 D,
  wf_dec (G1 & x ~ S2 & G2) D ->
  stable_typ S1 ->
  subtyp (G1 & x ~ S1 & G2) S1 S2 ->
  wf_dec (G1 & x ~ S1 & G2) D.
Proof.
  introv WfT St. apply* narrow_wf.
Qed.

Lemma good_bounds_to_old: forall G,
  good_bounds G ->
  good_bounds_old G.
Proof.
  introv Gb. unfold good_bounds_old. induction Gb; introv Bi.
  - exfalso. apply (binds_empty_inv Bi).
  - apply binds_push_inv in Bi. destruct Bi as [[Eq1 Eq2] | [Ne Bi]].
    * subst. exact H.
    * apply (weaken_good_bounds_typ_end (okadmit _)). apply (IHGb _ _ Bi).
Qed.

Lemma narrow_subtyp_subdec:
   (forall G T1 T2, subtyp G T1 T2 -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S1 & G2) ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    subtyp (G1 & x ~ S1 & G2) T1 T2)
/\ (forall G D1 D2, subdec G D1 D2 -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S1 & G2) ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    subdec (G1 & x ~ S1 & G2) D1 D2).
Proof.
  apply subtyp_mutind.
  + (* case subtyp_refl *)
    intros. subst. apply subtyp_refl. apply* narrow_wf.
  + (* case subtyp_top *)
    intros. subst. apply subtyp_top. apply* narrow_wf.
  + (* case subtyp_bot *)
    intros. subst. apply subtyp_bot. apply* narrow_wf.
  + (* case subtyp_rcd *)
    eauto.
  + (* case subtyp_sel_l *)
    introv Bi2 WfX SbX XHas St IHSt Eq SbS1 Gb StS. subst.
    lets WfX': (narrow_wf_typ_middle WfX SbS1 StS).
    specialize (IHSt _ _ _ _ _ eq_refl SbS1 Gb StS).
    lets XHas': ((proj1 narrow_has_stable) _ _ _ XHas _ _ _ _ _ eq_refl SbX StS).
    lets P: (narrow_binds_raw Bi2 StS). destruct P as [Bi1 | [Eq1 [Eq2 Bi1]]].
    - apply (subtyp_sel_l Bi1 WfX' SbX XHas' IHSt).
    - subst.
      lets P: (swap_sub_and_typ_has StS XHas'). destruct P as [D [S1Has Sd]].
      apply invert_subdec_typ_sync_left in Sd. destruct Sd as [T' [U' [Eq [StT StU]]]].
      subst D.
      refine (subtyp_trans _ StU).
      apply (subtyp_sel_l Bi1 (proj1 (subtyp_regular StS)) SbS1 S1Has).
      apply good_bounds_to_old in Gb.
      unfold good_bounds_old, good_bounds_typ in Gb.
      specialize (Gb _ _ Bi1). destruct Gb as [_ Gb]. apply (Gb _ _ _ S1Has).
  + (* case subtyp_sel_r *)
    introv Bi2 WfX SbX XHas St IHSt Eq SbS1 Gb StS. subst.
    lets WfX': (narrow_wf_typ_middle WfX SbS1 StS).
    specialize (IHSt _ _ _ _ _ eq_refl SbS1 Gb StS).
    lets XHas': ((proj1 narrow_has_stable) _ _ _ XHas _ _ _ _ _ eq_refl SbX StS).
    lets P: (narrow_binds_raw Bi2 StS). destruct P as [Bi1 | [Eq1 [Eq2 Bi1]]].
    - apply (subtyp_sel_r Bi1 WfX' SbX XHas' IHSt).
    - subst.
      lets P: (swap_sub_and_typ_has StS XHas'). destruct P as [D [S1Has Sd]].
      apply invert_subdec_typ_sync_left in Sd. destruct Sd as [T' [U' [Eq [StT StU]]]].
      subst D.
      refine (subtyp_trans StT _).
      apply (subtyp_sel_r Bi1 (proj1 (subtyp_regular StS)) SbS1 S1Has).
      apply good_bounds_to_old in Gb.
      unfold good_bounds_old, good_bounds_typ in Gb.
      specialize (Gb _ _ Bi1). destruct Gb as [_ Gb]. apply (Gb _ _ _ S1Has).
  + (* case subtyp_and *) eauto.
  + (* case subtyp_and_l *)
    intros. subst. apply subtyp_and_l; apply* narrow_wf.
  + (* case subtyp_and_r *)
    intros. subst. apply subtyp_and_r; apply* narrow_wf.
  + (* case subtyp_or *) eauto.
  + (* case subtyp_or_l *)
    intros. subst. apply subtyp_or_l; apply* narrow_wf.
  + (* case subtyp_or_r *)
    intros. subst. apply subtyp_or_r; apply* narrow_wf.
  + (* case subtyp_trans *)
    intros. subst.
    specialize (H _ _ _ _ _ eq_refl H2 H3 H4).
    specialize (H0 _ _ _ _ _ eq_refl H2 H3 H4).
    apply subtyp_trans with T2; eauto.
  + (* case subdec_typ *) eauto.
  + (* case subdec_mtd *) eauto.
Qed.

Print Assumptions narrow_subtyp_subdec.

Lemma narrow_subtyp_middle: forall G1 x S1 S2 G2 T1 T2,
  subtyp (G1 & x ~ S2 & G2) T1 T2 ->
  stable_typ S1 ->
  good_bounds (G1 & x ~ S1 & G2) ->
  subtyp (G1 & x ~ S1 & G2) S1 S2 ->
  subtyp (G1 & x ~ S1 & G2) T1 T2.
Proof.
  introv St StS. apply* narrow_subtyp_subdec.
Qed.

Lemma narrow_subtyp_end: forall G x S1 S2 T1 T2,
  subtyp (G & x ~ S2) T1 T2 ->
  stable_typ S1 ->
  good_bounds (G & x ~ S1) ->
  subtyp (G & x ~ S1) S1 S2 ->
  subtyp (G & x ~ S1) T1 T2.
Proof.
  introv St StS. destruct narrow_subtyp_subdec as [P _].
  specialize (P _ _ _ St G x S1 S2 empty). repeat rewrite concat_empty_r in P. eauto.
Qed.

(* -------- *)

Inductive gb_dec: ctx -> dec -> Prop :=
| gb_dec_typ: forall G L Lo Hi,
    subtyp G Lo Hi ->
    gb_dec G (dec_typ L Lo Hi)
| gb_dec_mtd: forall G m U V,
    gb_dec G (dec_mtd m U V).

Hint Constructors gb_dec.

(* inverted bounds 
Inductive ib_dec: ctx -> dec -> Prop :=
| ib_dec_typ: forall G L Lo Hi,
    subtyp G Hi Lo ->
    ~ subtyp G Lo Hi ->
    ib_dec G (dec_typ L Lo Hi).

   Problem with "~ subtyp G Lo Hi" is that it means "cannot prove", not
   "really not subtyp", so it's not preserved by narrowing, because
   maybe before narrowing, a.T1 <: a.T2 cannot be proven, but after narrowing it can. *)

Lemma top_not_subtyp_of_bot: forall G,
  ~ subtyp G typ_top typ_bot.
Proof.
  unfold not. introv St. gen_eq T2: typ_bot. gen_eq T1: typ_top.
  induction St; intros Eq1 Eq2; subst; try discriminate.
  (* case subtyp_trans *)
  destruct T2 as [ | | D | a L | U V | U V ]; auto.
  + (* case rcd *)
    

  try solve [inversions St1];
  try solve [inversions St2].
Abort. (* see existential/nohas-lambdaDOT.v, existential/lamvdaDOT, this is very messy *)

Lemma narrow_gb_dec: forall G1 x S1 S2 G2 D,
  gb_dec (G1 & x ~ S2 & G2) D ->
  stable_typ S1 ->
  good_bounds (G1 & x ~ S1 & G2) ->
  subtyp (G1 & x ~ S1 & G2) S1 S2 ->
  gb_dec (G1 & x ~ S1 & G2) D.
Proof.
  introv GbD Sb Gb StS. inversions GbD; constructor.
  apply* narrow_subtyp_middle.
Qed.

Lemma var_has_to_gb: forall G T D x,
  good_bounds G ->
  binds x T G ->
  typ_has G T D ->
  gb_dec G D.
Proof.
  introv Gb Bi THas.
  destruct D as [L Lo Hi | m U V].
  - apply good_bounds_to_old in Gb. unfold good_bounds_old, good_bounds_typ in Gb.
    specialize (Gb _ _ Bi). destruct Gb as [_ Gb].
    specialize (Gb L Lo Hi THas).
    apply (gb_dec_typ _ Gb).
  - apply gb_dec_mtd.
Qed.

Lemma intersect_preserves_gb_dec: forall G D1 D2 D12,
  D1 && D2 == D12 ->
  gb_dec G D1 ->
  gb_dec G D2 ->
  gb_dec G D12.
Proof.
  introv Eq Gb1 Gb2. unfold intersect_dec in Eq. case_if.
  destruct D1 as [L S1 U1 | m S1 U1];
  destruct D2 as [L' S2 U2 | m' S2 U2]; try discriminate.
  - simpl in H. symmetry in H. inversions H. inversions Eq. apply gb_dec_typ.
    inversions Gb1. inversions Gb2.
    (* Does not hold, even if good_bounds G, because D1, D2 might not occur in G at all *)
Abort.

Lemma narrow_has_gb:
   (forall G T D2, typ_has G T D2 -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2 & G2) ->
    good_bounds (G1 & x ~ S1 & G2) ->
    gb_dec G D2 ->
    wf_typ (G1 & x ~ S1 & G2) T ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    exists D1,
      typ_has (G1 & x ~ S1 & G2) T D1 /\
      subdec (G1 & x ~ S1 & G2) D1 D2 /\
      gb_dec (G1 & x ~ S1 & G2) D1)
/\ (forall G T l, typ_hasnt G T l -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2 & G2) ->
    good_bounds (G1 & x ~ S1 & G2) ->
    wf_typ (G1 & x ~ S1 & G2) T ->
    subtyp (G1 & x ~ S1 & G2) S1 S2 ->
    typ_hasnt (G1 & x ~ S1 & G2) T l 
    \/ exists D, 
         label_of_dec D = l /\
         typ_has (G1 & x ~ S1 & G2) T D /\
         gb_dec  (G1 & x ~ S1 & G2) D).
Proof.
  apply typ_has_mutind.
  + (* case typ_bot_has *)
    intros. subst. exists (dec_bot l). apply (conj (typ_bot_has _ _)).
    split.
    - destruct l; simpl; eauto.
    - apply* narrow_gb_dec.
  (*
  + (* case typ_bot_has *)
    intros. subst. exists (dec_bot l). apply (conj (typ_bot_has _ _)).
    destruct l as [L | m].
    - repeat split.
      * simpl. eauto.
      * simpl in *. inversions H2. apply gb_dec_typ. apply* narrow_subtyp_middle.
    - simpl. eauto.
  *)
  + (* case typ_rcd_has *)
    intros. subst. apply invert_wf_rcd in H4. exists D.
    repeat split; eauto. apply* narrow_gb_dec.
  + (* case typ_sel_has *)
    intros G x X2 L Lo2 Hi2 D2 Bix2 X2Has0 IH1 Hi2Has0 IH2 G1 x0 S1 S2 G2 Eq Sb Gb2 Gb1
           GbD Wf St.
    subst.
    apply invert_wf_sel in Wf. destruct Wf as [X1 [T [U [Bix1 [X1Has [WfX1 [WfT WfU]]]]]]].
    lets StX: (narrow_binds_2 WfX1 Bix2 Bix1 St).
    lets WfX2: (proj2 (subtyp_regular StX)).
    specialize (IH1 _ _ _ _ _ eq_refl Sb Gb2 Gb1 (var_has_to_gb Gb2 Bix2 X2Has0) WfX2 St).
    destruct IH1 as [D0 [X2Has [Sd0 GbD1]]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo1 [Hi1 [Eq [StLo12 StHi12]]]]. subst D0.
    lets WfHi2: (proj2 (subtyp_regular StHi12)).
    specialize (IH2 _ _ _ _ _ eq_refl Sb Gb2 Gb1 GbD WfHi2 St).
    destruct IH2 as [D1 [Hi2Has [Sd12 Gb']]].
    lets P: (swap_sub_and_typ_has StX X2Has).
            (********************)
    destruct P as [D0 [X1Has' Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo0 [Hi0 [Eq [StLo01 StHi01]]]]. subst D0.
    lets StLo: (subtyp_trans StLo12 StLo01).
    lets StHi: (subtyp_trans StHi01 StHi12).
    lets P: (swap_sub_and_typ_has StHi Hi2Has).
            (********************)
    destruct P as [D0 [Hi0Has Sd01]].
    exists D0. repeat split.
    - apply (typ_sel_has Bix1 X1Has' Hi0Has).
    - apply (subdec_trans Sd01 Sd12).
    - (* also need swap_sub_and_typ_has which preserves gb_dec *)
      admit. (* <----------- *) 
  + (* case typ_and_has_1 *)
    introv _ IH1 _ IH2. introv Eq Sb Gb2 Gb1 GbD Wf St. subst. rename D into D1.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ _ _ _ _ eq_refl Sb Gb2 Gb1 GbD Wf1 St).
    specialize (IH2 _ _ _ _ _ eq_refl Sb Gb2 Gb1 Wf2 St).
    destruct IH1 as [D1' [T1Has [Sd1 GbD1']]].
    lets Eql1: (subdec_to_label_of_dec_eq Sd1).
    destruct IH2 as [T2Hasnt | [D2 [Eql2 [T2Has GbD2]]]].
    - exists D1'.
      rewrite <- Eql1 in T2Hasnt.
      split.
      * apply (typ_and_has_1 T1Has T2Hasnt).
      * apply (conj Sd1 GbD1').
    - rewrite <- Eql2 in Eql1. destruct (intersect_dec_total _ _ Eql1) as [D12 Eq].
      exists D12. repeat split.
      * apply (typ_and_has_12 T1Has T2Has Eq).
      * refine (subdec_trans _ Sd1).
        lets WfD1: (typ_has_preserves_wf T1Has Wf1).
        lets WfD2: (typ_has_preserves_wf T2Has Wf2).
                   (********************)
        apply (subdec_intersect_l Eq WfD1 WfD2).
      * (* would need intersect_preserves_gb_dec, but that doesn't hold *)
Abort.

Axiom un_narrow_has_middle: forall G1 x S1 S2 G2 T D1,
  typ_has (G1 & x ~ S1 & G2) T D1 ->
  wf_typ  (G1 & x ~ S1 & G2) T ->
  subtyp  (G1 & x ~ S1 & G2) S1 S2 ->
  typ_hasnt (G1 & x ~ S2 & G2) T (label_of_dec D1) \/
  exists D2,
    typ_has (G1 & x ~ S2 & G2) T D2 /\
    subdec  (G1 & x ~ S1 & G2) D1 D2.

(* narrow_has together with good bounds for the dec *)

(*
Lemma narrow_typ_has_good_bounds_1: forall G1 x S1 S2 G2 T,
  typ_has (G1 & x ~ S2 & G2) T (dec_typ L Lo2 Hi2) ->
  sub
  good_bounds     (G1 & x ~ S1 & G2) ->
  stable_typ S1 ->
  subtyp          (G1 & x ~ S1 & G2) S1 S2 ->
  good_bounds_typ (G1 & x ~ S1 & G2) T.
Proof.*)


(* won't hold, and not sure if usable *)
Lemma narrow_good_bounds_typ: forall G1 x S1 S2 G2 T,
  good_bounds     (G1 & x ~ S1 & G2) ->
  good_bounds_typ (G1 & x ~ S2 & G2) T ->
  stable_typ S1 ->
  subtyp          (G1 & x ~ S1 & G2) S1 S2 ->
  good_bounds_typ (G1 & x ~ S1 & G2) T.
Proof.
  introv Gb GbT Sb StS. unfold good_bounds_typ in *.
  split. admit. destruct GbT as [WfT GbT].
  introv THas.
  lets WfT': (narrow_wf_typ_middle WfT Sb StS).
  (* need to un-narrow THas in order to feed it to GbT! *)
  lets THas': (un_narrow_has_middle THas WfT' StS).
  destruct THas' as [THasnt | [D2 [THas' Sd]]].
  - (* screwed *) admit.
  - (* screwed as well, because GbT specialized with D2 will only give suptyp for the
       imprecise bounds of D2, but we need precise Lo<:Hi *)
Abort.

(* TODO doesn't hold, but it should be possible to prove some big alpha-renaming lemma
   to replace this if L is big enough. *)
Axiom cofinite_vars_eq: forall (L: fset var) (x y: var), x \notin L -> y \notin L -> x = y.

Lemma un_narrow: forall G1 x S1 S2 G2 y T,
  wf_typ (G1 & x ~ S2 & G2) T ->
  good_bounds (G1 & x ~ S2 & G2) ->
  good_bounds (G1 & x ~ S1 & G2 & y ~ T) ->
  subtyp (G1 & x ~ S1 & G2) S1 S2 ->
  good_bounds (G1 & x ~ S2 & G2 & y ~ T).
Admitted.

(* The good_bounds hyp is for the less precise S2, because if we want to get it for
   the more precise S1, we can just use the hyp rules. *)
Lemma narrow_ty_end_only:
   (forall G t T, ty_trm G t T -> forall G1 x S1 S2,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S1) ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2) ->
    subtyp (G1 & x ~ S1) S1 S2 ->
    ty_trm (G1 & x ~ S1) t T)
/\ (forall G d D, ty_def G d D -> forall G1 x S1 S2,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S1) ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2) ->
    subtyp (G1 & x ~ S1) S1 S2 ->
    ty_def (G1 & x ~ S1) d D)
/\ (forall G ds T, ty_defs G ds T -> forall G1 x S1 S2,
    G = G1 & x ~ S2 ->
    ok (G1 & x ~ S1) ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2) ->
    subtyp (G1 & x ~ S1) S1 S2 ->
    ty_defs (G1 & x ~ S1) ds T).
Proof.
  apply ty_mutind.
  + (* case ty_var *)
    introv Bi2 WfT Eq Ok Sb Gb StS. subst.
    lets WfT': (narrow_wf_typ_end WfT Sb StS).
    lets P: (narrow_binds_end WfT' Bi2 StS). destruct P as [T1 [Bi1 St]].
    lets WfT1: (proj1 (subtyp_regular St)).
    apply ty_sbsm with T1; eauto.
  + (* case ty_call *)
    introv Tyt IH1 T2Has Tyu IH2 WfV2. introv Eq Ok Sb Gb StS.
    subst. rename T into T2, V into V2.
    specialize (IH1 _ _ _ _ eq_refl Ok Sb Gb StS).
    (* old (ty_imp/ty_trm)
    inversions IH1. rename H into Tyt', H0 into StT.
    specialize (IH2 _ _ _ _ eq_refl Ok Sb Gb StS).
    lets P: (narrow_has_end T2Has (proj2 (subtyp_regular StT)) StS).
    destruct P as [D [T2Has' Sd]]. apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [U2' [V2' [Eq [StU2 StV2]]]]. subst D.
    lets P: (swap_sub_and_typ_has StT T2Has'). destruct P as [D [T1Has Sd]].
    apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [U2'' [V2'' [Eq [StU2' StV2']]]]. subst D.
    apply ty_sbsm with V2''.
    - apply (ty_call Tyt' T1Has).
      * apply (ty_imp_sbsm IH2). apply (subtyp_trans StU2 StU2').
      * apply (proj1 (subtyp_regular StV2')).
    - apply (subtyp_trans StV2' StV2).
    *)
    admit.
  + (* case ty_new *)
    introv Tyds IH1 _ IH2 WfU Eq Ok1 Sb Gb St. subst.
    assert (C: exists L1 U', forall y, y \notin L1 -> 
      ty_defs (G1 & x ~ S1 & G2 & y ~ open_typ y T) (open_defs y ds) (open_typ y T) /\
      ty_trm (G1 & x ~ S1 & G2 & y ~ open_typ y T) (open_trm y u) U' /\
      (* wf_typ (G1 & x ~ S1 & G2) U' *)
      subtyp (G1 & x ~ S1 & G2) U' U).
    {
      pick_fresh y; assert (yL: y \notin L) by auto.
      destruct (env_case G2) as [Eq1 | [x' [S2' Eq1]]].
      - subst. rewrite concat_empty_r in *. subst.
Abort.
     (* IH is useless! 
      specialize (IH1 y yL G1 x S1 S2 (G2 & y ~ open_typ y T)).
      specialize (IH2 y yL G1 x S1 S2 (G2 & y ~ open_typ y T)).
      repeat rewrite concat_assoc in IH1, IH2.
      specialize (Tyds y yL).
      lets Ok2: (ok_middle_change S2 Ok1).
      lets GbT: (ty_defs_to_good_bounds_typ Tyds).
      assert (Ok': ok (G1 & (x ~ S1 & G2) & y ~ open_typ y T)) by (apply okadmit).
      apply (weaken_good_bounds_typ_middle Ok') in GbT.

      assert (Ok2': ok (G1 & x ~ S2 & G2 & y ~ open_typ y T)) by (apply okadmit).
      lets Gb': (good_bounds_push_ty_defs Gb Tyds Ok2').
      assert (Ok1': ok (G1 & x ~ S1 & G2 & y ~ open_typ y T)) by auto.
      apply (weaken_subtyp_end Ok1') in St.
      specialize (IH1 eq_refl Ok1' Sb Gb' St).
      specialize (IH2 eq_refl Ok1' Sb Gb' St).
      inversions IH2. rename T1 into U', H into Tyu, H0 into StU.
      match goal with
      | F: y \notin (?L1 \u ?L2) |- _ => exists (L1 \u L2)
      end.
      exists U'.
      intros y0 y0Fr.
      rewrite (cofinite_vars_eq y0Fr Fr).
      refine (conj IH1 (conj Tyu _)).
      (* Problem: y cannot appear in U (by WfU), but what if it suddenly occurs in U'?
         Or in other words: How to ensure that narrowing preserves the "fv-restriction"? *)
      admit. (* almost StU *)
    }
    destruct C as [L1 [U' C]].
    apply ty_sbsm with U'.
    - apply_fresh ty_new as y; try pick_fresh y;
      assert (yL1: y \notin L1) by auto; specialize (C y yL1).
      * apply (proj31 C).
      * apply (proj32 C).
      * apply (proj1 (subtyp_regular (proj33 C))).
    - pick_fresh y; assert (yL1: y \notin L1) by auto; specialize (C y yL1).
      apply (proj33 C).
  + (* case ty_hyp *)
    introv WfT Ty IH Eq Ok Sb Gb2 StS. subst.
    apply (IH Gb2 _ _ _ _ _ eq_refl Ok Sb Gb2 StS).
  + (* case ty_sbsm *)
    introv Ty IH St Eq Ok Sb Gb2 StS. subst.
    apply ty_imp_hyp.
    - refine (narrow_wf_typ_middle _ Sb StS). apply (proj2 (subtyp_regular St)).
    - intro Gb1. apply ty_imp_sbsm with T1.
      * apply* IH.
      * apply (narrow_subtyp_middle St Sb Gb1 StS).
  + (* case ty_tdef *)
    introv St Eq Ok Sb Gb2 StS. subst.
    apply ty_def_hyp.
    - refine (narrow_wf_dec_middle _ Sb StS). destruct (subtyp_regular St) as [WfT WfU].
      apply (wf_tmem _ WfT WfU).
    - intro Gb1. apply ty_tdef. apply (narrow_subtyp_middle St Sb Gb1 StS).
  + (* case ty_mdef *)
    introv WfT WfU Tyu IH Eq Ok Sb Gb2 StS. subst.
    lets WfT': (narrow_wf_typ_middle WfT Sb StS).
    lets WfU': (narrow_wf_typ_middle WfU Sb StS).
    apply_fresh ty_mdef as y.
    - exact WfT'.
    - exact WfU'.
    - assert (yL: y \notin L) by auto.
      specialize (IH y yL G1 x S1 S2 (G2 & y ~ T)). repeat rewrite concat_assoc in IH.
      assert (Ok': ok (G1 & x ~ S1 & G2 & y ~ T)) by auto.
      apply ty_imp_hyp.
      * apply (weaken_wf_typ_end WfU' Ok').
      * intro Gb1. refine (IH eq_refl Ok' Sb _ (weaken_subtyp_end Ok' StS)).
        (* needs un-narrowing !! *)
        apply (un_narrow WfT Gb2 Gb1 StS).
  + (* case ty_defs_nil *) eauto.
  + (* case ty_defs_cons *)
    intros. subst. apply* ty_defs_cons.
Qed.
*)

(* Doesn't hold as a lemma because ty_tdef needs subtyp directly without going through
   a ty_trm. TODO add a rule for it, but with a flag whether it's allowed, because
   we don't want to allow it in wf_sto! *) 
Lemma ty_def_hyp: forall G d D,
  wf_dec G D ->
  (forall G' : ctx, subenv G' G -> good_bounds G' -> ty_def G' d D) ->
  ty_def G d D.
Admitted.
(*
Proof.
  introv Wf Ty.
  destruct d as [L Lo Hi | m U V u]; destruct D as [L' Lo' Hi'| m' U' V'].
  - assert (Tyd: ty_def G (def_typ L Lo Hi) (dec_typ L Lo Hi)). {
      constructor.
  - 
*)

Lemma narrow_ty:
   (forall G t T, ty_trm G t T -> forall G',
    ok G' ->
    subenv G' G ->
    ty_trm G' t T)
/\ (forall G d D, ty_def G d D -> forall G',
    ok G' ->
    subenv G' G ->
    ty_def G' d D)
/\ (forall G ds T, ty_defs G ds T -> forall G',
    ok G' ->
    subenv G' G ->
    ty_defs G' ds T).
Proof.
  apply ty_mutind.
  + (* case ty_var *)
    introv Bi2 WfT Ok Se. subst.
    (*lets WfT': (narrow_wf_typ_middle WfT Se).*)
    assert (WfT': wf_typ G' T) by admit.
    (*lets P: (narrow_binds WfT' Bi2 Se). destruct P as [T1 [Bi1 St]].
    lets WfT1: (proj1 (subtyp_regular St)).
    apply ty_sbsm with T1; eauto.*)
    admit.
  + (* case ty_call *)
    introv Tyt IH1 T2Has Tyu IH2 WfV2. introv Ok Se.
    subst. rename T into T2, V into V2.
    specialize (IH1 _ Ok Se).
    rename IH1 into Tyt'.
    specialize (IH2 _ Ok Se).
    admit. (*
    lets P: (narrow_has_middle T2Has (ty_trm_regular Tyt') StS).
    destruct P as [D [T2Has' Sd]]. apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [U2' [V2' [Eq [StU2 StV2]]]]. subst D.
    refine (ty_sbsm _ StV2).
    apply (ty_call Tyt' T2Has').
    - apply (ty_sbsm IH2 StU2).
    - apply (proj1 (subtyp_regular StV2)).
    *)
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Ok1 Se. subst.
    pick_fresh y; assert (yL: y \notin L) by auto.
    specialize (Tyds y yL).
    lets P: (subenv_concat_inv Se). destruct P as [G1' [G2' [Eq Se1]]]. subst.
    specialize (IH1 y yL (G1' & y ~ open_typ y T) (okadmit _) (subenv_push _ _ Se1)).
    specialize (IH2 y yL (G1' & y ~ open_typ y T) (okadmit _) (subenv_push _ _ Se1)).
    apply_fresh ty_new as y'; try (assert (Eq: y' = y) by admit; subst y').
                              (******************************** cofinite vars stuff! *)
    * apply IH1.
    * (* Note: typing u imprecisely solves the fv-restriction problem we had before *)
      apply IH2.
    * admit. (* narrow WfU refine (narrow_wf_typ_middle WfU Sb (weaken_subtyp_end _ St))*)
  + (* case ty_hyp *)
    introv WfT Ty IH Ok Se. subst.
    assert (WfT': wf_typ G' T) by admit.
    apply (ty_hyp WfT').
    intros G'' Se' Gb''.
    (* Note that we do not have to un-narrow Gb'' to Gb', because ty_hyp now is stronger *)
    refine (IH G'' _ Gb'' G'' (okadmit _) _).
    - apply (subenv_trans Se' Se).
    - apply subenv_refl.
  + (* case ty_sbsm *)
    introv Ty IH St Ok Se. subst.
    apply ty_hyp.
    - lets WfT: (proj2 (subtyp_regular St)). admit. (* narrow WfT *)
    - intros G'' Se' Gb. lets Se2: (subenv_trans Se' Se).
      apply ty_sbsm with T1.
      * apply* IH. apply okadmit.
      * admit. (* narrowing with St with Se2 *)
  + (* case ty_tdef *)
    introv St Ok Se. subst.
    apply ty_def_hyp.
    - (*refine (narrow_wf_dec_middle _ Sb StS'). destruct (subtyp_regular St) as [WfT WfU].
      apply (wf_tmem _ WfT WfU). *) admit.
    - intros G'' Se' Gb. apply ty_tdef. admit. (* subtyp narrowing *)
  + (* case ty_mdef *)
    introv WfT WfU Tyu IH Ok Se. subst.
    lets P: (subenv_concat_inv Se). destruct P as [G1' [G2' [Eq Se1]]]. subst.
    apply_fresh ty_mdef as y.
    - admit. (* narrow_wf *)
    - admit. (* narrow_wf *)
    - assert (yL: y \notin L) by auto.
      (* Note: No more need for un-narrowing (because good_bounds is no longer a hyp,
         but it's not just moved to ty_hyp *)
      apply (IH y yL (G1' & y ~ T) (okadmit _) (subenv_push _ _ Se1)).
  + (* case ty_defs_nil *) eauto.
  + (* case ty_defs_cons *)
    intros. subst. apply* ty_defs_cons.
Qed.

(* The good_bounds hyp is for the less precise S2, because if we want to get it for
   the more precise S1, we can just use the hyp rules.
Lemma narrow_ty_OLD:
   (forall G t T, ty_trm G t T -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    ok (G1 & x ~ S1 & G2) ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2 & G2) ->
    subtyp (G1 & x ~ S1) S1 S2 ->
    ty_trm (G1 & x ~ S1 & G2) t T)
/\ (forall G d D, ty_def G d D -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    ok (G1 & x ~ S1 & G2) ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2 & G2) ->
    subtyp (G1 & x ~ S1) S1 S2 ->
    ty_def (G1 & x ~ S1 & G2) d D)
/\ (forall G ds T, ty_defs G ds T -> forall G1 x S1 S2 G2,
    G = G1 & x ~ S2 & G2 ->
    ok (G1 & x ~ S1 & G2) ->
    stable_typ S1 ->
    good_bounds (G1 & x ~ S2 & G2) ->
    subtyp (G1 & x ~ S1) S1 S2 ->
    ty_defs (G1 & x ~ S1 & G2) ds T).
Proof.
  apply ty_mutind.
  + (* case ty_var *)
    introv Bi2 WfT Eq Ok Sb Gb StS. subst. apply (weaken_subtyp_end Ok) in StS.
    lets WfT': (narrow_wf_typ_middle WfT Sb StS).
    lets P: (narrow_binds WfT' Bi2 StS). destruct P as [T1 [Bi1 St]].
    lets WfT1: (proj1 (subtyp_regular St)).
    apply ty_sbsm with T1; eauto.
  + (* case ty_call *)
    introv Tyt IH1 T2Has Tyu IH2 WfV2. introv Eq Ok Sb Gb StS.
    subst. rename T into T2, V into V2.
    specialize (IH1 _ _ _ _ _ eq_refl Ok Sb Gb StS).
    rename IH1 into Tyt'.
    specialize (IH2 _ _ _ _ _ eq_refl Ok Sb Gb StS).
    apply (weaken_subtyp_end Ok) in StS.
    lets P: (narrow_has_middle T2Has (ty_trm_regular Tyt') StS).
    destruct P as [D [T2Has' Sd]]. apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [U2' [V2' [Eq [StU2 StV2]]]]. subst D.
    refine (ty_sbsm _ StV2).
    apply (ty_call Tyt' T2Has').
    - apply (ty_sbsm IH2 StU2).
    - apply (proj1 (subtyp_regular StV2)).
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Eq Ok1 Sb Gb St. subst.
    assert (Eq': (exists G0', G0 = G1 & G0') \/ (exists G3', G3 = G3' & G2)) by admit.
    destruct Eq' as [[G0' Eq'] | [G3' Eq']].
    - subst. assert (Eq'': G2 = G0' & x ~ S2 & G3) by admit. clear Eq. subst G2.
      (* no need to do narrowing because it happend to far to the right in env *)
      clear IH1 IH2.
      do 2 rewrite <- concat_assoc. rewrite (concat_assoc G0').
      apply ty_sbsm with U.
      { apply_fresh ty_new as y; try pick_fresh y;
        assert (yL: y \notin L) by auto.
        + apply* Tyds.
        + apply* Tyu.
        + exact WfU. }
      { apply subtyp_refl. apply (weaken_wf_typ_end WfU).
        repeat rewrite concat_assoc. exact Ok1. }
    - subst. rewrite concat_assoc in Eq.
      assert (Eq'': G1 = G0 & x ~ S2 & G3') by admit. subst G1. clear Eq Tyu.
      pick_fresh y; assert (yL: y \notin L) by auto.
      specialize (Tyds y yL).
      specialize (IH1 y yL G0 x S1 S2 (G3' & y ~ open_typ y T)).
      specialize (IH2 y yL G0 x S1 S2 (G3' & y ~ open_typ y T)).
      repeat rewrite concat_assoc in *.
      specialize (IH1 eq_refl (okadmit _) Sb).
      specialize (IH2 eq_refl (okadmit _) Sb).
      apply shrink_good_bounds in Gb.
           (******************)
      lets GbT: (ty_defs_to_good_bounds_typ Tyds).
      lets Gb': (good_bounds_push Gb GbT).
      specialize (IH1 Gb' St).
      specialize (IH2 Gb' St).
      apply_fresh ty_new as y'; try (assert (Eq: y' = y) by admit; subst y').
                                (******************************** cofinite vars stuff! *)
      * apply IH1.
      * (* Note: typing u imprecisely solves the fv-restriction problem we had before *)
        apply IH2.
      * refine (narrow_wf_typ_middle WfU Sb (weaken_subtyp_end _ St)). auto.
(*
  + (* case ty_new *)
    introv Tyds IH1 _ IH2 WfU Eq Ok1 Sb Gb St. subst.
    assert (Eq': (exists G0', G0 = G1 & G0') \/ (exists G3', G3 = G3' & G2)) by admit.
    destruct Eq' as [[G0' Eq'] | [G3' Eq']].
    - subst. assert (Eq'': G2 = G0' & x ~ S2 & G3) by admit. clear Eq. subst G2.
      pick_fresh y; assert (yL: y \notin L) by auto.
      specialize (IH1 y yL (G1 & y ~ open_typ y T & G0') x S1 S2 G3).
      specialize (IH2 y yL (G1 & y ~ open_typ y T & G0') x S1 S2 G3).
      repeat rewrite concat_assoc in *.
      specialize (IH1 eq_refl (okadmit _) Sb).
      specialize (IH2 eq_refl (okadmit _) Sb).
      specialize (Tyds y yL).
      lets GbT: (ty_defs_to_good_bounds_typ Tyds). repeat rewrite concat_assoc in GbT.
      (* Problem: (open_typ y T) has good bounds only in 
         (G1 & y ~ open_typ y T & G0' & x ~ S2 & G3), but in order to apply the IHs,
         we need to insert (y ~ open_typ y T) into the env of Gb just after G1,
         so we need to strengthen GbT to (G1 & y ~ open_typ y T)! *)

    assert (C: exists L1 U', forall y, y \notin L1 -> 
      ty_defs (G1 & x ~ S1 & G2 & y ~ open_typ y T) (open_defs y ds) (open_typ y T) /\
      ty_trm (G1 & x ~ S1 & G2 & y ~ open_typ y T) (open_trm y u) U' /\
      (* wf_typ (G1 & x ~ S1 & G2) U' *)
      subtyp (G1 & x ~ S1 & G2) U' U).
    {
      pick_fresh y; assert (yL: y \notin L) by auto.
      specialize (IH1 y yL G1 x S1 S2 (G2 & y ~ open_typ y T)).
      specialize (IH2 y yL G1 x S1 S2 (G2 & y ~ open_typ y T)).
      repeat rewrite concat_assoc in IH1, IH2.
      specialize (Tyds y yL).
      lets Ok2: (ok_middle_change S2 Ok1).
      lets GbT: (ty_defs_to_good_bounds_typ Tyds).
      assert (Ok': ok (G1 & (x ~ S1 & G2) & y ~ open_typ y T)) by (apply okadmit).
      apply (weaken_good_bounds_typ_middle Ok') in GbT.

      assert (Ok2': ok (G1 & x ~ S2 & G2 & y ~ open_typ y T)) by (apply okadmit).
      lets Gb': (good_bounds_push_ty_defs Gb Tyds Ok2').
      assert (Ok1': ok (G1 & x ~ S1 & G2 & y ~ open_typ y T)) by auto.
      apply (weaken_subtyp_end Ok1') in St.
      specialize (IH1 eq_refl Ok1' Sb Gb' St).
      specialize (IH2 eq_refl Ok1' Sb Gb' St).
      inversions IH2. rename T1 into U', H into Tyu, H0 into StU.
      match goal with
      | F: y \notin (?L1 \u ?L2) |- _ => exists (L1 \u L2)
      end.
      exists U'.
      intros y0 y0Fr.
      rewrite (cofinite_vars_eq y0Fr Fr).
      refine (conj IH1 (conj Tyu _)).

      (* Problem: y cannot appear in U (by WfU), but what if it suddenly occurs in U'?
         Or in other words: How to ensure that narrowing preserves the "fv-restriction"? *)
      admit. (* almost StU *)
    }
*)
  + (* case ty_hyp *)
    introv WfT Ty IH Eq Ok Sb Gb2 StS. subst.
    apply (IH Gb2 _ _ _ _ _ eq_refl Ok Sb Gb2 StS).
  + (* case ty_sbsm *)
    introv Ty IH St Eq Ok Sb Gb2 StS. subst.
    lets StS': (weaken_subtyp_end Ok StS).
    apply ty_hyp.
    - refine (narrow_wf_typ_middle _ Sb StS'). apply (proj2 (subtyp_regular St)).
    - intro Gb1. apply ty_sbsm with T1.
      * apply* IH.
      * apply (narrow_subtyp_middle St Sb Gb1 StS').
  + (* case ty_tdef *)
    introv St Eq Ok Sb Gb2 StS. subst.
    lets StS': (weaken_subtyp_end Ok StS).
    apply ty_def_hyp.
    - refine (narrow_wf_dec_middle _ Sb StS'). destruct (subtyp_regular St) as [WfT WfU].
      apply (wf_tmem _ WfT WfU).
    - intro Gb1. apply ty_tdef. apply (narrow_subtyp_middle St Sb Gb1 StS').
  + (* case ty_mdef *)
    introv WfT WfU Tyu IH Eq Ok Sb Gb2 StS. subst.
    assert (Eq': (exists G0', G0 = G1 & G0') \/ (exists G3', G3 = G3' & G2)) by admit.
    destruct Eq' as [[G0' Eq'] | [G3' Eq']].
    - subst. assert (Eq'': G2 = G0' & x ~ S2 & G3) by admit. clear Eq. subst G2.
      (* no need to do narrowing because it happend to far to the right in env *)
      clear IH.
      do 2 rewrite <- concat_assoc. rewrite (concat_assoc G0').
      apply_fresh ty_mdef as y; try pick_fresh y;
        assert (yL: y \notin L) by auto.
        * exact WfT.
        * exact WfU.
        * apply* Tyu.
    - subst. rewrite concat_assoc in Eq.
      assert (Eq'': G1 = G0 & x ~ S2 & G3') by admit. subst G1. clear Eq.
      rewrite concat_assoc in *.
      lets StS': (weaken_subtyp_end (ok_concat_inv_l Ok) StS).
      lets WfT': (narrow_wf_typ_middle WfT Sb StS').
      lets WfU': (narrow_wf_typ_middle WfU Sb StS').
      apply_fresh ty_mdef as y.
      * exact WfT'.
      * exact WfU'.
      * assert (yL: y \notin L) by auto.
        specialize (IH y yL G0 x S1 S2 (G3' & y ~ T)).
        repeat rewrite concat_assoc in *.
        specialize (IH eq_refl (okadmit _) Sb).
        apply ty_hyp.
        { apply (weaken_wf_typ_end WfU'). auto. }
        { intro Gb. refine (IH _ StS).
          apply shrink_good_bounds in Gb2.
          (* now what if the bounds of T only are good because some type members in
             S1 are much more precise than in S2??? 
            how can un-narrowing hold?? *)
          admit. }
(*
  + (* case ty_mdef *)
    introv WfT WfU Tyu IH Eq Ok Sb Gb2 StS. subst.
    lets WfT': (narrow_wf_typ_middle WfT Sb StS).
    lets WfU': (narrow_wf_typ_middle WfU Sb StS).
    apply_fresh ty_mdef as y.
    - exact WfT'.
    - exact WfU'.
    - assert (yL: y \notin L) by auto.
      specialize (IH y yL G1 x S1 S2 (G2 & y ~ T)). repeat rewrite concat_assoc in IH.
      assert (Ok': ok (G1 & x ~ S1 & G2 & y ~ T)) by auto.
      apply ty_imp_hyp.
      * apply (weaken_wf_typ_end WfU' Ok').
      * intro Gb1. refine (IH eq_refl Ok' Sb _ (weaken_subtyp_end Ok' StS)).
        (* needs un-narrowing !! *)
        apply (un_narrow WfT Gb2 Gb1 StS).
*)
  + (* case ty_defs_nil *) eauto.
  + (* case ty_defs_cons *)
    intros. subst. apply* ty_defs_cons.
Qed.
*)

Lemma narrow_ty_end: forall G x S1 S2 t T,
  ty_trm (G & x ~ S2) t T ->
  ok (G & x ~ S1) ->
  stable_typ S1 ->
  good_bounds (G & x ~ S2) ->
  subtyp (G & x ~ S1) S1 S2 ->
  ty_trm (G & x ~ S1) t T.
Proof.
  introv Ty Ok Sb Gb St. destruct narrow_ty as [P _].
  refine (P _ _ _ Ty (G & x ~ S1) Ok _).
  apply (subenv_sub (subenv_refl G) Sb St).
Qed.

Print Assumptions narrow_ty.


(* ###################################################################### *)
(** ** Helper *)

Lemma invert_ty_var: forall G x T,
  good_bounds G ->
  ty_trm G (trm_var (avar_f x)) T ->
  exists T', binds x T' G /\ subtyp G T' T.
Proof.
  introv Gb Ty. gen_eq t: (trm_var (avar_f x)). induction Ty; intro Eq; inversions Eq.
  - exists T. auto.
  - apply* H1. apply subenv_refl.
  - specialize (IHTy Gb eq_refl). destruct IHTy as [T0 [Bi St]].
    exists T0. apply (conj Bi). apply (subtyp_trans St H).
Qed.


(* ###################################################################### *)
(** ** Progress *)

Lemma progress_proof:
  forall G t T, ty_trm G t T -> forall s,
    wf_sto s G ->
    (exists t' s', red t s t' s') \/ (exists x o, t = trm_var (avar_f x) /\ binds x o s).
Proof.
  apply (ty_trm_ind (fun G t T => forall s,
    wf_sto s G ->
    (exists t' s', red t s t' s') \/ (exists x o, t = trm_var (avar_f x) /\ binds x o s))).
  + (* case ty_var *)
    introv BiG WfT Wfs.
    right. destruct (ctx_binds_to_sto_binds Wfs BiG) as [o [Bis Tyds]].
    exists x o. auto.
  + (* case ty_call *)
    introv Ty1 IHrec THas Ty2 IHarg WfV Wfs. left.
    specialize (IHrec s Wfs). destruct IHrec as [IHrec | IHrec].
    - (* case receiver is an expression *)
      destruct IHrec as [s' [e' IHrec]]. do 2 eexists. apply (red_call1 m _ IHrec).
    - (* case receiver is  a var *)
      destruct IHrec as [x [ds [Eq Bis]]]. subst.
      specialize (IHarg s Wfs). destruct IHarg as [IHarg | IHarg].
      * (* arg is an expression *)
        destruct IHarg as [s' [e' IHarg]]. do 2 eexists. apply (red_call2 x m IHarg).
      * (* arg is a var *)
        destruct IHarg as [y [o [Eq Bisy]]]. subst.
        apply (invert_ty_var (wf_sto_to_good_bounds Wfs)) in Ty1.
        destruct Ty1 as [T' [BiG StT]].
        lets P: (swap_sub_and_typ_has StT THas). destruct P as [D1 [T'Has Sd]].
        apply invert_subdec_mtd_sync_left in Sd. destruct Sd as [U' [V' [Eq [StU StV]]]].
        subst.
        lets P: (typ_has_to_defs_has Wfs T'Has Bis BiG).
        destruct P as [d [dsHas Tyd]].
        inversions Tyd. rename H4 into WfU', H5 into WfV', H6 into Tybody.
        exists (open_trm y u) s.
        apply (red_call y Bis dsHas).
  + (* case ty_new *)
    introv Tyds Tyu IH WfU Wfs.
    left. pick_fresh x.
    exists (open_trm x u) (s & x ~ (open_defs x ds)).
    apply* red_new.
  + (* case ty_hyp *)
    introv WfT Ty IH Wfs.
    lets Gb: (wf_sto_to_good_bounds Wfs).
    apply* IH. apply subenv_refl.
  + (* case ty_sbsm *)
    introv Ty IH St Wf. apply (IH s Wf).
Qed.

Theorem progress_result: progress.
Proof.
  unfold progress. introv Wf Ty. apply* progress_proof.
Qed.

Print Assumptions progress_result.


(* ###################################################################### *)
(** ** Helper lemmas for preservation *)

Lemma fv_ctx_types_push: forall G x T,
  fv_ctx_types (G & x ~ T) = (fv_ctx_types G) \u (fv_typ T).
Proof.
  intros.
  unfold fv_ctx_types. unfold fv_in_values.
  rewrite values_def. rewrite <- cons_to_push.
  rewrite LibList.map_cons. rewrite LibList.fold_right_cons.
  simpl. rewrite union_comm. reflexivity.
Qed.

(* replaces super-fresh x by a not-so-fresh y *)
Lemma ty_open_defs_change_var: forall y G S ds T,
  ok G ->
  y # G ->
  exists L, forall x, x \notin L ->
  good_bounds (G & x ~ open_typ x S) ->
  ty_defs (G & x ~ open_typ x S) (open_defs x ds) (open_typ x T) ->
  ty_defs (G & y ~ open_typ y S) (open_defs y ds) (open_typ y T).
Proof.
  introv Ok yG. let L := gather_vars in exists (L \u fv_typ (open_typ y S)).
  intros x Fr Gb Ty.
  destruct (classicT (x = y)) as [Eq | Ne].
  + subst. assumption.
  + assert (xG: x # G) by auto.
    assert (Okyx: ok (G & y ~ open_typ y S & x ~ open_typ x S)) by auto.
    lets Ty': (weaken_ty_defs_middle Gb Okyx Ty).
    rewrite* (@subst_intro_defs x y ds).
    lets P: (@defs_subst_principle _ _ y _ _ _ Ty' Okyx).
    assert (FrS: x \notin (fv_typ S)) by auto.
    rewrite <- (@subst_intro_typ x y S FrS) in P.
    assert (FrT: x \notin (fv_typ T)) by auto.
    rewrite <- (@subst_intro_typ x y T FrT) in P.
    assert (Fr': (x \notin (fv_ctx_types (G & y ~ open_typ y S)))). {
      rewrite fv_ctx_types_push. rewrite notin_union. auto.
    }
    rewrite (@subst_fresh_ctx x y _ Fr') in P.
    apply P. apply binds_push_eq.
Qed.

(* replaces super-fresh x by a not-so-fresh y *)
Lemma ty_open_trm_change_var: forall y G S t T,
  ok G ->
  y # G ->
  exists L, forall x, x \notin L ->
  good_bounds (G & x ~ open_typ x S) ->
  ty_trm (G & x ~ open_typ x S) (open_trm x t) T ->
  ty_trm (G & y ~ open_typ y S) (open_trm y t) T.
Proof.
  introv Ok yG. let L := gather_vars in exists (L \u fv_typ (open_typ y S)).
  intros x Fr Gb Ty.
  destruct (classicT (x = y)) as [Eq | Ne].
  + subst. assumption.
  + assert (xG: x # G) by auto.
    assert (Okyx: ok (G & y ~ open_typ y S & x ~ open_typ x S)) by auto.
    lets Ty': (weaken_ty_trm_middle Gb Okyx Ty).
    rewrite* (@subst_intro_trm x y t).
    lets P: (@trm_subst_principle _ _ y _ _ _ Ty' Okyx).
    assert (FrS: x \notin (fv_typ S)) by auto.
    rewrite <- (@subst_intro_typ x y S FrS) in P.
    assert (FrT: x \notin (fv_typ T)) by auto.
    rewrite (@subst_fresh_typ x y T FrT) in P.
    assert (Fr': (x \notin (fv_ctx_types (G & y ~ open_typ y S)))). {
      rewrite fv_ctx_types_push. rewrite notin_union. auto.
    }
    rewrite (@subst_fresh_ctx x y _ Fr') in P.
    apply P. apply binds_push_eq.
Qed.

Lemma defs_have_stable_typ: forall G ds T,
  ty_defs G ds T -> stable_typ T.
Proof.
  introv Tyds. induction Tyds; eauto.
Qed.

Lemma invert_ty_new: forall G ds u U,
  good_bounds G ->
  ty_trm G (trm_new ds u) U ->
  exists L T U' G1 G2,
     (G = G1 & G2)
  /\ (forall x, x \notin L ->
        ty_defs (G1 & x ~ open_typ x T) (open_defs x ds) (open_typ x T))
  /\ (forall x, x \notin L ->
        ty_trm (G1 & x ~ open_typ x T) (open_trm x u) U')
  /\ (wf_typ G1 U')
  /\ (subtyp G U' U).
Proof.
  introv Gb Ty. gen_eq t: (trm_new ds u). induction Ty; intro Eq; inversions Eq.
  - exists L T U G1 G2. lets WfU: (@weaken_wf_typ_end G1 G2 U H2 (okadmit _)).
    eauto 10.
  - apply* H1. apply subenv_refl.
  - specialize (IHTy Gb eq_refl).
    destruct IHTy as [L [T0 [U' [G1 [G2 [Eq [Tyds [Tyu [Wf St]]]]]]]]].
    subst. exists L T0 U' G1 G2. repeat split.
    * apply Tyds.
    * intros x xL. apply (Tyu x xL).
    * exact Wf.
    * apply (subtyp_trans St H).
Qed.

Lemma invert_ty_call: forall G t m V2 u,
  good_bounds G ->
  ty_trm G (trm_call t m u) V2 ->
  exists T U V1,
    ty_trm G t T /\
    typ_has G T (dec_mtd m U V1) /\
    ty_trm G u U /\
    subtyp G V1 V2.
Proof.
  introv Gb Ty. gen_eq t0: (trm_call t m u). induction Ty; intro Eq; inversions Eq.
  - do 3 eexists. eauto.
  - apply (H1 _ (subenv_refl _) Gb Gb eq_refl).
  - specialize (IHTy Gb eq_refl). destruct IHTy as [T [U [V [Tyt [THas [Tyu St]]]]]].
    exists T U V. repeat split; auto. apply (subtyp_trans St H).
Qed.


(* ###################################################################### *)
(** ** Preservation *)

Theorem preservation_proof: preservation.
Proof.
  introv Wf Ty Red. gen G T Wf Ty. induction Red.
  + (* red_call *)
    intros G V Wf TyCall.
    rename H into Bis, H0 into dsHas, T into U2, U into V2, V into V2'.
    exists (@empty typ). rewrite concat_empty_r. apply (conj Wf).
    lets Gb: (wf_sto_to_good_bounds Wf).
    apply (invert_ty_call Gb) in TyCall.
    destruct TyCall as [T [U2'' [V2'' [Tyx [THas [Tyy StV]]]]]].
    apply (invert_ty_var Gb) in Tyx. destruct Tyx as [T' [BiGx StT]].
    apply (invert_ty_var Gb) in Tyy. destruct Tyy as [U2''' [BiGy StU]].
    lets P: (swap_sub_and_typ_has StT THas). destruct P as [D1 [T'Has Sd]].
    apply invert_subdec_mtd_sync_left in Sd. destruct Sd as [U1 [V1 [Eq [StU' StV']]]].
    subst D1.
    lets P: (typ_has_to_defs_has Wf T'Has Bis BiGx). destruct P as [d [dsHas' Tyd]].
    inversions Tyd.
    clear H4. rename H5 into WfV, H6 into Tybody, u into body'.
    assert (Eq: def_mtd m U1 V1 body' = def_mtd m U2 V2 body). {
      refine (defs_has_unique _ dsHas' dsHas). reflexivity.
    }
    inversions Eq. clear dsHas'.
    pick_fresh y'.
    assert (y'L: y' \notin L) by auto.
    specialize (Tybody y' y'L).
    lets Ok: (wf_sto_to_ok_G Wf).
    (* Before we can apply the substitution principle, we must narrow 
       y' ~ U2 to y' ~ U1 in Tybody.
       But narrowing requires good_bounds: *)
    assert (Gb': good_bounds (G1 & y' ~ U2)). {
      (*
      lets GbU1: ((good_bounds_to_old Gb) _ _ BiGy).
      lets GbU2: (supertyp_has_good_bounds StU GbU1).
      assert (Oky': ok (G1 & G2 & y' ~ U2)) by auto.
      apply (good_bounds_push Gb).*)
      admit. (*!!*)
    }
    rename U2''' into U1.
    assert (Oky': ok (G1 & G2 & y' ~ U1)) by auto.
    destruct (ctx_binds_to_sto_binds Wf BiGy) as [dsy [Bisy Tydsy]].
    lets SbU1: (defs_have_stable_typ Tydsy).
    lets Tybody': (narrow_ty_end Tybody _ SbU1 Gb' (subtyp_trans StU StU')).
                  (*****************)
    lets P: (@trm_subst_principle_imp G y' y _ U1 V2 Tybody' Oky').
             (*******************)
    assert (y'U1: y' \notin (fv_typ U1)) by auto.
    rewrite (@subst_fresh_typ y' y U1 y'U1) in P.
    assert (y'body: y' \notin (fv_trm body)) by auto.
    rewrite <- (@subst_intro_trm y' y body y'body) in P.
    assert (EqG: (subst_ctx y' y G) = G). { refine (@subst_fresh_ctx y' y _ _). auto. }
    rewrite EqG in P.
    apply (ty_imp_sbsm (P BiGy)).
    assert (EqV2: (subst_typ y' y V2) = V2). { refine (@subst_fresh_typ y' y _ _). auto. }
    rewrite EqV2. exact StV.
  + (* red_new *)
    introv Wf Ty. inversions Ty. rename H1 into StT.
    lets Gb: (wf_sto_to_good_bounds Wf).
    apply (invert_ty_new Gb) in H0.
    destruct H0 as [L [Tds [Tyds [Tyt WfT]]]].
    exists (x ~ (open_typ x Tds)).
    assert (xG: x # G) by apply* sto_unbound_to_ctx_unbound.
    lets Ok: (wf_sto_to_ok_G Wf).
    assert (Okx: forall X, ok (G & x ~ X)) by auto.
    lets C1: (@ty_open_defs_change_var x G Tds ds Tds Ok xG). destruct C1 as [L1 C1].
    lets C2: (@ty_open_trm_change_var  x G Tds t  T1  Ok xG). destruct C2 as [L2 C2].
    pick_fresh x'.
    assert (x'L: x' \notin L) by auto.
    assert (x'L1: x' \notin L1) by auto.
    assert (x'L2: x' \notin L2) by auto.
    specialize (Tyds x' x'L). specialize (Tyt x' x'L).
    split.
    - refine (wf_sto_push Wf H xG _). apply* C1.
      apply (good_bounds_push_ty_defs Gb Tyds). auto.
    - refine (ty_sbsm _ (weaken_subtyp_end (Okx _) StT)). apply* C2.
      apply (good_bounds_push_ty_defs Gb Tyds). auto.
  + (* red_call1 *)
    intros G Tr2 Wf TyCall.
    lets Gb: (wf_sto_to_good_bounds Wf).
    apply (invert_ty_imp_call Gb) in TyCall.
    destruct TyCall as [To2 [Ta [Tr1 [Tyo [Has [Tya Str]]]]]].
    specialize (IHRed _ _ Wf (ty_trm_to_ty_imp Tyo)). destruct IHRed as [G' [Wf' Tyo']].
    inversions Tyo'. rename T1 into To1, H into Tyo', H0 into Sto.
    exists G'. apply (conj Wf').
    lets Ok': (wf_sto_to_ok_G Wf').
    apply (weaken_subtyp_end Ok') in Str.
    lets Has': (weaken_typ_has_end Ok' Has).
    lets P: (swap_sub_and_typ_has Sto Has'). destruct P as [D [Has'' Sd]].
            (********************)
    apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [Ta1' [Tr1' [Eq [Sta Str']]]]. subst.
    refine (ty_sbsm _ (subtyp_trans Str' Str)).
    refine (ty_call Tyo' Has'' _ _).
    - refine (ty_imp_sbsm _ Sta). apply (weaken_ty_imp_end Ok' Gb Tya).
    - apply (proj1 (subtyp_regular Str')).
  + (* red_call2 *)
    intros G Tr2 Wf TyCall.
    lets Gb: (wf_sto_to_good_bounds Wf).
    apply (invert_ty_imp_call Gb) in TyCall.
    destruct TyCall as [To2 [Ta [Tr1 [Tyo [Has [Tya Str]]]]]].
    specialize (IHRed _ _ Wf Tya). destruct IHRed as [G' [Wf' Tya']].
    lets Ok': (wf_sto_to_ok_G Wf').
    lets Has': (weaken_typ_has_end Ok' Has).
    exists G'.
    lets Tyo': (weaken_ty_trm_end Ok' Gb Tyo).
    lets WfD: (typ_has_preserves_wf Has' (ty_trm_regular Tyo')). inversions WfD.
    rename H3 into WfTa2, H5 into WfTr2.
    apply (conj Wf').
    refine (ty_sbsm _ (weaken_subtyp_end Ok' Str)).
    refine (ty_call Tyo' Has' Tya' WfTr2).
Qed.

Print Assumptions preservation_proof.
