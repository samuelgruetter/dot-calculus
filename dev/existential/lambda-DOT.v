
(*
lambda-DOT:
Lambda calculus with records, abstract type members, union and intersection types,
but without self references in types, and thus without recursive types nor recursive
functions.
*)

Set Implicit Arguments.

(* CoqIDE users: Run ln/open.sh to start coqide, then open this file. *)
Require Import LibLN.


(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter fld_label: Set.
Parameter mtd_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_fld: fld_label -> label
| label_mtd: mtd_label -> label.

(*
Definition typ_label := label.
Definition fld_label := label.
Definition mtd_label := label.
*)
(*
Dont' use different labels because we want l1 <> l2 in defs_has_skip
Parameter typ_label: Set.
Parameter fld_label: Set.
Parameter mtd_label: Set.
*)

Module labels.
  Parameter L: typ_label.
  Parameter l: fld_label.
  Parameter m: mtd_label.
  Parameter apply: mtd_label.
End labels.

(*
Inductive label: Set :=
| label_typ: nat -> label
| label_fld: nat -> label
| label_mtd: nat -> label.

(* Some default labels for examples: *)
Module labels.
  Parameter n0: nat.
  Parameter n1: nat.
  Axiom n0_not_n1: n0 <> n1.
  Definition L: label := label_typ n0.
  Definition l: label := label_fld n0.
  Definition m: label := label_mtd n0.
  Definition apply: label := label_mtd n1.
End labels.
*)

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive pth : Set :=
  | pth_var : avar -> pth.

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* {D}, no self reference *)
  | typ_sel  : pth -> typ_label -> typ (* p.L *)
  | typ_and  : typ -> typ -> typ
  | typ_or   : typ -> typ -> typ
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_fld  : fld_label -> typ -> dec
  | dec_mtd  : mtd_label -> typ -> typ -> dec.

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_sel  : trm -> fld_label -> trm
  | trm_call : trm -> mtd_label -> trm -> trm
  | trm_new  : defs -> trm (* will later have a nameless self reference, but not yet now *)
with def : Set :=
  | def_typ : typ_label -> typ -> typ -> def (* same as dec_typ *)
  | def_fld : fld_label -> typ -> avar -> def (* cannot have term here, assign it first *)
  | def_mtd : mtd_label -> typ -> typ -> trm -> def (* one nameless argument *)
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env defs.

(** *** Syntactic sugar *)
Definition trm_fun(T U: typ)(body: trm) := 
            trm_new (defs_cons defs_nil (def_mtd labels.apply T U body)).
Definition trm_app(func arg: trm) := trm_call func labels.apply arg.
Definition trm_let(T U: typ)(rhs body: trm) := trm_app (trm_fun T U body) rhs.
Definition typ_arrow(T1 T2: typ) := typ_rcd (dec_mtd labels.apply T1 T2).


(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ L _ _ => label_typ L
| def_fld l _ _ => label_fld l
| def_mtd m _ _ _ => label_mtd m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => label_typ L
| dec_fld l _ => label_fld l
| dec_mtd m _ _ => label_mtd m
end.

Inductive defs_hasnt: defs -> label -> Prop :=
| defs_hasnt_nil: forall l,
    defs_hasnt defs_nil l
| defs_hasnt_cons: forall d ds l,
    defs_hasnt ds l ->
    label_of_def d <> l ->
    defs_hasnt (defs_cons ds d) l.

Inductive defs_has: defs -> def -> Prop :=
| defs_has_hit: forall d ds,
    defs_hasnt ds (label_of_def d) ->
    defs_has (defs_cons ds d) d
| defs_has_skip: forall d1 d2 ds,
    defs_has ds d1 ->
    label_of_def d2 <> label_of_def d1 ->
    defs_has (defs_cons ds d2) d1
(* only def_typ can be merged, def_fld and def_mtd must be unique *)
| defs_has_merge: forall L Lo1 Hi1 Lo2 Hi2 ds,
    defs_has ds (def_typ L Lo1 Hi1) ->
    defs_has (defs_cons ds (def_typ L Lo2 Hi2))
      (def_typ L (typ_or Lo1 Lo2) (typ_and Hi1 Hi2)).

(*
Inductive defs_hasnt_typ: defs -> typ_label -> Prop :=
| defs_hasnt_typ_nil: forall L,
    defs_hasnt_typ defs_nil L
| defs_hasnt_typ_cons: forall L0 S0 U0 ds L,
    defs_hasnt_typ ds L ->
    L0 <> L ->
    defs_hasnt_typ (defs_cons ds (def_typ L0 S0 U0)) L.

Inductive defs_hasnt_fld: defs -> fld_label -> Prop :=
| defs_hasnt_fld_nil: forall l,
    defs_hasnt_fld defs_nil l
| defs_hasnt_fld_cons: forall l0 T0 x ds l,
    defs_hasnt_fld ds l ->
    l0 <> l ->
    defs_hasnt_fld (defs_cons ds (def_fld l0 T0 x)) l.

Inductive defs_hasnt_mtd: defs -> mtd_label -> Prop :=
| defs_hasnt_mtd_nil: forall m,
    defs_hasnt_mtd defs_nil m
| defs_hasnt_mtd_cons: forall m0 S0 U0 t ds m,
    defs_hasnt_mtd ds m ->
    m0 <> m ->
    defs_hasnt_mtd (defs_cons ds (def_mtd m0 S0 U0 t)) m.

Definition label_of_def(d: def): label := match d with
| def_typ L _ _ => L
| def_fld l _ _ => l
| def_mtd m _ _ _ => m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ L _ _ => L
| dec_fld l _ => l
| dec_mtd m _ _ => m
end.

Inductive defs_has: defs -> def -> Prop :=
| defs_has_hit_typ: forall L S U ds,
    defs_hasnt_typ ds L ->
    defs_has (defs_cons ds (def_typ L S U)) (def_typ L S U)
| defs_has_hit_fld: forall l T x ds,
    defs_hasnt_fld ds l ->
    defs_has (defs_cons ds (def_fld l T x)) (def_fld l T x)
| defs_has_hit_mtd: forall m S U t ds,
    defs_hasnt_mtd ds m ->
    defs_has (defs_cons ds (def_mtd m S U t)) (def_mtd m S U t)
| defs_has_skip: forall d0 d ds,
    defs_has ds d ->
    label_of_def d0 <> label_of_def d ->
    defs_has (defs_cons ds d0) d.

| defs_has_skip: forall l1 d1 ds l2 d2,
    defs_has ds l1 d1 ->
    l2 <> l1 ->
    defs_has (defs_cons ds l2 d2) l1 d1
(* only def_typ can be merged, def_fld and def_mtd must be unique *)
| defs_has_merge: forall l Lo1 Hi1 Lo2 Hi2 ds,
    defs_has ds l (def_typ Lo1 Hi1) ->
    defs_has (defs_cons ds l (def_typ Lo2 Hi2)) l
      (def_typ (typ_or Lo1 Lo2) (typ_and Hi1 Hi2)).
*)


(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k) 
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Definition open_rec_pth (k: nat) (u: var) (p: pth) : pth :=
  match p with
  | pth_var a => pth_var (open_rec_avar k u a)
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top       => typ_top
  | typ_bot       => typ_bot
  | typ_rcd D     => typ_rcd (open_rec_dec k u D)
  | typ_sel p L   => typ_sel (open_rec_pth k u p) L
  | typ_and T1 T2 => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_or  T1 T2 => typ_or  (open_rec_typ k u T1) (open_rec_typ k u T2)
  end
with open_rec_dec (k: nat) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_fld l T   => dec_fld l (open_rec_typ k u T)
  | dec_mtd m T U => dec_mtd m (open_rec_typ k u T) (open_rec_typ k u U)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_sel e n    => trm_sel (open_rec_trm k u e) n
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  | trm_new ds     => trm_new (open_rec_defs (*S k*) k u ds) (* TODO enable self ref *)
  end
with open_rec_def (k: nat) (u: var) (d: def) { struct d } : def :=
  match d with
  | def_typ L Lo Hi => def_typ L (open_rec_typ k u Lo) (open_rec_typ k u Hi)
  | def_fld f T a => def_fld f (open_rec_typ k u T) (open_rec_avar k u a)
  | def_mtd m T1 T2 e => def_mtd m (open_rec_typ k u T1) (open_rec_typ k u T2)
                       (open_rec_trm (S k) u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs) { struct ds } : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_pth  u p := open_rec_pth   0 u p.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u d := open_rec_dec   0 u d.
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

Definition fv_pth (p: pth) : vars :=
  match p with
  | pth_var a => fv_avar a
  end.

Fixpoint fv_typ (T: typ) { struct T } : vars :=
  match T with
  | typ_top       => \{}
  | typ_bot       => \{}
  | typ_rcd D     => (fv_dec D)
  | typ_sel p L   => (fv_pth p)
  | typ_and T U   => (fv_typ T) \u (fv_typ U)
  | typ_or  T U   => (fv_typ T) \u (fv_typ U)
  end
with fv_dec (D: dec) { struct D } : vars :=
  match D with
  | dec_typ _ T U => (fv_typ T) \u (fv_typ U)
  | dec_fld _ T   => (fv_typ T)
  | dec_mtd _ T U => (fv_typ T) \u (fv_typ U)
  end.

(* Since we define defs ourselves instead of using [list def], we don't have any
   termination proof problems: *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var x        => (fv_avar x)
  | trm_new ds       => (fv_defs ds)
  | trm_sel t l      => (fv_trm t)
  | trm_call t1 m t2 => (fv_trm t1) \u (fv_trm t2)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T U => (fv_typ T) \u (fv_typ U)
  | def_fld _ T x => (fv_typ T) \u (fv_avar x)
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
  | red_sel : forall s x y l T ds,
      binds x ds s ->
      defs_has ds (def_fld l T y) ->
      red (trm_sel (trm_var (avar_f x)) l) s
          (trm_var y) s
  | red_call : forall s x y m ds T U body,
      binds x ds s ->
      defs_has ds (def_mtd m T U body) ->
      red (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) s
          (open_trm y body) s
  | red_new : forall s ds x,
      x # s ->
      red (trm_new ds) s
          (trm_var (avar_f x)) (s & x ~ ds (*open_defs x ds*)) (* TODO enable self ref *)
  (* congruence rules *)
  | red_call1 : forall s o m a s' o',
      red o s o' s' ->
      red (trm_call o  m a) s
          (trm_call o' m a) s'
  | red_call2 : forall s x m a s' a',
      red a s a' s' ->
      red (trm_call (trm_var (avar_f x)) m a ) s
          (trm_call (trm_var (avar_f x)) m a') s'
  | red_sel1 : forall s o l s' o',
      red o s o' s' ->
      red (trm_sel o  l) s
          (trm_sel o' l) s'.


(* ###################################################################### *)
(** ** Typing *)

Definition pth2trm(p: pth): trm := match p with
  | pth_var a => trm_var a
end.

Reserved Notation "D1 && D2 == D3" (at level 40).
Reserved Notation "D1 || D2 == D3" (at level 40).

(* Not defined as a function because it's not total: Only defined if same kind of dec
   and same label. *)
Inductive intersect_dec: dec -> dec -> dec -> Prop :=
| intersect_dec_typ: forall L (T1 U1 T2 U2: typ),
    (dec_typ L T1 U1) && (dec_typ L T2 U2) == (dec_typ L (typ_or T1 T2) (typ_and U1 U2))
| intersect_dec_fld: forall l T1 T2,
    (dec_fld l T1) && (dec_fld l T2) == (dec_fld l (typ_and T1 T2))
| intersect_dec_mtd: forall m T1 U1 T2 U2,
    (dec_mtd m T1 U1) && (dec_mtd m T2 U2) == (dec_mtd m (typ_or T1 T2) (typ_and U1 U2))
where "D1 && D2 == D3" := (intersect_dec D1 D2 D3).

Inductive union_dec: dec -> dec -> dec -> Prop :=
| union_dec_typ: forall L T1 U1 T2 U2,
    (dec_typ L T1 U1) || (dec_typ L T2 U2) == (dec_typ L (typ_and T1 T2) (typ_or U1 U2))
| union_dec_fld: forall l T1 T2,
    (dec_fld l T1) || (dec_fld l T2) == (dec_fld l (typ_or T1 T2))
| union_dec_mtd: forall m T1 U1 T2 U2,
    (dec_mtd m T1 U1) || (dec_mtd m T2 U2) == (dec_mtd m (typ_and T1 T2) (typ_or U1 U2))
where "D1 || D2 == D3" := (union_dec D1 D2 D3).

(* on paper: G |- T ∍z D
   in Coq: "has" returns a dec without opening it
   but in lambda-DOT, there are no self-references anyways *)
Inductive typ_has: ctx -> typ -> dec -> Prop :=
(*| typ_top_has: typ_top has nothing *)
(*| typ_bot_has: in subdec_typ, we require that Lo2 <: Lo1 <: Hi1 <: Hi2,
      so the dec_typ that typ_bot could have, i.e.
      (dec_typ typ_top typ_bot) is not a subdec of anything, so better say
      typ_bot has no members!
      But now that we're always imprecise, we can say that typ_bot not only
      has (dec_typ typ_top typ_bot), but *any* dec, and then use subdec_refl
      to say that it's a subdec of itself. *)
  | typ_bot_has: forall G D, typ_has G typ_bot D
  | typ_rcd_has: forall G D,
      typ_has G (typ_rcd D) D
  | typ_sel_has: forall G p T L Lo Hi D,
      ty_trm G (pth2trm p) T ->
      typ_has G T (dec_typ L Lo Hi) ->
      (* This subtype check will hopefully make proofs easier, but
         does it restrict the expressiveness of the language?
      subtyp G Lo Hi -> *)
      typ_has G Hi D ->
      typ_has G (typ_sel p L) D
  | typ_and_has_1: forall G T1 T2 D,
      typ_has G T1 D ->
      typ_has G (typ_and T1 T2) D
  | typ_and_has_2: forall G T1 T2 D,
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
with subtyp: ctx -> typ -> typ -> Prop :=
  | subtyp_refl: forall G T,
      subtyp G T T
  | subtyp_top: forall G T,
      subtyp G T typ_top
  | subtyp_bot: forall G T,
      subtyp G typ_bot T
  | subtyp_rcd: forall G D1 D2,
      subdec G D1 D2 ->
      subtyp G (typ_rcd D1) (typ_rcd D2)
  | subtyp_sel_l: forall G p X L S U T,
      ty_trm G (pth2trm p) X ->
      typ_has G X (dec_typ L S U) ->
      (*subtyp G S U -> <--- not needed because if U has D, then p.L has D as well *)
      subtyp G U T ->
      subtyp G (typ_sel p L) T
  | subtyp_sel_r: forall G p X L S U T,
      ty_trm G (pth2trm p) X ->
      typ_has G X (dec_typ L S U) ->
      subtyp G S U -> (* <--- makes proofs a lot easier!! *)
      subtyp G T S ->
      subtyp G T (typ_sel p L)
  | subtyp_and: forall G S T1 T2,
      subtyp G S T1 ->
      subtyp G S T2 ->
      subtyp G S (typ_and T1 T2)
  | subtyp_and_l: forall G T1 T2 S,
      subtyp G T1 S ->
      subtyp G (typ_and T1 T2) S
  | subtyp_and_r: forall G T1 T2 S,
      subtyp G T2 S ->
      subtyp G (typ_and T1 T2) S
  | subtyp_or: forall G T1 T2 S,
      subtyp G T1 S ->
      subtyp G T2 S ->
      subtyp G (typ_or T1 T2) S
  | subtyp_or_l: forall G S T1 T2,
      subtyp G S T1 ->
      subtyp G S (typ_or T1 T2)
  | subtyp_or_r: forall G S T1 T2,
      subtyp G S T2 ->
      subtyp G S (typ_or T1 T2)
  | subtyp_trans: forall G T1 T2 T3,
      subtyp G T1 T2 ->
      subtyp G T2 T3 ->
      subtyp G T1 T3
with subdec: ctx -> dec -> dec -> Prop :=
  | subdec_typ: forall G L Lo1 Hi1 Lo2 Hi2,
      (* Lo2 <: Lo1 <: Hi1 <: Hi2 *)
      subtyp G Lo2 Lo1 ->
      subtyp G Lo1 Hi1 ->
      subtyp G Hi1 Hi2 ->
      subdec G (dec_typ L Lo1 Hi1) (dec_typ L Lo2 Hi2)
  | subdec_fld: forall G l T1 T2,
      subtyp G T1 T2 ->
      subdec G (dec_fld l T1) (dec_fld l T2)
  | subdec_mtd: forall G m S1 T1 S2 T2,
      subtyp G S2 S1 ->
      subtyp G T1 T2 ->
      subdec G (dec_mtd m S1 T1) (dec_mtd m S2 T2)
  | subdec_refl: forall G D,
      subdec G D D
with ty_trm: ctx -> trm -> typ -> Prop :=
  | ty_var: forall G x T,
      binds x T G ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_sel: forall G t T l U,
      ty_trm G t T ->
      typ_has G T (dec_fld l U) ->
      ty_trm G (trm_sel t l) U
  | ty_call: forall G t T m U V u,
      ty_trm G t T ->
      typ_has G T (dec_mtd m U V) ->
      ty_trm G u U ->
      ty_trm G (trm_call t m u) V
  | ty_new: forall G ds T, (* TODO enable self reference *)
      ty_defs G ds T ->
      ty_trm G (trm_new ds) T
  | ty_sbsm: forall G t T U,
      ty_trm G t T ->
      subtyp G T U ->
      ty_trm G t U
with ty_def: ctx -> def -> dec -> Prop :=
  | ty_typ: forall G L S T,
      subtyp G S T -> (* <----- only allow realizable bounds *)
      ty_def G (def_typ L S T) (dec_typ L S T)
  | ty_fld: forall G l v T,
      ty_trm G (trm_var v) T ->
      ty_def G (def_fld l T v) (dec_fld l T)
  | ty_mtd: forall L m G S T t,
      (forall x, x \notin L -> ty_trm (G & x ~ S) (open_trm x t) T) ->
      ty_def G (def_mtd m S T t) (dec_mtd m S T)
with ty_defs: ctx -> defs -> typ -> Prop :=
  | ty_defs_nil: forall G,
      ty_defs G defs_nil typ_top
  | ty_defs_cons: forall G ds d T D,
      ty_defs G ds T ->
      ty_def G d D ->
      can_add G ds d ->
      ty_defs G (defs_cons ds d) (typ_and T (typ_rcd D))
with can_add: ctx -> defs -> def -> Prop :=
  | can_add_typ: forall G ds L Lo Hi,
      defs_hasnt ds (label_typ L) ->
      subtyp G Lo Hi ->
      can_add G ds (def_typ L Lo Hi)
  | can_refine_typ: forall G ds L Lo1 Hi1 Lo2 Hi2,
      defs_has ds (def_typ L Lo1 Hi1) ->
      (* added dec must have good bounds: *)
      subtyp G Lo2 Hi2 ->
      (* and if intersected with existing bounds, still good: *)
      subtyp G Lo1 Hi2 ->
      subtyp G Lo2 Hi1 ->
      can_add G ds (def_typ L Lo2 Hi2)
  | can_add_fld: forall G ds l T x,
      defs_hasnt ds (label_fld l) ->
      can_add G ds (def_fld l T x)
  | can_add_mtd: forall G ds m T1 T2 t,
      defs_hasnt ds (label_mtd m) ->
      can_add G ds (def_mtd m T1 T2 t).

(** *** Well-formed store *)
Inductive wf_sto: sto -> ctx -> Prop :=
  | wf_sto_empty : wf_sto empty empty
  | wf_sto_push : forall s G x ds T,
      wf_sto s G ->
      x # s ->
      x # G ->
      (* In lambda-DOT, ds may not use a self reference, so it's "G" and not "G & z ~ T" *)
      ty_defs G ds T ->
      (* No need to check if realizable bounds, because that's already done by ty_def *)
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
  (exists G', wf_sto s' G' /\ ty_trm G' e' T).


(* ###################################################################### *)
(* ###################################################################### *)
(** * Infrastructure *)

(* ###################################################################### *)
(** ** Induction principles *)

Scheme trm_mut  := Induction for trm  Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, def_mut, defs_mut.

Scheme typ_mut  := Induction for typ  Sort Prop
with   dec_mut  := Induction for dec  Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut.

Scheme typ_has_mut := Induction for typ_has Sort Prop
with   subtyp_mut  := Induction for subtyp  Sort Prop
with   subdec_mut  := Induction for subdec  Sort Prop
with   ty_trm_mut  := Induction for ty_trm  Sort Prop
with   ty_def_mut  := Induction for ty_def  Sort Prop
with   ty_defs_mut := Induction for ty_defs Sort Prop
with   can_add_mut := Induction for can_add Sort Prop.
Combined Scheme ty_mutind from typ_has_mut,
                               subtyp_mut, subdec_mut,
                               ty_trm_mut, ty_def_mut, ty_defs_mut, can_add_mut.

Scheme subtyp_mut2  := Induction for subtyp  Sort Prop
with   subdec_mut2  := Induction for subdec  Sort Prop.
Combined Scheme subtyp_subdec_mut from subtyp_mut2, subdec_mut2.


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
  let J := gather_vars_with (fun x : dec       => fv_dec   x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors typ_has subtyp subdec ty_trm ty_def ty_defs can_add.
Hint Constructors defs_has defs_hasnt.

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.


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

Definition subst_pth (z: var) (u: var) (p: pth) : pth :=
  match p with
  | pth_var a => pth_var (subst_avar z u a)
  end.

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top     => typ_top
  | typ_bot     => typ_bot
  | typ_rcd D   => typ_rcd (subst_dec z u D)
  | typ_sel p L => typ_sel (subst_pth z u p) L
  | typ_and T1 T2 => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_or  T1 T2 => typ_or  (subst_typ z u T1) (subst_typ z u T2)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_fld l T   => dec_fld l (subst_typ z u T)
  | dec_mtd m T U => dec_mtd m (subst_typ z u T) (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_new ds       => trm_new (subst_defs z u ds)
  | trm_sel t l      => trm_sel (subst_trm z u t) l
  | trm_call t1 m t2 => trm_call (subst_trm z u t1) m (subst_trm z u t2)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ L T1 T2   => def_typ L (subst_typ z u T1) (subst_typ z u T2)
  | def_fld l T x     => def_fld l (subst_typ z u T) (subst_avar z u x)
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

Lemma subst_fresh_pth: forall x y,
  (forall p: pth, x \notin fv_pth p -> subst_pth x y p = p).
Proof.
  intros. destruct p. simpl. f_equal. apply* subst_fresh_avar.
Qed.

Lemma subst_fresh_typ_dec_decs: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall d : dec , x \notin fv_dec  d  -> subst_dec  x y d  = d ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_pth.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec_decs x y).

Lemma subst_fresh_trm_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ_dec_decs).
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
    rewrite (subst_fresh_typ _ _ N1).
    reflexivity.
Qed.

Definition subst_fvar(x y z: var): var := If x = z then y else z.

Lemma subst_open_commute_avar: forall x y u,
  (forall a: avar, forall n: Datatypes.nat,
    subst_avar x y (open_rec_avar n u a) 
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

Lemma subst_open_commute_pth: forall x y u,
  (forall p: pth, forall n: Datatypes.nat,
    subst_pth x y (open_rec_pth n u p) 
    = open_rec_pth n (subst_fvar x y u) (subst_pth x y p)).
Proof.
  intros. unfold subst_pth, open_pth, open_rec_pth. destruct p.
  f_equal. apply subst_open_commute_avar.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec_decs: forall x y u,
  (forall t : typ, forall n: Datatypes.nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall d : dec , forall n: Datatypes.nat, 
     subst_dec x y (open_rec_dec n u d)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y d)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_pth.
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
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ_dec_decs).
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

Lemma subst_open_commute_typ: forall x y u T,
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T).
Proof.
  intros. apply* subst_open_commute_typ_dec_decs.
Qed.

Lemma subst_open_commute_dec: forall x y u D,
  subst_dec x y (open_dec u D) = open_dec (subst_fvar x y u) (subst_dec x y D).
Proof.
  intros. apply* subst_open_commute_typ_dec_decs.
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
  destruct (@subst_fresh_typ_dec_decs x u) as [Q _]. rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_dec: forall x u D, x \notin (fv_dec D) ->
  open_dec u D = subst_dec x u (open_dec x D).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_dec.
  destruct (@subst_fresh_typ_dec_decs x u) as [_ Q]. rewrite* (Q D).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_undo_avar: forall x y,
  (forall a, y \notin fv_avar a -> (subst_avar y x (subst_avar x y a)) = a).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + unfold fv_avar in H. assert (y <> v) by auto. repeat case_if; reflexivity.
Qed.

Lemma subst_undo_pth: forall x y,
  (forall p, y \notin fv_pth p -> (subst_pth y x (subst_pth x y p)) = p).
Proof.
  intros. destruct p. unfold subst_pth. f_equal.
  unfold fv_pth in H.
  apply* subst_undo_avar.
Qed.

Lemma subst_undo_typ_dec_decs: forall x y,
   (forall T , y \notin fv_typ  T  -> (subst_typ  y x (subst_typ  x y T )) = T )
/\ (forall D , y \notin fv_dec  D  -> (subst_dec  y x (subst_dec  x y D )) = D ).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*.
  apply* subst_undo_pth.
Qed.

Lemma subst_undo_trm_def_defs: forall x y,
   (forall t , y \notin fv_trm  t  -> (subst_trm  y x (subst_trm  x y t )) = t )
/\ (forall d , y \notin fv_def  d  -> (subst_def  y x (subst_def  x y d )) = d )
/\ (forall ds, y \notin fv_defs ds -> (subst_defs y x (subst_defs x y ds)) = ds).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_def, fv_defs in *; f_equal*;
    (apply* subst_undo_avar || apply* subst_undo_typ_dec_decs).
Qed.

Lemma subst_typ_undo: forall x y T,
  y \notin fv_typ T -> (subst_typ y x (subst_typ x y T)) = T.
Proof.
  apply* subst_undo_typ_dec_decs.
Qed.

Lemma subst_dec_undo: forall x y D,
  y \notin fv_dec D -> (subst_dec y x (subst_dec x y D)) = D.
Proof.
  apply* subst_undo_typ_dec_decs.
Qed.

Lemma subst_trm_undo: forall x y t,
  y \notin fv_trm t -> (subst_trm y x (subst_trm x y t)) = t.
Proof.
  apply* subst_undo_trm_def_defs.
Qed.


(* ###################################################################### *)
(** ** Trivial inversion lemmas *)

Lemma invert_subdec_typ_sync_right: forall G D2 L Lo1 Hi1,
  subdec G (dec_typ L Lo1 Hi1) D2 ->
  (dec_typ L Lo1 Hi1) = D2 \/
  exists Lo2 Hi2, D2 = (dec_typ L Lo2 Hi2) /\
                  subtyp G Lo2 Lo1 /\
                  subtyp G Lo1 Hi1 /\
                  subtyp G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd.
  - right. exists Lo2 Hi2. auto.
  - left. reflexivity.
Qed.

Lemma invert_subdec_typ_sync_left: forall G D1 L Lo2 Hi2,
   subdec G D1 (dec_typ L Lo2 Hi2) ->
   D1 = (dec_typ L Lo2 Hi2) \/
   exists Lo1 Hi1, D1 = (dec_typ L Lo1 Hi1) /\
                   subtyp G Lo2 Lo1 /\
                   subtyp G Lo1 Hi1 /\
                   subtyp G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd.
  - right. exists Lo1 Hi1. auto.
  - auto.
Qed.

Lemma invert_subdec_fld_sync_left: forall G D l T2,
   subdec G D (dec_fld l T2) ->
   D = (dec_fld l T2) \/
   exists T1, D = (dec_fld l T1) /\
              subtyp G T1 T2.
Proof.
  introv Sd. inversions Sd.
  - right. exists T1. auto.
  - auto.
Qed.

Lemma invert_subdec_mtd_sync_left: forall G D m T2 U2,
   subdec G D (dec_mtd m T2 U2) ->
   D = (dec_mtd m T2 U2) \/
   exists T1 U1, D = (dec_mtd m T1 U1) /\
                 subtyp G T2 T1 /\
                 subtyp G U1 U2.
Proof.
  introv Sd. inversions Sd.
  - right. exists S1 T1. auto.
  - auto.
Qed.

Lemma invert_ty_defs_cons: forall G ds0 T1 T2,
  ty_defs G ds0 (typ_and T1 T2) ->
  exists d ds D, ds0 = defs_cons ds d /\
                 ty_defs G ds T1 /\
                 T2 = typ_rcd D /\
                 ty_def G d D.
Proof.
  introv H. inversions H. exists d ds D. auto.
Qed.

Lemma wf_sto_to_ok_s: forall s G,
  wf_sto s G -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto s G -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

Lemma ctx_binds_to_sto_binds: forall s G x T,
  wf_sto s G ->
  binds x T G ->
  exists o, binds x o s.
Proof.
  introv Wf Bi. gen x T Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - eauto.
    - eauto.
Qed.

Lemma sto_binds_to_ctx_binds: forall s G x ds,
  wf_sto s G ->
  binds x ds s ->
  exists T, binds x T G.
Proof.
  introv Wf Bi. gen x Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. exists T. reflexivity.
    - auto.
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

Lemma invert_ty_var: forall G x T,
  ty_trm G (trm_var (avar_f x)) T ->
  exists T', subtyp G T' T /\ binds x T' G.
Proof.
  introv Ty. gen_eq t: (trm_var (avar_f x)). gen x.
  induction Ty; intros x' Eq; try (solve [ discriminate ]).
  + inversions Eq. exists T.
    apply (conj (subtyp_refl _ _)). assumption.
  + subst. specialize (IHTy _ eq_refl). destruct IHTy as [T' [St Bi]].
    exists T'. split.
    - apply subtyp_trans with T.
      * apply St.
      * apply H.
    - apply Bi.
Qed.


(* ###################################################################### *)
(** ** Weakening *)

Lemma weakening:
   (forall G T D, typ_has G T D -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      typ_has (G1 & G2 & G3) T D)
/\ (forall G T1 T2, subtyp G T1 T2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subtyp (G1 & G2 & G3) T1 T2)
/\ (forall G D1 D2, subdec G D1 D2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdec (G1 & G2 & G3) D1 D2)
/\ (forall G t T, ty_trm G t T -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      ty_trm (G1 & G2 & G3) t T)
/\ (forall G d D, ty_def G d D -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      ty_def (G1 & G2 & G3) d D)
/\ (forall G ds Ds, ty_defs G ds Ds -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      ty_defs (G1 & G2 & G3) ds Ds)
/\ (forall G ds d, can_add G ds d -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      can_add (G1 & G2 & G3) ds d).
Proof.
  apply ty_mutind.
  + (* case typ_bot_has *)
    intros. apply typ_bot_has.
  + (* case typ_rcd_has *)
    intros. apply* typ_rcd_has.
  + (* case typ_sel_has *)
    intros. apply* typ_sel_has.
  + (* case typ_and_has_1 *)
    intros. apply* typ_and_has_1.
  + (* case typ_and_has_2 *)
    intros. apply* typ_and_has_2.
  + (* case typ_and_has_12 *)
    intros. apply* typ_and_has_12.
  + (* case typ_or_has *)
    intros. apply* typ_or_has.
  + (* case subtyp_refl *)
    intros. apply subtyp_refl.
  + (* case subtyp_top *)
    intros. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. apply subtyp_bot.
  + (* case subtyp_rcd *)
    intros. apply* subtyp_rcd.
  + (* case subtyp_sel_l *)
    intros. subst. apply* subtyp_sel_l.
  + (* case subtyp_sel_r *)
    intros. subst. apply* subtyp_sel_r.
  + (* case subtyp_and *)
    intros. apply* subtyp_and.
  + (* case subtyp_and_l *)
    intros. apply* subtyp_and_l.
  + (* case subtyp_and_r *)
    intros. apply* subtyp_and_r.
  + (* case subtyp_or *)
    intros. apply* subtyp_or.
  + (* case subtyp_or_l *)
    intros. apply* subtyp_or_l.
  + (* case subtyp_or_r *)
    intros. apply* subtyp_or_r.
  + (* case subtyp_trans *)
    intros. subst. apply* subtyp_trans.
  + (* case subdec_typ *)
    intros. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. apply* subdec_mtd.
  + (* case subdec_refl *)
    intros. apply* subdec_refl.
  + (* case ty_var *)
    intros. subst. apply ty_var. apply* binds_weaken.
  + (* case ty_sel *)
    intros. subst. apply* ty_sel.
  + (* case ty_call *)
    intros. subst. apply* ty_call.
  + (* case ty_new *)
    intros G ds T Tyds IHTyds G1 G2 G3 Eq Ok. subst. apply* ty_new.
  + (* case ty_sbsm *)
    intros. apply ty_sbsm with T.
    - apply* H.
    - apply* H0.
  + (* case ty_typ *)
    intros. apply* ty_typ. 
  + (* case ty_fld *)
    intros. apply* ty_fld.
  + (* case ty_mtd *) 
    intros. subst. rename H into IH.
    apply_fresh ty_mtd as x.
    rewrite <- concat_assoc.
    refine (IH x _ G1 G2 (G3 & x ~ S) _ _).
    - auto.
    - symmetry. apply concat_assoc.
    - rewrite concat_assoc. auto.
  + (* case ty_dsnil *) 
    intros. apply ty_defs_nil.
  + (* case ty_dscons *) 
    intros. apply* ty_defs_cons.
  + (* case can_add_typ *)
    intros. apply* can_add_typ.
  + (* case can_refine_typ *)
    intros. apply* can_refine_typ.
  + (* case can_add_fld *)
    intros. apply* can_add_fld.
  + (* case can_add_mtd *)
    intros. apply* can_add_mtd.
Qed.

Lemma weaken_subtyp_middle: forall G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp (G1      & G3) S U ->
  subtyp (G1 & G2 & G3) S U.
Proof.
  destruct weakening as [_ [W _]].
  introv Hok123 Hst.
  specialize (W (G1 & G3) S U Hst).
  specialize (W G1 G2 G3 eq_refl Hok123).
  apply W.
Qed.

Lemma env_add_empty: forall (P: ctx -> Prop) (G: ctx), P G -> P (G & empty).
Proof.
  intros.
  assert ((G & empty) = G) by apply concat_empty_r.
  rewrite -> H0. assumption.
Qed.  

Lemma env_remove_empty: forall (P: ctx -> Prop) (G: ctx), P (G & empty) -> P G.
Proof.
  intros.
  assert ((G & empty) = G) by apply concat_empty_r.
  rewrite <- H0. assumption.
Qed.

Lemma weaken_subtyp_end: forall G1 G2 S U,
  ok (G1 & G2) -> 
  subtyp G1        S U ->
  subtyp (G1 & G2) S U.
Proof.
  introv Hok Hst.
  apply (env_remove_empty (fun G0 => subtyp G0 S U) (G1 & G2)).
  apply weaken_subtyp_middle.
  apply (env_add_empty (fun G0 => ok G0) (G1 & G2) Hok).
  apply (env_add_empty (fun G0 => subtyp G0 S U) G1 Hst).
Qed.

Lemma weaken_subdec_middle: forall G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subdec (G1      & G3) S U ->
  subdec (G1 & G2 & G3) S U.
Proof.
  destruct weakening as [_ [_ [W _]]].
  introv Hok123 Hst.
  specialize (W (G1 & G3) S U Hst).
  specialize (W G1 G2 G3 eq_refl Hok123).
  apply W.
Qed.

Lemma weaken_subdec_end: forall G1 G2 D1 D2,
  ok (G1 & G2) -> 
  subdec G1        D1 D2 ->
  subdec (G1 & G2) D1 D2.
Proof.
  introv Ok Sd.
  destruct weakening as [_ [_ [W _]]].
  rewrite <- (concat_empty_r G1) in Sd.
  specialize (W (G1 & empty) D1 D2 Sd G1 G2 empty).
  repeat progress rewrite concat_empty_r in *.
  apply (W eq_refl Ok).
Qed.

Lemma weaken_ty_trm_end: forall G1 G2 e T,
  ok (G1 & G2) -> ty_trm G1 e T -> ty_trm (G1 & G2) e T.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [W _]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_defs_end: forall G1 G2 is Ds,
  ok (G1 & G2) -> ty_defs G1 is Ds -> ty_defs (G1 & G2) is Ds.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [_ [W _]]]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_trm_middle: forall G1 G2 G3 t T,
  ok (G1 & G2 & G3) -> ty_trm (G1 & G3) t T -> ty_trm (G1 & G2 & G3) t T.
Proof.
  intros. apply* weakening.
Qed.


(* ###################################################################### *)
(** ** Misc *)

Definition ctx_size(G: ctx) := LibList.length G.

Lemma ctx_size_zero_inv: forall G, ctx_size G = 0 -> G = empty.
Proof.
  rewrite empty_def.
  apply LibList.length_zero_inv.
Qed.

Lemma vars_dont_type_in_empty_env: forall G t T,
  ty_trm G t T ->
  forall x, t = (trm_var (avar_f x)) ->
  G = empty ->
  False.
Proof.
  introv Ty. induction Ty; try discriminate; intros x' Eq1 Eq2; inversions Eq1.
  + (* case ty_var *)
    apply (binds_empty_inv H).
  + (* case ty_sbsm *)
    inversions H0. apply* IHTy.
Qed.


(* ###################################################################### *)
(** ** More inversion lemmas *)

Lemma invert_wf_sto: forall s G,
  wf_sto s G ->
  forall x T2,
  ty_trm G (trm_var (avar_f x)) T2 ->
  exists ds G1 G2 T1,
    G = G1 & x ~ T1 & G2 /\ 
    ty_defs G1 ds T1.
Proof.
  intros s G Wf. induction Wf; intros.
  + exfalso. apply (vars_dont_type_in_empty_env H eq_refl eq_refl).
  + rename T into X, H2 into Tyy, x0 into y, T2 into Y2.
    apply invert_ty_var in Tyy. destruct Tyy as [Y1 [St BiG]].
    unfold binds in BiG. rewrite get_push in BiG.
    case_if.
    - inversions BiG.
      exists ds G (@empty typ) Y1. rewrite concat_empty_r.
      apply (conj eq_refl H1).
    - specialize (IHWf y Y1 (ty_var BiG)).
      destruct IHWf as [dsY [G1 [G2 [Y' [EqG TydsY]]]]]. subst.
      lets Eq: (binds_middle_eq_inv BiG (wf_sto_to_ok_G Wf)). subst Y'.
      exists dsY G1 (G2 & x ~ X) Y1.
      rewrite concat_assoc.
      apply (conj eq_refl TydsY).
Qed.

Lemma invert_wf_sto_old: forall s G,
  wf_sto s G ->
    forall x ds T,
      binds x ds s -> 
      binds x T G ->
      exists G1 G2,
        G = G1 & x ~ T & G2 /\ 
        ty_defs G ds T.
Proof.
  intros s G Wf. induction Wf; intros.
  + false* binds_empty_inv.
  + unfold binds in *. rewrite get_push in *.
    case_if.
    - inversions H2. inversions H3.
      exists G (@empty typ). rewrite concat_empty_r.
      apply (conj eq_refl).
      lets Ok: (wf_sto_to_ok_G Wf).
      refine (weaken_ty_defs_end _ H1). auto.
    - specialize (IHWf x0 ds0 T0 H2 H3).
      destruct IHWf as [G1 [G2 [EqG Ty]]]. subst.
      exists G1 (G2 & x ~ T).
      rewrite concat_assoc.
      apply (conj eq_refl).
      apply weaken_ty_defs_end.
      * apply wf_sto_to_ok_G in Wf. auto.
      * exact Ty.
Qed.

Lemma invert_wf_sto_with_sbsm: forall s G,
  wf_sto s G ->
  forall x ds T2, 
    binds x ds s ->
    ty_trm G (trm_var (avar_f x)) T2 -> (* <- instead of binds *)
    exists T1, subtyp G T1 T2
            /\ ty_defs G ds T1.
Proof.
  introv Wf Bis Tyx.
  apply invert_ty_var in Tyx. destruct Tyx as [T' [St BiG]].
  destruct (invert_wf_sto_old Wf Bis BiG) as [G1 [G2 [Eq Tyds]]].
  subst. exists T'.
  lets Ok: (wf_sto_to_ok_G Wf).
  apply (conj St).
  auto.
Qed.

Lemma invert_wf_sto_without_binds: forall s G x T2,
  wf_sto s G ->
  ty_trm G (trm_var (avar_f x)) T2 ->
  exists T1 ds,
    ty_defs G ds T1 /\
    subtyp G T1 T2 /\
    binds x T1 G /\
    binds x ds s.
Proof.
  introv Wf Ty.
  apply invert_ty_var in Ty. destruct Ty as [T1 [St BiG]].
  lets Bis: (ctx_binds_to_sto_binds Wf BiG). destruct Bis as [ds Bis].
  lets P: (invert_wf_sto_old Wf Bis BiG). destruct P as [G1 [G2 [Eq Tyds]]].
  exists T1 ds. apply (conj Tyds). apply (conj St). apply (conj BiG Bis).
Qed.



(* ###################################################################### *)
(** ** Soundness helper lemmas *)

(* Hyptheses:  X1 ----subtyp----> X2 ----typ_has---> D2
   Conclusion: X1 ----typ_has---> D1 ----subdec----> D1
In the system which used expansion instead of typ_has, this didn't work,
because we were not sure if X1 had an expansion or not. *)
Definition swap_sub_and_has_until(n: nat) := forall s G x X1 X2 D2,
  subtyp G X1 X2 ->
  typ_has G X2 D2 ->
  ctx_size G <= n ->
  wf_sto s G ->
  ty_trm G (trm_var (avar_f x)) X1 -> (* <-- witnesses realizability of X1 *)
  exists D1,
    typ_has G X1 D1 /\
    subdec G D1 D2.

Lemma swap_sub_and_has_base: swap_sub_and_has_until 0.
Proof.
  introv St THas Eq' Wf Ty. assert (Eq: ctx_size G = 0) by omega.
   apply ctx_size_zero_inv in Eq. subst.
  exfalso. apply (@vars_dont_type_in_empty_env _ _ _ Ty x eq_refl eq_refl).
Qed.

(* "widens G T1 T2" means that "G |- T1 <: T2" and T2 does not contain path types,
    and T2 is the smallest such type.
Inductive widens: ctx -> typ -> typ -> Prop :=
| widens_top: forall G,
    widens G typ_top typ_top
| widens_bot: forall G,
    widens G typ_bot typ_bot
|*)

(* "no_path_types T" means that T contains no path types (but T's members can) *)
Inductive no_path_types: typ -> Prop :=
| no_path_types_top: no_path_types typ_top
| no_path_types_bot: no_path_types typ_bot
| no_path_types_rcd: forall D, no_path_types (typ_rcd D)
| no_path_types_and: forall T1 T2,
    no_path_types T1 -> no_path_types T2 -> no_path_types (typ_and T1 T2)
| no_path_types_or: forall T1 T2,
    no_path_types T1 -> no_path_types T2 -> no_path_types (typ_or T1 T2).

Inductive is_bot: ctx -> typ -> Prop :=
| is_bot_bot: forall G, is_bot G typ_bot
| is_bot_sel: forall G p T L Lo Hi,
     ty_trm G (pth2trm p) T ->
     typ_has G T (dec_typ L Lo Hi) ->
     is_bot G Hi ->
     is_bot G (typ_sel p L)
| is_bot_and_l: forall G T1 T2, is_bot G T1 -> is_bot G (typ_and T1 T2)
| is_bot_and_r: forall G T1 T2, is_bot G T2 -> is_bot G (typ_and T1 T2)
| is_bot_or: forall G T1 T2, is_bot G T1 -> is_bot G T2 -> is_bot G (typ_or T1 T2).

Module V3.

Lemma subtyp_preserves_is_bot: forall G T1 T2,
  subtyp G T1 T2 ->
  is_bot G T2 ->
  is_bot G T1.
Proof.
  introv St. induction St; intros Ib.
  + (* case subtyp_refl *)
    assumption.
  + (* case subtyp_top *)
    inversions Ib.
  + (* case subtyp_bot *)
    apply is_bot_bot.
  + (* case subtyp_rcd *)
    inversions Ib.
  + (* case subtyp_sel_l *)
    apply (is_bot_sel _ H H0). apply (IHSt Ib).
  + (* case subtyp_sel_r *)
    inversions Ib. apply IHSt2. apply IHSt1. admit. (* TODO imprecision!!!*)
  + (* case subtyp_and *)
    inversions Ib; auto.
  + (* case subtyp_and_l *)
    apply is_bot_and_l. apply* IHSt.
  + (* case subtyp_and_r *)
    apply is_bot_and_r. apply* IHSt.
  + (* case subtyp_or *)
    apply is_bot_or; auto.
  + (* case subtyp_or_l *)
    inversions Ib; auto.
  + (* case subtyp_or_r *)
    inversions Ib; auto.
  + (* case subtyp_trans *)
    apply IHSt1. apply IHSt2. exact Ib.
Qed.

End V3.

Module V2.

Inductive is_bot: typ -> Prop :=
| is_bot_bot: is_bot typ_bot
| is_bot_and_l: forall T1 T2, is_bot T1 -> is_bot (typ_and T1 T2)
| is_bot_and_r: forall T1 T2, is_bot T2 -> is_bot (typ_and T1 T2)
| is_bot_or: forall T1 T2, is_bot T1 -> is_bot T2 -> is_bot (typ_or T1 T2).

Lemma subtyp_preserves_is_bot: forall G T1 T2,
  subtyp G T1 T2 ->
  is_bot T2 ->
  (*no_path_types T1 ->*)
  is_bot T1.
Proof.
  introv St. induction St; intros Ib (* N*).
  + (* case subtyp_refl *)
    assumption.
  + (* case subtyp_top *)
    inversions Ib.
  + (* case subtyp_bot *)
    apply is_bot_bot.
  + (* case subtyp_rcd *)
    inversions Ib.
  + (* case subtyp_sel_l *)
    admit. (*inversions N. TODO............*)
  + (* case subtyp_sel_r *)
    inversions Ib.
  + (* case subtyp_and *)
    inversions Ib; auto.
  + (* case subtyp_and_l *)
    apply is_bot_and_l. apply* IHSt.
  + (* case subtyp_and_r *)
    apply is_bot_and_r. apply* IHSt.
  + (* case subtyp_or *)
    apply is_bot_or; auto.
  + (* case subtyp_or_l *)
    inversions Ib; auto.
  + (* case subtyp_or_r *)
    inversions Ib; auto.
  + (* case subtyp_trans *)
    apply IHSt1. apply IHSt2. exact Ib.
Qed.

End V2.

Definition subtyp_preserves_is_bot_for(n: nat) := forall s G T1 T2,
  ctx_size G = n ->
  wf_sto s G ->
  subtyp G T1 T2 ->
  is_bot G T2 ->
  is_bot G T1.

Lemma pth_is_var: forall p, exists x, p = (pth_var (avar_f x)).
Proof.
  intro p. destruct p as [v]. destruct v as [n | x].
  - admit. (* bound var not possible... TODO need closed-ness hypothesis for this *)
  - exists x. reflexivity.
Qed.

Lemma subtyp_preserves_is_bot_base: subtyp_preserves_is_bot_for 0.
Admitted.

Lemma subtyp_preserves_is_bot_step: forall n,
  (forall k, k <= n -> subtyp_preserves_is_bot_for k) ->
 subtyp_preserves_is_bot_for (S n).
Proof.
  intros n IH. unfold subtyp_preserves_is_bot_for in *.
  introv Eq Wf St Ib. induction St.
  + (* case subtyp_refl *)
    exact Ib.
  + (* case subtyp_top *)
    inversions Ib.
  + (* case subtyp_bot *)
    apply is_bot_bot.
  + (* case subtyp_rcd *)
    inversions Ib.
  + (* case subtyp_sel_l *)
    apply (is_bot_sel _ H H0). apply* IHSt.
  + (* case subtyp_sel_r *)
    rename H into Ty, H0 into XHas, S into Lo0, U into Hi0.
    inversions Ib.
    (* Problem: imprecision! To apply IHSt1 and IHSt2, we would need "is_bot G Hi0",
       but we only have it for Hi. So throw away these IHs. *)
    clear Lo0 Hi0 X Ty XHas St1 St2 IHSt1 IHSt2.
    destruct (pth_is_var p) as [x Eqx]. rewrite Eqx in *. clear Eqx p.
    rename T0 into X2, H1 into Tyx, H3 into XHas, H4 into Ib. simpl in Tyx.
    lets P: (invert_wf_sto Wf Tyx).
    destruct P as [ds [G1 [G2 [X1 [EqG Tyds]]]]].
    (* The plan was to apply IH on "Lo <: Hi", which should hold in a smaller env,
       but that would only be the case if L:Lo..Hi was the precise dec in x!
       So we need swap_sub_and_has_step, but can't use it because we're a helper for it. *)
    admit.
  + (* case subtyp_and *)
    admit.
  + (* case subtyp_and_l *)
    admit.
  + (* case subtyp_and_r *)
    admit.
  + (* case subtyp_or *)
    admit.
  + (* case subtyp_or_l *)
    admit.
  + (* case subtyp_or_r *)
    admit.
  + (* case subtyp_trans *)
    admit.

Qed.

Theorem strong_induction: forall P: nat -> Prop,
  P 0 ->
  (forall n: nat, (forall k: nat, k <= n -> P k) -> P (S n)) ->
  forall n: nat, P n.
Proof.
  intros P Base Step n. assert (forall k, k <= n -> P k). {
    induction n.
    + intros. assert (k = 0) by omega. subst. exact Base.
    + intros k Leq. assert (C: k = S n \/ k <= n) by omega.
      destruct C as [C | C].
      - subst. apply Step. exact IHn.
      - apply IHn. exact C.
  }
  apply H. omega.
Qed.

Lemma subtyp_preserves_is_bot: forall G s T1 T2,
  wf_sto s G ->
  subtyp G T1 T2 ->
  is_bot G T2 ->
  is_bot G T1.
Proof.
  intros G s T1 T2.
  lets P: (strong_induction _ subtyp_preserves_is_bot_base subtyp_preserves_is_bot_step).
  unfold subtyp_preserves_is_bot_for in P.
  apply (P (ctx_size G) s G T1 T2 eq_refl).
Qed.

(*
Lemma subtyp_preserves_is_bot: forall G T1 T2,
  subtyp G T1 T2 ->
  is_bot G T2 ->
  is_bot G T1.
Proof.
  introv St. induction St; intros Ib.
  + (* case subtyp_refl *)
    assumption.
  + (* case subtyp_top *)
    inversions Ib.
  + (* case subtyp_bot *)
    apply is_bot_bot.
  + (* case subtyp_rcd *)
    inversions Ib.
  + (* case subtyp_sel_l *)
    apply (is_bot_sel _ H H0). apply (IHSt Ib).
  + (* case subtyp_sel_r *)
    inversions Ib. apply IHSt2. apply IHSt1. admit. (* TODO imprecision!!!*)
  + (* case subtyp_and *)
    inversions Ib; auto.
  + (* case subtyp_and_l *)
    apply is_bot_and_l. apply* IHSt.
  + (* case subtyp_and_r *)
    apply is_bot_and_r. apply* IHSt.
  + (* case subtyp_or *)
    apply is_bot_or; auto.
  + (* case subtyp_or_l *)
    inversions Ib; auto.
  + (* case subtyp_or_r *)
    inversions Ib; auto.
  + (* case subtyp_trans *)
    apply IHSt1. apply IHSt2. exact Ib.
Qed.
*)

Lemma type_of_defs_contains_no_path_types: forall G ds T,
  ty_defs G ds T -> no_path_types T.
Proof.
  introv Tyds. induction Tyds.
  + apply no_path_types_top.
  + apply no_path_types_and.
    - exact IHTyds.
    - apply no_path_types_rcd.
Qed.

(*
Lemma invert_no_path_type_subtyp_of_bot: forall G T,
  subtyp G T typ_bot ->
  no_path_types T ->
  is_bot T.
Proof.
  introv St. gen_eq T': typ_bot. induction St; intros Eq N; subst.
  + (* case subtyp_refl *)
    apply is_bot_bot.
  + (* case subtyp_top *)
    discriminate.
  + (* case subtyp_bot *)
    apply is_bot_bot.
  + (* case subtyp_rcd *)
    discriminate.
  + (* case subtyp_sel_l *)
    inversions N.
  + (* case subtyp_sel_r *)
    discriminate.
  + (* case subtyp_and *)
    discriminate.
  + (* case subtyp_and_l *)
    inversions N. apply is_bot_and_l. apply* IHSt.
  + (* case subtyp_and_r *)
    inversions N. apply is_bot_and_r. apply* IHSt.
  + (* case subtyp_or *)
    inversions N. apply is_bot_or; auto.
  + (* case subtyp_or_l *)
    discriminate.
  + (* case subtyp_or_r *)
    discriminate.
  + (* case subtyp_trans *)
    admit.
*)

Lemma defs_are_not_bot: forall G ds X1,
  subtyp G X1 typ_bot ->
  ty_defs G ds X1 ->
  False.
Proof.
  introv St. gen ds. gen_eq X2: typ_bot. induction St; intro Eq; subst.
  + (* case subtyp_refl *)
    introv Tyds. inversions Tyds.
  + (* case subtyp_top *)
    discriminate.
  + (* case subtyp_bot *)
    introv Tyds. inversions Tyds.
  + (* case subtyp_rcd *)
    discriminate.
  + (* case subtyp_sel_l *)
    introv Tyds. inversions Tyds. (* defs don't type as p.L *)
  + (* case subtyp_sel_r *)
    discriminate.
  + (* case subtyp_and *)
    discriminate.
  + (* case subtyp_and_l *)
    introv Tyds. apply invert_ty_defs_cons in Tyds. rename ds into ds0.
    destruct Tyds as [d [ds [D [Eq1 [Tyds [Eq2 Tyd]]]]]]. subst. apply* IHSt.
  + (* case subtyp_and_r *)
    introv Tyds. apply invert_ty_defs_cons in Tyds. rename ds into ds0.
    destruct Tyds as [d [ds [D [Eq1 [Tyds [Eq2 Tyd]]]]]]. subst.
    admit. (* TODO typ_rcd might be a subtype of typ_bot in an unrealizable env! *)
  + (* case subtyp_or *)
    introv Tyds. inversions Tyds.
  + (* case subtyp_or_l *)
    introv Tyds. discriminate.
  + (* case subtyp_or_r *)
    introv Tyds. discriminate.
  + (* case subtyp_trans *)
    introv Tyds. refine (IHSt1 _ _ Tyds). (* TODO might not hold!  *)
Abort.

Lemma defs_are_not_bot: forall s G ds T,
  ty_defs G ds T ->
  wf_sto s G ->
  is_bot G T ->
  False.
Proof.
  introv Tyds. induction Tyds; introv Wf Ib.
  - inversions Ib.
  - inversions Ib.
    + auto.
    + inversions H3.
Qed.

Lemma defs_are_not_bot_old: forall s G ds X1,
  subtyp G X1 typ_bot ->
  ty_defs G ds X1 ->
  wf_sto s G ->
(*
  binds x X1 G ->
  binds x ds s ->
*)
  False.
Proof.
  introv St. gen s ds. gen_eq X2: typ_bot. induction St; intro Eq; subst.
  + (* case subtyp_refl *)
    introv Tyds Wf. inversions Tyds.
  + (* case subtyp_top *)
    discriminate.
  + (* case subtyp_bot *)
    introv Tyds Wf. inversions Tyds.
  + (* case subtyp_rcd *)
    discriminate.
  + (* case subtyp_sel_l *)
    introv Tyds Wf. inversions Tyds. (* defs don't type as p.L *)
  + (* case subtyp_sel_r *)
    discriminate.
  + (* case subtyp_and *)
    discriminate.
  + (* case subtyp_and_l *)
    introv Tyds Wf. apply invert_ty_defs_cons in Tyds. rename ds into ds0.
    destruct Tyds as [d [ds [D [Eq1 [Tyds [Eq2 Tyd]]]]]]. subst. apply* IHSt.
  + (* case subtyp_and_r *)
    introv Tyds Wf. apply invert_ty_defs_cons in Tyds. rename ds into ds0.
    destruct Tyds as [d [ds [D [Eq1 [Tyds [Eq2 Tyd]]]]]]. subst.
    lets P: (subtyp_preserves_is_bot Wf St (is_bot_bot G)). inversions P.
  + (* case subtyp_or *)
    introv Tyds. inversions Tyds.
  + (* case subtyp_or_l *)
    introv Tyds. discriminate.
  + (* case subtyp_or_r *)
    introv Tyds. discriminate.
  + (* case subtyp_trans *)
    introv Tyds. refine (IHSt1 _ _ _ Tyds). (* TODO might not hold!  *)


    admit.
Qed.

(*
    destruct p as [v]. destruct v as [n|v]; [admit | idtac]. (* cannot have bound var *)
    inversions Tyds.
    refine (IHSt eq_refl s _ v _ Wf _ _).
    apply IHSt.
*)

(* let's try without any realizability guarantees: *)
Lemma swap_sub_and_has: forall G T1 T2 D2,
  subtyp G T1 T2 ->
  typ_has G T2 D2 ->
  exists D1,
    typ_has G T1 D1 /\
    subdec G D1 D2.
Proof.
  introv St. gen D2. induction St; introv T2Has.
  + (* case subtyp_refl *)
    eauto.
  + (* case subtyp_top *)
    inversions T2Has.
  + (* case subtyp_bot *)
    eauto.
  + (* case subtyp_rcd *)
    inversions T2Has. eauto.
  + (* case subtyp_sel_l *)
    rename S into Lo, U into Hi.
    specialize (IHSt D2 T2Has). destruct IHSt as [D1 [HiHas Sd]].
    exists D1. refine (conj _ Sd). apply (typ_sel_has _ H H0 HiHas).
  + (* case subtyp_sel_r *)
    rename S into Lo, U into Hi.
    (* need IH for the Lo2..Hi2 inside T2Has, not for the ones from Lo..Hi *)
    specialize (IHSt
  + (* case subtyp_and *)
    admit.
  + (* case subtyp_and_l *)
    admit.
  + (* case subtyp_and_r *)
    admit.
  + (* case subtyp_or *)
    admit.
  + (* case subtyp_or_l *)
    admit.
  + (* case subtyp_or_r *)
    admit.
  + (* case subtyp_trans *)
    admit.
Qed.

Lemma swap_sub_and_has_step: forall n,
  swap_sub_and_has_until n -> swap_sub_and_has_until (S n).
Proof.
  introv swap_sub_and_has_IH. introv St. gen s x D2. induction St.
  + (* case subtyp_refl *)
    intros. exists D2. auto.
  + (* case subtyp_top *)
    intros. inversions H. (* contradiction *)
  + (* case subtyp_bot *)
    intros. exists D2. auto.
    (* case subtyp_bot if bot has no members:
    introv THas Eq Wf Tyx. rename T into X2.
    lets P: (invert_wf_sto_without_binds Wf Tyx).
    destruct P as [X1 [ds [Tyds [St [BiG Bis]]]]].
    exfalso.
    lets B: (subtyp_preserves_is_bot Wf St (is_bot_bot G)).
    apply (defs_are_not_bot Tyds Wf B). (* <--- not proven!! *)
    *)
  + (* case subtyp_rcd *)
    admit.
  + (* case subtyp_sel_l *)
    rename S into Lo, U into Hi, H into Ty, H0 into XHas, T into T2.
    introv T2Has Leq Wf Tyx.
    specialize (IHSt _ _ _ T2Has Leq Wf). (* how to get something which types as Hi?
    maybe x, because it has type p.L, but for this, we need Lo<:Hi, which we could get
    from store, but to do so, we need to bridge another imprecision gap... *)

    destruct IHSt as [D1 [F [n' [HiHas Sd]]]].



    intros G p L Lo Hi T2 n pHas St IHSt l D2 T2Has.
    specialize (IHSt _ _ T2Has). destruct IHSt as [D1 [F [n' [HiHas Sd]]]].
    exists D1 F n'. split.
    - apply (typ_sel_has p pHas HiHas).
    - intros x xF. specialize (Sd x xF).
      lets St': (subtyp_tmode (subtyp_sel_l _ pHas (subtyp_tmode (subtyp_refl _ _ 0)))).
      refine (narrow_subdec_end _ St' Sd). apply okadmit.
  + (* case subtyp_sel_r *)
    intros G p L Lo1 Hi1 T1 n pHas1 St1 IH1 St2 IH2 l D2 pLHas.
    apply invert_typ_sel_has in pLHas. destruct pLHas as [Lo2 [Hi2 [pHas2 Hi2Has]]].
    lets P: (intersect_has pHas1 pHas2). simpl in P.
    assert (s: sto) by admit. assert (Wf: wf_sto s G) by admit. (* TODO as hypothesis *)
    apply (has_to_good_bounds _ Wf) in P.
    destruct P as [n' StB].
    lets StA: (subtyp_tmode (subtyp_or_l Lo2 (subtyp_tmode (subtyp_refl G Lo1 n')))).
    lets StC: (subtyp_tmode (subtyp_and_r Hi1 (subtyp_tmode (subtyp_refl G Hi2 n')))).
    lets St: (subtyp_trans StA (subtyp_trans StB StC)).
    (* TODO termination measure ??? *)
    lets Q: (swap_sub_and_has_IH St Hi2Has).
    destruct Q as [Dm [Fm [n'' [Lo1Has Sdm2]]]].
    lets R: (swap_sub_and_has_IH St2 Lo1Has).
    destruct R as [D1 [F1 [n''' [T1Has Sd1m]]]].
    exists D1 (F1 \u Fm) (max n''' n'').
    apply (conj T1Has).
    intros x Frx.
    assert (xF1: x \notin F1) by auto. specialize (Sd1m x xF1).
    assert (xFm: x \notin Fm) by auto. specialize (Sdm2 x xFm).
    lets Sdm2': (narrow_subdec_end (okadmit _) St2 Sdm2).
    apply (subdec_trans_with_different_sizes Sd1m Sdm2').
  + (* case subtyp_tmode *)
    intros. apply* H0.
  + (* case subtyp_trans *)
    introv St12 IH12 St23 IH23 T3Has. rename D2 into D3.
    specialize (IH23 _ _ T3Has). destruct IH23 as [D2 [L23 [n23 [T2Has Sd23]]]].
    specialize (IH12 _ _ T2Has). destruct IH12 as [D1 [L12 [n12 [T1Has Sd12]]]].
    exists D1 (L12 \u L23) (max n12 n23). apply (conj T1Has).
    intros x N.
    assert (xL12: x \notin L12) by auto. specialize (Sd12 x xL12).
    assert (xL23: x \notin L23) by auto. specialize (Sd23 x xL23).
    lets Sd23': (narrow_subdec_end (okadmit _) St12 Sd23).
    apply (subdec_trans_with_different_sizes Sd12 Sd23').
  + (* case subtyp_and *)
    intros G T U V n StU IHU StV IHV l D2 UVHas.
    apply invert_typ_and_has in UVHas. destruct UVHas as [UHas | [VHas | UVHas]].
    - apply* IHU.
    - apply* IHV.
    - destruct UVHas as [D2U [D2V [UHas [VHas Eq]]]]. subst.
      specialize (IHU _ _ UHas). destruct IHU as [D1U [LU [nU [THasD1U SdU]]]].
      specialize (IHV _ _ VHas). destruct IHV as [D1V [LV [nV [THasD1V SdV]]]].
      exists (intersect_dec D1U D1V) (LU \u LV) (max nU nV).
      apply (conj (intersect_typ_has THasD1U THasD1V)).
      intros x Frx.
      assert (xLU: x \notin LU) by auto. specialize (SdU x xLU).
      assert (xLV: x \notin LV) by auto. specialize (SdV x xLV).
      admit. (* TODO follows from SdU and SdV *)
  + (* case subtyp_and_l *)
    intros G U V T n St IH l D2 THas.
    specialize (IH _ _ THas). destruct IH as [D1U [L [n' [UHas Sd]]]].
    exists D1U L n'. split.
    - apply (typ_and_has_1 _ UHas).
    - intros x xL. specialize (Sd x xL).
      lets St': (subtyp_tmode (subtyp_and_l V (subtyp_tmode (subtyp_refl G U 0)))).
      apply (narrow_subdec_end (okadmit _) St' Sd).
  + (* case subtyp_and_r *)
    intros G U V T n St IH l D2 THas.
    specialize (IH _ _ THas). destruct IH as [D1V [L [n' [VHas Sd]]]].
    exists D1V L n'. split.
    - apply (typ_and_has_2 _ VHas).
    - intros x xL. specialize (Sd x xL).
      lets St': (subtyp_tmode (subtyp_and_r U (subtyp_tmode (subtyp_refl G V 0)))).
      apply (narrow_subdec_end (okadmit _) St' Sd).
  + (* case subtyp_or *)
    intros G U V T n StU IHU StV IHV l D2 THas.
    specialize (IHU _ _ THas). destruct IHU as [DU [LU [nU [UHas SdU]]]].
    specialize (IHV _ _ THas). destruct IHV as [DV [LV [nV [VHas SdV]]]].
    exists (union_dec DU DV) (LU \u LV) (max nU nV).
    apply (conj (union_typ_has UHas VHas)).
    intros x Frx.
    assert (xLU: x \notin LU) by auto. specialize (SdU x xLU).
    assert (xLV: x \notin LV) by auto. specialize (SdV x xLV).
    rewrite (distribute_open_dec_over_union_dec x DU DV).
    assert (SdAnd: subdec (G & x ~ typ_or U V)
                          (intersect_dec (open_dec x D2) (open_dec x D2))
                          (open_dec x D2)
                          (max nU nV)).
    admit. (* doesn't hold because subdec_refl doesn't (need good bounds) *)
    refine (subdec_trans _ SdAnd).
    (*
    apply subdec_or. doesn't match: we have intersect<:union, but want union<:intersect!
    *)
    admit. (*
  + (* case subtyp_or *)
    intros G U V T n StU IHU StV IHV l D2 THas.
    specialize (IHU _ _ THas). destruct IHU as [DU [LU [nU [UHas SdU]]]].
    specialize (IHV _ _ THas). destruct IHV as [DV [LV [nV [VHas SdV]]]].
    exists (union_dec DU DV) (LU \u LV) (max nU nV).
    apply (conj (union_typ_has UHas VHas)).
    intros x Frx.
    assert (xLU: x \notin LU) by auto. specialize (SdU x xLU).
    assert (xLV: x \notin LV) by auto. specialize (SdV x xLV).
    rewrite (distribute_open_dec_over_union_dec x DU DV).
    (* SdU is with (x: U), but we need it with (x: (typ_or U V)),
       but narrowing goes the other way round! 
       Intersection types to the rescue! *)
    lets StAndU: (subtyp_tmode (subtyp_and_l V (subtyp_tmode (subtyp_refl G U 7)))).
    apply (narrow_subdec_end (okadmit _) StAndU) in SdU.
    lets StAndV: (subtyp_tmode (subtyp_and_r U (subtyp_tmode (subtyp_refl G V 7)))).
    apply (narrow_subdec_end (okadmit _) StAndV) in SdV.
    assert (StAndOr: subtyp oktrans G (typ_and U V) (typ_or U V) 7). {
      apply subtyp_tmode. apply subtyp_or_l. exact StAndU.
    }
    (* doesn't help, still the wrong way!
    apply (narrow_subdec_end (okadmit _) StAndOr).*)
    apply subdec_union.
    admit. admit. (*
  + (* case subtyp_or *)
    intros G U V T n StU IHU StV IHV l D2 THas.
    (* only use left side (U) *)
    specialize (IHU _ _ THas). destruct IHU as [DU [LU [nU [UHas SdU]]]].
    exists DU LU nU. split.
    - apply typ_or_has.*)
  *)
  + (* case subtyp_or_l *)
    admit.
  + (* case subtyp_or_r *)
    admit.
Qed.


(* whenever we put an (x:T) binding into G, we ensure that x is not in fv(T),
   so if we have "G |- T has (L: Lo..Hi)", Lo and Hi don't contain x either,
   so we can shrink G until just before x, and Lo/Hi are still wf,
   so invoke swap_sub_and_has with this smaller G *)

Lemma has_sound: forall s G x ds T2 D2,
  wf_sto s G ->
  binds x ds s ->
  ty_trm G (trm_var (avar_f x)) T2 ->
  typ_has G T2 D2 ->
  exists T1 D1,
    ty_defs G ds T1 /\
    typ_has G T1 D1 /\
    subdec G D1 D2.
Proof.
  introv Wf Bis Tyx THas.
  destruct (invert_wf_sto_with_sbsm Wf Bis Tyx) as [X1 [St Tyds]].
  lets P: (swap_sub_and_has St X2Has).
          (*************************)
  destruct P as [D1 [L [n' [X1Has Sd]]]].
  pick_fresh z. assert (zL: z \notin L) by auto. specialize (Sd z zL).
  exists X1 D1 n'.
  refine (conj Tyds (conj X1Has _)).
  (* close enough ;-) [need some substitution...]

  lets BiG: (sto_binds_to_ctx_binds Wf Bis).
  lets Tyx1: (ty_var BiG).
  lets Ok: (wf_sto_to_ok_G Wf).
  assert (Ok': ok (G & z ~ typ_bind Ds1)) by auto.
  lets Sds': (@subdecs_subst_principle _ z x (typ_bind Ds1)
              (***********************) (open_decs z Ds1) (open_decs z Ds2) Ok' Sds Tyx1).
  assert (zDs1: z \notin fv_decs Ds1) by auto.
  assert (zDs2: z \notin fv_decs Ds2) by auto.
  rewrite <- (@subst_intro_decs z x Ds1 zDs1) in Sds'.
  rewrite <- (@subst_intro_decs z x Ds2 zDs2) in Sds'.
  apply (decs_has_open x) in Ds2Has.
  destruct (decs_has_preserves_sub Ds2Has Sds') as [D1 [Ds1Has Sd]].
  exists Ds1 D1.
  apply (conj Tyds (conj Ds1Has Sd)).
  *)
Admitted.

Print Assumptions has_sound.
*)

(*
Lemma ty_open_defs_change_var: forall x y G ds Ds S,
  ok (G & x ~ S) ->
  ok (G & y ~ S) ->
  x \notin fv_defs ds ->
  x \notin fv_decs Ds ->
  ty_defs (G & x ~ S) (open_defs x ds) (open_decs x Ds) ->
  ty_defs (G & y ~ S) (open_defs y ds) (open_decs y Ds).
Proof.
  introv Okx Oky Frds FrDs Ty.
  destruct (classicT (x = y)) as [Eq | Ne].
  + subst. assumption.
  + assert (Okyx: ok (G & y ~ S & x ~ S)) by destruct* (ok_push_inv Okx).
    assert (Ty': ty_defs (G & y ~ S & x ~ S) (open_defs x ds) (open_decs x Ds))
      by apply (weaken_ty_defs_middle Ty Okyx).
    rewrite* (@subst_intro_defs x y ds).
    rewrite* (@subst_intro_decs x y Ds).
    lets Tyy: (ty_var (binds_push_eq y S G)).
    destruct (subst_principles y S) as [_ [_ [_ [_ [_ [_ [_ P]]]]]]].
             (****************)
    specialize (P _ _ _ Ty' (G & y ~ S) empty x).
    rewrite concat_empty_r in P.
    specialize (P eq_refl Tyy Okyx).
    unfold subst_ctx in P. rewrite map_empty in P. rewrite concat_empty_r in P.
    exact P.
Qed.
*)

(* ###################################################################### *)
(** ** Progress *)

Theorem progress_result: progress.
Proof.
  introv Wf Ty. gen G e T Ty s Wf.
  introv Ty. induction Ty.
  + (* case ty_var *)
    rename H into BiG. introv Wf.
    right. destruct (ctx_binds_to_sto_binds Wf BiG) as [o Bis].
    exists x o. auto.
  + (* case ty_sel *)
    rename H into THas. introv Wf.
    left. specialize (IHTy s Wf). destruct IHTy as [IH | IH].
    (* receiver is an expression *)
    - destruct IH as [s' [e' IH]]. do 2 eexists. apply (red_sel1 l IH).
    (* receiver is a var *)
    - destruct IH as [x [ds [Eq Bis]]]. subst.
      lets P: (has_sound Wf Bis Has).
              (*********)
      destruct P as [T1 [D1 [n [Tyds [THas Sd]]]]].
      lets Q: (invert_ty_defs Tyds THas).
              (**************)
      destruct Q as [d [D0 [n0 [dsHas [Tyd Sd']]]]].
      assert (exists T0 r, d = (def_fld T0 r)) by admit. (* <------ TODO *)
      destruct H as [T0 [r Eq]]. subst d.
      exists (trm_var r) s.
      apply (red_sel Bis dsHas).
  (* case ty_call *)
  + intros G t m U V u Has IHrec Tyu IHarg s Wf. left.
    specialize (IHrec s Wf eq_refl). destruct IHrec as [IHrec | IHrec].
    - (* case receiver is an expression *)
      destruct IHrec as [s' [e' IHrec]]. do 2 eexists. apply (red_call1 m _ IHrec).
    - (* case receiver is  a var *)
      destruct IHrec as [x [[Tds ds] [Eq Bis]]]. subst.
      specialize (IHarg s Wf). destruct IHarg as [IHarg | IHarg].
      * (* arg is an expression *)
        destruct IHarg as [s' [e' IHarg]]. do 2 eexists. apply (red_call2 x m IHarg).
      * (* arg is a var *)
        destruct IHarg as [y [o [Eq Bisy]]]. subst.
        lets P: (has_sound Wf Bis Has).
                (*********)
        destruct P as [Ds1 [D1 [Tyds [Ds1Has Sd]]]].
        destruct (decs_has_to_defs_has Tyds Ds1Has) as [d dsHas].
        destruct (defs_has_mtd_sync dsHas) as [body Eqd]. subst.
        exists (open_trm y body) s.
        apply (red_call y Bis dsHas).
  (* case ty_new *)
  + intros L G ds Ds Tyds F s Wf.
    left. pick_fresh x.
    exists (trm_var (avar_f x)) (s & x ~ (object Ds ds)).
    apply* red_new.
  (* case ty_sbsm *)
  + intros. auto_specialize. assumption.
Qed.

Print Assumptions progress_result.


(* ###################################################################### *)
(** ** Preservation *)

Theorem preservation_proof:
  forall e s e' s' (Hred: red e s e' s') G T (Hwf: wf_sto s G) (Hty: ty_trm G e T),
  exists H, wf_sto s' (G & H) /\ ty_trm (G & H) e' T.
Proof.
  intros s e s' e' Red. induction Red.
  (* red_call *)
  + intros G U3 Wf TyCall. rename H into Bis, H0 into dsHas, T into X1.
    exists (@empty typ). rewrite concat_empty_r. apply (conj Wf).
    apply invert_ty_call in TyCall.
    destruct TyCall as [T2 [U2 [Has [StU23 Tyy]]]].
    lets P: (has_sound Wf Bis Has).
            (*********)
    destruct P as [Ds1 [D1 [Tyds [Ds1Has Sd]]]].
    apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [T1 [U1 [Eq [StT StU12]]]]. subst D1.
    destruct (invert_ty_mtd_inside_ty_defs Tyds dsHas Ds1Has) as [L0 Tybody].
    apply invert_ty_var in Tyy.
    destruct Tyy as [T3 [StT3 Biy]].
    pick_fresh y'.
    rewrite* (@subst_intro_trm y' y body).
    assert (Fry': y' \notin fv_typ U3) by auto.
    assert (Eqsubst: (subst_typ y' y U3) = U3)
      by apply* subst_fresh_typ_dec_decs.
    rewrite <- Eqsubst.
    lets Ok: (wf_sto_to_ok_G Wf).
    apply (@trm_subst_principle G y' y (open_trm y' body) T1 _).
           (*******************)
    - auto.
    - assert (y'L0: y' \notin L0) by auto. specialize (Tybody y' y'L0).
      apply (ty_sbsm Tybody).
      apply weaken_subtyp_end. auto. apply (subtyp_trans StU12 StU23).
    - refine (ty_sbsm _ StT). refine (ty_sbsm _ StT3). apply (ty_var Biy).
  (* red_sel *)
  + intros G T3 Wf TySel. rename H into Bis, H0 into dsHas.
    exists (@empty typ). rewrite concat_empty_r. apply (conj Wf).
    apply invert_ty_sel in TySel.
    destruct TySel as [T2 [StT23 Has]].
    lets P: (has_sound Wf Bis Has).
            (*********)
    destruct P as [Ds1 [D1 [Tyds [Ds1Has Sd]]]].
    apply invert_subdec_fld_sync_left in Sd.
    destruct Sd as [T1 [Eq StT12]]. subst D1.
    refine (ty_sbsm _ StT23).
    refine (ty_sbsm _ StT12).
    apply (invert_ty_fld_inside_ty_defs Tyds dsHas Ds1Has).
  (* red_new *)
  + rename T into Ds1. intros G T2 Wf Ty.
    apply invert_ty_new in Ty.
    destruct Ty as [StT12 [L [Tyds Cb]]].
    exists (x ~ (typ_bind Ds1)).
    pick_fresh x'. assert (Frx': x' \notin L) by auto.
    specialize (Tyds x' Frx').
    assert (xG: x # G) by apply* sto_unbound_to_ctx_unbound.
    split.
    - apply (wf_sto_push _ Wf H xG).
      * apply* (@ty_open_defs_change_var x').
      * exact Cb. (* was a "meh TODO" before cbounds :-) *)
    - lets Ok: (wf_sto_to_ok_G Wf). assert (Okx: ok (G & x ~ (typ_bind Ds1))) by auto.
      apply (weaken_subtyp_end Okx) in StT12.
      refine (ty_sbsm _ StT12). apply ty_var. apply binds_push_eq.
  (* red_call1 *)
  + intros G Tr2 Wf TyCall.
    apply invert_ty_call in TyCall.
    destruct TyCall as [Ta [Tr1 [Has [St Tya]]]].
    apply invert_has in Has.
    destruct Has as [Has | Has].
    - (* case has_trm *)
      destruct Has as [To [Ds [Tyo [Exp [DsHas Clo]]]]].
      specialize (IHRed G To Wf Tyo). destruct IHRed as [H [Wf' Tyo']].
      lets Ok: (wf_sto_to_ok_G Wf').
      exists H. apply (conj Wf').
      apply (weaken_subtyp_end Ok) in St.
      refine (ty_sbsm _ St).
      apply (@ty_call (G & H) o' m Ta Tr1 a).
      * refine (has_trm Tyo' _ DsHas Clo).
        apply (weaken_exp_end Ok Exp).
      * apply (weaken_ty_trm_end Ok Tya).
    - (* case has_var *)
      destruct Has as [x [Tx [Ds [D' [Eqx _]]]]]. subst.
      inversion Red. (* contradiction: vars don't step *)
  (* red_call2 *)
  + intros G Tr2 Wf TyCall.
    apply invert_ty_call in TyCall.
    destruct TyCall as [Ta [Tr1 [Has [St Tya]]]].
    specialize (IHRed G Ta Wf Tya).
    destruct IHRed as [H [Wf' Tya']].
    exists H. apply (conj Wf').
    lets Ok: wf_sto_to_ok_G Wf'.
    apply (weaken_subtyp_end Ok) in St.
    refine (ty_sbsm _ St).
    apply (@ty_call (G & H) _ m Ta Tr1 a').
    - apply (weaken_has_end Ok Has).
    - assumption.
  (* red_sel1 *)
  + intros G T2 Wf TySel.
    apply invert_ty_sel in TySel.
    destruct TySel as [T1 [St Has]].
    apply invert_has in Has.
    destruct Has as [Has | Has].
    - (* case has_trm *)
      destruct Has as [To [Ds [Tyo [Exp [DsHas Clo]]]]].
      specialize (IHRed G To Wf Tyo). destruct IHRed as [H [Wf' Tyo']].
      lets Ok: (wf_sto_to_ok_G Wf').
      exists H. apply (conj Wf').
      apply (weaken_subtyp_end Ok) in St.
      refine (ty_sbsm _ St). apply (@ty_sel (G & H) o' l T1).
      refine (has_trm Tyo' _ DsHas Clo).
      apply (weaken_exp_end Ok Exp).
    - (* case has_var *)
      destruct Has as [x [Tx [Ds [D' [Eqx _]]]]]. subst.
      inversion Red. (* contradiction: vars don't step *)
Qed.

Theorem preservation_result: preservation.
Proof.
  introv Hwf Hty Hred.
  destruct (preservation_proof Hred Hwf Hty) as [H [Hwf' Hty']].
  exists (G & H). split; assumption.
Qed.

Print Assumptions preservation_result.
