
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
      typ_bot has no members! *)
  | typ_rcd_has: forall G D,
      typ_has G (typ_rcd D) D
  | typ_sel_has: forall G p T L Lo Hi D,
      ty_trm G (pth2trm p) T ->
      typ_has G T (dec_typ L Lo Hi) ->
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
  | ty_dsnil: forall G,
      ty_defs G defs_nil typ_top
  | ty_dscons: forall G ds d T D,
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
