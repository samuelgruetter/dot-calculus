
(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.

Set Implicit Arguments.


(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Inductive label: Type :=
| label_typ: nat -> label
| label_fld: nat -> label
| label_mtd: nat -> label.

(*
Definition typ_label := nat.
Definition fld_label := nat.
Definition mtd_label := nat.
*)

Definition nat := tt. (* do not use nat ;-) *)

Inductive avar : Set :=
  | avar_b : Datatypes.nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to tenv or venv *)

Inductive pth : Set :=
  | pth_var : avar -> pth.

Inductive typ : Set :=
  | typ_top : typ
  | typ_bot : typ
  | typ_rfn : typ -> label -> dec -> typ (* T { z => l: D }, z nameless *)
  | typ_sel : pth -> label -> typ (* p.L *)
  | typ_and : typ -> typ -> typ
  | typ_or  : typ -> typ -> typ
with dec : Set :=
  | dec_typ  : typ -> typ -> dec
  | dec_fld  : typ -> dec
  | dec_mtd : typ -> typ -> dec.

Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_new  : defs -> trm (* with nameless self reference *)
  | trm_sel  : trm -> label -> trm
  | trm_call : trm -> label -> trm -> trm
with def : Set :=
  | def_typ : typ -> typ -> def (* same as dec_typ *)
  | def_fld : typ -> avar -> def (* cannot have a term here, need to assign first *)
  | def_mtd : typ -> typ -> trm -> def (* one nameless argument *)
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> label -> def -> defs.


(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env defs.

(** *** Syntactic sugar *)
Definition trm_fun(T U: typ)(body: trm) := 
            trm_new (defs_cons defs_nil (label_mtd 0) (def_mtd T U body)).
Definition trm_app(func arg: trm) := trm_call func (label_mtd 0) arg.
Definition trm_let(T U: typ)(rhs body: trm) := trm_app (trm_fun T U body) rhs.
Definition typ_arrow(T1 T2: typ) := typ_rfn typ_top (label_mtd 0) (dec_mtd T1 T2).


(* ###################################################################### *)
(** ** Declaration and definition lists *)

(*
Definition label_for_def(n: nat)(d: def): label := match d with
| def_typ _ _    => label_typ n
| def_fld _ _    => label_fld n
| def_mtd _ _ _  => label_mtd n
end.
Definition label_for_dec(n: nat)(D: dec): label := match D with
| dec_typ _ _ => label_typ n
| dec_fld _   => label_fld n
| dec_mtd _ _ => label_mtd n
end.

Fixpoint get_def(l: label)(ds: defs): option def := match ds with
| defs_nil => None
| defs_cons n d ds' => If l = label_for_def n d then Some d else get_def l ds'
end.
Definition defs_has(ds: defs)(l: label)(d: def): Prop := (get_def l ds = Some d).

Definition defs_hasnt(ds: defs)(l: label): Prop := (get_def l ds = None).
*)

Inductive label_matches_dec: label -> dec -> Prop :=
  | label_matches_dec_typ: forall n Lo Hi, label_matches_dec (label_typ n) (dec_typ Lo Hi)
  | label_matches_dec_fld: forall n T,     label_matches_dec (label_fld n) (dec_fld T)
  | label_matches_dec_mtd: forall n T1 T2, label_matches_dec (label_mtd n) (dec_mtd T1 T2).

Inductive label_matches_def: label -> def -> Prop :=
  | label_matches_def_typ: forall n Lo Hi,
    label_matches_def (label_typ n) (def_typ Lo Hi)
  | label_matches_def_fld: forall n T x,
    label_matches_def (label_fld n) (def_fld T x)
  | label_matches_def_mtd: forall n T1 T2 t,
    label_matches_def (label_mtd n) (def_mtd T1 T2 t).

(*
Inductive matching_label: label -> dec -> Prop :=
  | matching_label_typ: forall n Lo Hi, matching_label (label_typ n) (dec_typ Lo Hi)
  | matching_label_fld: forall n T,     matching_label (label_fld n) (dec_fld T)
  | matching_label_mtd: forall n T1 T2, matching_label (label_mtd n) (dec_mtd T1 T2).
*)

Inductive defs_hasnt: defs -> label -> Prop :=
| defs_hasnt_nil: forall l,
    defs_hasnt defs_nil l
| defs_hasnt_cons: forall l0 d0 ds l,
    defs_hasnt ds l ->
    l0 <> l ->
    defs_hasnt (defs_cons ds l0 d0) l.

Inductive defs_has: defs -> label -> def -> Prop :=
| defs_has_hit: forall l d ds,
    label_matches_def l d ->
    defs_hasnt ds l ->
    defs_has (defs_cons ds l d) l d
| defs_has_skip: forall l1 d1 ds l2 d2,
    defs_has ds l1 d1 ->
    l2 <> l1 ->
    defs_has (defs_cons ds l2 d2) l1 d1
(* only def_typ can be merged, def_fld and def_mtd must be unique *)
| defs_has_merge: forall l Lo1 Hi1 Lo2 Hi2 ds,
    defs_has ds l (def_typ Lo1 Hi1) ->
    defs_has (defs_cons ds l (def_typ Lo2 Hi2)) l
      (def_typ (typ_or Lo1 Lo2) (typ_and Hi1 Hi2)).


(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k) 
   by a free variable x. *)

Definition open_rec_avar (k: Datatypes.nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Definition open_rec_pth (k: Datatypes.nat) (u: var) (p: pth) : pth :=
  match p with
  | pth_var a => pth_var (open_rec_avar k u a)
  end.

Fixpoint open_rec_typ (k: Datatypes.nat) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top       => typ_top
  | typ_bot       => typ_bot
  | typ_rfn T l D => typ_rfn (open_rec_typ k u T) l (open_rec_dec (S k) u D)
  | typ_sel p L   => typ_sel (open_rec_pth k u p) L
  | typ_and T1 T2 => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_or T1 T2  => typ_or (open_rec_typ k u T1) (open_rec_typ k u T2)
  end
with open_rec_dec (k: Datatypes.nat) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ T U => dec_typ (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_fld T   => dec_fld (open_rec_typ k u T)
  | dec_mtd T U => dec_mtd (open_rec_typ k u T) (open_rec_typ k u U)
  end.

Fixpoint open_rec_trm (k: Datatypes.nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_new ds     => trm_new (open_rec_defs (S k) u ds)
  | trm_sel e n    => trm_sel (open_rec_trm k u e) n
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: Datatypes.nat) (u: var) (d: def) { struct d } : def :=
  match d with
  | def_typ Lo Hi => def_typ (open_rec_typ k u Lo) (open_rec_typ k u Hi)
  | def_fld T a => def_fld (open_rec_typ k u T) (open_rec_avar k u a)
  | def_mtd T1 T2 e => def_mtd (open_rec_typ k u T1) (open_rec_typ k u T2)
                       (open_rec_trm (S k) u e)
  end
with open_rec_defs (k: Datatypes.nat) (u: var) (ds: defs) { struct ds } : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl l d => defs_cons (open_rec_defs k u tl) l (open_rec_def k u d)
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
  | typ_rfn T l D => (fv_typ T) \u (fv_dec D)
  | typ_sel p L   => (fv_pth p)
  | typ_and T U   => (fv_typ T) \u (fv_typ U)
  | typ_or  T U   => (fv_typ T) \u (fv_typ U)
  end
with fv_dec (D: dec) { struct D } : vars :=
  match D with
  | dec_typ T U => (fv_typ T) \u (fv_typ U)
  | dec_fld T   => (fv_typ T)
  | dec_mtd T U => (fv_typ T) \u (fv_typ U)
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
  | def_typ T U => (fv_typ T) \u (fv_typ U)
  | def_fld T x => (fv_typ T) \u (fv_avar x)
  | def_mtd T U u => (fv_typ T) \u (fv_typ U) \u (fv_trm u)
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl _ d => (fv_defs tl) \u (fv_def d)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).


(* ###################################################################### *)
(** ** Operational Semantics *)

(** Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
    Whenever we introduce a new avar_f (only happens in red_new), we choose one
    which is not in the store, so we never have name clashes. *)
Inductive red : trm -> sto -> trm -> sto -> Prop :=
  (* computation rules *)
  | red_call : forall s x y m ds T U body,
      binds x ds s ->
      defs_has ds m (def_mtd T U body) ->
      red (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) s
          (open_trm y body) s
  | red_sel : forall s x y l T ds,
      binds x ds s ->
      defs_has ds l (def_fld T y) ->
      red (trm_sel (trm_var (avar_f x)) l) s
          (trm_var y) s
  | red_new : forall s ds x,
      x # s ->
      red (trm_new ds) s
          (trm_var (avar_f x)) (s & x ~ (open_defs x ds))
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

(* tmode = "is transitivity at top level accepted?" *)
Inductive tmode : Type := notrans | oktrans.

(* pmode = "do the "has" judgments needed in subtyping have to be precise?"
Inductive pmode : Type := pr | ip. *)

Definition pth2trm(p: pth): trm := match p with
  | pth_var a => trm_var a
end.

(*
Definition intersect_dec(D1 D2: dec): 
  forall l, matching_label l D1 -> matching_label l D2 -> dec := match D1, D2 with
  | dec_typ T1 U1, dec_typ T2 U2 => dec_typ (typ_or T1 T2) (typ_and U1 U2)
  | dec_fld T1   , dec_fld T2    => dec_fld (typ_and T1 T2)
  | dec_mtd T1 U1, dec_mtd T2 U2 => dec_mtd (typ_or T1 T2) (typ_and U1 U2)
  | _, _ => dec_typ typ_top typ_bot (* just any dummy value *)
end.
*)

Definition intersect_dec(D1 D2: dec): dec := match D1, D2 with
  | dec_typ T1 U1, dec_typ T2 U2 => dec_typ (typ_or T1 T2) (typ_and U1 U2)
  | dec_fld T1   , dec_fld T2    => dec_fld (typ_and T1 T2)
  | dec_mtd T1 U1, dec_mtd T2 U2 => dec_mtd (typ_or T1 T2) (typ_and U1 U2)
  | _, _ => dec_fld typ_bot (* just any dummy value *)
end.

Definition union_dec(D1 D2: dec): dec := match D1, D2 with
  | dec_typ T1 U1, dec_typ T2 U2 => dec_typ (typ_and T1 T2) (typ_or U1 U2)
  | dec_fld T1   , dec_fld T2    => dec_fld (typ_or T1 T2)
  | dec_mtd T1 U1, dec_mtd T2 U2 => dec_mtd (typ_and T1 T2) (typ_and U1 U2)
  | _, _ => dec_fld typ_bot (* just any dummy value *)
end.

(*
(* not defined as a function because it's not total (only defined if same kind of dec) *)
Inductive intersect_dec: dec -> dec -> dec -> Prop :=
| intersect_dec_typ: forall T1 U1 T2 U2,
    intersect_dec (dec_typ T1 U1) (dec_typ T2 U2) (dec_typ (typ_or T1 T2) (typ_and U1 U2))
| intersect_dec_fld: forall T1 T2,
    intersect_dec (dec_fld T1) (dec_fld T2) (dec_fld (typ_and T1 T2))
| intersect_dec_mtd: forall T1 U1 T2 U2,
    intersect_dec (dec_mtd T1 U1) (dec_mtd T2 U2) (dec_mtd (typ_or T1 T2) (typ_and U1 U2)).

Inductive union_dec: dec -> dec -> dec -> Prop :=
| union_dec_typ: forall T1 U1 T2 U2,
    union_dec (dec_typ T1 U1) (dec_typ T2 U2) (dec_typ (typ_and T1 T2) (typ_or U1 U2))
| union_dec_fld: forall T1 T2,
    union_dec (dec_fld T1) (dec_fld T2) (dec_fld (typ_or T1 T2))
| union_dec_mtd: forall T1 U1 T2 U2,
    union_dec (dec_mtd T1 U1) (dec_mtd T2 U2) (dec_mtd (typ_and T1 T2) (typ_or U1 U2)).
*)

(*
Before, when we had expansion, we had the problem that existence of an expansion in
precise typing was not preserved by narrowing:
z: { A: Bot..{f: Int}, B: Bot..Top }, z.A expands to {f: Int}, everything is fine
After narrowing:
z: { A: Bot..z.B /\ {f: Int}, B: Bot..z.A }, z.A has no finite expansion proof!
And existence of an expansion was absolutely crucial to prove "has" judgments, eg
to prove that an object a of type z.A still has a field f after narrowing.

Now, we do the expansion only for the members we're interested in, so we can just
forget the z.B part of z.A's upper bound and only look at {f: Int}, which is what
we need.
*)

(* on paper: G |- T ∍z D
   in Coq: "has" returns a dec without opening it *)
Inductive typ_has: ctx -> typ -> label -> dec -> Prop :=
(*| typ_top_has: typ_top has nothing *)
(*| typ_bot_has: in subdec_typ, we require that Lo2 <: Lo1 <: Hi1 <: Hi2,
      so the dec_typ that typ_bot could have, i.e.
      (dec_typ typ_top typ_bot) is not a subdec of anything, so better say
      typ_bot has no members! *)
  | typ_rfn_has_1: forall G T1 l1 D1 l D,
      typ_has G T1 l D ->
      typ_has G (typ_rfn T1 l1 D1) l D
  | typ_rfn_has_2: forall G T l D,
      label_matches_dec l D ->
      typ_has G (typ_rfn T l D) l D
  | typ_rfn_has_12: forall G T l D1 D2,
      typ_has G T l D1 ->
      typ_has G (typ_rfn T l D2) l (intersect_dec D1 D2)
  | typ_sel_has: forall G p L Lo Hi l D,
      has G (pth2trm p) L (dec_typ Lo Hi) ->
      typ_has G Hi l D ->
      typ_has G (typ_sel p L) l D
  | typ_and_has_1: forall G T1 T2 l D,
      typ_has G T1 l D ->
      typ_has G (typ_and T1 T2) l D
  | typ_and_has_2: forall G T1 T2 l D,
      typ_has G T2 l D ->
      typ_has G (typ_and T1 T2) l D
  | typ_and_has_12: forall G T1 T2 l D1 D2,
      typ_has G T1 l D1 ->
      typ_has G T2 l D2 ->
      typ_has G (typ_and T1 T2) l (intersect_dec D1 D2)
  | typ_or_has: forall G T1 T2 l D1 D2,
      typ_has G T1 l D1 ->
      typ_has G T2 l D2 ->
      typ_has G (typ_or T1 T2) l (union_dec D1 D2)
with has: ctx -> trm -> label -> dec -> Prop :=
  | has_trm : forall G t T l D,
      ty_trm G t T ->
      typ_has G T l D ->
      (forall z, (open_dec z D) = D) ->
      has G t l D
  | has_pth : forall G v T l D,
      ty_trm G (trm_var (avar_f v)) T ->
      typ_has G T l D ->
      has G (trm_var (avar_f v)) l (open_dec v D)
with subtyp: tmode -> ctx -> typ -> typ -> Datatypes.nat -> Prop :=
  | subtyp_refl: forall G T n,
      subtyp notrans G T T n
  | subtyp_top: forall G T n,
      subtyp notrans G T typ_top n
  | subtyp_bot: forall G T n,
      subtyp notrans G typ_bot T n
  | subtyp_rfn_l: forall G T1 l1 D1 T2 n,
      subtyp oktrans G T1 T2 n ->
      subtyp notrans G (typ_rfn T1 l1 D1) T2 n
  (* If T1 is not a subtype of T2, subtyp_rfn_l does not apply.
     If you still believe that (typ_rfn T1 l1 D1) is a subtype of T2, you have
     to use subtyp_rfn_r instead. *)
  | subtyp_rfn_r: forall L G T1 T2 l D1 D2 n,
      subtyp oktrans G T1 T2 n ->
      typ_has G T1 l D1 ->
      (forall z, z \notin L -> subdec (G & z ~ T1) (open_dec z D1) (open_dec z D2) n) ->
      subtyp notrans G T1 (typ_rfn T2 l D2) (S n)
  | subtyp_sel_l: forall G p L S U T n,
      has G (pth2trm p) L (dec_typ S U) ->
      subtyp oktrans G U T n ->
      subtyp notrans G (typ_sel p L) T n
  | subtyp_sel_r: forall G p L S U T n,
      has G (pth2trm p) L (dec_typ S U) ->
      subtyp oktrans G S U n -> (* <--- makes proofs a lot easier!! *)
      subtyp oktrans G T S n ->
      subtyp notrans G T (typ_sel p L) n
  | subtyp_tmode: forall G T1 T2 n,
      subtyp notrans G T1 T2 n ->
      subtyp oktrans G T1 T2 n
  | subtyp_trans: forall G T1 T2 T3 n,
      subtyp oktrans G T1 T2 n ->
      subtyp oktrans G T2 T3 n ->
      subtyp oktrans G T1 T3 n
  | subtyp_and: forall G S T1 T2 n,
      subtyp oktrans G S T1 n ->
      subtyp oktrans G S T2 n ->
      subtyp notrans G S (typ_and T1 T2) n
  | subtyp_and_l: forall G T1 T2 S n,
      subtyp oktrans G T1 S n ->
      subtyp notrans G (typ_and T1 T2) S n
  | subtyp_and_r: forall G T1 T2 S n,
      subtyp oktrans G T2 S n ->
      subtyp notrans G (typ_and T1 T2) S n
  | subtyp_or: forall G T1 T2 S n,
      subtyp oktrans G T1 S n ->
      subtyp oktrans G T2 S n ->
      subtyp notrans G (typ_or T1 T2) S n
  | subtyp_or_l: forall G S T1 T2 n,
      subtyp oktrans G S T1 n ->
      subtyp notrans G S (typ_or T1 T2) n
  | subtyp_or_r: forall G S T1 T2 n,
      subtyp oktrans G S T2 n ->
      subtyp notrans G S (typ_or T1 T2) n
with subdec: ctx -> dec -> dec -> Datatypes.nat -> Prop :=
  | subdec_typ: forall G Lo1 Hi1 Lo2 Hi2 n,
      (* Lo2 <: Lo1 <: Hi1 <: Hi2 *)
      subtyp oktrans G Lo2 Lo1 n ->
      subtyp oktrans G Lo1 Hi1 n ->
      subtyp oktrans G Hi1 Hi2 n ->
      subdec G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2) n
  | subdec_fld: forall G T1 T2 n,
      subtyp oktrans G T1 T2 n ->
      subdec G (dec_fld T1) (dec_fld T2) n
  | subdec_mtd: forall G S1 T1 S2 T2 n,
      subtyp oktrans G S2 S1 n ->
      subtyp oktrans G T1 T2 n ->
      subdec G (dec_mtd S1 T1) (dec_mtd S2 T2) n
with ty_trm: ctx -> trm -> typ -> Prop :=
  | ty_var: forall G x T,
      binds x T G ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_sel: forall G t l T,
      has G t l (dec_fld T) ->
      ty_trm G (trm_sel t l) T
  | ty_call: forall G t m U V u,
      has G t m (dec_mtd U V) ->
      ty_trm G u U ->
      ty_trm G (trm_call t m u) V
  | ty_new: forall L G ds T,
      (forall x, x \notin L -> ty_defs (G & x ~ T) (open_defs x ds) T) ->
      ty_trm G (trm_new ds) T
  | ty_sbsm: forall G t T U n,
      ty_trm G t T ->
      subtyp oktrans G T U n ->
      ty_trm G t U
with ty_def: ctx -> def -> dec -> Prop :=
  | ty_typ: forall G S T n,
      subtyp oktrans G S T n -> (* <----- only allow realizable bounds *)
      ty_def G (def_typ S T) (dec_typ S T)
  | ty_fld: forall G v T,
      ty_trm G (trm_var v) T ->
      ty_def G (def_fld T v) (dec_fld T)
  | ty_mtd: forall L G S T t,
      (forall x, x \notin L -> ty_trm (G & x ~ S) (open_trm x t) T) ->
      ty_def G (def_mtd S T t) (dec_mtd S T)
(* Note: ty_defs should be called with a self reference in the environment so that the
   defs can refer to "this". *)
with ty_defs: ctx -> defs -> typ -> Prop :=
  | ty_dsnil: forall G,
      ty_defs G defs_nil typ_top
  | ty_dscons: forall G ds d T D l,
      ty_defs G ds T ->
      ty_def G d D ->
      label_matches_dec l D ->
      can_add G ds l d ->
      ty_defs G (defs_cons ds l d) (typ_rfn T l D)
(* Note: can_add should also be called with a self reference in the environment. *)
with can_add: ctx -> defs -> label -> def -> Prop :=
  | can_add_typ: forall G ds L Lo Hi n,
      defs_hasnt ds L ->
      subtyp oktrans G Lo Hi n ->
      can_add G ds L (def_typ Lo Hi)
  | can_refine_typ: forall G ds L Lo1 Hi1 Lo2 Hi2 n1 n2 n3,
      defs_has ds L (def_typ Lo1 Hi1) ->
      (* added dec must have good bounds: *)
      subtyp oktrans G Lo2 Hi2 n1 ->
      (* and if intersected with existing bounds, still good: *)
      subtyp oktrans G Lo1 Hi2 n2 ->
      subtyp oktrans G Lo2 Hi1 n3 ->
      can_add G ds L (def_typ Lo2 Hi2)
  | can_add_fld: forall G ds l T x,
      defs_hasnt ds l ->
      can_add G ds l (def_fld T x)
  | can_add_mtd: forall G ds m T1 T2 t,
      defs_hasnt ds m ->
      can_add G ds m (def_mtd T1 T2 t).


(* "ty_def G ds d D" means "d has type D, and it's ok to put ds in front of it",
with ty_def: ctx -> defs -> def -> dec -> Prop :=
  | ty_typ: forall G S T n,
      subtyp oktrans G S T n -> (* <----- only allow realizable bounds *)
      ty_def G (def_typ S T) (dec_typ S T)
  | ty_fld: forall G v T,
      ty_trm G (trm_var v) T ->
      ty_def G (def_fld T v) (dec_fld T)
  | ty_mtd: forall L G S T t,
      (forall x, x \notin L -> ty_trm (G & x ~ S) (open_trm x t) T) ->
      ty_def G (def_mtd S T t) (dec_mtd S T)
*)

(*
with real_typ: ctx -> typ -> Prop :=
  | real_top: forall G,
      real_typ G typ_top
(*| real_bot: bottom type is not realizable *)
  | real_rfn: 
*)

(*
Inductive wf_typ: ctx -> typ -> Prop :=
  | wf_top : forall G,
      wf_typ G typ_top
  | wf_bot : forall G,
      wf_typ G typ_bot
  | wf_bind : forall L G Ds,
      (forall z, z \notin L -> wf_decs (G & z ~ typ_bind Ds) Ds) ->
      wf_typ G (typ_bind Ds)
  | wf_sel1 : forall G x L Lo Hi,
      has pr G (trm_var (avar_f x)) L (dec_typ Lo Hi) ->
      wf_typ G Lo ->
      wf_typ G Hi ->
      wf_typ G (typ_sel (pth_var (avar_f x)) L)
  | wf_sel2 : forall G x L U,
      has pr G (trm_var (avar_f x)) L (dec_typ typ_bot U) ->
      (* note: no check on U --> allows recursive class types are possible *)
      wf_typ G (typ_sel (pth_var (avar_f x)) L)
with wf_dec : ctx -> dec -> Prop :=
  | wf_tmem : forall G Lo Hi,
      wf_typ G Lo ->
      wf_typ G Hi ->
      wf_dec G (dec_typ Lo Hi)
  | wf_fld : forall G T,
      wf_typ G T ->
      wf_dec G (dec_fld T)
  | wf_mtd : forall G A R,
      wf_typ G A ->
      wf_typ G R ->
      wf_dec G (dec_mtd A R)
with wf_decs : ctx -> decs -> Prop :=
  | wf_nil : forall G,
      wf_decs G decs_nil
  | wf_cons : forall G n D Ds,
      wf_dec G D ->
      wf_decs G Ds ->
      wf_decs G (decs_cons n D Ds).
*)

(** *** Well-formed store *)
Inductive wf_sto: sto -> ctx -> Prop :=
  | wf_sto_empty : wf_sto empty empty
  | wf_sto_push : forall s G x ds T,
      wf_sto s G ->
      x # s ->
      x # G ->
      (* What's below is the same as the ty_new rule, but ds have already been opened
         with x, so there's no need to open again. *)
      ty_defs (G & x ~ T) ds T ->
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
with   has_mut     := Induction for has     Sort Prop
with   subtyp_mut  := Induction for subtyp  Sort Prop
with   subdec_mut  := Induction for subdec  Sort Prop
with   ty_trm_mut  := Induction for ty_trm  Sort Prop
with   ty_def_mut  := Induction for ty_def  Sort Prop
with   ty_defs_mut := Induction for ty_defs Sort Prop
with   can_add_mut := Induction for can_add Sort Prop.
Combined Scheme ty_mutind from typ_has_mut, has_mut,
                               subtyp_mut, subdec_mut,
                               ty_trm_mut, ty_def_mut, ty_defs_mut, can_add_mut.

Scheme has_mut2    := Induction for has    Sort Prop
with   ty_trm_mut2 := Induction for ty_trm Sort Prop.
Combined Scheme ty_has_mutind from has_mut2, ty_trm_mut2.

Scheme subtyp_mut2  := Induction for subtyp  Sort Prop
with   subdec_mut2  := Induction for subdec  Sort Prop.
Combined Scheme subtyp_subdec_mut from subtyp_mut2, subdec_mut2.


(* ###################################################################### *)
(** ** Tactics *)

Ltac auto_specialize :=
  repeat match goal with
  | Impl: ?Cond ->            _ |- _ => let HC := fresh in 
      assert (HC: Cond) by auto; specialize (Impl HC); clear HC
  | Impl: forall (_ : ?Cond), _ |- _ => match goal with
      | p: Cond |- _ => specialize (Impl p)
      end
  end.

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

Hint Constructors typ_has has subtyp subdec ty_trm ty_def ty_defs can_add.
Hint Constructors defs_has defs_hasnt.
Hint Constructors label_matches_def label_matches_dec.

(* ###################################################################### *)
(** ** Library extensions *)

Lemma fresh_push_eq_inv: forall A x a (E: env A),
  x # (E & x ~ a) -> False.
Proof.
  intros. rewrite dom_push in H. false H. rewrite in_union.
  left. rewrite in_singleton. reflexivity.
Qed.

Definition vars_empty: vars := \{}. (* because tactic [exists] cannot infer type var *)


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
  | typ_rfn T l D => typ_rfn (subst_typ z u T) l (subst_dec z u D)
  | typ_sel p L => typ_sel (subst_pth z u p) L
  | typ_and T1 T2 => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_or  T1 T2 => typ_or  (subst_typ z u T1) (subst_typ z u T2)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ T U => dec_typ (subst_typ z u T) (subst_typ z u U)
  | dec_fld T   => dec_fld (subst_typ z u T)
  | dec_mtd T U => dec_mtd (subst_typ z u T) (subst_typ z u U)
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
  | def_typ T1 T2 => def_typ (subst_typ z u T1) (subst_typ z u T2)
  | def_fld T x => def_fld (subst_typ z u T) (subst_avar z u x)
  | def_mtd T1 T2 b => def_mtd (subst_typ z u T1) (subst_typ z u T2) (subst_trm z u b)
  end
with subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest l d => defs_cons (subst_defs z u rest) l (subst_def z u d)
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
(** ** Helper lemmas for definition/declaration lists *)

(* does not hold any more because grammar does not enforce that label_fld
   can only be the label for dec_fld!
Lemma defs_has_fld_sync: forall n d ds,
  defs_has ds (label_fld n) d -> exists T x, d = (def_fld T x).
Proof.
 induction ds; unfolds defs_has, get_def. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_def in H. destruct* d; discriminate.
    - apply* IHds.
Qed.

Lemma defs_has_mtd_sync: forall n d ds,
  defs_has ds (label_mtd n) d -> exists e, d = (def_mtd e).
Proof.
  introv Hhas. induction ds; unfolds defs_has, get_def. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_def in H. destruct* d; discriminate.
    - apply* IHds.
Qed.

Lemma decs_has_typ_sync: forall n D Ds,
  decs_has Ds (label_typ n) D -> exists Lo Hi, D = (dec_typ Lo Hi).
Proof.
  introv Hhas. induction Ds; unfolds decs_has, get_dec. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_dec in H. destruct* D; discriminate.
    - apply* IHDs.
Qed.

Lemma decs_has_fld_sync: forall n d ds,
  decs_has ds (label_fld n) d -> exists x, d = (dec_fld x).
Proof.
  introv Hhas. induction ds; unfolds decs_has, get_dec. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_dec in H. destruct* d; discriminate.
    - apply* IHds.
Qed.

Lemma decs_has_mtd_sync: forall n d ds,
  decs_has ds (label_mtd n) d -> exists T U, d = (dec_mtd T U).
Proof.
  introv Hhas. induction ds; unfolds decs_has, get_dec. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_dec in H. destruct* d; discriminate.
    - apply* IHds.
Qed.*)


(* ###################################################################### *)
(** ** Context size lemmas *)

Definition ctx_size(G: ctx) := LibList.length G.

Lemma inc_max_ctx:
   (forall m     G T1  T2  n1, subtyp m G T1  T2  n1 ->
      forall n2, n1 <= n2  ->  subtyp m G T1  T2  n2  )
/\ (forall       G D1  D2  n1, subdec   G D1  D2  n1 ->
      forall n2, n1 <= n2 ->   subdec   G D1  D2  n2  ).
Proof.
  apply subtyp_subdec_mut; try solve [intros; [constructor*
    || apply* subtyp_sel_l
    || apply* subtyp_sel_r
  ]].
  + (* case subtyp_rfn_r *)
    introv St IHSt THas Sd IHSd HLe. rename n into n1.
    destruct n2 as [|n2]; [omega | idtac].
    assert (n1 <= n2) by omega. apply* subtyp_rfn_r.
  + (* case subtyp_trans *)
    intros. apply subtyp_trans with T2; auto.
  + (* case subtyp_and_r *)
    intros. apply subtyp_and_r. apply* H.
  + (* case subtyp_or_r *)
    intros. apply subtyp_or_r. apply* H.
Qed.

Definition subtyp_max_ctx := proj1 inc_max_ctx.
Definition subdec_max_ctx := proj2 inc_max_ctx.

Lemma ctx_size_push: forall G z T, ctx_size (G & z ~ T) = S (ctx_size G).
Proof.
  intros. unfold ctx_size. rewrite <- cons_to_push.
  rewrite LibList.length_cons. omega.
Qed.

Lemma ctx_size_swap_middle: forall G1 x T y U G2,
  ctx_size (G1 & x ~ T & G2) = ctx_size (G1 & y ~ U & G2).
Proof.
  intros. rewrite concat_def. rewrite single_def. unfold ctx_size.
  repeat progress rewrite LibList.length_app. auto.
Qed.


(* ###################################################################### *)
(** ** Trivial inversion lemmas *)

Lemma invert_subdec_typ_sync_right: forall G D2 Lo1 Hi1 n,
  subdec G (dec_typ Lo1 Hi1) D2 n ->
  exists Lo2 Hi2, D2 = (dec_typ Lo2 Hi2) /\
                  subtyp oktrans G Lo2 Lo1 n /\
                  subtyp oktrans G Lo1 Hi1 n /\
                  subtyp oktrans G Hi1 Hi2 n.
Proof.
  introv Sd. inversions Sd. exists Lo2 Hi2. auto.
Qed.

Lemma invert_subdec_typ_sync_left: forall G D Lo2 Hi2 n,
   subdec G D (dec_typ Lo2 Hi2) n ->
   exists Lo1 Hi1, D = (dec_typ Lo1 Hi1) /\
                   subtyp oktrans G Lo2 Lo1 n /\
                   subtyp oktrans G Lo1 Hi1 n /\
                   subtyp oktrans G Hi1 Hi2 n.
Proof.
  introv Sd. inversions Sd. exists Lo1 Hi1. auto.
Qed.

Lemma invert_subdec_fld_sync_left: forall G D T2 n,
   subdec G D (dec_fld T2) n ->
   exists T1, D = (dec_fld T1) /\
              subtyp oktrans G T1 T2 n.
Proof.
  introv Sd. inversions Sd. exists T1. auto.
Qed.

Lemma invert_subdec_mtd_sync_left: forall G D T2 U2 n,
   subdec G D (dec_mtd T2 U2) n ->
   exists T1 U1, D = (dec_mtd T1 U1) /\
                 subtyp oktrans G T2 T1 n /\
                 subtyp oktrans G U1 U2 n.
Proof.
  introv Sd. inversions Sd. exists S1 T1. auto.
Qed.

(*
Lemma invert_subdec_typ: forall m G Lo1 Hi1 Lo2 Hi2,
  subdec m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2) ->
  subtyp m oktrans G Lo2 Lo1 /\ subtyp m oktrans G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. auto.
Qed.
*)

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

(*
Lemma ty_def_to_label_for_eq: forall G d D n, 
  ty_def G d D ->
  label_for_def n d = label_for_dec n D.
Proof.
  intros. inversions H; reflexivity.
Qed.
*)

(*
Lemma extract_ty_def_from_ty_defs: forall G l d ds D Ds,
  ty_defs G ds Ds ->
  defs_has ds l d ->
  decs_has Ds l D ->
  ty_def G d D.
Proof.
  introv HdsDs. induction HdsDs.
  + intros. inversion H.
  + introv dsHas DsHas. unfolds defs_has, decs_has, get_def, get_dec. 
    rewrite (ty_def_to_label_for_eq n H) in dsHas. case_if.
    - inversions dsHas. inversions DsHas. assumption.
    - apply* IHHdsDs.
Qed.
*)

Lemma invert_ty_var: forall G x T,
  ty_trm G (trm_var (avar_f x)) T ->
  exists T' n, subtyp oktrans G T' T n /\ binds x T' G.
Proof.
  introv Ty. gen_eq t: (trm_var (avar_f x)). gen x.
  induction Ty; intros x' Eq; try (solve [ discriminate ]).
  + inversions Eq. exists T 0.
    apply (conj (subtyp_tmode (subtyp_refl _ _ _))). assumption.
  + subst. specialize (IHTy _ eq_refl). destruct IHTy as [T' [n2 [St Bi]]].
    exists T' (max n n2). split.
    - apply subtyp_trans with T.
      * apply (subtyp_max_ctx St). apply Max.le_max_r.
      * apply (subtyp_max_ctx H). apply Max.le_max_l.
    - exact Bi.
Qed.

(*
Lemma invert_ty_mtd_inside_ty_defs: forall G ds Ds m S T body,
  ty_defs G ds Ds ->
  defs_has ds (label_mtd m) (def_mtd body) ->
  decs_has Ds (label_mtd m) (dec_mtd S T) ->
  (* conclusion is the premise needed to construct a ty_mtd: *)
  exists L, forall x, x \notin L -> ty_trm (G & x ~ S) (open_trm x body) T.
Proof.
  introv HdsDs dsHas DsHas.
  lets H: (extract_ty_def_from_ty_defs HdsDs dsHas DsHas).
  inversions* H. 
Qed.

Lemma invert_ty_fld_inside_ty_defs: forall G ds Ds l v T,
  ty_defs G ds Ds ->
  defs_has ds (label_fld l) (def_fld v) ->
  decs_has Ds (label_fld l) (dec_fld T) ->
  (* conclusion is the premise needed to construct a ty_fld: *)
  ty_trm G (trm_var v) T.
Proof.
  introv HdsDs dsHas DsHas.
  lets H: (extract_ty_def_from_ty_defs HdsDs dsHas DsHas).
  inversions* H. 
Qed.
*)

Lemma not_defs_has_and_hasnt: forall ds l d,
  defs_has ds l d -> defs_hasnt ds l -> False.
Proof.
  intro ds. induction ds.
  - introv nilHas. inversions nilHas. (* contradiction *)
  - introv dsHas dsHasnt. inversions dsHas; inversions dsHasnt; auto_star.
Qed.

Lemma defs_has_and_hasnt: forall ds l1 d1 l2,
  defs_has ds l1 d1 -> defs_hasnt ds l2 -> l1 <> l2.
Proof.
  introv dsHas dsHasnt. intro. subst. apply (not_defs_has_and_hasnt dsHas dsHasnt).
Qed.

Lemma invert_typ_rfn_has: forall G T l0 D0 l D,
  typ_has G (typ_rfn T l0 D0) l D ->
  typ_has G T l D \/
  label_matches_dec l0 D0 /\ l0 = l /\ D0 = D \/
  exists D1, typ_has G T l D1 /\ l0 = l /\ D = (intersect_dec D1 D0).
Proof.
  introv THas. inversions THas; eauto 10.
Qed.

Lemma invert_typ_sel_has: forall G p L l D,
  typ_has G (typ_sel p L) l D ->
  exists Lo Hi, has G (pth2trm p) L (dec_typ Lo Hi) /\ typ_has G Hi l D.
Proof. intros. inversions* H. Qed.

Lemma invert_typ_and_has: forall G T1 T2 l D,
  typ_has G (typ_and T1 T2) l D ->
  typ_has G T1 l D \/
  typ_has G T2 l D \/ 
  exists D1 D2, typ_has G T1 l D1 /\ typ_has G T2 l D2 /\ D = intersect_dec D1 D2.
Proof.
  introv THas. inversions THas; eauto 10.
Qed.

Lemma invert_typ_or_has: forall G T1 T2 l D,
  typ_has G (typ_or T1 T2) l D ->
  exists D1 D2, typ_has G T1 l D1 /\ typ_has G T2 l D2 /\ D = union_dec D1 D2.
Proof.
  introv THas. inversions THas; eauto 10.
Qed.

Lemma invert_can_add_typ: forall G ds L Lo Hi,
  can_add G ds L (def_typ Lo Hi) ->
     (exists n, defs_hasnt ds L /\
                subtyp oktrans G Lo Hi n)
  \/ (exists n1 n2 n3 Lo1 Hi1, defs_has ds L (def_typ Lo1 Hi1) /\
                subtyp oktrans G Lo Hi n1 /\
                subtyp oktrans G Lo1 Hi n2 /\
                subtyp oktrans G Lo Hi1 n3).
Proof.
  introv C. inversions C; [left | right].
  - exists n. auto.
  - exists n1 n2 n3 Lo1 Hi1. auto.
Qed.

Lemma invert_can_add_fld: forall G ds l T x,
  can_add G ds l (def_fld T x) ->
  defs_hasnt ds l.
Proof.
  introv C. inversions* C.
Qed.

Lemma invert_can_add_mtd: forall G ds m T1 T2 t,
  can_add G ds m (def_mtd T1 T2 t) ->
  defs_hasnt ds m.
Proof.
  introv C. inversions* C.
Qed.

(* Not needed:
Lemma subdec_typ_refl: forall G Lo Hi n,
  subtyp oktrans G Lo Hi n -> subdec G (dec_typ Lo Hi) (dec_typ Lo Hi) n.
Proof.
  introv St. apply subdec_typ.
  + apply subtyp_tmode. apply subtyp_refl.
  + exact St.
  + apply subtyp_tmode. apply subtyp_refl.
Qed.
Hint Resolve subdec_typ_refl.
*)

Lemma defs_has_hit_eq: forall ds l D1 D2, 
  defs_hasnt ds l ->
  defs_has (defs_cons ds l D1) l D2 ->
  D1 = D2.
Proof.
  introv dsHasnt dsHas. inversions dsHas.
  + (* case defs_has_hit *)
    reflexivity.
  + (* case defs_has_skip *)
    false* H5.
  + (* case defs_has_merge *)
    exfalso. apply (not_defs_has_and_hasnt H4 dsHasnt).
Qed.

Lemma defs_has_unique: forall ds l D1 D2,
  defs_has ds l D1 ->
  defs_has ds l D2 ->
  D1 = D2.
Proof.
  intro ds. induction ds; introv dsHas1 dsHas2.
  + inversions dsHas1. (* contradiction *)
  + inversions dsHas1; inversions dsHas2.
    - reflexivity.
    - false* H7.
    - exfalso. apply (not_defs_has_and_hasnt H6 H5).
    - false* H5.
    - apply* IHds.
    - false* H5.
    - exfalso. apply (not_defs_has_and_hasnt H4 H6).
    - false* H6.
    - specialize (IHds _ _ _ H4 H6). inversions IHds. reflexivity.
Qed.

Lemma invert_defs_has_merge: forall ds l Lo0 Hi0 Lo1 Hi1 Lo Hi,
  defs_has ds l (def_typ Lo1 Hi1) ->
  defs_has (defs_cons ds l (def_typ Lo0 Hi0)) l (def_typ Lo Hi) ->
  Lo = typ_or Lo1 Lo0 /\ Hi = typ_and Hi1 Hi0.
Proof.
  introv dsHas H. inversions H.
  + (* case defs_has_hit *)
    exfalso. apply (not_defs_has_and_hasnt dsHas H7).
  + (* case defs_has_skip *)
    false* H6.
  + (* case defs_has_merge *)
    lets Eq: (defs_has_unique dsHas H5). inversions Eq. auto.
Qed.

Lemma invert_defs_has_skip: forall ds l0 d0 l D,
  defs_has (defs_cons ds l0 d0) l D ->
  l0 <> l ->
  defs_has ds l D.
Proof.
  introv dsHas Ne. inversions dsHas.
  + (* case defs_has_hit *)
    false* Ne.
  + (* case defs_has_skip *)
    exact H4.
  + (* case defs_has_merge *)
    false* Ne.
Qed.

Lemma subtyp_or_and: forall G Lo0 Hi0 Lo1 Hi1 n1 n2 n3 n4,
  subtyp oktrans G Lo0 Hi0 n1 ->
  subtyp oktrans G Lo1 Hi0 n2 ->
  subtyp oktrans G Lo0 Hi1 n3 ->
  subtyp oktrans G Lo1 Hi1 n4 ->
  exists n, subtyp oktrans G (typ_or Lo1 Lo0) (typ_and Hi1 Hi0) n.
Proof.
  introv St1 St2 St3 St4.
  remember (max n1 (max n2 (max n3 n4))) as n.
  assert (n1 <= n /\ n2 <= n /\ n3 <= n /\ n4 <= n). {
    lets L1: (Max.le_max_l n1 (max n2 (max n3 n4))).
    lets L2: (Max.le_max_l n2 (max n3 n4)).
    lets L3: (Max.le_max_l n3 n4).
    lets R1: (Max.le_max_r n1 (max n2 (max n3 n4))).
    lets R2: (Max.le_max_r n2 (max n3 n4)).
    lets R3: (Max.le_max_r n3 n4).
    omega.
  }
  exists n.
  apply subtyp_tmode. apply subtyp_and; apply subtyp_tmode; apply subtyp_or.
  + apply (subtyp_max_ctx St4). omega.
  + apply (subtyp_max_ctx St3). omega.
  + apply (subtyp_max_ctx St2). omega.
  + apply (subtyp_max_ctx St1). omega.
Qed.

Lemma ty_defs_to_good_bounds: forall G ds T l Lo Hi,
  ty_defs G ds T ->
  defs_has ds l (def_typ Lo Hi) ->
  exists n, subtyp oktrans G Lo Hi n.
Proof.
  introv Tyds. gen l Lo Hi. induction Tyds.
  + introv dsHas. inversions dsHas. (* contradiction *)
  + rename H into Tyd0, l into l0, D into D0, d into d0, H0 into M, H1 into C.
    introv dsHas. destruct (classicT (l0 = l)) as [Eq | Ne].
    - (* case l0 = l *)
      subst. destruct d0 as [Lo0 Hi0 | T0 a | U0 V0 t]; inversions Tyd0.
      * apply invert_can_add_typ in C.
        destruct C as [ [n' [dsHasnt St]]
                      | [n1 [n2 [n3 [Lo1 [Hi1 [dsHas' [St1 [St2 St3]]]]]]]]].
        { lets Eq: (defs_has_hit_eq dsHasnt dsHas). inversions Eq. exists n'. exact St. }
        { specialize (IHTyds _ _ _ dsHas'). destruct IHTyds as [n4 St4].
          destruct (invert_defs_has_merge dsHas' dsHas) as [Eq1 Eq2]. subst.
          apply (subtyp_or_and St1 St2 St3 St4). }
      * inversions dsHas. false* H6.
      * inversions dsHas. false* H6.
    - (* case l0 <> l *)
      lets dsHas': (invert_defs_has_skip dsHas Ne).
      apply (IHTyds _ _ _ dsHas').
Qed.

Lemma invert_ty_defs: forall G l ds T D2,
  ty_defs G ds T ->
  typ_has G T l D2 ->
  exists d D1 n, defs_has ds l d /\ ty_def G d D1 /\ subdec G D1 D2 n.
Proof.
  introv Tyds. gen l D2. induction Tyds.
  + introv THas. inversions THas. (* contradiction *)
  + rename H into Tyd0, l into l0, D into D0, d into d0, H0 into M, H1 into C.
    introv THas.
    apply invert_typ_rfn_has in THas.
    destruct d0 as [Lo0 Hi0 | T0 a | U0 V0 t].
    - inversions Tyd0. inversions M.
      apply invert_can_add_typ in C.
      destruct THas as [THas | [[M' [Eq1 Eq2]] | [D1 [THas [Eq1 Eq2]]]]].
      * specialize (IHTyds _ _ THas). destruct IHTyds as [d [D1 [n'' [dsHas [Tyd Sd]]]]].
        destruct (classicT ((label_typ n0) = l)) as [Eq | Ne].
        (* case l0 = l *) {
          subst. destruct C as [ [n' [dsHasnt St]]
                               | [n1 [n2 [n3 [Lo1 [Hi1 [dsHas' [St1 [St2 St3]]]]]]]]].
          + false (not_defs_has_and_hasnt dsHas dsHasnt).
          + lets Eq: (defs_has_unique dsHas dsHas'). subst. inversions Tyd.
            apply invert_subdec_typ_sync_right in Sd.
            destruct Sd as [Lo1' [Hi1' [Eq [St5 [St6 St7]]]]]. subst.
            rename H4 into St4.
            lets St9: (subtyp_or_and St1 St2 St3 St4). destruct St9 as [n9 St9].
            exists (def_typ (typ_or Lo1 Lo0) (typ_and Hi1 Hi0))
                   (dec_typ (typ_or Lo1 Lo0) (typ_and Hi1 Hi0)) n9.
            repeat split.
            - apply defs_has_merge. exact dsHas'.
            - apply ty_typ with n9. exact St9.
            - assert (n'' = n9) by admit. subst. apply subdec_typ.
              * apply subtyp_tmode. apply subtyp_or_l. exact St5.
              * exact St9.
              * apply subtyp_tmode. apply subtyp_and_l. exact St7.
        }
        (* case l0 <> l *) { eauto 10. }
      * subst. destruct C as [ [n' [dsHasnt St]]
                             | [n1 [n2 [n3 [Lo1 [Hi1 [dsHas' [St1 [St2 St3]]]]]]]]].
        { exists (def_typ Lo0 Hi0) (dec_typ Lo0 Hi0) n. eauto 10. }
        { lets St4: (ty_defs_to_good_bounds Tyds dsHas'). destruct St4 as [n4 St4].
          lets St9: (subtyp_or_and St1 St2 St3 St4). destruct St9 as [n9 St9].
          exists (def_typ (typ_or Lo1 Lo0) (typ_and Hi1 Hi0))
                 (dec_typ (typ_or Lo1 Lo0) (typ_and Hi1 Hi0)) n9.
          repeat split.
          + apply defs_has_merge. exact dsHas'.
          + apply ty_typ with n9. exact St9.
          + apply subdec_typ.
            - apply subtyp_tmode. apply subtyp_or_r. apply subtyp_tmode. apply subtyp_refl.
            - exact St9.
            - apply subtyp_tmode. apply subtyp_and_r. apply subtyp_tmode. apply subtyp_refl.
        }
      * subst.
        specialize (IHTyds _ _ THas). destruct IHTyds as [d [D1' [n'' [dsHas [Tyd Sd]]]]].
        destruct C as [ [n' [dsHasnt St]]
                      | [n1 [n2 [n3 [Lo1 [Hi1 [dsHas' [St1 [St2 St3]]]]]]]]].
        { exfalso. apply (not_defs_has_and_hasnt dsHas dsHasnt). }
        { lets Eq: (defs_has_unique dsHas dsHas'). subst. inversions Tyd.
          apply invert_subdec_typ_sync_right in Sd.
          destruct Sd as [Lo1' [Hi1' [Eq [St5 [St6 St7]]]]]. subst. simpl.
          rename H4 into St4.
          lets St9: (subtyp_or_and St1 St2 St3 St4). destruct St9 as [n9 St9].
          exists (def_typ (typ_or Lo1 Lo0) (typ_and Hi1 Hi0))
                 (dec_typ (typ_or Lo1 Lo0) (typ_and Hi1 Hi0)) n9.
          repeat split.
          + apply defs_has_merge. exact dsHas'.
          + apply ty_typ with n9. exact St9.
          + assert (n'' = n9) by admit. subst. apply subdec_typ.
            - apply subtyp_tmode. apply subtyp_or.
              * apply subtyp_tmode. apply subtyp_or_l. exact St5.
              * apply subtyp_tmode. apply subtyp_or_r.
                apply subtyp_tmode. apply subtyp_refl.
            - exact St9.
            - apply subtyp_tmode. apply subtyp_and.
              * apply subtyp_tmode. apply subtyp_and_l. exact St7.
              * apply subtyp_tmode. apply subtyp_and_r.
                apply subtyp_tmode. apply subtyp_refl.
        }
    - apply invert_can_add_fld in C. rename C into dsHasnt.
      destruct THas as [THas | [[M' [Eq1 Eq2]] | [D1 [THas [Eq1 Eq2]]]]].
      * specialize (IHTyds _ _ THas). destruct IHTyds as [d [D1 [n [dsHas [Tyd Sd]]]]].
        lets Ne: (defs_has_and_hasnt dsHas dsHasnt).
        exists d D1 n. auto.
      * subst. inversions Tyd0.
        exists (def_fld T0 a) (dec_fld T0) 0. inversions M. auto.
      * subst.
        specialize (IHTyds _ _ THas). destruct IHTyds as [d [D1' [n [dsHas [Tyd Sd]]]]].
        false (not_defs_has_and_hasnt dsHas dsHasnt).
    - apply invert_can_add_mtd in C. rename C into dsHasnt.
      destruct THas as [THas | [[M' [Eq1 Eq2]] | [D1 [THas [Eq1 Eq2]]]]].
      * specialize (IHTyds _ _ THas). destruct IHTyds as [d [D1 [n [dsHas [Tyd Sd]]]]].
        lets Ne: (defs_has_and_hasnt dsHas dsHasnt).
        exists d D1 n. auto.
      * subst. inversions Tyd0.
        exists (def_mtd U0 V0 t) (dec_mtd U0 V0) 0. inversions M. eauto 10.
      * subst.
        specialize (IHTyds _ _ THas). destruct IHTyds as [d [D1' [n [dsHas [Tyd Sd]]]]].
        false (not_defs_has_and_hasnt dsHas dsHasnt).
Qed.

Print Assumptions invert_ty_defs.

(*
Lemma decs_has_to_defs_has: forall G l ds Ds D,
  ty_defs G ds Ds ->
  decs_has Ds l D ->
  exists d, defs_has ds l d.
Proof.
  introv Ty Bi. induction Ty; unfolds decs_has, get_dec. 
  + discriminate.
  + unfold defs_has. folds get_dec. rewrite get_def_cons. case_if.
    - exists d. reflexivity.
    - rewrite <- (ty_def_to_label_for_eq n H) in Bi. case_if. apply (IHTy Bi).
Qed.

Print Assumptions decs_has_to_defs_has.

Lemma defs_has_to_decs_has: forall G l ds Ds d,
  ty_defs G ds Ds ->
  defs_has ds l d ->
  exists D, decs_has Ds l D.
Proof.
  introv Ty dsHas. induction Ty; unfolds defs_has, get_def. 
  + discriminate.
  + unfold decs_has. folds get_def. rewrite get_dec_cons. case_if.
    - exists D. reflexivity.
    - rewrite -> (ty_def_to_label_for_eq n H) in dsHas. case_if. apply (IHTy dsHas).
Qed.

Print Assumptions defs_has_to_decs_has.

Lemma label_for_dec_open: forall z D n,
  label_for_dec n (open_dec z D) = label_for_dec n D.
Proof.
  intros. destruct D; reflexivity.
Qed.
*)


(* ###################################################################### *)
(** ** Uniqueness *)

(* Whooops! There's no uniqueness for typ_has and has, because:
   - typ_has can ignore one side of typ_and or typ_rfn
   - subsumption
*)

(* ty_def is unique because all defs are ascribed, and after the ascription,
   there's no chance to do any subsumption *)
Lemma ty_def_unique: forall G d D1 D2,
  ty_def G d D1 -> ty_def G d D2 -> D1 = D2.
Proof.
  introv Ty1 Ty2. destruct d; inversions Ty1; inversions Ty2; reflexivity.
Qed.

Lemma ty_defs_unique: forall G ds T1 T2,
  ty_defs G ds T1 -> ty_defs G ds T2 -> T1 = T2.
Proof.
  intros G ds. induction ds; introv Ty1 Ty2; inversions Ty1; inversions Ty2.
  + reflexivity.
  + f_equal.
    - apply* IHds.
    - apply* ty_def_unique.
Qed.


(* ###################################################################### *)
(** ** Weakening *)

Lemma weakening:
   (forall G T l D, typ_has G T l D -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      typ_has (G1 & G2 & G3) T l D)
/\ (forall G t l d, has G t l d -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      has (G1 & G2 & G3) t l d)
/\ (forall m G T1 T2 n, subtyp m G T1 T2 n -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subtyp m (G1 & G2 & G3) T1 T2 n)
/\ (forall G D1 D2 n, subdec G D1 D2 n -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdec (G1 & G2 & G3) D1 D2 n)
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
/\ (forall G ds l d, can_add G ds l d -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      can_add (G1 & G2 & G3) ds l d).
Proof.
  apply ty_mutind.
  + (* case typ_rfn_has_1 *)
    intros. apply* typ_rfn_has_1.
  + (* case typ_rfn_has_2 *)
    intros. apply* typ_rfn_has_2.
  + (* case typ_rfn_has_12 *)
    intros. apply* typ_rfn_has_12.
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
  + (* case has_trm  *)
    intros. apply* has_trm.
  + (* case has_pth  *)
    intros. subst. apply has_pth with T.
    - apply* H. (* apply* binds_weaken. *)
    - apply* H0.
  + (* case subtyp_refl *)
    intros. apply subtyp_refl.
  + (* case subtyp_top *)
    intros. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. apply subtyp_bot.
  + (* case subtyp_rfn_l *)
    intros. apply* subtyp_rfn_l.
  + (* case subtyp_rfn_r *)
    introv St IHSt THas IHTHas Sd IHSd Eq Ok. subst.
    apply_fresh subtyp_rfn_r as z.
    - apply* IHSt.
    - apply* IHTHas.
    - rewrite <- concat_assoc.
      assert (zL: z \notin L) by auto.
      specialize (Sd z zL).
      refine (IHSd z zL G1 G2 (G3 & z ~ T1) _ _).
        * rewrite <- concat_assoc. reflexivity.
        * rewrite concat_assoc. auto.
  + (* case subtyp_asel_l *)
    intros. subst. apply* subtyp_sel_l.
  + (* case subtyp_asel_r *)
    intros. subst. apply* subtyp_sel_r.
  + (* case subtyp_tmode *)
    intros. apply subtyp_tmode. apply* H.
  + (* case subtyp_trans *)
    intros. subst. apply* subtyp_trans.
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
  + (* case subdec_typ *)
    intros. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. apply* subdec_mtd.
  + (* case ty_var *)
    intros. subst. apply ty_var. apply* binds_weaken.
  + (* case ty_sel *)
    intros. subst. apply* ty_sel.
  + (* case ty_call *)
    intros. subst. apply* ty_call.
  + (* case ty_new *)
    intros L G ds T Tyds IHTyds G1 G2 G3 Eq Ok. subst.
    apply_fresh ty_new as x.
    - assert (xL: x \notin L) by auto.
      specialize (IHTyds x xL G1 G2 (G3 & x ~ T)).
      rewrite <- concat_assoc. apply IHTyds.
      * rewrite concat_assoc. reflexivity.
      * rewrite concat_assoc. auto.
  + (* case ty_sbsm *)
    intros. apply ty_sbsm with T n.
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
    intros. apply ty_dsnil.
  + (* case ty_dscons *) 
    intros. apply* ty_dscons.
  + (* case can_add_typ *)
    intros. apply* can_add_typ.
  + (* case can_refine_typ *)
    intros. apply* can_refine_typ.
  + (* case can_add_fld *)
    intros. apply* can_add_fld.
  + (* case can_add_mtd *)
    intros. apply* can_add_mtd.
Qed.

Print Assumptions weakening.

Lemma weaken_subtyp_middle: forall m G1 G2 G3 S U n,
  ok (G1 & G2 & G3) -> 
  subtyp m (G1      & G3) S U n ->
  subtyp m (G1 & G2 & G3) S U n.
Proof.
  destruct weakening as [_ [_ [W _]]].
  introv Hok123 Hst.
  specialize (W m (G1 & G3) S U n Hst).
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

Lemma weaken_subtyp_end: forall m G1 G2 S U n,
  ok (G1 & G2) -> 
  subtyp m G1        S U n ->
  subtyp m (G1 & G2) S U n.
Proof.
  introv Hok Hst.
  apply (env_remove_empty (fun G0 => subtyp m G0 S U n) (G1 & G2)).
  apply weaken_subtyp_middle.
  apply (env_add_empty (fun G0 => ok G0) (G1 & G2) Hok).
  apply (env_add_empty (fun G0 => subtyp m G0 S U n) G1 Hst).
Qed.

(*
Lemma weaken_has_end: forall m G1 G2 t l d,
  ok (G1 & G2) -> has m G1 t l d -> has m (G1 & G2) t l d.
Proof.
  intros.
  destruct weakening as [_ [W _]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W m (G1 & empty)); rewrite* concat_empty_r.
Qed.
*)

Lemma weaken_subdec_middle: forall G1 G2 G3 S U n,
  ok (G1 & G2 & G3) -> 
  subdec (G1      & G3) S U n ->
  subdec (G1 & G2 & G3) S U n.
Proof.
  destruct weakening as [_ [_ [_ [W _]]]].
  introv Hok123 Hst.
  specialize (W (G1 & G3) S U n Hst).
  specialize (W G1 G2 G3 eq_refl Hok123).
  apply W.
Qed.

Lemma weaken_subdec_end: forall G1 G2 D1 D2 n,
  ok (G1 & G2) -> 
  subdec G1        D1 D2 n ->
  subdec (G1 & G2) D1 D2 n.
Proof.
  introv Ok Sd.
  destruct weakening as [_ [_ [_ [W _]]]].
  rewrite <- (concat_empty_r G1) in Sd.
  specialize (W (G1 & empty) D1 D2 _ Sd G1 G2 empty).
  repeat progress rewrite concat_empty_r in *.
  apply (W eq_refl Ok).
Qed.

Lemma weaken_ty_trm_end: forall G1 G2 e T,
  ok (G1 & G2) -> ty_trm G1 e T -> ty_trm (G1 & G2) e T.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [W _]]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

(*
Lemma weaken_ty_def_end: forall G1 G2 i d,
  ok (G1 & G2) -> ty_def G1 i d -> ty_def (G1 & G2) i d.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [_ [_ [W _]]]]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.
*)

Lemma weaken_ty_defs_end: forall G1 G2 is Ds,
  ok (G1 & G2) -> ty_defs G1 is Ds -> ty_defs (G1 & G2) is Ds.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [_ [_ [W _]]]]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_trm_middle: forall G1 G2 G3 t T,
  ok (G1 & G2 & G3) -> ty_trm (G1 & G3) t T -> ty_trm (G1 & G2 & G3) t T.
Proof.
  intros. apply* weakening.
Qed.

(*
Lemma weaken_ty_def_middle: forall G1 G2 G3 d D,
  ty_def (G1 & G3) d D -> ok (G1 & G2 & G3) -> ty_def (G1 & G2 & G3) d D.
Proof.
  intros. apply* weakening.
Qed.

Lemma weaken_ty_defs_middle: forall G1 G2 G3 ds Ds,
  ty_defs (G1 & G3) ds Ds -> ok (G1 & G2 & G3) -> ty_defs (G1 & G2 & G3) ds Ds.
Proof.
  intros. apply* weakening.
Qed.
*)


(* ###################################################################### *)
(** ** The substitution principle *)

(*

without dependent types:

                  G, x: S |- e : T      G |- u : S
                 ----------------------------------
                            G |- [u/x]e : T

with dependent types:

                  G1, x: S, G2 |- t : T      G1 |- y : S
                 ---------------------------------------
                      G1, [y/x]G2 |- [y/x]t : [y/x]T


Note that in general, u is a term, but for our purposes, it suffices to consider
the special case where u is a variable.
*)

Lemma subst_binds: forall x y v T G,
  binds v T G ->
  binds v (subst_typ x y T) (subst_ctx x y G).
Proof.
  introv Bi. unfold subst_ctx. apply binds_map. exact Bi.
Qed.

(*
Inductive tyvar: pmode -> ctx -> var -> typ -> Prop :=
  | tyvar_pr: forall G x T,
      binds x T G ->
      tyvar pr G x T
  | tyvar_ip: forall G x T,
      ty_trm G (trm_var (avar_f x)) T ->
      tyvar ip G x T.
*)

(* TODO doesn't hold as such, we need some wf-ness as well *)
Lemma middle_notin: forall G1 x S G2,
  ok (G1 & x ~ S & G2) ->
  x # G1 /\
  x \notin fv_ctx_types G1 /\
  x \notin fv_typ S /\
  x \notin dom G2.
Admitted.

Lemma ok_concat_binds_left_to_notin_right: forall (A: Type) y (S: A) G1 G2,
  ok (G1 & G2) -> binds y S G1 -> y # G2.
Admitted.

Lemma concat_subst_ctx: forall x y G1 G2,
  subst_ctx x y G1 & subst_ctx x y G2 = subst_ctx x y (G1 & G2).
Proof.
  intros. unfold subst_ctx. rewrite map_concat. reflexivity.
Qed.

(* TODO also need x <> z *)
Lemma subst_dec_preserves_clo: forall D x y,
  (forall z : var, open_dec z D = D) ->
  (forall z : var, open_dec z (subst_dec x y D) = subst_dec x y D).
Admitted.

Lemma subst_ctx_preserves_notin: forall x y z G,
  z # G -> z # (subst_ctx x y G).
  (* because subst_ctx only modifies rhs, not lhs of bindings *)
Admitted.

Axiom okadmit: forall G: ctx, ok G.

Lemma subst_principles: forall y S,
   (forall G T l D, typ_has G T l D -> forall G1 G2 x,
     G = G1 & x ~ S & G2 ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & x ~ S & G2) ->
     typ_has (G1 & (subst_ctx x y G2)) (subst_typ x y T) l (subst_dec x y D))
/\ (forall G t l D, has G t l D -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     has (G1 & (subst_ctx x y G2)) (subst_trm x y t) l (subst_dec x y D))
/\ (forall m G T U n, subtyp m G T U n -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     subtyp m (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U) n)
/\ (forall G D1 D2 n, subdec G D1 D2 n -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     subdec (G1 & (subst_ctx x y G2)) (subst_dec x y D1) (subst_dec x y D2) n)
/\ (forall G t T, ty_trm G t T -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     ty_trm (G1 & (subst_ctx x y G2)) (subst_trm x y t) (subst_typ x y T))
/\ (forall G d D, ty_def G d D -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     ty_def (G1 & (subst_ctx x y G2)) (subst_def x y d) (subst_dec x y D))
/\ (forall G ds T, ty_defs G ds T -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     ty_defs (G1 & (subst_ctx x y G2)) (subst_defs x y ds) (subst_typ x y T))
/\ (forall G ds l d, can_add G ds l d -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     can_add (G1 & (subst_ctx x y G2)) (subst_defs x y ds) l (subst_def x y d)).
Proof.
  intros y S. apply ty_mutind.
  + (* case typ_rfn_has_1 *)
    admit.
  + (* case typ_rfn_has_2 *)
    admit.
  + (* case typ_rfn_has_12 *)
    admit.
  + (* case typ_sel_has *)
    admit.
  + (* case typ_and_has_1 *)
    admit.
  + (* case typ_and_has_2 *)
    admit.
  + (* case typ_and_has_12 *)
    admit.
  + (* case typ_or_has *)
    admit.
  + (* case has_trm *)
    intros G t T l D Ty IHTy THas IHTHas Clo G1 G2 x EqG Tyy Ok.
    subst. specialize (IHTy _ _ _ eq_refl Tyy Ok).
    apply has_trm with (subst_typ x y T).
    - exact IHTy.
    - apply* IHTHas.
    - apply (subst_dec_preserves_clo _ _ Clo).
  + (* case has_pth *)
    intros G z T l D Ty IHTy THas IHTHas G1 G2 x EqG Tyy Ok.
    subst. specialize (IHTy _ _ _ eq_refl Tyy Ok). simpl in *. case_if.
    - (* case z = x *)
      rewrite (subst_open_commute_dec x y x D). unfold subst_fvar. case_if.
      apply has_pth with (subst_typ x y T).
      * exact IHTy.
      * apply* IHTHas.
    - (* case z <> x *)
      rewrite (subst_open_commute_dec x y z D). unfold subst_fvar. case_if.
      apply has_pth with (subst_typ x y T).
      * exact IHTy.
      * apply* IHTHas.
  + (* case subtyp_refl *)
    introv EqG Ty Ok. subst. apply subtyp_refl.
  + (* case subtyp_top *)
    intros. simpl. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. simpl. apply subtyp_bot.
  + (* case subtyp_rfn_l *)
    admit.
  + (* case subtyp_rfn_r *)
    admit.
  + (* case subtyp_sel_l *)
    intros G p L Lo Hi T n Has IHHas St IHSt G1 G2 x EqG Tyy Ok. subst.
    specialize (IHSt _ _ _ eq_refl Tyy Ok).
    specialize (IHHas _ _ _ eq_refl Tyy Ok).
    destruct p as [v].
    destruct v as [n0 | v]; [admit | idtac]. (* bound vars not contradicts wf-ness *)
    simpl in *.
    assert (Eq: (trm_var (If v = x then avar_f y else avar_f v)) =
       (pth2trm (pth_var (If v = x then avar_f y else avar_f v))))
    by (case_if; reflexivity). rewrite Eq in IHHas.
    case_if; apply (subtyp_sel_l _ IHHas IHSt).
  + (* case subtyp_sel_r *)
    intros G p L Lo Hi T n Has IHHas St1 IHSt1 St2 IHSt2 G1 G2 x EqG Tyy Ok. subst.
    specialize (IHSt1 _ _ _ eq_refl Tyy Ok).
    specialize (IHSt2 _ _ _ eq_refl Tyy Ok).
    specialize (IHHas _ _ _ eq_refl Tyy Ok).
    destruct p as [v].
    destruct v as [n0 | v]; [admit | idtac]. (* bound vars not contradicts wf-ness *)
    simpl in *.
    assert (Eq: (trm_var (If v = x then avar_f y else avar_f v)) =
       (pth2trm (pth_var (If v = x then avar_f y else avar_f v))))
    by (case_if; reflexivity). rewrite Eq in IHHas.
    case_if; apply (subtyp_sel_r _ IHHas IHSt1 IHSt2).
  + (* case subtyp_tmode *)
    intros G T1 T2 n St IH G1 G2 x EqG Tyy Ok. subst.
    specialize (IH _ _ _ eq_refl Tyy Ok).
    apply (subtyp_tmode IH).
  + (* case subtyp_trans *)
    intros G T1 T2 T3 St12 IH12 St23 IH23 G1 G2 x Eqm EqG Tyy Ok. subst.
    apply* subtyp_trans.
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
  + (* case subdec_typ *)
    intros. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. apply* subdec_mtd.
  + (* case ty_var *)
    intros G z T Biz G1 G2 x EqG Tyy Ok. subst G.
    destruct (middle_notin Ok) as [xG1 [N2 [N3 N4]]].
    unfold subst_trm, subst_avar. case_var.
    - (* case z = x *)
      assert (EqST: T = S) by apply (binds_middle_eq_inv Biz Ok). subst.
      lets Ty: (invert_ty_var Tyy).
      destruct Ty as [S' [n [St Biy]]].
      lets yG2: (ok_concat_binds_left_to_notin_right (ok_remove Ok) Biy).
      apply (@subst_ctx_preserves_notin x y y G2) in yG2.
      apply weaken_ty_trm_end.
      * unfold subst_ctx. auto.
      * rewrite (@subst_fresh_typ x y S N3). exact Tyy.
    - (* case z <> x *)
      apply ty_var.
      rewrite <- (subst_fresh_ctx y G1 N2).
      rewrite -> (concat_subst_ctx _ _).
      lets Bi': (binds_subst Biz C).
      apply (subst_binds _ _ Bi').
  + (* case ty_sel *)
    intros G t l T Has IH G1 G2 x Eq Bi Ok. apply* ty_sel.
  + (* case ty_call *)
    intros G t m U V u Has IHt Tyu IHu G1 G2 x Eq Bi Ok. apply* ty_call.
  + (* case ty_new *)
    intros L G ds T Tyds IHTyds G1 G2 x Eq Tyy Ok. subst G. admit. (*
    apply_fresh ty_new as z.
      fold subst_defs.
      lets C: (@subst_open_commute_defs x y z ds).
      unfolds open_defs. unfold subst_fvar in C. case_var.
      rewrite <- C.
      admit.  TODO
      lets D: (@subst_open_commute_decs x y z Ds).
      unfolds open_defs. unfold subst_fvar in D. case_var.
      rewrite <- D.
      rewrite <- concat_assoc.
      assert (zL: z \notin L) by auto.
      specialize (IHTyds z zL G1 (G2 & z ~ typ_bind Ds) x). rewrite concat_assoc in IHTyds.
      specialize (IHTyds eq_refl Bi).
      unfold subst_ctx in IHTyds. rewrite map_push in IHTyds. unfold subst_ctx.
      apply IHTyds. auto.
      *)
  + (* case ty_sbsm *)
    intros G t T U n Ty IHTy St IHSt G1 G2 x Eq Bi Ok. subst.
    apply ty_sbsm with (subst_typ x y T) n.
    - apply* IHTy.
    - apply* IHSt.
  + (* case ty_typ *)
    intros. simpl. apply ty_typ with n. apply* H.
  + (* case ty_fld *)
    intros. apply* ty_fld.
  + (* case ty_mtd *)
    intros L G T U t Ty IH G1 G2 x Eq Bi Ok. subst.
    apply_fresh ty_mtd as z. fold subst_trm. fold subst_typ.
    lets C: (@subst_open_commute_trm x y z t).
    unfolds open_trm. unfold subst_fvar in C. case_var.
    rewrite <- C.
    rewrite <- concat_assoc.
    assert (zL: z \notin L) by auto.
    specialize (IH z zL G1 (G2 & z ~ T) x). rewrite concat_assoc in IH.
    specialize (IH eq_refl Bi).
    unfold subst_ctx in IH. rewrite map_push in IH. unfold subst_ctx.
    apply IH. auto.
  + (* case ty_dsnil *)
    intros. apply ty_dsnil.
  + (* case ty_dscons *)
    intros. admit. (* TODO *)
  + (* case can_add_typ *)
    admit.
  + (* case can_refine_typ *)
    admit.
  + (* case can_add_fld *)
    admit.
  + (* case can_add_mtd *)
    admit.
Admitted.

Print Assumptions subst_principles.

Lemma trm_subst_principle: forall G x y t S T,
  ok (G & x ~ S) ->
  ty_trm (G & x ~ S) t T ->
  ty_trm G (trm_var (avar_f y)) S ->
  ty_trm G (subst_trm x y t) (subst_typ x y T).
Proof.
  introv Hok tTy yTy. destruct (subst_principles y S) as [_ [_ [_ [_ [P _]]]]].
  specialize (P _ t T tTy G empty x).
  unfold subst_ctx in P. rewrite map_empty in P.
  repeat (progress (rewrite concat_empty_r in P)).
  apply* P.
Qed.

Lemma subdec_subst_principle: forall G x y S D1 D2 n,
  ok (G & x ~ S) ->
  subdec (G & x ~ S) D1 D2 n ->
  ty_trm G (trm_var (avar_f y)) S ->
  subdec G (subst_dec x y D1) (subst_dec x y D2) n.
Proof.
  introv Hok Sd yTy. destruct (subst_principles y S) as [_ [_ [_ [P _]]]].
  specialize (P _ D1 D2 n Sd G empty x).
  unfold subst_ctx in P. rewrite map_empty in P.
  repeat (progress (rewrite concat_empty_r in P)).
  apply* P.
Qed.


(* ###################################################################### *)
(** ** Narrowing *)

Lemma narrow_ty_trm_end: forall G y T1 T2 u U n,
  ok (G & y ~ T2) ->
  subtyp oktrans G T1 T2 n ->
  ty_trm (G & y ~ T2) u U ->
  ty_trm (G & y ~ T1) u U.
Proof.
  introv Ok St Tyu.
  (* Step 1: rename *)
  pick_fresh z.
  assert (Okzy: ok (G & z ~ T2 & y ~ T2)) by admit.
  apply (weaken_ty_trm_middle Okzy) in Tyu.
  assert (Biz: binds z T2 (G & z ~ T2)) by auto.
  lets Tyz: (ty_var Biz).
  lets Tyu': (trm_subst_principle Okzy Tyu Tyz).
  (* Step 2: the actual substitution *)
  assert (Biy: binds y T1 (G & y ~ T1)) by auto.
  assert (Ok': ok (G & y ~ T1)) by admit.
  apply (weaken_subtyp_end Ok') in St.
  lets Tyy: (ty_sbsm (ty_var Biy) St).
  assert (Okyz: ok (G & y ~ T1 & z ~ T2)) by auto.
  apply (weaken_ty_trm_middle Okyz) in Tyu'.
  lets Tyu'': (trm_subst_principle Okyz Tyu' Tyy).
  rewrite subst_trm_undo, subst_typ_undo in Tyu''; auto.
Qed.

Lemma narrow_subdec_end: forall G y T1 T2 D1 D2 n0 n,
  ok (G & y ~ T2) ->
  subtyp oktrans G T1 T2 n0 ->
  subdec (G & y ~ T2) D1 D2 n ->
  subdec (G & y ~ T1) D1 D2 n.
Proof.
  introv Ok St Sd.
  (* Step 1: rename *)
  pick_fresh z.
  assert (Okzy: ok (G & z ~ T2 & y ~ T2)) by admit.
  apply (weaken_subdec_middle Okzy) in Sd.
  assert (Biz: binds z T2 (G & z ~ T2)) by auto.
  lets Tyz: (ty_var Biz).
  lets Tyu': (subdec_subst_principle Okzy Sd Tyz).
  (* Step 2: the actual substitution *)
  assert (Biy: binds y T1 (G & y ~ T1)) by auto.
  assert (Ok': ok (G & y ~ T1)) by admit.
  apply (weaken_subtyp_end Ok') in St.
  lets Tyy: (ty_sbsm (ty_var Biy) St).
  assert (Okyz: ok (G & y ~ T1 & z ~ T2)) by auto.
  apply (weaken_subdec_middle Okyz) in Tyu'.
  lets Tyu'': (subdec_subst_principle Okyz Tyu' Tyy).
  do 2 rewrite subst_dec_undo in Tyu''; auto.
Qed.


(* ###################################################################### *)
(** ** More inversion lemmas *)

Lemma invert_var_has_dec: forall G x l D,
  has G (trm_var (avar_f x)) l D ->
  exists T D', ty_trm G (trm_var (avar_f x)) T /\
               typ_has G T l D' /\
               open_dec x D' = D.
Proof.
  introv Has. inversions Has.
  (* case has_trm *)
  + subst. exists T D. auto.
  (* case has_pth *)
  + exists T D0. auto.
Qed.

(*
Lemma invert_has: forall G t l D,
   has ip G t l D ->
   (exists T Ds,      ty_trm G t T /\
                      exp ip G T Ds /\
                      decs_has Ds l D /\
                      (forall z : var, open_dec z D = D))
\/ (exists x T Ds D', t = (trm_var (avar_f x)) /\
                      ty_trm G (trm_var (avar_f x)) T /\
                      exp ip G T Ds /\
                      decs_has Ds l D' /\
                      open_dec x D' = D).
Proof.
  introv Has. inversions Has.
  (* case has_trm *)
  + subst. left. exists T Ds. auto.
  (* case has_var *)
  + right. exists v T Ds D0. auto.
Qed.
*)

Lemma invert_var_has_dec_typ: forall G v L S U,
  has G (trm_var (avar_f v)) L (dec_typ S U) ->
  exists T S' U', ty_trm G (trm_var (avar_f v)) T /\
                  typ_has G T L (dec_typ S' U') /\
                  open_typ v S' = S /\
                  open_typ v U' = U.
Proof.
  introv Has. apply invert_var_has_dec in Has.
  destruct Has as [T [D' [Ty [THas Eq]]]].
  destruct D' as [ Lo Hi | T' | S' U' ]; try solve [ inversion Eq ].
  unfold open_dec, open_rec_dec in Eq. fold open_rec_typ in Eq.
  inversion Eq as [Eq'].
  exists T Lo Hi. auto.
Qed.

(*
Lemma invert_var_has_dec_fld: forall G x l T,
  has ip G (trm_var (avar_f x)) l (dec_fld T) ->
  exists X Ds T', ty_trm G (trm_var (avar_f x)) X /\
                  exp ip G X Ds /\
                  decs_has Ds l (dec_fld T') /\
                  open_typ x T' = T.
Proof.
  introv Has. apply invert_var_has_dec in Has.
  destruct Has as [X [Ds [D [Tyx [Exp [Has Eq]]]]]].
  destruct D as [ Lo Hi | T' | T1 T2 ]; try solve [ inversion Eq ].
  unfold open_dec, open_rec_dec in Eq. fold open_rec_typ in Eq.
  inversion Eq as [Eq'].
  exists X Ds T'. auto.
Qed.

Lemma invert_var_has_dec_mtd: forall G x l S U,
  has ip G (trm_var (avar_f x)) l (dec_mtd S U) ->
  exists X Ds S' U', ty_trm G (trm_var (avar_f x)) X /\
                     exp ip G X Ds /\
                     decs_has Ds l (dec_mtd S' U') /\
                     open_typ x S' = S /\
                     open_typ x U' = U.
Proof.
  introv Has. apply invert_var_has_dec in Has.
  destruct Has as [X [Ds [D [Tyx [Exp [Has Eq]]]]]].
  destruct D as [ Lo Hi | T' | S' U' ]; try solve [ inversion Eq ].
  unfold open_dec, open_rec_dec in Eq. fold open_rec_typ in Eq.
  inversion Eq as [Eq'].
  exists X Ds S' U'. auto.
Qed.

Lemma invert_has_pr: forall G x l D,
  has pr G (trm_var (avar_f x)) l D ->
  exists T Ds D', binds x T G /\
                  exp pr G T Ds /\
                  decs_has Ds l D' /\
                  D = open_dec x D'.
Proof.
  introv Has. inversions Has. exists T Ds D0. auto.
Qed.

Lemma invert_exp_sel: forall m G v L Ds,
  exp m G (typ_sel (pth_var (avar_f v)) L) Ds ->
  exists Lo Hi, has m G (trm_var (avar_f v)) L (dec_typ Lo Hi) /\
                exp m G Hi Ds.
Proof.
  introv Exp. inversions Exp. exists Lo Hi. auto.
Qed.


Lemma invert_ty_sel_var: forall G x l T,
  ty_trm G (trm_sel (trm_var (avar_f x)) l) T ->
  has ip G (trm_var (avar_f x)) (label_fld l) (dec_fld T).
Proof.
  introv Ty. gen_eq t0: (trm_sel (trm_var (avar_f x)) l). gen x l.
  induction Ty; try (solve [ intros; discriminate ]).
  (* base case: no subsumption *)
  + intros x l0 Eq. inversions Eq. assumption.
  (* step: subsumption *)
  + intros x l Eq. subst. specialize (IHTy _ _ eq_refl).
    apply invert_var_has_dec_fld in IHTy.
    destruct IHTy as [X [Ds [T' [Tyx [Exp [Has Eq]]]]]].
    (*
    assert Tyx': ty_trm G (trm_var (avar_f x)) (ty_or X (typ_bind (dec_fld U)))
      by subsumption
    then the expansion of (ty_or X (typ_bind (dec_fld U))) has (dec_fld (t_or T U))
    since T <: U, (t_or T U) is kind of the same as U <-- but not enough!
    *)
Abort.

(* TODO does not hold currently! *)
Axiom top_subtyp_of_empty_bind: forall m1 m2 G, 
  subtyp m1 m2 G typ_top (typ_bind decs_nil).

Lemma exp_to_subtyp: forall G T Ds,
  exp ip G T Ds ->
  subtyp ip oktrans G T (typ_bind Ds).
Proof.
  introv Exp. gen_eq m: ip. induction Exp; intro Eq; subst.
  + apply top_subtyp_of_empty_bind.
  + apply subtyp_refl_all.
  + specialize (IHExp eq_refl). apply subtyp_tmode. apply (subtyp_sel_l H IHExp).
Qed.
*)

Lemma invert_ty_sel_weak: forall G t l T,
  ty_trm G (trm_sel t l) T ->
  exists T' n, subtyp oktrans G T' T n /\ has G t l (dec_fld T').
Proof.
  introv Ty. gen_eq t0: (trm_sel t l). gen t l.
  induction Ty; intros t' l' Eq; try (solve [ discriminate ]).
  + inversions Eq. exists T 0. apply (conj (subtyp_tmode (subtyp_refl _ _ _))). auto.
  + subst. rename t' into t, l' into l, H into St2. specialize (IHTy _ _ eq_refl).
    destruct IHTy as [T' [n' [St1 Has]]]. exists T' (max n' n). refine (conj _ Has).
    lets Le1: (Max.le_max_l n' n).
    lets Le2: (Max.le_max_r n' n).
    lets St1': (subtyp_max_ctx St1 Le1).
    lets St2': (subtyp_max_ctx St2 Le2).
    apply (subtyp_trans St1' St2').
Qed.

(*Lemma force_open_dec: forall D v, exists D', (open_dec v D') = D. Admitted.*)

Lemma has_sbsm: forall G t l D1 D2 n,
  has G t l D1 -> subdec G D1 D2 n -> has G t l D2.
Proof.
  introv Has Sd.
  (* should be part of hypotheses, or of some wf-ness: *)
  assert (CloD2: forall z, open_dec z D2 = D2) by admit.
  inversions Has.
  + (* case has_trm *)
    rename H into Ty, H0 into THas, H1 into Cl.
    assert (St: exists n', subtyp oktrans G T (typ_rfn T l D2) n'). {
      admit.
    }
    destruct St as [n' St].
    apply has_trm with (typ_rfn T l D2).
    - apply (ty_sbsm Ty St).
    - apply typ_rfn_has_2. admit. (* TODO matching_label *)
    - exact CloD2.
  + (* case has_pth *)
    rename H into Ty, H0 into THas, D into D1, D2 into D2.
    rewrite <- (CloD2 v) in *.
    assert (St: exists n', subtyp oktrans G T (typ_rfn T l D2) n'). {
      exists (S n). apply subtyp_tmode.
      apply_fresh subtyp_rfn_r as z.
      - apply subtyp_tmode. apply subtyp_refl.
      - apply THas.
      - admit. (* substitute z by v, TODO *)
    }
    destruct St as [n' St].
    apply has_pth with (typ_rfn T l D2).
    - apply (ty_sbsm Ty St).
    - apply typ_rfn_has_2. admit. (* TODO matching_label *)
Qed.

Lemma invert_ty_sel: forall G t l T,
  ty_trm G (trm_sel t l) T ->
  has G t l (dec_fld T).
Proof.
  introv Ty.
  destruct (invert_ty_sel_weak Ty) as [T' [n [St Has]]].
  apply (has_sbsm Has (subdec_fld St)).
Qed.

(*
Lemma invert_ty_call_weak: forall G t m V2 u,
  ty_trm G (trm_call t m u) V2 ->
  exists U V1, has ip G t (label_mtd m) (dec_mtd U V1)
               /\ subtyp ip oktrans G V1 V2
               /\ ty_trm G u U.
Proof.
  introv Ty. gen_eq e: (trm_call t m u). gen t m u.
  induction Ty; intros t0 m0 u0 Eq; try solve [ discriminate ]; symmetry in Eq.
  + (* case ty_call *)
    inversions Eq. exists U V. lets StV: (subtyp_refl_all ip oktrans G V). auto.
  + (* case ty_sbsm *)
    subst t. specialize (IHTy _ _ _ eq_refl).
    rename t0 into t, m0 into m, u0 into u, U into V3, T into V2.
    destruct IHTy as [U [V1 [Has [St12 Tyu]]]].
    exists U V1.
    lets St13: (subtyp_trans St12 H).
    auto.
Qed.
*)

Lemma invert_ty_call: forall G t m V u,
  ty_trm G (trm_call t m u) V ->
  exists U, has G t m (dec_mtd U V) /\ ty_trm G u U.
Proof.
  intros. inversions H.
  + eauto.
  + admit. (* subsumption case, TODO similar to invert_ty_sel *)
Admitted.

Lemma invert_ty_new: forall G ds T2,
  ty_trm G (trm_new ds) T2 ->
  exists L T1 n,
    subtyp oktrans G T1 T2 n /\
    (forall x, x \notin L ->
               ty_defs (G & x ~ T1) (open_defs x ds) T1).
Proof.
  introv Ty. gen_eq t0: (trm_new ds). gen ds.
  induction Ty; intros ds' Eq; try (solve [ discriminate ]); symmetry in Eq.
  + (* case ty_new *)
    inversions Eq. exists L T 0. split.
    - apply (subtyp_tmode (subtyp_refl _ _ _)).
    - assumption.
  + (* case ty_sbsm *)
    subst. rename ds' into ds. specialize (IHTy _ eq_refl).
    destruct IHTy as [L [T' [n' [St Tyds]]]].
    exists L T' (max n' n).
    lets Le1: (Max.le_max_l n' n).
    lets Le2: (Max.le_max_r n' n).
    lets St1': (subtyp_max_ctx St Le1).
    lets St2': (subtyp_max_ctx H Le2).
    apply (conj (subtyp_trans St1' St2') Tyds).
Qed.

Lemma invert_wf_sto: forall s G,
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
      exists G (@empty typ). rewrite concat_empty_r. auto.
    - specialize (IHWf x0 ds0 T0 H2 H3).
      destruct IHWf as [G1 [G2 [EqG Ty]]]. subst.
      exists G1 (G2 & x ~ T).
      rewrite concat_assoc.
      apply (conj eq_refl).
      apply weaken_ty_defs_end.
      * apply wf_sto_to_ok_G in Wf. auto.
      * exact Ty.
Qed.

(*
Lemma invert_wf_sto_with_weakening: forall s G,
  wf_sto s G ->
  forall x ds Ds T,
    binds x (object Ds ds) s -> 
    binds x T G 
    -> T = (typ_bind Ds) 
    /\ ty_defs G (open_defs x ds) (open_decs x Ds)
    /\ cbounds_decs Ds.
Proof.
  introv Wf Bs BG.
  lets P: (invert_wf_sto Wf).
  specialize (P x ds Ds T Bs BG).
  destruct P as [EqT [G1 [G2 [EqG [Ty F]]]]]. subst.
  apply (conj eq_refl).
  lets Ok: (wf_sto_to_ok_G Wf).
  split.
  + apply (weaken_ty_defs_end Ok Ty).
  + exact F.
Qed.
*)

Lemma invert_wf_sto_with_sbsm: forall s G,
  wf_sto s G ->
  forall x ds T2, 
    binds x ds s ->
    ty_trm G (trm_var (avar_f x)) T2 -> (* <- instead of binds *)
    exists T1 n, subtyp oktrans G T1 T2 n
              /\ ty_defs G ds T1.
Proof.
  introv Wf Bis Tyx.
  apply invert_ty_var in Tyx. destruct Tyx as [T' [n [St BiG]]].
  destruct (invert_wf_sto Wf Bis BiG) as [G1 [G2 [Eq Tyds]]].
  subst. exists T' n.
  lets Ok: (wf_sto_to_ok_G Wf).
  apply (conj St).
  auto.
Qed.

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

Lemma subdec_trans: forall  G D1 D2 D3 n,
  subdec G D1 D2 n -> subdec G D2 D3 n -> subdec G D1 D3 n.
Proof.
  introv H12 H23. inversions H12; inversions H23; constructor;
  solve [ assumption | (eapply subtyp_trans; eassumption)].
Qed.

Lemma intersect_ty_has:
   (forall G t l D1, has G t l D1 -> forall D2, has G t l D2 ->
      has G t l (intersect_dec D1 D2))
/\ (forall G t T1, ty_trm G t T1 -> forall T2, ty_trm G t T2 ->
      ty_trm G t (typ_and T1 T2)).
Proof.
  apply ty_has_mutind.
  + (* case has_trm *)
    admit.
  + (* case has_pth *)
    admit.
  + (* case ty_var *)
    intros G x T1 Bi T2 Ty2.
    apply invert_ty_var in Ty2. destruct Ty2 as [T1' [n [St Bi']]].
    rewrite (binds_func Bi' Bi) in *. clear Bi' T1'.
    refine (ty_sbsm _ (subtyp_tmode (subtyp_and (subtyp_tmode (subtyp_refl _ _ _)) St))).
    apply (ty_var Bi).
  + (* case ty_sel  *)
    intros G t l T1 Has1 IH T2 Ty2.
    lets Has2: (invert_ty_sel Ty2).
    specialize (IH _ Has2). simpl in IH.
    apply (ty_sel IH).
  + (* case ty_call *)
    admit.
  + (* case ty_new *)
    admit.
  + (* case ty_sbsm *)
    admit.
Qed.

Definition intersect_has := proj1 intersect_ty_has.
Definition intersect_ty_trm := proj2 intersect_ty_has.

Lemma intersect_typ_has: forall G T l D1 D2,
  typ_has G T l D1 ->
  typ_has G T l D2 ->
  typ_has G T l (intersect_dec D1 D2).
Admitted. (* maybe modulo swap lef/right? *)

Lemma union_typ_has: forall G U V l D1 D2,
  typ_has G U l D1 ->
  typ_has G V l D2 ->
  typ_has G (typ_or U V) l (union_dec D1 D2).
Admitted. (* maybe modulo swap lef/right? *)


(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(* TODO doesn't hold if dec_typ with bad bounds!*)
Lemma subdec_refl: forall G D, subdec G D D 0. Admitted.

(* oktrans mode --> should be easy, just juggle with numbers *)
Lemma subdec_trans_with_different_sizes: forall G D1 D2 D3 n12 n23,
  subdec G D1 D2 n12 ->
  subdec G D2 D3 n23 ->
  subdec G D1 D3 (max n12 n23).
Proof.
  intros.
  assert (n12 = n23) by admit. subst.
  assert (max n23 n23 = n23) by admit. rewrite H1.
  apply (subdec_trans H H0).
Qed.


(* ###################################################################### *)
(** ** Soundness helper lemmas *)

(* Hyptheses:  X1 ----subtyp----> X2 ----typ_has---> D2
   Conclusion: X1 ----typ_has---> D1 ----subdec----> D1
In the system which used expansion instead of typ_has, this didn't work,
because we were not sure if X1 had an expansion or not. *)
Definition swap_sub_and_has_statement := forall m G X1 X2 n l D2,
  subtyp m G X1 X2 n ->
  typ_has G X2 l D2 ->
  exists D1 L n',
    typ_has G X1 l D1 /\
    forall x, x \notin L -> subdec (G & x ~ X1) (open_dec x D1) (open_dec x D2) n'.

(*
Lemma typ_has_to_good_bounds: forall G T L Lo Hi ds,
  typ_has G T L (dec_typ Lo Hi) ->
  ty_defs G ds T -> (* <-- witnesses realizability of T *)
  exists n, subtyp oktrans G Lo Hi n.
Proof.
  intros G T L Lo2 Hi2 ds THas Tyds.
  lets P: (invert_ty_defs Tyds THas). destruct P as [d [D1 [n [dsHas [Tyd Sd]]]]].
  apply invert_subdec_typ_sync_left in Sd.
  destruct Sd as [Lo1 [Hi1 [Eq [StLo21 [StLoHi1 StHi12]]]]]. subst.
  exists n.
  apply (subtyp_trans StLo21).
  apply (subtyp_trans StLoHi1).
  exact StHi12.
Qed.
*)

(* Lookup x to get ds *)
Lemma sto_lookup: forall s G x T2,
  wf_sto s G ->
  ty_trm G (trm_var (avar_f x)) T2 ->
  exists T1 ds n, 
    ty_defs G ds T1 /\
    subtyp oktrans G T1 T2 n /\
    binds x T1 G /\
    binds x ds s.
Proof.
  introv Wf Ty.
  apply invert_ty_var in Ty. destruct Ty as [T1 [n [St BiG]]].
  lets Bis: (ctx_binds_to_sto_binds Wf BiG). destruct Bis as [ds Bis].
  lets P: (invert_wf_sto Wf Bis BiG). destruct P as [G1 [G2 [Eq Tyds]]].
  exists T1 ds n. apply (conj Tyds). apply (conj St). apply (conj BiG Bis).
Qed.

Lemma distribute_open_dec_over_dec_typ: forall v Lo Hi,
  open_dec v (dec_typ Lo Hi) = dec_typ (open_typ v Lo) (open_typ v Hi).
Admitted.

Lemma distribute_open_dec_over_union_dec: forall x D1 D2,
  open_dec x (union_dec D1 D2) = union_dec (open_dec x D1) (open_dec x D2).
Admitted.

Hint Resolve subtyp_max_ctx.

Lemma subdec_union: forall G DU DV D2 nU nV,
  subdec G DU D2 nU ->
  subdec G DV D2 nV ->
  subdec G (union_dec DU DV) D2 (max nU nV).
Proof.
  introv SdU SdV.
  lets leU: (Max.le_max_l nU nV).
  lets leV: (Max.le_max_r nU nV).
  destruct D2 as [Lo2 Hi2 | T2 | T1 T2].
  + apply invert_subdec_typ_sync_left in SdU.
    apply invert_subdec_typ_sync_left in SdV.
    destruct SdU as [LoU [HiU [Eq [StU1 [StU2 StU3]]]]]. subst.
    destruct SdV as [LoV [HiV [Eq [StV1 [StV2 StV3]]]]]. subst.
    simpl.
    apply subdec_typ.
    - apply subtyp_tmode. apply subtyp_and.
      * apply (subtyp_max_ctx StU1 leU).
      * apply (subtyp_max_ctx StV1 leV).
    - apply subtyp_tmode. apply subtyp_and_l. apply subtyp_tmode. apply subtyp_or_l.
      apply (subtyp_max_ctx StU2 leU).
    - apply subtyp_tmode. apply subtyp_or.
      * apply (subtyp_max_ctx StU3 leU).
      * apply (subtyp_max_ctx StV3 leV).
  + apply invert_subdec_fld_sync_left in SdU.
    apply invert_subdec_fld_sync_left in SdV.
    destruct SdU as [U [Eq StU]]. subst.
    destruct SdV as [V [Eq StV]]. subst.
    simpl. eauto 10.
  + apply invert_subdec_mtd_sync_left in SdU.
    apply invert_subdec_mtd_sync_left in SdV.
    destruct SdU as [UA [UR [Eq [StU1 StU2]]]]. subst.
    destruct SdV as [VA [VR [Eq [StV1 StV2]]]]. subst.
    simpl. eauto 10.
Qed.

Print Assumptions subdec_union.

Axiom swap_sub_and_has_IH: swap_sub_and_has_statement.

Lemma has_to_good_bounds: forall s G p L Lo Hi,
  wf_sto s G -> (* <-- witnesses realizability of the type of p *)
  has G (pth2trm p) L (dec_typ Lo Hi) ->
  exists n, subtyp oktrans G Lo Hi n.
Proof.
  intros s G p L Lo2' Hi2' Wf Has.
  destruct p as [v]. simpl in Has.
  destruct v as [n|v]; [admit | idtac]. (* TODO path cannot be a bound var *)
  apply invert_var_has_dec_typ in Has.
  destruct Has as [T2 [Lo2 [Hi2 [Ty [T2Has [Eq1 Eq2]]]]]]. subst.
  (* lookup v in the store: *)
  lets P: (sto_lookup Wf Ty). destruct P as [T1 [ds [n [Tyds [St [Bis BiG]]]]]].
  lets Q: (swap_sub_and_has_IH St T2Has).
  destruct Q as [D1 [F [n' [T1Has Sd]]]].
  pick_fresh z.
  assert (zF: z \notin F) by auto. specialize (Sd z zF).
  (* TODO substitution: *)
  assert (Sd': subdec G (open_dec v D1) (open_dec v (dec_typ Lo2 Hi2)) n') by admit.
  assert (Eq: exists Lo1 Hi1, D1 = (dec_typ Lo1 Hi1)) by admit.
  destruct Eq as [Lo1 [Hi1 Eq]]. subst. simpl in Sd'.
  rewrite (distribute_open_dec_over_dec_typ v Lo1 Hi1) in Sd'.
  rewrite (distribute_open_dec_over_dec_typ v Lo2 Hi2) in Sd'.
  inversions Sd'.
  exists n'. apply (subtyp_trans H4). apply (subtyp_trans H6). exact H7.
Qed.

Lemma swap_sub_and_has: swap_sub_and_has_statement.
Proof.
  (* We don't use the [induction] tactic because we want to intro everything ourselves: *)
  introv St. gen l D2. gen m G X1 X2 n.
  apply (subtyp_ind (fun m G X1 X2 n => forall l D2,
    typ_has G X2 l D2 ->
    exists D1 L n',
      typ_has G X1 l D1 /\
      (forall x, x \notin L -> subdec (G & x ~ X1) (open_dec x D1) (open_dec x D2) n'))).
  + (* case subtyp_refl *)
    introv n THas. exists D2 vars_empty 0. apply (conj THas).
    intros z zL. apply subdec_refl.
  + (* case subtyp_top *)
    introv n THas. inversions THas. (* contradiction *)
  + (* case subtyp_bot *)
    introv n THas. admit. (* TODO need witness that T is not bottom *)
  + (* case subtyp_rfn_l *)
    intros G T1 l0 D0 T2 n St IHSt l D2 T2Has.
    specialize (IHSt _ _ T2Has).
    destruct IHSt as [D1 [L [n' [T1Has Sd]]]]. exists D1 L n'. split.
    - apply typ_rfn_has_1. exact T1Has.
    - intros x xL. specialize (Sd x xL).
      lets St': (subtyp_tmode (subtyp_rfn_l l0 D0 (subtyp_tmode (subtyp_refl G T1 0)))).
      refine (narrow_subdec_end _ St' Sd). apply okadmit.
  + (* case subtyp_rfn_r *)
    introv St IHSt T1Has Sd T2Has. rename l into ll. rename l0 into l.
    apply invert_typ_rfn_has in T2Has.
    destruct T2Has as [T2Has | [[M [Eq1 Eq2]] | [D2' [T2Has [Eq1 Eq2]]]]].
    - (* T2Has only looked left *)
      specialize (IHSt _ _ T2Has). destruct IHSt as [D1' [L' [n' [T1Has' Sd']]]].
      exists D1' L' n'. auto.
    - (* T2Has only looked right *)
      subst ll D0. exists D1 L n. auto.
    - (* T2Has took intersection of left and right *)
      subst.
      specialize (IHSt _ _ T2Has). destruct IHSt as [D1' [L' [n' [T1Has' Sd']]]].
      exists (intersect_dec D1' D1) (L' \u L) (max n' n). split.
      * apply (intersect_typ_has T1Has' T1Has).
      * intros x N. 
        assert (xL: x \notin L) by auto. specialize (Sd x xL).
        assert (xL': x \notin L') by auto. specialize (Sd' x xL').
        admit. (* TODO distribute open over intersect etc, should hold *)
  + (* case subtyp_sel_l *)
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
    introv St1 IH1 St2 IH2 T12Has.
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
Qed.

Lemma has_sound: forall s G x ds l D2,
  wf_sto s G ->
  binds x ds s ->
  has G (trm_var (avar_f x)) l D2 ->
  exists T1 D1 n,
    ty_defs G ds T1 /\ (* T1 is already opened and uses x as the self reference *)
    typ_has G T1 l D1 /\
    subdec G D1 D2 n.
Proof.
  introv Wf Bis Has.
  apply invert_var_has_dec in Has.
  destruct Has as [X2 [D2' [Tyx [X2Has Clo]]]]. subst. rename D2' into D2.
  destruct (invert_wf_sto_with_sbsm Wf Bis Tyx) as [X1 [n [St Tyds]]].
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
  set (progress_for := fun s e =>
                         (exists e' s', red e s e' s') \/
                         (exists x o, e = (trm_var (avar_f x)) /\ binds x o s)).
  apply (ty_has_mutind
    (fun G e l d Has => forall s, wf_sto s G   -> progress_for s e)
    (fun G e T Ty      => forall s, wf_sto s G -> progress_for s e));
    unfold progress_for; clear progress_for.
  (* case has_trm *)
  + intros. auto.
  (* case has_var *)
  + introv Ty IH THas Wf.
    right. apply invert_ty_var in Ty. destruct Ty as [T' [n [St BiG]]].
    destruct (ctx_binds_to_sto_binds Wf BiG) as [o Bis].
    exists v o. auto.
  (* case ty_var *)
  + intros G x T BiG s Wf.
    right. destruct (ctx_binds_to_sto_binds Wf BiG) as [o Bis].
    exists x o. auto.
  (* case ty_sel *)
  + intros G t l T Has IH s Wf.
    left. specialize (IH s Wf). destruct IH as [IH | IH].
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


(************ garbage *************************)

(* The typ_has with more precision thanks to typ_hasnt, but probably/hopefully we don't
   want/need this precision (?) *)

Inductive typ_has: ctx -> typ -> label -> dec -> Prop :=
(*| typ_top_has: typ_top has nothing *)
(*| typ_bot_has: in subdec_typ, we require that Lo2 <: Lo1 <: Hi1 <: Hi2,
      so the dec_typ that typ_bot could have, i.e.
      (dec_typ typ_top typ_bot) is not a subdec of anything, so better say
      typ_bot has no members! *)
  | typ_rfn_has_1: forall G T1 l1 D1 l D,
      typ_has G T1 l D ->
      l <> l1 ->
      typ_has G (typ_rfn T1 l1 D1) l D
  | typ_rfn_has_2: forall G T l D,
      typ_hasnt G T l ->
      typ_has G (typ_rfn T l D) l D
  | typ_rfn_has_12: forall G T l D1 D2 D12,
      typ_has G T l D1 ->
      intersect_dec D1 D2 D12 ->
      typ_has G (typ_rfn T l D2) l D12
  | typ_sel_has: forall G p L Lo Hi l D,
      has G (typ_sel p L) L (dec_typ Lo Hi) ->
      typ_has G Hi l D ->
      typ_has G (typ_sel p L) l D
  | typ_and_has_1: forall G T1 T2 l D,
      typ_has G T1 l D ->
      typ_hasnt G T2 l ->
      typ_has G (typ_and T1 T2) l D
  | typ_and_has_2: forall G T1 T2 l D,
      typ_hasnt G T1 l ->
      typ_has G T2 l D ->
      typ_has G (typ_and T1 T2) l D
  | typ_and_has_12: forall G T1 T2 l D1 D2 D12,
      typ_has G T1 l D1 ->
      typ_has G T2 l D2 ->
      intersect_dec D1 D2 D12 ->
      typ_has G (typ_and T1 T2) D12



  | typ_or_has

with typ_hasnt: ctx -> typ -> label -> Prop :=
  | typ_top_hasnt: forall G l,
      typ_hasnt G typ_top l
(*| typ_hasnt_bot: typ_bot has everything *)
  | typ_rfn_hasnt: forall G T1 l1 D1 l,
      typ_hasnt G T1 l ->
      l1 <> l ->
      typ_hasnt G (typ_rfn T1 l1 D1) l
  (* Note: "p.L hasn't l" does not mean that whatever type this abstract type will be
     instantiated with, p.L has no member named l.
     It just means that with the assumptions in G, we cannot prove that p.L has an l. *)
  | typ_sel_hasnt: forall G p L Lo Hi l,
      has G (pth2trm p) L (dec_typ Lo Hi) ->
      typ_hasnt G Hi l ->
      typ_hasnt G (typ_sel p L) l
  | typ_and_hasnt_1: forall G T1 T2 l,
      typ_hasnt G T1 l ->
      typ_hasnt G (typ_and T1 T2) l
  | typ_and_hasnt_2: forall G T1 T2 l,
      typ_hasnt G T2 l ->
      typ_hasnt G (typ_and T1 T2) l
  | typ_or_hasnt: forall G T1 T2 l,
      typ_hasnt G T1 l ->
      typ_hasnt G T2 l ->
      typ_hasnt G (typ_or T1 T2) l

