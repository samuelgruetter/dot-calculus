
(*
max-ctx-growth-ip-pr-muDot:

Idea: subtype judgments give max env growth wrt size of env in conclusion,
use it as termination measure for narrowing/exp_preserves_sub
*)

Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.


(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

(** If it's clear whether a type, field or method is meant, we use nat, 
    if not, we use label: *)
Inductive label: Type :=
| label_typ: nat -> label
| label_fld: nat -> label
| label_mtd: nat -> label.

Inductive avar : Type :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to tenv or venv *)

Inductive pth : Type :=
  | pth_var : avar -> pth.

Inductive typ : Type :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_bind : decs -> typ (* { z => decs } *)
  | typ_sel : pth -> label -> typ (* p.L *)
with dec : Type :=
  | dec_typ  : typ -> typ -> dec
  | dec_fld  : typ -> dec
  | dec_mtd : typ -> typ -> dec
with decs : Type :=
  | decs_nil : decs
  | decs_cons : nat -> dec -> decs -> decs.

(* decs which could possibly be the expansion of bottom *)
Inductive bdecs : Type :=
  | bdecs_bot : bdecs
  | bdecs_decs : decs -> bdecs.

Inductive trm : Type :=
  | trm_var  : avar -> trm
  | trm_new  : decs -> defs -> trm
  | trm_sel  : trm -> nat -> trm
  | trm_call : trm -> nat -> trm -> trm
with def : Type :=
  | def_typ : def (* just a placeholder *)
  | def_fld : avar -> def (* cannot have term here, need to assign first *)
  | def_mtd : trm -> def (* one nameless argument *)
with defs : Type :=
  | defs_nil : defs
  | defs_cons : nat -> def -> defs -> defs.

Inductive obj : Type :=
  | object : decs -> defs -> obj. (* { z => Ds }{ z => ds } *)

(** *** Typing environment ("Gamma") *)
Definition ctx := env typ.

(** *** Value environment ("store") *)
Definition sto := env obj.

(** *** Syntactic sugar *)
Definition trm_fun(T U: typ)(body: trm) := 
            trm_new (decs_cons 0 (dec_mtd T U)  decs_nil)
                    (defs_cons 0 (def_mtd body) defs_nil).
Definition trm_app(func arg: trm) := trm_call func 0 arg.
Definition trm_let(T U: typ)(rhs body: trm) := trm_app (trm_fun T U body) rhs.
Definition typ_arrow(T1 T2: typ) := typ_bind (decs_cons 0 (dec_mtd T1 T2) decs_nil).


(* ###################################################################### *)
(** ** Declaration and definition lists *)

Definition label_for_def(n: nat)(d: def): label := match d with
| def_typ     => label_typ n
| def_fld _   => label_fld n
| def_mtd _   => label_mtd n
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
Fixpoint get_dec(l: label)(Ds: decs): option dec := match Ds with
| decs_nil => None
| decs_cons n D Ds' => If l = label_for_dec n D then Some D else get_dec l Ds'
end.

Definition defs_has(ds: defs)(l: label)(d: def): Prop := (get_def l ds = Some d).
Definition decs_has(Ds: decs)(l: label)(D: dec): Prop := (get_dec l Ds = Some D).

Definition defs_hasnt(ds: defs)(l: label): Prop := (get_def l ds = None).
Definition decs_hasnt(Ds: decs)(l: label): Prop := (get_dec l Ds = None).

Inductive bdecs_has: bdecs -> label -> dec -> Prop :=
  | bdecs_has_decs: forall Ds l D,
      decs_has Ds l D ->
      bdecs_has (bdecs_decs Ds) l D
  | bdecs_has_typ: forall L,
      bdecs_has bdecs_bot (label_typ L) (dec_typ typ_top typ_bot)
  | bdecs_has_fld: forall l,
      bdecs_has bdecs_bot (label_fld l) (dec_fld typ_bot)
  | bdecs_has_mtd: forall m,
      bdecs_has bdecs_bot (label_mtd m) (dec_mtd typ_top typ_bot).


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
  | typ_top     => typ_top
  | typ_bot     => typ_bot
  | typ_bind Ds => typ_bind (open_rec_decs (S k) u Ds)
  | typ_sel p L => typ_sel (open_rec_pth k u p) L
  end
with open_rec_dec (k: nat) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ T U => dec_typ (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_fld T   => dec_fld (open_rec_typ k u T)
  | dec_mtd T U => dec_mtd (open_rec_typ k u T) (open_rec_typ k u U)
  end
with open_rec_decs (k: nat) (u: var) (Ds: decs) { struct Ds } : decs :=
  match Ds with
  | decs_nil          => decs_nil
  | decs_cons n D Ds' => decs_cons n (open_rec_dec k u D) (open_rec_decs k u Ds')
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_new Ds ds  => trm_new (open_rec_decs k u Ds) (open_rec_defs (S k) u ds)
  | trm_sel e n    => trm_sel (open_rec_trm k u e) n
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: nat) (u: var) (d: def) { struct d } : def :=
  match d with
  | def_typ   => def_typ
  | def_fld a => def_fld (open_rec_avar k u a)
  | def_mtd e => def_mtd (open_rec_trm (S k) u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs) { struct ds } : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons n d tl => defs_cons n (open_rec_def k u d) (open_rec_defs k u tl)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_pth  u p := open_rec_pth   0 u p.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u d := open_rec_dec   0 u d.
Definition open_decs u l := open_rec_decs  0 u l.
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
  | typ_top     => \{}
  | typ_bot     => \{}
  | typ_bind Ds => fv_decs Ds
  | typ_sel p L => fv_pth p
  end
with fv_dec (D: dec) { struct D } : vars :=
  match D with
  | dec_typ T U => (fv_typ T) \u (fv_typ U)
  | dec_fld T   => (fv_typ T)
  | dec_mtd T U => (fv_typ T) \u (fv_typ U)
  end
with fv_decs (Ds: decs) { struct Ds } : vars :=
  match Ds with
  | decs_nil          => \{}
  | decs_cons n D Ds' => (fv_dec D) \u (fv_decs Ds')
  end.

Definition fv_bdecs (Ds: bdecs) : vars := match Ds with
  | bdecs_decs Ds0 => fv_decs Ds0
  | bdecs_bot => \{}
  end.

(* Since we define defs ourselves instead of using [list def], we don't have any
   termination proof problems: *)
Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var x        => (fv_avar x)
  | trm_new Ds ds    => (fv_decs Ds) \u (fv_defs ds)
  | trm_sel t l      => (fv_trm t)
  | trm_call t1 m t2 => (fv_trm t1) \u (fv_trm t2)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ   => \{}
  | def_fld x => fv_avar x
  | def_mtd u => fv_trm u
  end
with fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons n d tl => (fv_def d) \u (fv_defs tl)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun T => fv_typ T) G).


(* ###################################################################### *)
(** ** Operational Semantics *)

(** Note: Terms given by user are closed, so they only contain avar_b, no avar_f.
    Whenever we introduce a new avar_f (only happens in red_new), we choose one
    which is not in the store, so we never have name clashes. *)
Inductive red : trm -> sto -> trm -> sto -> Prop :=
  (* computation rules *)
  | red_call : forall s x y m T ds body,
      binds x (object T ds) s ->
      defs_has (open_defs x ds) (label_mtd m) (def_mtd body) ->
      red (trm_call (trm_var (avar_f x)) m (trm_var (avar_f y))) s
          (open_trm y body) s
  | red_sel : forall s x y l T ds,
      binds x (object T ds) s ->
      defs_has (open_defs x ds) (label_fld l) (def_fld y) ->
      red (trm_sel (trm_var (avar_f x)) l) s
          (trm_var y) s
  | red_new : forall s T ds x,
      x # s ->
      red (trm_new T ds) s
          (trm_var (avar_f x)) (s & x ~ (object T ds))
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

(* pmode = "do the "has" judgments needed in subtyping have to be precise?" *)
Inductive pmode : Type := pr | ip.

(* Does this type, and all types that it syntactically contains, have collapsed
   bounds for all type members? *)
Inductive cbounds_typ: typ -> Prop :=
  | cbounds_top:
      cbounds_typ typ_top
  | cbounds_bot:
      cbounds_typ typ_bot
  | cbounds_bind : forall Ds,
      cbounds_decs Ds ->
      cbounds_typ (typ_bind Ds)
  | cbounds_sel: forall p L,
      cbounds_typ (typ_sel p L)
with cbounds_dec: dec -> Prop :=
  | cbounds_dec_typ: forall T,
      cbounds_dec (dec_typ T T) (* <-- that's the whole point *)
  | cbounds_dec_fld: forall T,
      cbounds_dec (dec_fld T)
  | cbounds_dec_mtd: forall T U,
      cbounds_dec (dec_mtd T U)
with cbounds_decs: decs -> Prop :=
  | cbounds_nil:
      cbounds_decs decs_nil
  | cbounds_cons: forall n D Ds,
      cbounds_dec D ->
      cbounds_decs Ds ->
      cbounds_decs (decs_cons n D Ds).

Inductive cbounds_ctx: ctx -> Prop :=
  | cbounds_empty: 
      cbounds_ctx empty
  | cbounds_push: forall G x T,
      cbounds_typ T ->
      cbounds_ctx G ->
      cbounds_ctx (G & x ~ T).

Definition ctx_size(G: ctx) := LibList.length G.

(* expansion returns a set of decs without opening them *)
Inductive exp : pmode -> ctx -> typ -> bdecs -> Prop :=
  | exp_top : forall m G, 
      exp m G typ_top (bdecs_decs decs_nil)
  | exp_bot : forall m G,
      exp m G typ_bot bdecs_bot
  | exp_bind : forall m G Ds,
      exp m G (typ_bind Ds) (bdecs_decs Ds)
  | exp_sel : forall m G x L Lo Hi Ds,
      has m G (trm_var (avar_f x)) L (dec_typ Lo Hi) ->
      exp m G Hi Ds ->
      exp m G (typ_sel (pth_var (avar_f x)) L) Ds
with has : pmode -> ctx -> trm -> label -> dec -> Prop :=
  | has_trm : forall G t T Ds l D,
      ty_trm G t T ->
      exp ip G T Ds ->
      bdecs_has Ds l D ->
      (forall z, (open_dec z D) = D) ->
      has ip G t l D
  | has_var : forall G v T Ds l D,
      ty_trm G (trm_var (avar_f v)) T ->
      exp ip G T Ds ->
      bdecs_has Ds l D ->
      has ip G (trm_var (avar_f v)) l (open_dec v D)
  | has_pr : forall G v T Ds l D,
      binds v T G ->
      exp pr G T Ds ->
      bdecs_has Ds l D ->
      has pr G (trm_var (avar_f v)) l (open_dec v D)
with subtyp : pmode -> tmode -> ctx -> typ -> typ -> nat -> Prop :=
  | subtyp_refl : forall m G T n,
      subtyp m notrans G T T n
  | subtyp_top : forall m G T n,
      subtyp m notrans G T typ_top n
  | subtyp_bot : forall m G T n,
      subtyp m notrans G typ_bot T n
  | subtyp_bind : forall L m G Ds1 Ds2 n,
      (forall z, z \notin L -> 
         subdecs m (G & z ~ (typ_bind Ds1))
                   (open_decs z Ds1) 
                   (open_decs z Ds2) n) ->
      subtyp m notrans G (typ_bind Ds1) (typ_bind Ds2) (S n)
  | subtyp_sel_l : forall m G x L S U T n,
      has m G (trm_var (avar_f x)) L (dec_typ S U) ->
      subtyp m oktrans G U T n ->
      subtyp m notrans G (typ_sel (pth_var (avar_f x)) L) T n
  | subtyp_sel_r : forall m G x L S U T n,
      has m G (trm_var (avar_f x)) L (dec_typ S U) ->
      subtyp m oktrans G S U n -> (* <--- makes proofs a lot easier!! *)
      subtyp m oktrans G T S n ->
      subtyp m notrans G T (typ_sel (pth_var (avar_f x)) L) n
  | subtyp_tmode : forall m G T1 T2 n,
      subtyp m notrans G T1 T2 n ->
      subtyp m oktrans G T1 T2 n
  | subtyp_trans : forall m G T1 T2 T3 n,
      subtyp m oktrans G T1 T2 n ->
      subtyp m oktrans G T2 T3 n ->
      subtyp m oktrans G T1 T3 n
  (* weaking axiom, needed to get env size right for termination measure *)
  | subtyp_weaken : forall m1 m2 G x S T1 T2 n,
      subtyp m1 m2 G T1 T2 (n+1) ->
      x # G ->
      (* TODO maybe also require that S wf in G? *)
      subtyp m1 m2 (G & x ~ S) T1 T2 n
with subdec : pmode -> ctx -> dec -> dec -> nat -> Prop :=
  | subdec_typ : forall m G Lo1 Hi1 Lo2 Hi2 n,
      (* Lo2 <: Lo1 <: Hi1 <: Hi2 *)
      subtyp m oktrans G Lo2 Lo1 n ->
      subtyp m oktrans G Lo1 Hi1 n ->
      subtyp m oktrans G Hi1 Hi2 n ->
      subdec m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2) n
  | subdec_fld : forall m G T1 T2 n,
      subtyp m oktrans G T1 T2 n ->
      subdec m G (dec_fld T1) (dec_fld T2) n
  | subdec_mtd : forall m G S1 T1 S2 T2 n,
      subtyp m oktrans G S2 S1 n ->
      subtyp m oktrans G T1 T2 n ->
      subdec m G (dec_mtd S1 T1) (dec_mtd S2 T2) n
  (* weaking axiom, needed to get env size right for termination measure
  | subdec_weaken : forall m G1 G2 D1 D2 n,
      subdec m G1 D1 D2 ((ctx_size G2) + n) ->
      ok (G1 & G2) ->
      subdec m (G1 & G2) D1 D2 n
  *)
with subdecs : pmode -> ctx -> decs -> decs -> nat -> Prop :=
  | subdecs_empty : forall m G Ds n,
      subdecs m G Ds decs_nil n
  | subdecs_push : forall m G n Ds1 Ds2 D1 D2 n1,
      decs_has Ds1 (label_for_dec n D2) D1 ->
      subdec  m G D1  D2  n1 ->
      subdecs m G Ds1 Ds2 n1 ->
      subdecs m G Ds1 (decs_cons n D2 Ds2) n1
  | subdecs_refl : forall m G Ds n,
      subdecs m G Ds Ds n
with ty_trm : ctx -> trm -> typ -> Prop :=
  | ty_var : forall G x T,
      binds x T G ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_sel : forall G t l T,
      has ip G t (label_fld l) (dec_fld T) ->
      ty_trm G (trm_sel t l) T
  | ty_call : forall G t m U V u,
      has ip G t (label_mtd m) (dec_mtd U V) ->
      ty_trm G u U ->
      ty_trm G (trm_call t m u) V
  | ty_new : forall L G ds Ds,
      (forall x, x \notin L ->
                 ty_defs (G & x ~ typ_bind Ds) (open_defs x ds) (open_decs x Ds)) ->
      cbounds_decs Ds ->
      ty_trm G (trm_new Ds ds) (typ_bind Ds)
  | ty_sbsm : forall G t T U n,
      ty_trm G t T ->
      subtyp ip oktrans G T U n ->
      ty_trm G t U
with ty_def : ctx -> def -> dec -> Prop :=
  | ty_typ : forall G S T,
      ty_def G def_typ (dec_typ S T)
  | ty_fld : forall G v T,
      ty_trm G (trm_var v) T ->
      ty_def G (def_fld v) (dec_fld T)
  | ty_mtd : forall L G S T t,
      (forall x, x \notin L -> ty_trm (G & x ~ S) (open_trm x t) T) ->
      ty_def G (def_mtd t) (dec_mtd S T)
with ty_defs : ctx -> defs -> decs -> Prop :=
  | ty_dsnil : forall G,
      ty_defs G defs_nil decs_nil
  | ty_dscons : forall G ds d Ds D n,
      ty_defs G ds Ds ->
      ty_def  G d D ->
      ty_defs G (defs_cons n d ds) (decs_cons n D Ds).

Inductive subbdecs: pmode -> ctx -> bdecs -> bdecs -> Prop :=
  | subbdecs_bot: forall m G Ds,
      subbdecs m G bdecs_bot Ds
  | subbdecs_decs: forall m G Ds1 Ds2 n,
      subdecs m G Ds1 Ds2 n ->
      subbdecs m G (bdecs_decs Ds1) (bdecs_decs Ds2).

Inductive dmode: Set := deep | shallow.
(* deep enters also computational types (typ_bind),
   shallow only enters non-expansive types (bounds of path types, and/or-types) *)

Inductive wf_typ: dmode -> ctx -> typ -> Prop :=
  | wf_top : forall m G,
      wf_typ m G typ_top
  | wf_bot : forall m G,
      wf_typ m G typ_bot
  | wf_bind_deep : forall L G Ds,
      (forall z, z \notin L -> wf_decs (G & z ~ typ_bind Ds) Ds) ->
      wf_typ deep G (typ_bind Ds)
  | wf_bind_shallow : forall G Ds,
      wf_typ shallow G (typ_bind Ds)
  | wf_sel1 : forall m G x L Lo Hi,
      has pr G (trm_var (avar_f x)) L (dec_typ Lo Hi) ->
      wf_typ m G Lo ->
      wf_typ m G Hi ->
      wf_typ m G (typ_sel (pth_var (avar_f x)) L)
  | wf_sel2 : forall G x L U,
      has pr G (trm_var (avar_f x)) L (dec_typ typ_bot U) ->
      (* deep wf-ness of U was already checked at the definition site of x.L (wf_tmem),
         so it's sufficient to do a shallow check --> allows x.L to appear recursively
         in U, but only behind a computational type --> following upper bound terminates *)
      wf_typ shallow G U ->
      wf_typ deep G (typ_sel (pth_var (avar_f x)) L)
with wf_dec : ctx -> dec -> Prop :=
  | wf_tmem : forall G Lo Hi,
      wf_typ deep G Lo ->
      wf_typ deep G Hi ->
      wf_dec G (dec_typ Lo Hi)
  | wf_fld : forall G T,
      wf_typ deep G T ->
      wf_dec G (dec_fld T)
  | wf_mtd : forall G A R,
      wf_typ deep G A ->
      wf_typ deep G R ->
      wf_dec G (dec_mtd A R)
with wf_decs : ctx -> decs -> Prop :=
  | wf_nil : forall G,
      wf_decs G decs_nil
  | wf_cons : forall G n D Ds,
      wf_dec G D ->
      wf_decs G Ds ->
      wf_decs G (decs_cons n D Ds).


(* returning a set of path types is not needed

(* wf_typ G T returns all path types occur in T's bounds in a non-expansive way
   (i.e. those occurrences which are not guarded by a computational type),
   including T itself if it's a path type *)
Inductive wf_typ: dmode -> ctx -> typ -> fset (pth * label) -> Prop :=
  | wf_top : forall m G,
      wf_typ m G typ_top \{}
  | wf_bot : forall m G,
      wf_typ m G typ_bot \{}
  | wf_bind_deep : forall L G Ds,
      (forall z, z \notin L -> wf_decs (G & z ~ typ_bind Ds) Ds) ->
      wf_typ deep G (typ_bind Ds) \{}
  | wf_bind_shallow : forall G Ds,
      wf_typ shallow G (typ_bind Ds) \{}
  | wf_sel1 : forall m G x L Lo Hi B1 B2,
      has pr G (trm_var (avar_f x)) L (dec_typ Lo Hi) ->
      wf_typ m G Lo B1 ->
      wf_typ m G Hi B2 ->
      wf_typ m G (typ_sel (pth_var (avar_f x)) L)
        (B1 \u (B2 \u \{(pth_var (avar_f x), L)}))
  | wf_sel2 : forall G x L U B,
      has pr G (trm_var (avar_f x)) L (dec_typ typ_bot U) ->
      wf_typ shallow G U B ->
      ((pth_var (avar_f x)), L) \notin B ->
      wf_typ deep G (typ_sel (pth_var (avar_f x)) L)
        (B \u \{(pth_var (avar_f x), L)})
with wf_dec : ctx -> dec -> Prop :=
  | wf_tmem : forall G Lo Hi B1 B2,
      wf_typ deep G Lo B1 ->
      wf_typ deep G Hi B2 ->
      wf_dec G (dec_typ Lo Hi)
  | wf_fld : forall G T B,
      wf_typ deep G T B ->
      wf_dec G (dec_fld T)
  | wf_mtd : forall G A R B1 B2,
      wf_typ deep G A B1 ->
      wf_typ deep G R B2 ->
      wf_dec G (dec_mtd A R)
with wf_decs : ctx -> decs -> Prop :=
  | wf_nil : forall G,
      wf_decs G decs_nil
  | wf_cons : forall G n D Ds,
      wf_dec G D ->
      wf_decs G Ds ->
      wf_decs G (decs_cons n D Ds).


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
      (* note: no check on U --> recursive class types are possible *)
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
  | wf_sto_push : forall s G x ds Ds,
      wf_sto s G ->
      x # s ->
      x # G ->
      (* What's below is the same as the ty_new rule, but we don't use ty_trm,
         because it could be subsumption *)
      ty_defs (G & x ~ typ_bind Ds) (open_defs x ds) (open_decs x Ds) ->
      cbounds_decs Ds ->
      wf_sto (s & x ~ (object Ds ds)) (G & x ~ typ_bind Ds).


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
with   dec_mut  := Induction for dec  Sort Prop
with   decs_mut := Induction for decs Sort Prop.
Combined Scheme typ_mutind from typ_mut, dec_mut, decs_mut.

Scheme exp_mut     := Induction for exp     Sort Prop
with   has_mut     := Induction for has     Sort Prop
with   subtyp_mut  := Induction for subtyp  Sort Prop
with   subdec_mut  := Induction for subdec  Sort Prop
with   subdecs_mut := Induction for subdecs Sort Prop
with   ty_trm_mut  := Induction for ty_trm  Sort Prop
with   ty_def_mut  := Induction for ty_def  Sort Prop
with   ty_defs_mut := Induction for ty_defs Sort Prop.
Combined Scheme ty_mutind from exp_mut, has_mut,
                               subtyp_mut, subdec_mut, subdecs_mut,
                               ty_trm_mut, ty_def_mut, ty_defs_mut.

Scheme has_mut2    := Induction for has    Sort Prop
with   ty_trm_mut2 := Induction for ty_trm Sort Prop.
Combined Scheme ty_has_mutind from has_mut2, ty_trm_mut2.

Scheme exp_mut20  := Induction for exp Sort Prop
with   has_mut20  := Induction for has Sort Prop.
Combined Scheme exp_has_mutind from exp_mut20, has_mut20.

Scheme exp_mut4     := Induction for exp     Sort Prop
with   has_mut4     := Induction for has     Sort Prop
with   subtyp_mut4  := Induction for subtyp  Sort Prop
with   ty_trm_mut4  := Induction for ty_trm  Sort Prop.
Combined Scheme exp_has_subtyp_ty_mutind from exp_mut4, has_mut4, subtyp_mut4, ty_trm_mut4.

Scheme subtyp_mut3  := Induction for subtyp  Sort Prop
with   subdec_mut3  := Induction for subdec  Sort Prop
with   subdecs_mut3 := Induction for subdecs Sort Prop.
Combined Scheme mutind3 from subtyp_mut3, subdec_mut3, subdecs_mut3.

Scheme exp_mut5     := Induction for exp     Sort Prop
with   has_mut5     := Induction for has     Sort Prop
with   subtyp_mut5  := Induction for subtyp  Sort Prop
with   subdec_mut5  := Induction for subdec  Sort Prop
with   subdecs_mut5 := Induction for subdecs Sort Prop.
Combined Scheme mutind5 from exp_mut5, has_mut5,
                             subtyp_mut5, subdec_mut5, subdecs_mut5.

Scheme exp_mut6     := Induction for exp     Sort Prop
with   has_mut6     := Induction for has     Sort Prop
with   subtyp_mut6  := Induction for subtyp  Sort Prop
with   subdec_mut6  := Induction for subdec  Sort Prop
with   subdecs_mut6 := Induction for subdecs Sort Prop
with   ty_trm_mut6  := Induction for ty_trm  Sort Prop.
Combined Scheme mutind6 from exp_mut6, has_mut6,
                             subtyp_mut6, subdec_mut6, subdecs_mut6,
                             ty_trm_mut6.

Scheme wf_typ_mut  := Induction for wf_typ  Sort Prop
with   wf_dec_mut  := Induction for wf_dec  Sort Prop
with   wf_decs_mut := Induction for wf_decs Sort Prop.
Combined Scheme wf_mutind from wf_typ_mut, wf_dec_mut, wf_decs_mut.


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
  let K := gather_vars_with (fun x : decs      => fv_decs  x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors subtyp.
Hint Constructors subdec.


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
  | typ_bind Ds => typ_bind (subst_decs z u Ds)
  | typ_sel p L => typ_sel (subst_pth z u p) L
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ T U => dec_typ (subst_typ z u T) (subst_typ z u U)
  | dec_fld T   => dec_fld (subst_typ z u T)
  | dec_mtd T U => dec_mtd (subst_typ z u T) (subst_typ z u U)
  end
with subst_decs (z: var) (u: var) (Ds: decs) { struct Ds } : decs :=
  match Ds with
  | decs_nil          => decs_nil
  | decs_cons n D Ds' => decs_cons n (subst_dec z u D) (subst_decs z u Ds')
  end.

Definition subst_bdecs (z: var) (u: var) (Ds: bdecs) := match Ds with
  | bdecs_decs Ds0 => bdecs_decs (subst_decs z u Ds0)
  | bdecs_bot => bdecs_bot
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_avar z u x)
  | trm_new Ds ds    => trm_new (subst_decs z u Ds) (subst_defs z u ds)
  | trm_sel t l      => trm_sel (subst_trm z u t) l
  | trm_call t1 m t2 => trm_call (subst_trm z u t1) m (subst_trm z u t2)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ => def_typ
  | def_fld x => def_fld (subst_avar z u x)
  | def_mtd b => def_mtd (subst_trm z u b)
  end
with subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons n d rest => defs_cons n (subst_def z u d) (subst_defs z u rest)
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
  (forall d : dec , x \notin fv_dec  d  -> subst_dec  x y d  = d ) /\
  (forall ds: decs, x \notin fv_decs ds -> subst_decs x y ds = ds).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_pth.
Qed.

Definition subst_fresh_typ(x y: var) := proj1 (subst_fresh_typ_dec_decs x y).

Lemma subst_fresh_bdecs: forall x y Ds, x \notin fv_bdecs Ds -> subst_bdecs x y Ds = Ds.
Proof.
  intros. destruct Ds. reflexivity. simpl. f_equal. apply* subst_fresh_typ_dec_decs.
Qed.

Lemma subst_fresh_trm_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*.
  + apply* subst_fresh_avar.
  + apply* subst_fresh_typ_dec_decs.
  + apply* subst_fresh_avar.
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
  (forall a: avar, forall n: nat,
    subst_avar x y (open_rec_avar n u a) 
    = open_rec_avar n (subst_fvar x y u) (subst_avar  x y a)).
Proof.
  intros. unfold subst_fvar, subst_avar, open_avar, open_rec_avar. destruct a.
  + repeat case_if; auto.
  + case_var*.
Qed.

Lemma subst_open_commute_pth: forall x y u,
  (forall p: pth, forall n: nat,
    subst_pth x y (open_rec_pth n u p) 
    = open_rec_pth n (subst_fvar x y u) (subst_pth x y p)).
Proof.
  intros. unfold subst_pth, open_pth, open_rec_pth. destruct p.
  f_equal. apply subst_open_commute_avar.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec_decs: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall d : dec , forall n: nat, 
     subst_dec x y (open_rec_dec n u d)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y d)) /\
  (forall ds: decs, forall n: nat, 
     subst_decs x y (open_rec_decs n u ds)
     = open_rec_decs n (subst_fvar x y u) (subst_decs x y ds)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_pth.
Qed.

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_trm_def_defs: forall x y u,
  (forall t : trm, forall n: nat,
     subst_trm x y (open_rec_trm n u t)
     = open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) /\
  (forall d : def , forall n: nat, 
     subst_def x y (open_rec_def n u d)
     = open_rec_def n (subst_fvar x y u) (subst_def x y d)) /\
  (forall ds: defs, forall n: nat, 
     subst_defs x y (open_rec_defs n u ds)
     = open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)).
Proof.
  intros. apply trm_mutind; intros; simpl; f_equal*.
  + apply* subst_open_commute_avar.
  + apply* subst_open_commute_typ_dec_decs.
  + apply* subst_open_commute_avar.
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

Lemma subst_open_commute_decs: forall x y u Ds,
  subst_decs x y (open_decs u Ds) = open_decs (subst_fvar x y u) (subst_decs x y Ds).
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
  destruct (@subst_fresh_typ_dec_decs x u) as [_ [Q _]]. rewrite* (Q D).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_intro_decs: forall x u Ds, x \notin (fv_decs Ds) ->
  open_decs u Ds = subst_decs x u (open_decs x Ds).
Proof.
  introv Fr. unfold open_trm. rewrite* subst_open_commute_decs.
  destruct (@subst_fresh_typ_dec_decs x u) as [_ [_ Q]]. rewrite* (Q Ds).
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
/\ (forall D , y \notin fv_dec  D  -> (subst_dec  y x (subst_dec  x y D )) = D )
/\ (forall Ds, y \notin fv_decs Ds -> (subst_decs y x (subst_decs x y Ds)) = Ds).
Proof.
  intros.
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec, fv_decs in *; f_equal*.
  apply* subst_undo_pth.
Qed.

Lemma subst_undo_trm_def_defs: forall x y,
   (forall t , y \notin fv_trm  t  -> (subst_trm  y x (subst_trm  x y t )) = t )
/\ (forall d , y \notin fv_def  d  -> (subst_def  y x (subst_def  x y d )) = d )
/\ (forall ds, y \notin fv_defs ds -> (subst_defs y x (subst_defs x y ds)) = ds).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_def, fv_defs in *; f_equal*.
  + apply* subst_undo_avar.
  + apply* subst_undo_typ_dec_decs.
  + apply* subst_undo_avar.
Qed.

Lemma subst_typ_undo: forall x y T,
  y \notin fv_typ T -> (subst_typ y x (subst_typ x y T)) = T.
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

Lemma defs_has_fld_sync: forall n d ds,
  defs_has ds (label_fld n) d -> exists x, d = (def_fld x).
Proof.
  introv Hhas. induction ds; unfolds defs_has, get_def. 
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
Qed.

Lemma get_def_cons : forall l n d ds,
  get_def l (defs_cons n d ds) = If l = (label_for_def n d) then Some d else get_def l ds.
Proof.
  intros. unfold get_def. case_if~.
Qed.

Lemma get_dec_cons : forall l n D Ds,
  get_dec l (decs_cons n D Ds) = If l = (label_for_dec n D) then Some D else get_dec l Ds.
Proof.
  intros. unfold get_dec. case_if~.
Qed.


(* ###################################################################### *)
(** ** Context size lemmas *)

Lemma inc_max_ctx:
   (forall m1 m2 G T1  T2  n1, subtyp  m1 m2 G T1  T2  n1 ->
      forall n2, n1 <= n2  ->  subtyp  m1 m2 G T1  T2  n2  )
/\ (forall m     G D1  D2  n1, subdec  m     G D1  D2  n1 ->
      forall n2, n1 <= n2 ->   subdec  m     G D1  D2  n2  )
/\ (forall m     G Ds1 Ds2 n1, subdecs m     G Ds1 Ds2 n1 ->
      forall n2, n1 <= n2 ->   subdecs m     G Ds1 Ds2 n2  ).
Proof.
  apply mutind3; try solve [intros; [constructor*
    || apply* subtyp_sel_l
    || apply* subtyp_sel_r]].
  + (* case subtyp_bind *)
    introv Sds IHSds Hle. rename n into n1. destruct n2 as [|n2]; [omega | idtac].
    assert (n1 <= n2) by omega. apply* subtyp_bind.
  + (* case subtyp_trans *)
    intros. apply subtyp_trans with T2; auto.
  + (* case subtyp_weaken *)
    introv St IH xG Hle. rename n into n1. refine (subtyp_weaken _ _ _ xG).
    apply IH. omega.
  + (* case subdecs_push *)
    intros. apply* subdecs_push.
Qed.

Definition subtyp_max_ctx := proj1 inc_max_ctx.
Definition subdec_max_ctx := proj1 (proj2 inc_max_ctx).
Definition subdecs_max_ctx := proj2 (proj2 inc_max_ctx).

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

Lemma invert_subdec_typ_sync_left: forall m G D Lo2 Hi2 n,
   subdec m G D (dec_typ Lo2 Hi2) n ->
   exists Lo1 Hi1, D = (dec_typ Lo1 Hi1) /\
                   subtyp m oktrans G Lo2 Lo1 n /\
                   subtyp m oktrans G Lo1 Hi1 n /\
                   subtyp m oktrans G Hi1 Hi2 n.
Proof.
  introv Sd. inversions Sd. exists Lo1 Hi1. auto.
Qed.

(*
Lemma invert_subdec_fld_sync_left: forall m G D T2,
   subdec m G D (dec_fld T2) ->
   exists T1, D = (dec_fld T1) /\
              subtyp m oktrans G T1 T2.
Proof.
  introv Sd. inversions Sd. exists T1. auto.
Qed.

Lemma invert_subdec_mtd_sync_left: forall m G D T2 U2,
   subdec m G D (dec_mtd T2 U2) ->
   exists T1 U1, D = (dec_mtd T1 U1) /\
                 subtyp m oktrans G T2 T1 /\
                 subtyp m oktrans G U1 U2.
Proof.
  introv Sd. inversions Sd. exists S1 T1. auto.
Qed.

Lemma invert_subdec_typ: forall m G Lo1 Hi1 Lo2 Hi2,
  subdec m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2) ->
  subtyp m oktrans G Lo2 Lo1 /\ subtyp m oktrans G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. auto.
Qed.
*)

Lemma invert_subdecs: forall m G Ds1 Ds2 n,
  subdecs m G Ds1 Ds2 n -> 
  forall l D2, decs_has Ds2 l D2 -> 
               (exists D1, decs_has Ds1 l D1 /\ subdec m G D1 D2 n).
Proof.
  introv Sds. induction Ds2; introv Has.
  + inversion Has.
  + inversions Sds.
    * unfold decs_has, get_dec in Has. case_if.
      - inversions Has.
        exists D1. split; assumption.
      - fold get_dec in Has. apply IHDs2; assumption.
    * exists D2. apply (conj Has). admit. (* TODO subdec_refl *)
Qed.

Lemma wf_sto_to_ok_s: forall s G,
  wf_sto s G -> ok s.
Proof. intros. induction H; jauto. Qed.

Lemma wf_sto_to_ok_G: forall s G,
  wf_sto s G -> ok G.
Proof. intros. induction H; jauto. Qed.

Hint Resolve wf_sto_to_ok_s wf_sto_to_ok_G.

Lemma wf_sto_to_cbounds_ctx: forall s G,
  wf_sto s G -> cbounds_ctx G.
Admitted. (* TODO holds *)

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

Lemma sto_binds_to_ctx_binds: forall s G x Ds ds,
  wf_sto s G ->
  binds x (object Ds ds) s ->
  binds x (typ_bind Ds) G.
Proof.
  introv Wf Bi. gen x Ds Bi. induction Wf; intros.
  + false* binds_empty_inv.
  + unfolds binds. rewrite get_push in *. case_if.
    - inversions Bi. reflexivity.
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

Lemma invert_wf_sto: forall s G,
  wf_sto s G ->
    forall x ds Ds T,
      binds x (object Ds ds) s -> 
      binds x T G ->
      T = (typ_bind Ds) /\ exists G1 G2,
        G = G1 & x ~ typ_bind Ds & G2 /\ 
        ty_defs (G1 & x ~ typ_bind Ds) (open_defs x ds) (open_decs x Ds) /\
        cbounds_decs Ds.
Proof.
  intros s G Wf. induction Wf; intros.
  + false* binds_empty_inv.
  + unfold binds in *. rewrite get_push in *.
    case_if.
    - inversions H3. inversions H4. split. reflexivity.
      exists G (@empty typ). rewrite concat_empty_r. auto.
    - specialize (IHWf x0 ds0 Ds0 T H3 H4).
      destruct IHWf as [EqDs [G1 [G2 [EqG [Ty F]]]]]. subst.
      apply (conj eq_refl).
      exists G1 (G2 & x ~ typ_bind Ds).
      rewrite concat_assoc.
      apply (conj eq_refl). auto.
Qed.

(*
Lemma subdec_sync: forall m G D1 D2,
   subdec m G D1 D2 ->
   (exists Lo1 Hi1 Lo2 Hi2, D1 = dec_typ Lo1 Hi1 /\ D2 = dec_typ Lo2 Hi2)
\/ (exists T1 T2, D1 = dec_fld T1 /\ D2 = dec_fld T2)
\/ (exists T1 U1 T2 U2, D1 = dec_mtd T1 U1 /\ D2 = dec_mtd T2 U2).
Proof.
  introv Sd. inversions Sd.
  + left. do 4 eexists. eauto.
  + right. left. eauto.
  + right. right. do 4 eexists. eauto.
Qed.

Ltac subdec_sync_for Hyp :=
  let Lo1 := fresh "Lo1" in
  let Hi1 := fresh "Hi1" in
  let Lo2 := fresh "Lo2" in
  let Hi2 := fresh "Hi2" in
  let Eq1 := fresh "Eq1" in
  let Eq2 := fresh "Eq2" in
  let T1  := fresh "T1"  in
  let T2  := fresh "T2"  in
  let U1  := fresh "U1"  in
  let U2  := fresh "U2"  in
  destruct (subdec_sync Hyp) as [[Lo1 [Hi1 [Lo2 [Hi2 [Eq1 Eq2]]]]] 
    | [[T1 [T2 [Eq1 Eq2]]] | [T1 [U1 [T2 [U2 [Eq1 Eq2]]]]]]].

Lemma subdec_to_label_for_eq: forall m G D1 D2 n,
  subdec m G D1 D2 ->
  (label_for_dec n D1) = (label_for_dec n D2).
Proof.
  introv Sd. subdec_sync_for Sd; subst; reflexivity.
Qed.
*)

Lemma invert_subdecs_push: forall m G Ds1 Ds2 n D2 n1,
  subdecs m G Ds1 (decs_cons n D2 Ds2) n1 -> 
    exists D1, decs_has Ds1 (label_for_dec n D2) D1
            /\ subdec m G D1 D2 n1
            /\ subdecs m G Ds1 Ds2 n1.
Proof.
  intros. inversions H.
  - eauto.
  - exists D2. split; [idtac | split].
    * unfold decs_has, get_dec. case_if. reflexivity.
    * admit. (* TODO subdec_refl doesn't hold if bad bounds!! *)
    * admit. (* TODO holds *)
Qed.

Lemma ty_def_to_label_for_eq: forall G d D n, 
  ty_def G d D ->
  label_for_def n d = label_for_dec n D.
Proof.
  intros. inversions H; reflexivity.
Qed.

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

Lemma invert_ty_var: forall G x T,
  ty_trm G (trm_var (avar_f x)) T ->
  exists T' n, subtyp ip oktrans G T' T n /\ binds x T' G.
Proof.
  introv Ty. gen_eq t: (trm_var (avar_f x)). gen x.
  induction Ty; intros x' Eq; try (solve [ discriminate ]).
  + inversions Eq. exists T 0.
    apply (conj (subtyp_tmode (subtyp_refl _ _ _ _))). assumption.
  + subst. specialize (IHTy _ eq_refl). destruct IHTy as [T' [n2 [St Bi]]].
    exists T' (max n n2). split.
    - apply subtyp_trans with T.
      * apply (subtyp_max_ctx St). apply Max.le_max_r.
      * apply (subtyp_max_ctx H). apply Max.le_max_l.
    - exact Bi.
Qed.

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

(* The converse does not hold because
   [(open_dec z D1) = (open_dec z D2)] does not imply [D1 = D2]. *)
Lemma decs_has_open: forall Ds l D z,
  decs_has Ds l D -> decs_has (open_decs z Ds) l (open_dec z D).
Proof.
  introv Has. induction Ds.
  + inversion Has.
  + unfold open_decs, open_rec_decs. fold open_rec_decs. fold open_rec_dec.
    unfold decs_has, get_dec. case_if.
    - unfold decs_has, get_dec in Has. rewrite label_for_dec_open in Has. case_if.
      inversions Has. reflexivity.
    - fold get_dec. apply IHDs. unfold decs_has, get_dec in Has.
      rewrite label_for_dec_open in H. case_if. apply Has.
Qed.

(* TODO does not hold because
   [(open_dec z D1) = (open_dec z D2)] does not imply [D1 = D2]. *)
Axiom decs_has_close_admitted: forall Ds l D z,
  decs_has (open_decs z Ds) l (open_dec z D) -> decs_has Ds l D.


(* ###################################################################### *)
(** ** Uniqueness *)

Lemma bdecs_has_unique: forall Ds l D1 D2,
  bdecs_has Ds l D1 ->
  bdecs_has Ds l D2 ->
  D1 = D2.
Proof.
  introv H1 H2. inversions H1; inversions H2; unfold decs_has in *;
  try (rewrite H in H1; inversions H1); reflexivity.
Qed.

Lemma exp_has_unique:
  (forall m G T Ds1, exp m G T Ds1 -> m = pr ->
     forall Ds2, exp pr G T Ds2 -> Ds1 = Ds2) /\ 
  (forall m G v l D1, has m G v l D1 -> m = pr ->
     forall D2, has pr G v l D2 -> D1 = D2).
Proof.
  apply exp_has_mutind; intros.
  + inversions H0. reflexivity.
  + inversions H0. reflexivity.
  + inversions H0. reflexivity.
  + inversions H2. specialize (H eq_refl _ H7). inversions H. apply* (H0 eq_refl).
  + discriminate.
  + discriminate.
  + inversions H1. lets Eq: (binds_func b H3). subst.
    specialize (H eq_refl Ds0 H4). subst Ds0.
    rewrite (bdecs_has_unique b0 H5). reflexivity.
Qed.

Lemma exp_unique: forall G T Ds1 Ds2,
  exp pr G T Ds1 -> exp pr G T Ds2 -> Ds1 = Ds2.
Proof. intros. apply* exp_has_unique. Qed.

Lemma has_unique: forall G v l D1 D2,
  has pr G v l D1 -> has pr G v l D2 -> D1 = D2.
Proof. intros. apply* exp_has_unique. Qed.


(* ###################################################################### *)
(** ** Expansion total *)

Lemma exp_total: forall m G T, wf_typ m G T -> exists Ds, exp pr G T Ds.
Proof.
  introv Wf. induction Wf.
  + (* case wf_top *)
    exists (bdecs_decs decs_nil). apply exp_top.
  + (* case wf_bot *)
    exists bdecs_bot. apply exp_bot.
  + (* case wf_bind_deep *)
    exists (bdecs_decs Ds). apply exp_bind.
  + (* case wf_bind_shallow  *)
    exists (bdecs_decs Ds). apply exp_bind.
  + (* case wf_sel1 *)
    destruct IHWf2 as [DsHi ExpHi].
    exists DsHi. apply (exp_sel H ExpHi).
  + (* case wf_sel2 *)
    destruct IHWf as [DsU ExpU].
    exists DsU. apply (exp_sel H ExpU).
Qed.

Print Assumptions exp_total.


(* ###################################################################### *)
(** ** Weakening *)

(*
Lemma align_env_eq: forall T (E1 E2 F1 F2: env T), E1 & E2 = F1 & F2 ->
   (exists G1 G2 G3, E1 = G1 & G2 /\ E2 = G3 /\ F1 = G1 /\ F2 = G2 & G3)
\/ (exists G1 G2 G3, F1 = G1 & G2 /\ F2 = G3 /\ E1 = G1 /\ E2 = G2 & G3).
Admitted.

Lemma ctx_size_cons: forall G1 G2,
  ctx_size (G1 & G2) = (ctx_size G1) + (ctx_size G2).
Admitted.
*)

Lemma weakening:
   (forall m G T Ds, exp m G T Ds -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      exp m (G1 & G2 & G3) T Ds)
/\ (forall m G t l d, has m G t l d -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      has m (G1 & G2 & G3) t l d)
/\ (forall m1 m2 G T1 T2 n, subtyp m1 m2 G T1 T2 n -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subtyp m1 m2 (G1 & G2 & G3) T1 T2 n)
/\ (forall m G D1 D2 n, subdec m G D1 D2 n -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdec m (G1 & G2 & G3) D1 D2 n)
/\ (forall m G Ds1 Ds2 n, subdecs m G Ds1 Ds2 n -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdecs m (G1 & G2 & G3) Ds1 Ds2 n)
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
      ty_defs (G1 & G2 & G3) ds Ds).
Proof.
  apply ty_mutind.
  + (* case exp_top *)
    intros. apply exp_top.
  + (* case exp_bot *)
    intros. apply exp_bot.
  + (* case exp_bind *)
    intros. apply exp_bind.
  + (* case exp_sel *)
    intros. apply* exp_sel.
  + (* case has_trm *)
    intros. apply* has_trm.
  + (* case has_var *)
    intros. apply* has_var.
  + (* case has_pr *)
    intros. subst. apply has_pr with T Ds.
    - apply* binds_weaken.
    - apply* H. 
    - assumption.
  + (* case subtyp_refl *)
    intros. apply subtyp_refl.
  + (* case subtyp_top *)
    intros. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. apply subtyp_bot.
  + (* case subtyp_bind *)
    introv Sds IHSds Eq1 Ok. subst.
    apply_fresh subtyp_bind as z.
    rewrite <- concat_assoc.
    assert (zL: z \notin L) by auto.
    specialize (Sds z zL).
    refine (IHSds z zL G1 G2 (G3 & z ~ typ_bind Ds1) _ _).
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
  + (* case subtyp_weaken *)
    introv St IH xG Eq Ok. destruct (env_case G3) as [Eq1 | [y [U [G4 Eq1]]]]; subst.
    - rewrite concat_empty_r in *. subst.
      destruct (env_case G2) as [Eq2 | [y [U [G4 Eq2]]]]; subst.
      * rewrite concat_empty_r in *. apply (subtyp_weaken _ _ St xG).
      * rewrite concat_assoc in *.
        specialize (IH G (x ~ S & G4) empty).
        rewrite concat_assoc in IH. repeat rewrite concat_empty_r in IH.
        refine (subtyp_weaken _ _ (IH eq_refl _) (proj2 (ok_push_inv Ok))). auto.
    - rewrite concat_assoc in *. apply eq_push_inv in Eq.
      destruct Eq as [Eq1 [Eq2 Eq3]]. subst.
      apply subtyp_weaken.
      * apply* IH.
      * apply (proj2 (ok_push_inv Ok)).
  + (* case subdec_typ *)
    intros. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. apply* subdec_mtd.
  + (* case subdecs_empty *)
    intros. apply subdecs_empty.
  + (* case subdecs_push *)
    introv Has Sd IHSd Sds IHSds Eq1 Ok.
    apply (subdecs_push n Has).
    - apply (IHSd _ _ _ Eq1 Ok).
    - apply (IHSds _ _ _ Eq1 Ok).
  + (* case subdecs_refl *)
    intros. apply subdecs_refl.
  + (* case ty_var *)
    intros. subst. apply ty_var. apply* binds_weaken.
  + (* case ty_sel *)
    intros. subst. apply* ty_sel.
  + (* case ty_call *)
    intros. subst. apply* ty_call.
  + (* case ty_new *)
    intros L G ds Ds Tyds IHTyds Cb G1 G2 G3 Eq Ok. subst.
    apply_fresh ty_new as x.
    - assert (xL: x \notin L) by auto.
      specialize (IHTyds x xL G1 G2 (G3 & x ~ typ_bind Ds)).
      rewrite <- concat_assoc. apply IHTyds.
      * rewrite concat_assoc. reflexivity.
      * rewrite concat_assoc. auto.
    - exact Cb.
  + (* case ty_sbsm *)
    intros. apply ty_sbsm with T n.
    - apply* H.
    - apply* H0.
  + (* case ty_typ *)
    intros. apply ty_typ. 
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
Qed.

Print Assumptions weakening.

Lemma weaken_exp_middle: forall m G1 G2 G3 T Ds,
  ok (G1 & G2 & G3) -> exp m (G1 & G3) T Ds -> exp m (G1 & G2 & G3) T Ds.
Proof.
  intros. apply* weakening.
Qed.

Lemma weaken_exp_end: forall m G1 G2 T Ds,
  ok (G1 & G2) -> exp m G1 T Ds -> exp m (G1 & G2) T Ds.
Proof.
  introv Ok Exp.
  assert (Eq1: G1 = G1 & empty) by (rewrite concat_empty_r; reflexivity).
  assert (Eq2: G1 & G2 = G1 & G2 & empty) by (rewrite concat_empty_r; reflexivity).
  rewrite Eq1 in Exp. rewrite Eq2 in Ok. rewrite Eq2.
  apply (weaken_exp_middle Ok Exp).
Qed.

Lemma weaken_subtyp_middle: forall m1 m2 G1 G2 G3 S U n,
  ok (G1 & G2 & G3) -> 
  subtyp m1 m2 (G1      & G3) S U n ->
  subtyp m1 m2 (G1 & G2 & G3) S U n.
Proof.
  destruct weakening as [_ [_ [W _]]].
  introv Hok123 Hst.
  specialize (W m1 m2 (G1 & G3) S U n Hst).
  specialize (W G1 G2 G3 eq_refl Hok123).
  apply W.
Qed.

Lemma weaken_subtyp_end: forall m1 m2 G1 G2 T1 T2 n,
  ok (G1 & G2) -> subtyp m1 m2 G1 T1 T2 n -> subtyp m1 m2 (G1 & G2) T1 T2 n.
Proof.
  introv Ok St.
  assert (Eq1: G1 = G1 & empty) by (rewrite concat_empty_r; reflexivity).
  assert (Eq2: G1 & G2 = G1 & G2 & empty) by (rewrite concat_empty_r; reflexivity).
  rewrite Eq1 in St. rewrite Eq2 in Ok. rewrite Eq2.
  apply (weaken_subtyp_middle Ok St).
Qed.

(*
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

Lemma weaken_subtyp_end: forall m1 m2 G1 G2 S U,
  ok (G1 & G2) -> 
  subtyp m1 m2 G1        S U ->
  subtyp m1 m2 (G1 & G2) S U.
Proof.
  introv Hok Hst.
  apply (env_remove_empty (fun G0 => subtyp m1 m2 G0 S U) (G1 & G2)).
  apply weaken_subtyp_middle.
  apply (env_add_empty (fun G0 => ok G0) (G1 & G2) Hok).
  apply (env_add_empty (fun G0 => subtyp m1 m2 G0 S U) G1 Hst).
Qed.

Lemma weaken_has_end: forall m G1 G2 t l d,
  ok (G1 & G2) -> has m G1 t l d -> has m (G1 & G2) t l d.
Proof.
  intros.
  destruct weakening as [_ [W _]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W m (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_subdec_middle: forall m G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subdec m (G1      & G3) S U ->
  subdec m (G1 & G2 & G3) S U.
Proof.
  destruct weakening as [_ [_ [_ [W _]]]].
  introv Hok123 Hst.
  specialize (W m (G1 & G3) S U Hst).
  specialize (W G1 G2 G3 eq_refl Hok123).
  apply W.
Qed.
*)

Lemma weaken_subdec_end: forall m G1 G2 D1 D2 n,
  ok (G1 & G2) -> 
  subdec m G1        D1 D2 n ->
  subdec m (G1 & G2) D1 D2 n.
Proof.
  introv Ok Sd.
  destruct weakening as [_ [_ [_ [W _]]]].
  rewrite <- (concat_empty_r G1) in Sd.
  specialize (W m (G1 & empty) D1 D2 _ Sd G1 G2 empty).
  repeat progress rewrite concat_empty_r in *.
  apply (W eq_refl Ok).
Qed.

Lemma weaken_ty_trm_end: forall G1 G2 e T,
  ok (G1 & G2) -> ty_trm G1 e T -> ty_trm (G1 & G2) e T.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [_ [W _]]]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_def_end: forall G1 G2 i d,
  ok (G1 & G2) -> ty_def G1 i d -> ty_def (G1 & G2) i d.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [_ [_ [W _]]]]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_defs_end: forall G1 G2 is Ds,
  ok (G1 & G2) -> ty_defs G1 is Ds -> ty_defs (G1 & G2) is Ds.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [_ [_ [_ W]]]]]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_trm_middle: forall G1 G2 G3 t T,
  ok (G1 & G2 & G3) -> ty_trm (G1 & G3) t T -> ty_trm (G1 & G2 & G3) t T.
Proof.
  intros. apply* weakening.
Qed.

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

Lemma subst_label_for_dec: forall n x y D,
  label_for_dec n (subst_dec x y D) = label_for_dec n D.
Proof.
  intros. destruct D; reflexivity.
Qed.

Lemma subst_decs_has: forall x y Ds l D,
  decs_has Ds l D ->
  decs_has (subst_decs x y Ds) l (subst_dec x y D).
Proof.
  introv Has. induction Ds.
  + inversion Has.
  + unfold subst_decs, decs_has, get_dec. fold subst_decs subst_dec get_dec.
    rewrite subst_label_for_dec.
    unfold decs_has, get_dec in Has. fold get_dec in Has. case_if.
    - inversions Has. reflexivity.
    - apply* IHDs.
Qed.

Lemma subst_bdecs_has: forall x y Ds l D,
  bdecs_has Ds l D ->
  bdecs_has (subst_bdecs x y Ds) l (subst_dec x y D).
Proof.
  intros. inversions H; simpl; try constructor. apply* subst_decs_has.
Qed.

Lemma subst_binds: forall x y v T G,
  binds v T G ->
  binds v (subst_typ x y T) (subst_ctx x y G).
Proof.
  introv Bi. unfold subst_ctx. apply binds_map. exact Bi.
Qed.

Inductive tyvar: pmode -> ctx -> var -> typ -> Prop :=
  | tyvar_pr: forall G x T,
      binds x T G ->
      tyvar pr G x T
  | tyvar_ip: forall G x T,
      ty_trm G (trm_var (avar_f x)) T ->
      tyvar ip G x T.

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

Lemma subst_decs_preserves_cbounds: forall x y Ds,
  cbounds_decs Ds -> cbounds_decs (subst_decs x y Ds).
Admitted.

Axiom okadmit: forall G: ctx, ok G.

(*
Lemma align_envs_2: forall T (E1 E2 F1 F2: env T) x S,
   E1 & E2 = F1 & x ~ S & F2 ->
   (exists G, F1 = E1 & G /\ E2 = G & x ~ S & F2)
\/ (exists G, F2 = G & E2 /\ E1 = F1 & x ~ S & G).
Admitted.
*)

Lemma subst_ctx_push: forall G x y z T,
  subst_ctx x y (G & z ~ T) = (subst_ctx x y G) & (z ~ subst_typ x y T).
Proof.
  intros. unfold subst_ctx. rewrite map_push. reflexivity.
Qed.

(* Why (n+1)? Because what counts is not the growth, but the max size. The only reason we
   measure the growth is that it's easier to measure. *)
Lemma subst_principles: forall y S,
   (forall m G T Ds, exp m G T Ds -> forall G1 G2 x,
     G = G1 & x ~ S & G2 ->
     tyvar m G1 y S ->
     ok (G1 & x ~ S & G2) ->
     exp m (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_bdecs x y Ds))
/\ (forall m G t l D, has m G t l D -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     tyvar m G1 y S ->
     ok (G1 & (x ~ S) & G2) ->
     has m (G1 & (subst_ctx x y G2)) (subst_trm x y t) l (subst_dec x y D))
/\ (forall m1 m2 G T U n, subtyp m1 m2 G T U n -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     tyvar m1 G1 y S ->
     ok (G1 & (x ~ S) & G2) ->
     subtyp m1 m2 (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U) (n+1))
/\ (forall m G D1 D2 n, subdec m G D1 D2 n -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     tyvar m G1 y S ->
     ok (G1 & (x ~ S) & G2) ->
     subdec m (G1 & (subst_ctx x y G2)) (subst_dec x y D1) (subst_dec x y D2) (n+1))
/\ (forall m G Ds1 Ds2 n, subdecs m G Ds1 Ds2 n -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     tyvar m G1 y S ->
     ok (G1 & (x ~ S) & G2) ->
     subdecs m (G1 & (subst_ctx x y G2)) (subst_decs x y Ds1) (subst_decs x y Ds2) (n+1))
/\ (forall G t T, ty_trm G t T -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     tyvar ip G1 y S ->
     ok (G1 & (x ~ S) & G2) ->
     ty_trm (G1 & (subst_ctx x y G2)) (subst_trm x y t) (subst_typ x y T))
/\ (forall G d D, ty_def G d D -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     tyvar ip G1 y S ->
     ok (G1 & (x ~ S) & G2) ->
     ty_def (G1 & (subst_ctx x y G2)) (subst_def x y d) (subst_dec x y D))
/\ (forall G ds Ds, ty_defs G ds Ds -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     tyvar ip G1 y S ->
     ok (G1 & (x ~ S) & G2) ->
     ty_defs (G1 & (subst_ctx x y G2)) (subst_defs x y ds) (subst_decs x y Ds)).
Proof.
  intros y S. apply ty_mutind.
  (* case exp_top *)
  + intros. simpl. apply exp_top.
  (* case exp_bot *)
  + intros. simpl. apply exp_bot.
  (* case exp_bind *)
  + intros. simpl. apply exp_bind.
  (* case exp_sel *)
  + intros m G v L Lo Hi Ds Has IHHas Exp IHExp G1 G2 x EqG Tyy Ok. subst.
    specialize (IHHas _ _ _ eq_refl Tyy Ok).
    specialize (IHExp _ _ _ eq_refl Tyy Ok).
    unfold subst_typ. unfold subst_pth. unfold subst_avar. case_if.
    - simpl in IHHas. case_if.
      apply (exp_sel IHHas IHExp).
    - simpl in IHHas. case_if.
      apply (exp_sel IHHas IHExp).
  + (* case has_trm *)
    intros G t T Ds l D Ty IHTy Exp IHExp Has Clo G1 G2 x EqG Bi Ok.
    subst. specialize (IHTy _ _ _ eq_refl Bi Ok).
    apply has_trm with (subst_typ x y T) (subst_bdecs x y Ds).
    - exact IHTy.
    - apply* IHExp.
    - apply* subst_bdecs_has.
    - apply (subst_dec_preserves_clo _ _ Clo).
  + (* case has_var *)
    intros G z T Ds l D Ty IHTy Exp IHExp Has G1 G2 x EqG Bi Ok.
    subst. specialize (IHTy _ _ _ eq_refl Bi Ok). simpl in *. case_if.
    - (* case z = x *)
      rewrite (subst_open_commute_dec x y x D). unfold subst_fvar. case_if.
      apply has_var with (subst_typ x y T) (subst_bdecs x y Ds).
      * exact IHTy.
      * apply* IHExp.
      * apply (subst_bdecs_has x y Has).
    - (* case z <> x *)
      rewrite (subst_open_commute_dec x y z D). unfold subst_fvar. case_if.
      apply has_var with (subst_typ x y T) (subst_bdecs x y Ds).
      * exact IHTy.
      * apply* IHExp.
      * apply (subst_bdecs_has x y Has).
  + (* case has_pr *)
    intros G z T Ds l D Bi Exp IHExp DsHas G1 G2 x EqG Ty Ok. subst. simpl in *.
    destruct (middle_notin Ok) as [N1 [N2 [N3 N4]]].
    case_if.
    - (* case z = x *)
      rewrite (subst_open_commute_dec x y x D). unfold subst_fvar. case_if.
      lets Eq: (binds_middle_eq_inv Bi Ok). subst T.
      inversion Ty; subst.
      apply has_pr with (subst_typ x y S) (subst_bdecs x y Ds).
      * rewrite (subst_fresh_typ _ _ N3).
        apply (binds_concat_left H).
        apply ok_remove in Ok.
        unfold subst_ctx.
        rewrite dom_map.
        apply (ok_concat_binds_left_to_notin_right Ok H).
      * apply* IHExp.
      * apply (subst_bdecs_has x y DsHas).
    - (* case z <> x *)
      rewrite (subst_open_commute_dec x y z D). unfold subst_fvar. case_if.
      apply has_pr with (subst_typ x y T) (subst_bdecs x y Ds).
      * lets Bi': (binds_subst Bi H).
        rewrite <- (subst_fresh_ctx y G1 N2).
        rewrite -> (concat_subst_ctx _ _).
        apply (subst_binds _ _ Bi').
      * apply* IHExp.
      * apply (subst_bdecs_has x y DsHas).
  + (* case subtyp_refl *)
    introv EqG Ty Ok. subst. apply subtyp_refl.
  + (* case subtyp_top *)
    intros. simpl. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. simpl. apply subtyp_bot.
  + (* case subtyp_bind *)
    intros L m G Ds1 Ds2 n Sds IH G1 G2 x EqG Bi Ok. subst.
    apply_fresh subtyp_bind as z. fold subst_decs.
    assert (zL: z \notin L) by auto.
    specialize (IH z zL G1 (G2 & z ~ typ_bind Ds1) x).
    rewrite concat_assoc in IH.
    specialize (IH eq_refl Bi).
    unfold subst_ctx in IH. rewrite map_push in IH. simpl in IH.
    rewrite concat_assoc in IH.
    rewrite (subst_open_commute_decs x y z Ds1) in IH.
    rewrite (subst_open_commute_decs x y z Ds2) in IH.
    unfold subst_fvar in IH.
    assert (x <> z) by auto. case_if.
    unfold subst_ctx. apply IH. apply okadmit.
  + (* case subtyp_sel_l *)
    intros m G v L Lo Hi T n Has IHHas St IHSt G1 G2 x EqG Bi Ok. subst.
    specialize (IHSt _ _ _ eq_refl Bi Ok).
    specialize (IHHas _ _ _ eq_refl Bi Ok).
    simpl in *.
    case_if; apply (subtyp_sel_l IHHas IHSt).
  + (* case subtyp_sel_r *)
    intros m G v L Lo Hi T n Has IHHas St1 IHSt1 St2 IHSt2 G1 G2 x EqG Bi Ok. subst.
    specialize (IHSt1 _ _ _ eq_refl Bi Ok).
    specialize (IHSt2 _ _ _ eq_refl Bi Ok).
    specialize (IHHas _ _ _ eq_refl Bi Ok).
    simpl in *.
    case_if; apply (subtyp_sel_r IHHas IHSt1 IHSt2).
  + (* case subtyp_tmode *)
    intros m G T1 T2 n St IH G1 G2 x EqG Bi Ok. subst.
    specialize (IH _ _ _ eq_refl Bi Ok).
    apply (subtyp_tmode IH).
  + (* case subtyp_trans *)
    intros m G T1 T2 T3 St12 IH12 St23 IH23 G1 G2 x Eqm EqG Bi Ok. subst.
    apply* subtyp_trans.
  + (* case subtyp_weaken *)
    introv St IH xG Eq Tyy Ok.
    destruct (env_case G2) as [Eq1 | [x1 [S1 [G4 Eq1]]]]; subst.
    - unfold subst_ctx. rewrite map_empty. rewrite concat_empty_r in *.
      apply eq_push_inv in Eq.
      destruct Eq as [Eq1 [Eq2 Eq3]]. subst x0 S0 G1.
      (* by St, T1 and T2 are wf in G, so: *)
      assert (Eq1: (subst_typ x y T1) = T1) by admit.
      assert (Eq2: (subst_typ x y T2) = T2) by admit.
      rewrite Eq1. rewrite Eq2. exact St.
    - rewrite concat_assoc in *.
      apply eq_push_inv in Eq.
      destruct Eq as [Eq1 [Eq2 Eq3]]. subst. rename xG into x1G, S into S0.
      specialize (IH G1 G4 x0 eq_refl Tyy (proj1 (ok_push_inv Ok))).
      rewrite subst_ctx_push. rewrite concat_assoc.
      apply (subtyp_weaken _ _ IH).
      assert (x1G4: x1 # subst_ctx x0 y G4) by apply* subst_ctx_preserves_notin.
      auto.
  + (* case subdec_typ *)
    intros. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. apply* subdec_mtd.
  + (* case subdecs_empty *)
    intros. apply subdecs_empty.
  + (* case subdecs_push *)
    intros m G n Ds1 Ds2 D1 D2 n1 Has Sd IH1 Sds IH2 G1 G2 x Eq1 Bi Ok. subst.
    specialize (IH1 _ _ _ eq_refl Bi Ok).
    specialize (IH2 _ _ _ eq_refl Bi Ok).
    apply (subst_decs_has x y) in Has.
    rewrite <- (subst_label_for_dec n x y D2) in Has.
    apply subdecs_push with (subst_dec x y D1); 
      fold subst_dec; fold subst_decs; assumption.
  + (* case subdecs_refl *)
    introv EqG Ty Ok. apply subdecs_refl.
  + (* case ty_var *)
    intros G z T Biz G1 G2 x EqG Tyy Ok. subst G.
    destruct (middle_notin Ok) as [xG1 [N2 [N3 N4]]].
    unfold subst_trm, subst_avar. case_var.
    - (* case z = x *)
      assert (EqST: T = S) by apply (binds_middle_eq_inv Biz Ok). subst.
      inversions Tyy. rename H into Tyy.
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
  (* case ty_sel *)
  + intros G t l T Has IH G1 G2 x Eq Bi Ok. apply* ty_sel.
  (* case ty_call *)
  + intros G t m U V u Has IHt Tyu IHu G1 G2 x Eq Bi Ok. apply* ty_call.
  (* case ty_new *)
  + intros L G ds Ds Tyds IHTyds Cb G1 G2 x Eq Bi Ok. subst G.
    apply_fresh ty_new as z.
    - fold subst_defs.
      lets C: (@subst_open_commute_defs x y z ds).
      unfolds open_defs. unfold subst_fvar in C. case_var.
      rewrite <- C.
      lets D: (@subst_open_commute_decs x y z Ds).
      unfolds open_defs. unfold subst_fvar in D. case_var.
      rewrite <- D.
      rewrite <- concat_assoc.
      assert (zL: z \notin L) by auto.
      specialize (IHTyds z zL G1 (G2 & z ~ typ_bind Ds) x). rewrite concat_assoc in IHTyds.
      specialize (IHTyds eq_refl Bi).
      unfold subst_ctx in IHTyds. rewrite map_push in IHTyds. unfold subst_ctx.
      apply IHTyds. auto.
    - apply (subst_decs_preserves_cbounds _ _ Cb).
  (* case ty_sbsm *)
  + intros G t T U n Ty IHTy St IHSt G1 G2 x Eq Bi Ok. subst.
    apply ty_sbsm with (subst_typ x y T) (n+1).
    - apply* IHTy.
    - apply* IHSt.
  (* case ty_typ *)
  + intros. simpl. apply ty_typ.
  (* case ty_fld *)
  + intros. apply* ty_fld.
  (* case ty_mtd *)
  + intros L G T U t Ty IH G1 G2 x Eq Bi Ok. subst.
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
  (* case ty_dsnil *)
  + intros. apply ty_dsnil.
  (* case ty_dscons *)
  + intros. apply* ty_dscons.
Qed.

Print Assumptions subst_principles.

Lemma trm_subst_principle: forall G x y t S T,
  ok (G & x ~ S) ->
  ty_trm (G & x ~ S) t T ->
  ty_trm G (trm_var (avar_f y)) S ->
  ty_trm G (subst_trm x y t) (subst_typ x y T).
Proof.
  introv Hok tTy yTy. destruct (subst_principles y S) as [_ [_ [_ [_ [_ [P _]]]]]].
  specialize (P _ t T tTy G empty x).
  unfold subst_ctx in P. rewrite map_empty in P.
  repeat (progress (rewrite concat_empty_r in P)).
  apply tyvar_ip in yTy.
  apply* P.
Qed.

Lemma pr_subdec_subst_principle: forall G x y S D1 D2 n,
  ok (G & x ~ S) ->
  subdec pr (G & x ~ S) D1 D2 n ->
  binds y S G ->
  subdec pr G (subst_dec x y D1) (subst_dec x y D2) (n+1).
Proof.
  introv Hok Sd yTy. destruct (subst_principles y S) as [_ [_ [_ [P _]]]].
  specialize (P _ _ D1 D2 _ Sd G empty x).
  unfold subst_ctx in P. rewrite map_empty in P.
  repeat (progress (rewrite concat_empty_r in P)).
  apply tyvar_pr in yTy.
  apply* P.
Qed.

Lemma pr_subdecs_subst_principle: forall G x y S Ds1 Ds2 n,
  ok (G & x ~ S) ->
  subdecs pr (G & x ~ S) Ds1 Ds2 n ->
  binds y S G ->
  subdecs pr G (subst_decs x y Ds1) (subst_decs x y Ds2) (n+1).
Proof.
  introv Hok Sds yTy. destruct (subst_principles y S) as [_ [_ [_ [_ [P _]]]]].
  specialize (P _ _ Ds1 Ds2 _ Sds G empty x).
  unfold subst_ctx in P. rewrite map_empty in P.
  repeat (progress (rewrite concat_empty_r in P)).
  apply tyvar_pr in yTy.
  apply* P.
Qed.

Lemma subdecs_subst_principle: forall G x y S Ds1 Ds2 n,
  ok (G & x ~ S) ->
  subdecs ip (G & x ~ S) Ds1 Ds2 n ->
  ty_trm G (trm_var (avar_f y)) S ->
  subdecs ip G (subst_decs x y Ds1) (subst_decs x y Ds2) (n+1).
Proof.
  introv Hok Sds yTy. destruct (subst_principles y S) as [_ [_ [_ [_ [P _]]]]].
  specialize (P _ _ Ds1 Ds2 _ Sds G empty x).
  unfold subst_ctx in P. rewrite map_empty in P.
  repeat (progress (rewrite concat_empty_r in P)).
  apply tyvar_ip in yTy.
  apply* P.
Qed.


(* ###################################################################### *)
(** ** Narrowing *)

(*
Lemma narrow_ty_trm: forall G y T1 T2 u U,
  ok (G & y ~ T2) ->
  subtyp ip oktrans G T1 T2 ->
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

Lemma narrow_subdec_adm: forall G y T1 T2 D1 D2,
  ok (G & y ~ T2) ->
  subtyp ip oktrans G T1 T2 ->
  subdec ip (G & y ~ T2) D1 D2 ->
  subdec ip (G & y ~ T1) D1 D2.
Admitted.

Lemma narrow_subdecs_adm: forall G y T1 T2 Ds1 Ds2,
  ok (G & y ~ T2) ->
  subtyp ip oktrans G T1 T2 ->
  subdecs ip (G & y ~ T2) Ds1 Ds2 ->
  subdecs ip (G & y ~ T1) Ds1 Ds2.
Admitted.
*)


(* ###################################################################### *)
(** ** More inversion lemmas *)

Lemma invert_var_has_dec: forall G x l D,
  has ip G (trm_var (avar_f x)) l D ->
  exists T Ds D', ty_trm G (trm_var (avar_f x)) T /\
                  exp ip G T Ds /\
                  bdecs_has Ds l D' /\
                  open_dec x D' = D.
Proof.
  introv Has. inversions Has.
  (* case has_trm *)
  + subst. exists T Ds D. auto.
  (* case has_var *)
  + exists T Ds D0. auto.
Qed.

Lemma invert_has: forall G t l D,
   has ip G t l D ->
   (exists T Ds,      ty_trm G t T /\
                      exp ip G T Ds /\
                      bdecs_has Ds l D /\
                      (forall z : var, open_dec z D = D))
\/ (exists x T Ds D', t = (trm_var (avar_f x)) /\
                      ty_trm G (trm_var (avar_f x)) T /\
                      exp ip G T Ds /\
                      bdecs_has Ds l D' /\
                      open_dec x D' = D).
Proof.
  introv Has. inversions Has.
  (* case has_trm *)
  + subst. left. exists T Ds. auto.
  (* case has_var *)
  + right. exists v T Ds D0. auto.
Qed.

Lemma invert_var_has_dec_typ: forall G x l S U,
  has ip G (trm_var (avar_f x)) l (dec_typ S U) ->
  exists X Ds S' U', ty_trm G (trm_var (avar_f x)) X /\
                     exp ip G X Ds /\
                     bdecs_has Ds l (dec_typ S' U') /\
                     open_typ x S' = S /\
                     open_typ x U' = U.
Proof.
  introv Has. apply invert_var_has_dec in Has.
  destruct Has as [X [Ds [D [Tyx [Exp [Has Eq]]]]]].
  destruct D as [ Lo Hi | T' | S' U' ]; try solve [ inversion Eq ].
  unfold open_dec, open_rec_dec in Eq. fold open_rec_typ in Eq.
  inversion Eq as [Eq'].
  exists X Ds Lo Hi. auto.
Qed.

Lemma invert_var_has_dec_fld: forall G x l T,
  has ip G (trm_var (avar_f x)) l (dec_fld T) ->
  exists X Ds T', ty_trm G (trm_var (avar_f x)) X /\
                  exp ip G X Ds /\
                  bdecs_has Ds l (dec_fld T') /\
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
                     bdecs_has Ds l (dec_mtd S' U') /\
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
                  bdecs_has Ds l D' /\
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

(*
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

Lemma invert_ty_sel: forall G t l T,
  ty_trm G (trm_sel t l) T ->
  exists T', subtyp ip oktrans G T' T /\ has ip G t (label_fld l) (dec_fld T').
Proof.
  introv Ty. gen_eq t0: (trm_sel t l). gen t l.
  induction Ty; intros t' l' Eq; try (solve [ discriminate ]).
  + inversions Eq. exists T. apply (conj (subtyp_refl_all _ _ _ _)). auto.
  + subst. rename t' into t, l' into l. specialize (IHTy _ _ eq_refl).
    destruct IHTy as [T' [St Has]]. exists T'. split.
    - apply subtyp_trans with T; assumption.
    - exact Has.
Qed.

Lemma invert_ty_call: forall G t m V u,
  ty_trm G (trm_call t m u) V ->
  exists U, has ip G t (label_mtd m) (dec_mtd U V) /\ ty_trm G u U.
Proof.
  intros. inversions H.
  + eauto.
  + admit. (* subsumption case *)
Abort.
*)

Lemma invert_ty_call: forall G t m V2 u,
  ty_trm G (trm_call t m u) V2 ->
  exists U V1 n, has ip G t (label_mtd m) (dec_mtd U V1)
               /\ subtyp ip oktrans G V1 V2 n
               /\ ty_trm G u U.
Proof.
  introv Ty. gen_eq e: (trm_call t m u). gen t m u.
  induction Ty; intros t0 m0 u0 Eq; try solve [ discriminate ]; symmetry in Eq.
  + (* case ty_call *)
    inversions Eq. exists U V. lets StV: (subtyp_tmode (subtyp_refl ip G V 0)). eauto.
  + (* case ty_sbsm *)
    subst t. specialize (IHTy _ _ _ eq_refl).
    rename t0 into t, m0 into m, u0 into u, U into V3, T into V2.
    destruct IHTy as [U [V1 [n' [Has [St12 Tyu]]]]].
    exists U V1.
    assert (n' = n) by admit. (* TODO doesn't hold but will work *) subst.
    lets St13: (subtyp_trans St12 H).
    eauto.
Qed.

(*
Lemma invert_ty_new: forall G ds Ds T2,
  ty_trm G (trm_new Ds ds) T2 ->
  subtyp ip oktrans G (typ_bind Ds) T2 /\
  exists L, (forall x, x \notin L ->
               ty_defs (G & x ~ typ_bind Ds) (open_defs x ds) (open_decs x Ds)) /\
            cbounds_decs Ds.
Proof.
  introv Ty. gen_eq t0: (trm_new Ds ds). gen Ds ds.
  induction Ty; intros Ds' ds' Eq; try (solve [ discriminate ]); symmetry in Eq.
  + (* case ty_new *)
    inversions Eq. apply (conj (subtyp_refl_all _ _ _ _)).
    exists L. auto.
  + (* case ty_sbsm *)
    subst. rename Ds' into Ds, ds' into ds. specialize (IHTy _ _ eq_refl).
    destruct IHTy as [St IHTy].
    apply (conj (subtyp_trans St H) IHTy).
Qed.

(* Note: This is only for notrans mode. Proving it for oktrans mode is the main
   challenge of the whole proof. *)
Lemma invert_subtyp_bind: forall m G Ds1 Ds2,
  subtyp m notrans G (typ_bind Ds1) (typ_bind Ds2) ->
  exists L, forall z, z \notin L ->
            subdecs m (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Proof.
  introv St. inversions St. exists L. assumption.
Qed.

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

Lemma invert_wf_sto_with_sbsm: forall s G,
  wf_sto s G ->
  forall x ds Ds T, 
    binds x (object Ds ds) s ->
    ty_trm G (trm_var (avar_f x)) T (* <- instead of binds *)
    -> exists n, subtyp ip oktrans G (typ_bind Ds) T n
    /\ ty_defs G (open_defs x ds) (open_decs x Ds)
    /\ cbounds_decs Ds.
Proof.
  introv Wf Bis Tyx.
  apply invert_ty_var in Tyx. destruct Tyx as [T'' [St BiG]].
  destruct (invert_wf_sto_with_weakening Wf Bis BiG) as [EqT [Tyds F]].
  subst T''.
  lets Ok: (wf_sto_to_ok_G Wf).
  apply (conj St).
  auto.
Qed.

Lemma collapse_bounds: forall G v l Lo Hi,
  cbounds_ctx G ->
  has pr G (trm_var (avar_f v)) l (dec_typ Lo Hi) ->
  Lo = Hi.
Proof.
  introv Cb Has. induction Cb.
  + inversions Has. false (binds_empty_inv H1).
  + apply invert_has_pr in Has. destruct Has as [T0 [Ds [D [Bi [Exp [DsHas Eq]]]]]].
    apply binds_push_inv in Bi. destruct Bi as [[Eq1 Eq2] | [Ne Bi]].
    - (* case x = v *)
      subst.
Admitted. (* TODO should hold *)
*)


(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(* subdecs_refl does not hold, because subdecs requires that for each dec in rhs
   (including hidden ones), there is an unhidden one in lhs *)
(* or that there are no hidden decs in rhs *)
(* so we just add it as a rule!
Lemma subdecs_refl: forall m G Ds,
  subdecs m G Ds Ds.
Proof.
Admitted. TODO does not hold!! *)

Lemma decs_has_preserves_sub: forall m G Ds1 Ds2 l D2 n,
  decs_has Ds2 l D2 ->
  subdecs m G Ds1 Ds2 n ->
  exists D1, decs_has Ds1 l D1 /\ subdec m G D1 D2 n.
Proof.
  introv Has Sds. induction Ds2.
  + inversion Has.
  + unfold decs_has, get_dec in Has. inversions Sds.
    * case_if.
      - inversions Has. exists D1. auto.
      - fold get_dec in Has. apply* IHDs2.
    * case_if.
      - inversions Has. exists D2. admit. (* TODO holds if subdec_refl holds *)
      - fold get_dec in Has. apply* IHDs2. admit. (* TODO holds modulo name clashes *)
Qed.

(*
Lemma decs_has_preserves_sub_D1_known: forall m G Ds1 Ds2 l D1 D2,
  decs_has Ds1 l D1 ->
  decs_has Ds2 l D2 ->
  subdecs m G Ds1 Ds2 ->
  subdec m G D1 D2.
Proof.
  introv Has1 Has2 Sds. induction Ds2.
  + inversion Has2.
  + unfold decs_has, get_dec in Has2. inversions Sds. case_if.
    - inversions Has2. rename H5 into Has1'.
      unfold decs_has in Has1, Has1'.
      rewrite Has1' in Has1. inversions Has1. assumption.
    - fold get_dec in Has2. apply* IHDs2.
Qed.
*)

Lemma subdec_trans: forall m G D1 D2 D3 n,
  subdec m G D1 D2 n -> subdec m G D2 D3 n -> subdec m G D1 D3 n.
Proof.
Admitted. (*
  introv H12 H23. inversions H12; inversions H23; constructor;
  solve [ assumption | (eapply subtyp_trans; eassumption)].
Qed.*)

Lemma subdecs_trans: forall m G Ds1 Ds2 Ds3 n,
  subdecs m G Ds1 Ds2 n ->
  subdecs m G Ds2 Ds3 n ->
  subdecs m G Ds1 Ds3 n.
Proof.
  introv H12 H23.
  induction Ds3.
  + inversions H23.
    - apply subdecs_empty.
    - exact H12.
  + rename d into D3.
    apply invert_subdecs_push in H23.
    destruct H23 as [D2 [H23a [H23b H23c]]].
    lets H12': (invert_subdecs H12).
    specialize (H12' _ _ H23a).
    destruct H12' as [D1 [Has Sd]].
    apply subdecs_push with D1.
    - assumption.
    - apply subdec_trans with D2; assumption.
    - apply (IHDs3 H23c).
Qed.

(* precise substitution
Lemma pr_subdecs_subst_principle: forall G x y S Ds1 Ds2 n,
  ok (G & x ~ S) ->
  subdecs pr (G & x ~ S) Ds1 Ds2 n ->
  binds y S G ->
  subdecs pr G (subst_decs x y Ds1) (subst_decs x y Ds2) n. (* <-- n preserved ?? *)
Admitted.
*)

Lemma open_decs_nil: forall z, (open_decs z decs_nil) = decs_nil.
Proof.
  intro z. reflexivity.
Qed.

(* a variation of exp_preserves_sub where the first expansion is not a hypothesis,
   but a conclusion (doesn't work because what if T1 has no expansion?)
Lemma swap_sub_and_exp: forall m2 s G T1 T2 Ds2,
  wf_sto s G ->
  subtyp pr m2 G T1 T2 ->
  exp pr G T2 Ds2 ->
  exists L Ds1,
    exp pr G T1 Ds1 /\
    forall z, z \notin L ->
      subdecs pr (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2)
*)

(*
(* does not hold because T1 could be a permutation of T2 *)
Axiom subsub2eq: forall m1 m2 G T1 T2,
  subtyp m1 m2 G T1 T2 ->
  subtyp m1 m2 G T2 T1 ->
  T1 = T2.
*)

(* env-grow restricted narrowing: Narrowing for derivations which grow the env by at
   most n0 entries
   Only deal with judgments for which env size is never bigger than g+n0
 *)
(*
Definition egr_narrowing(g n0: nat): Prop :=
   (forall m G T Ds2, exp m G T Ds2 -> forall G1 G2 x DsA DsB,
    m = pr ->
    g = ctx_size G ->
    ok G ->
    G = G1 & x ~ (typ_bind DsB) & G2 ->
    subdecs pr (G1 & x ~ typ_bind DsA) (open_decs x DsA) (open_decs x DsB)
            ((ctx_size G2) + n0) ->
    exists L Ds1,
      exp pr (G1 & x ~ (typ_bind DsA) & G2) T Ds1 /\ 
      forall z, z \notin L ->
        subdecs pr (G1 & x ~ typ_bind DsA & G2 & z ~ typ_bind Ds1)
                (open_decs z Ds1) (open_decs z Ds2)
                (pred n0)) (* <- note: pred 0 = 0 *)
/\ (forall m G t l D2, has m G t l D2 -> forall G1 G2 x DsA DsB,
    m = pr ->
    g = ctx_size G ->
    ok G ->
    G = G1 & x ~ (typ_bind DsB) & G2 ->
    subdecs pr (G1 & x ~ (typ_bind DsA)) (open_decs x DsA) (open_decs x DsB)
            ((ctx_size G2) + n0) ->
    exists D1,
      has    pr (G1 & x ~ (typ_bind DsA) & G2) t l D1 /\ 
      subdec pr (G1 & x ~ (typ_bind DsA) & G2) D1 D2 n0)
/\ (forall m1 m2 G T1 T2 n, subtyp m1 m2 G T1 T2 n -> forall G1 G2 x DsA DsB,
    m1 = pr ->
    g = ctx_size G ->
    n0 = n ->
    ok G ->
    G = G1 & x ~ (typ_bind DsB) & G2 ->
    subdecs pr (G1 & x ~ (typ_bind DsA)) (open_decs x DsA) (open_decs x DsB)
            ((ctx_size G2) + n) ->
    subtyp pr oktrans (G1 & x ~ (typ_bind DsA) & G2) T1 T2 n)
/\ (forall m G D1 D2 n, subdec m G D1 D2 n -> forall G1 G2 x DsA DsB,
    m = pr ->
    g = ctx_size G ->
    n0 = n ->
    ok G ->
    G = G1 & x ~ (typ_bind DsB) & G2 ->
    subdecs pr (G1 & x ~ (typ_bind DsA)) (open_decs x DsA) (open_decs x DsB)
            ((ctx_size G2) + n) ->
    subdec pr (G1 & x ~ (typ_bind DsA) & G2) D1 D2 n)
/\ (forall m G Ds1 Ds2 n, subdecs m G Ds1 Ds2 n -> forall G1 G2 x DsA DsB,
    m = pr ->
    g = ctx_size G ->
    n0 = n ->
    ok G ->
    G = G1 & x ~ (typ_bind DsB) & G2 ->
    subdecs pr (G1 & x ~ (typ_bind DsA)) (open_decs x DsA) (open_decs x DsB)
            ((ctx_size G2) + n) ->
    subdecs pr (G1 & x ~ (typ_bind DsA) & G2) Ds1 Ds2 n).

(* env-grow-restricted exp_preserves_sub *)
Definition egr_exp_preserves_sub_pr(g n0: nat): Prop := forall m2 G T1 T2 Ds1 Ds2 n,
  subtyp pr m2 G T1 T2 n ->
  g = ctx_size G ->
  n0 = n ->
  exp pr G T1 Ds1 ->
  exp pr G T2 Ds2 ->
  exists L, forall z, z \notin L ->
    subdecs pr (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2) (pred n0). 

Lemma exp_preserves_sub_base_case: forall m1 m2 G T1 T2 n,
  subtyp m1 m2 G T1 T2 n ->
  forall Ds1 Ds2,
  m1 = pr ->
  n = 0 ->
  exp m1 G T1 Ds1 ->
  exp m1 G T2 Ds2 ->
  Ds2 = decs_nil \/ Ds1 = Ds2. (* TODO does not hold any more because of subtyp_weaken ax*)
Proof.
  apply (subtyp_ind (fun m1 m2 G T1 T2 n => forall Ds1 Ds2,
    m1 = pr ->
    n = 0 ->
    exp m1 G T1 Ds1 ->
    exp m1 G T2 Ds2 ->
    Ds2 = decs_nil \/ Ds1 = Ds2)).
  + (* case subtyp_refl *)
    introv Eq _ Exp1 Exp2. subst. right. apply (exp_unique Exp1 Exp2).
  + (* case subtyp_top *)
    introv Eq _ Exp1 Exp2. subst. left. inversions Exp2. reflexivity.
  + (* case subtyp_bot *)
    introv Eq _ Exp1. inversions Exp1.
  + (* case subtyp_bind *)
    introv Sds Eq1 Eq2 Exp1 Exp2. false Eq2.
  + (* case subtyp_sel_l *)
    introv Has2 St IHSt Eq1 Eq2 Exp1 Exp2. subst.
    apply invert_exp_sel in Exp1. destruct Exp1 as [Lo1 [Hi1 [Has1 Exp1]]].
    lets Eq: (has_unique Has2 Has1).
             (**********)
    inversions Eq.
    apply* IHSt.
  + (* case subtyp_sel_r *)
    introv Has St1 IHSt1 St2 IHSt2 Eq1 Eq2 Exp1 Exp2.
    rename S into Lo, U into Hi. subst.
    apply invert_exp_sel in Exp2. destruct Exp2 as [Lo' [Hi' [Has' Exp2]]].
    lets Eq: (has_unique Has' Has). inversions Eq. clear Has'.
             (**********)
    assert (ExpLo: exists DsLo, exp pr G Lo DsLo) by apply exp_total.
    destruct ExpLo as [DsLo ExpLo].
    specialize (IHSt1 DsLo Ds2 eq_refl eq_refl ExpLo Exp2).
    specialize (IHSt2 Ds1 DsLo eq_refl eq_refl Exp1 ExpLo).
    destruct IHSt1 as [IH1 | IH1]; destruct IHSt2 as [IH2 | IH2].
    - auto.
    - auto.
    - left. subst DsLo. exact IH2.
    - right. subst DsLo. exact IH2.
  + (* case subtyp_tmode *)
    introv St IHSt Eq1 Eq2 Exp1 Exp2. apply* IHSt.
  + (* case subtyp_trans *)
    introv St12 IH12 St23 IH23 Eq1 Eq2 Exp1 Exp3. subst. rename Ds2 into Ds3.
    assert (Exp2: exists Ds2, exp pr G T2 Ds2) by apply exp_total.
    destruct Exp2 as [Ds2 Exp2].
    specialize (IH12 _ _ eq_refl eq_refl Exp1 Exp2).
    specialize (IH23 _ _ eq_refl eq_refl Exp2 Exp3).
    destruct IH12 as [IH12 | IH12]; destruct IH23 as [IH23 | IH23].
    - auto.
    - left. subst Ds3. exact IH12.
    - auto.
    - right. subst Ds2. exact IH23.
  + (* case subtyp_weaken *)
    introv St IH xG Eq1 Eq2 Exp1 Exp2. subst.
    (* TODO invoke IH for (ctx_size G), which is smaller than (ctx_size (G & x ~ S)) *)
    admit. (* !!! *)
Qed.

Print Assumptions exp_preserves_sub_base_case.

Lemma egr_exp_preserves_sub_pr_0: forall g, egr_exp_preserves_sub_pr g 0.
Proof.
  unfold egr_exp_preserves_sub_pr. introv St Eq1 Eq2 Exp1 Exp2. subst. simpl.
  lets M: (exp_preserves_sub_base_case St eq_refl eq_refl Exp1 Exp2).
  exists vars_empty. intros z _. destruct M as [Eq | Eq]; subst Ds2.
  - apply subdecs_empty.
  - apply subdecs_refl.
Qed.

Lemma egr_narrowing_to_narrow_subdecs_end: forall g n,
  egr_narrowing g n ->
  forall Ds1 Ds2 G x DsA DsB,
    g = ctx_size (G & x ~ typ_bind DsB) ->
    subdecs pr (G & x ~ typ_bind DsB) Ds1 Ds2 n -> 
    subdecs pr (G & x ~ typ_bind DsA) (open_decs x DsA) (open_decs x DsB) n ->
    subdecs pr (G & x ~ typ_bind DsA) Ds1 Ds2 n.
Proof.
  intros g n N. destruct N as [_ [_ [_ [_ N]]]].
  introv Eq Sds12 SdsAB. subst.
  assert (Ok: ok (G & x ~ typ_bind DsB)) by apply okadmit.
  specialize (N pr _ _ _ _ Sds12 G empty x DsA DsB eq_refl).
  repeat progress rewrite ctx_size_push in N.
  do 2 rewrite concat_empty_r in N.
  assert (Eq: ctx_size empty = 0). admit. (* TODO trivial *)
  rewrite Eq in N.
  simpl in N.
  apply (N eq_refl eq_refl Ok eq_refl SdsAB).
Qed.

Lemma egr_narrowing_to_exp_preserves_sub_pr_step: forall g d,
  egr_narrowing (S g) d -> egr_exp_preserves_sub_pr g (S d).
Proof.
  intros g d N0. unfold egr_exp_preserves_sub_pr. simpl.
  (* We don't use the [induction] tactic because we want to intro everything ourselves: *)
  intros m2 G T1 T2 Ds1 Ds2 n St.
  gen_eq m1: pr. gen m1 m2 G T1 T2 n St Ds1 Ds2.
  lets N: (egr_narrowing_to_narrow_subdecs_end N0). clear N0.
  apply (subtyp_ind (fun m1 m2 G T1 T2 n => forall Ds1 Ds2,
    m1 = pr ->
    g = ctx_size G ->
    S d = n ->
    exp m1 G T1 Ds1 ->
    exp m1 G T2 Ds2 ->
    exists L, forall z, _ ->
      subdecs m1 (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2) d)).
  + (* case subtyp_refl *)
    introv Eq1 Eq2 Eq3 Exp1 Exp2. subst.
    lets Eq: (exp_unique Exp1 Exp2).
    subst. exists vars_empty. intros z zL. apply subdecs_refl.
  + (* case subtyp_top *)
    introv Eq1 Eq2 Eq3 Exp1 Exp2.
    inversions Exp2. exists vars_empty. intros z zL.
    unfold open_decs, open_rec_decs. apply subdecs_empty.
  + (* case subtyp_bot *)
    introv Eq1 Eq2 Eq3 Exp1.
    inversions Exp1.
  + (* case subtyp_bind *)
    introv Sds Eq1 Eq2 Eq3 Exp1 Exp2.
    inversions Exp1. inversions Exp2. exists L. inversions Eq3.
    intros z zL. apply (Sds z zL).
  + (* case subtyp_sel_l *)
    (* This case does not need subdecs_trans, because Exp1 is precise, so the expansion
       of x.L is the same as the expansion of its upper bound Hi1, and we can just apply
       the IH for Hi1<:T *)
    introv Has2 St IHSt Eq1 Eq2 Eq3 Exp1 Exp2. subst.
    apply invert_exp_sel in Exp1. destruct Exp1 as [Lo1 [Hi1 [Has1 Exp1]]].
    lets Eq: (has_unique Has2 Has1).
             (**********)
    inversions Eq.
    apply* IHSt.
  + (* case subtyp_sel_r *)
    (* This case needs subdecs_trans: Ds1 <: DsLo <: Ds2 *)
    introv Has St1 IHSt1 St2 IHSt2 Eq1 Eq2 Eq3 Exp1 Exp2.
    rename S into Lo, U into Hi. subst.
    apply invert_exp_sel in Exp2. destruct Exp2 as [Lo' [Hi' [Has' Exp2]]].
    lets Eq: (has_unique Has' Has). inversions Eq. clear Has'.
             (**********)
    assert (ExpLo: exists DsLo, exp pr G Lo DsLo) by apply exp_total. (* <----- *)
    destruct ExpLo as [DsLo ExpLo].
    specialize (IHSt1 DsLo Ds2 eq_refl eq_refl eq_refl ExpLo Exp2).
    specialize (IHSt2 Ds1 DsLo eq_refl eq_refl eq_refl Exp1 ExpLo).
    destruct IHSt1 as [L1 IH1].
    destruct IHSt2 as [L2 IH2].
    exists (L1 \u L2). intros z zn.
    assert (zL1: z \notin L1) by auto. specialize (IH1 z zL1).
    assert (zL2: z \notin L2) by auto. specialize (IH2 z zL2).
    (* narrowing with d [smaller than d+1 :-)] *)
    refine (subdecs_trans IH2 (N _ _ _ _ _ _ _ IH1 IH2)).
    symmetry. apply ctx_size_push.
  + (* case subtyp_mode *)
    intros. subst. apply* H0.
  + (* case subtyp_trans *)
    introv St12 IHSt12 St23 IHSt23 Eq1 Eq2 Eq3 Exp1 Exp3.
    rename Ds2 into Ds3. subst.
    assert (Exp2: exists Ds2, exp pr G T2 Ds2) by apply exp_total. (* <----- *)
    destruct Exp2 as [Ds2 Exp2].
    specialize (IHSt12 Ds1 Ds2 eq_refl eq_refl eq_refl Exp1 Exp2).
    destruct IHSt12 as [L1 Sds12].
    specialize (IHSt23 Ds2 Ds3 eq_refl eq_refl eq_refl Exp2 Exp3).
    destruct IHSt23 as [L2 Sds23].
    exists (L1 \u L2). intros z zn.
    assert (zL1: z \notin L1) by auto. specialize (Sds12 z zL1).
    assert (zL2: z \notin L2) by auto. specialize (Sds23 z zL2).
    (* narrowing with d [smaller than d+1 :-)] *)
    refine (subdecs_trans Sds12 (N _ _ _ _ _ _ _ Sds23 Sds12)).
    symmetry. apply ctx_size_push.
  + (* case subtyp_weaken *)
    introv St IH xG Eq1 Eq2 Exp1 Exp2. subst.
    (* Oh no! subtyp_weaken changes (ctx_size + growth) to (ctx_size-1 + growth+1),
       and that's just the opposite direction than the termination measure!!!
       Idea was that it changes to (ctx_size-1 + growth). *)
Abort.

(* no base case needed for narrowing because [egr_narrowing d] depends on
   [egr_exp_preserves_sub d] anyways *)

Lemma subdecs_nil_l2r: forall m G Ds n,
  subdecs m G decs_nil Ds n -> Ds = decs_nil.
Proof.
  introv Sds. inversions Sds.
  - reflexivity.
  - inversions H. (* contradiction *)
  - reflexivity.
Qed.

(*
Lemma subdec_weakening_size_trick: forall m G1 G2 D1 D2 n,
  subdec m G1 D1 D2 ((ctx_size G2) + n) ->
  subdec m (G1 & G2) D1 D2 n.
*)

(* TODO does not hold currently, but if we add a weakening axiom to the rules,
   it should work.
   But what effects will that weakening axiom have...? *)
Lemma subdec_weakening_size_trick: forall m G1 G2 D1 D2 n,
  subdec m G1 D1 D2 ((ctx_size G2) + n) ->
  subdec m (G1 & G2) D1 D2 n.
Admitted.

Lemma egr_narrowing_proof: forall g d,
  (d = 0 \/ exists c, S c = d /\ egr_narrowing (S g) c) ->
  egr_exp_preserves_sub_pr g d ->
  egr_narrowing g d.
Proof.
  intros g d N E. unfold egr_narrowing. apply mutind5.
  + (* case exp_top *)
    intros. exists vars_empty decs_nil. split.
    - apply exp_top.
    - intros. rewrite open_decs_nil. apply subdecs_empty.
  + (* case exp_bind *)
    intros. subst. exists vars_empty Ds. split.
    - apply exp_bind.
    - intros. apply subdecs_refl.
  + (* case exp_sel *)
    intros m G v L Lo2 Hi2 Ds2 Has2 IHHas Exp2 IHExp.
    intros G1 G2 x DsA DsB E1 E2 Ok2 E3 SdsAB.
    specialize (IHHas _ _ _ _ _ E1 E2 Ok2 E3 SdsAB).
    specialize (IHExp _ _ _ _ _ E1 E2 Ok2 E3 SdsAB).
    subst.
    destruct IHHas as [D1 [IHHas Sd]].
    destruct IHExp as [L0 [Dsm [IHExp Sds2]]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo21 [StLoHi1 StHi12]]]]]. subst D1.
    assert (A: exists Ds1, exp pr (G1 & x ~ (typ_bind DsA) & G2) Hi1 Ds1) 
      by apply exp_total. (* <----- *)
    destruct A as [Ds1 Exp1].
    destruct N as [N | [c [Eq N]]].
    (* case d = 0 *) {
      subst d. clear E.
      lets E: (exp_preserves_sub_base_case StHi12 eq_refl eq_refl Exp1 IHExp).
      exists L0 Ds1. apply (conj (exp_sel IHHas Exp1)).
      intros z zL0. specialize (Sds2 z zL0).
      destruct E as [E | E]; subst Dsm.
      - rewrite open_decs_nil in Sds2.
        apply subdecs_nil_l2r in Sds2. rewrite Sds2. apply subdecs_empty.
      - exact Sds2.
    }
    (* case d > 0, so write d as d = n + 1 *) {
      subst d. rename c into n.
      (* apply exp_preserves_sub: *)
      lets Sds1: (E _ _ Hi1 Hi2 Ds1 Dsm _ StHi12 
                    (ctx_size_swap_middle G1 x (typ_bind DsB) x (typ_bind DsA) G2)
                    eq_refl Exp1 IHExp).
      destruct Sds1 as [L1 Sds1].
      exists (L0 \u L1) Ds1. apply (conj (exp_sel IHHas Exp1)).
      intros z zL01.
      assert (zL0: z \notin L0) by auto. specialize (Sds2 z zL0).
      assert (zL1: z \notin L1) by auto. specialize (Sds1 z zL1).
      (* Sds1 has a pred because exp_preserves_sub has one,
         Sds2 has a pred because the narrowing IH for exp has one.
         simpl will turn this (pred (S n)) into n. *)
      simpl in *.
      assert (Sds2n: subdecs pr (G1 & x ~ typ_bind DsA & G2 & z ~ typ_bind Ds1 & empty)
                       (open_decs z Dsm) (open_decs z Ds2)
                       n). (* <-- have to take n because P/N are from that level *) {
        (* apply narrowing *)
        destruct N as [_ [_ [_ [_ P]]]].
        assert (Eq: (n = ctx_size empty + n)) by admit. (* TODO trivial *)
        rewrite Eq in Sds1.
        refine (P pr _ _ _ _ Sds2 _ empty _ _ _ eq_refl _ eq_refl _ _ Sds1).
        - rewrite ctx_size_push. f_equal. apply ctx_size_swap_middle.
        - apply okadmit.
        - symmetry. apply concat_empty_r.
      }
      rewrite concat_empty_r in Sds2n.
      apply (subdecs_trans Sds1 Sds2n).
    }
  + (* case has_trm *)
    intros; discriminate.
  + (* case has_var *)
    intros; discriminate.
  + (* case has_pr *)
    intros G v T Ds2 l D2 Bi Exp IHExp DsHas.
    introv _ Eq1 Ok Eq2 SdsAB. subst.
    assert (OkA: ok (G1 & x ~ typ_bind DsA & G2)) by apply okadmit.
    destruct (classicT (v = x)) as [Eq | Ne].
    - (* case v = x *)
      subst. lets Eq: (binds_middle_eq_inv Bi Ok). subst.
      inversions Exp. (* DsB = Ds2 *) rename Ds2 into DsB.
      apply (decs_has_open x) in DsHas.
      lets Sd: (decs_has_preserves_sub DsHas SdsAB).
      destruct Sd as [D1' [DsAHas Sd]].
      assert (exists D1, open_dec x D1 = D1') by admit.
      destruct H as [D1 Eq]. subst.
      exists (open_dec x D1).
      apply subdec_weakening_size_trick in Sd.
           (***************************)
      refine (conj _ Sd).
      apply has_pr with (typ_bind DsA) DsA.
      * assert (xG2: x # G2) by admit.
        apply (binds_middle_eq G1 (typ_bind DsA) xG2).
      * apply exp_bind.
      * apply (decs_has_close_admitted DsA D1 x DsAHas).
    - lets BiA: (binds_weaken (binds_subst Bi Ne) OkA).
      specialize (IHExp _ _ _ _ _ eq_refl eq_refl Ok eq_refl SdsAB).
      destruct IHExp as [L [Ds1 [Exp1 Sds12]]].
      pick_fresh z. assert (zL: z \notin L) by auto.
      specialize (Sds12 z zL).
      apply (decs_has_open z) in DsHas.
      lets Sd: (decs_has_preserves_sub DsHas Sds12).
      destruct Sd as [D1' [Ds1Has Sd]].
      assert (exists D1, open_dec z D1 = D1') by admit.
      destruct H as [D1 Eq]. subst.
      exists (open_dec v D1).
      (* T appears in env, and suppose env only typ_bind: *)
      assert (Eq: T = typ_bind Ds1) by admit. (* <------ *)
      subst.
      lets P: (@pr_subdec_subst_principle (G1 & x ~ typ_bind DsA & G2) z v (typ_bind Ds1)
        (open_dec z D1) (open_dec z D2) (pred d)).
      assert (OkA': ok (G1 & x ~ typ_bind DsA & G2 & z ~ typ_bind Ds1)) by auto.
      specialize (P OkA' Sd BiA).
      assert (Impl1: z \notin fv_decs Ds1 -> z \notin fv_dec D1) by admit.
      assert (Impl2: z \notin fv_decs Ds2 -> z \notin fv_dec D2) by admit.
      assert (FrD1: z \notin fv_dec D1) by auto.
      assert (FrD2: z \notin fv_dec D2) by auto.
      rewrite <- (@subst_intro_dec z v D1 FrD1) in P.
      rewrite <- (@subst_intro_dec z v D2 FrD2) in P.
      (* no more wasted 1 because subst now has (n+1) in conclusion
      assert (Hle: pred d <= d) by omega.
      lets P': (subdec_max_ctx P Hle).
      refine (conj _ P').*)
      assert (Eq: (pred d + 1) = d) by admit. (* TODO doesn't hold if d=0!!!*)
      rewrite Eq in P.
      refine (conj _ P).
      apply has_pr with (typ_bind Ds1) Ds1.
      * exact BiA.
      * apply exp_bind.
      * apply (decs_has_close_admitted Ds1 D1 z Ds1Has).
  + (* case subtyp_refl *)
    introv Eq1 Eq2 Eq3 Ok Eq4 SdsAB. subst.
    apply subtyp_tmode. apply subtyp_refl.
  + (* case subtyp_top *)
    intros. apply subtyp_tmode. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. apply subtyp_tmode. apply subtyp_bot.
  + (* case subtyp_bind *)
    introv Sds IHSds. introv Eq1 Eq2 Eq3 Ok Eq4 SdsAB. subst.
    (* IHSds is useless because it requires S n = n *)
    clear IHSds.
    apply subtyp_tmode. apply_fresh subtyp_bind as z.
    assert (zL: z \notin L) by auto.
    specialize (Sds z zL).
    destruct N as [N | N]; [omega | idtac].
    destruct N as [n' [Eq N]]. inversions Eq.
    destruct N as [_ [_ [_ [_ P]]]].
    specialize (P pr (G1 & x ~ typ_bind DsB & G2 & z ~ typ_bind Ds1)).
    specialize (P (open_decs z Ds1) (open_decs z Ds2) n Sds).
    rewrite ctx_size_push in P.
    specialize (P G1 (G2 & z ~ typ_bind Ds1) x DsA DsB).
    rewrite concat_assoc in P.
    rewrite ctx_size_push in P.
    assert (Eq: (S (ctx_size G2)) + n = (ctx_size G2) + S n) by omega. rewrite Eq in P.
    rewrite concat_assoc in P.
    refine (P eq_refl eq_refl eq_refl (okadmit _) eq_refl SdsAB).
  + (* case subtyp_sel_l *)
    introv Has2 IHHas St IHSt.
    introv Eq1 Eq2 Eq3 Ok Eq4 SdsAB. subst.
    specialize (IHSt  _ _ _ _ _ eq_refl eq_refl eq_refl Ok eq_refl SdsAB).
    specialize (IHHas _ _ _ _ _ eq_refl eq_refl Ok eq_refl SdsAB).
    destruct IHHas as [D1 [Has1 Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo21 [StLoHi1 StHi12]]]]]. subst D1.
    apply subtyp_tmode. apply (subtyp_sel_l Has1).
    apply (subtyp_trans StHi12 IHSt).
  + (* case subtyp_sel_r *)
    intros m G v L Lo2 Hi2 T n Has2 IHHas StLo2Hi2 IHStLo2Hi2 StT1Lo2 IHStTLo2.
    introv Eq1 Eq2 Eq3 Ok Eq4 SdsAB. subst.
    specialize (IHHas _ _ _ _ _ eq_refl eq_refl Ok eq_refl SdsAB).
    destruct IHHas as [D1 [Has1 Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo21 [StLoHi1 StHi12]]]]]. subst D1.
    specialize (IHStTLo2 _ _ _ _ _ eq_refl eq_refl eq_refl Ok eq_refl SdsAB).
    apply subtyp_tmode.
    lets StTLo1: (subtyp_trans IHStTLo2 StLo21).
    apply (subtyp_sel_r Has1 StLoHi1 StTLo1).
  + (* case subtyp_tmode *)
    introv St IHSt Eq1 Eq2 Eq3 Ok Eq4 SdsAB. subst.
    refine (IHSt _ _ _ _ _ eq_refl eq_refl eq_refl _ eq_refl _); assumption.
  + (* case subtyp_trans *)
    introv St12 IHSt12 St23 IHSt23 Eq1 Eq2 Eq3 Ok Eq4 SdsAB. subst.
    apply subtyp_trans with T2.
    - refine (IHSt12 _ _ _ _ _ eq_refl eq_refl eq_refl _ eq_refl _); assumption.
    - refine (IHSt23 _ _ _ _ _ eq_refl eq_refl eq_refl _ eq_refl _); assumption.
  + (* case subtyp_weaken *)
    introv St IH xG Eq1 Eq2 Eq3 Ok Eq4 SdsAB. subst.
    (* IH is useless, and the outer IHs would need 1 smaller!!! *)
    admit. (* doesn't work with termination measure!!!*)
  + (* case subdec_typ *)
    intros. subst. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. subst. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. subst. apply* subdec_mtd.
  + (* case subdecs_empty *)
    intros. subst. apply subdecs_empty.
  + (* case subdecs_push *)
    intros. subst. apply* subdecs_push.
  + (* case subdecs_refl *)
    intros. subst. apply* subdecs_refl.
Qed.

(*
Lemma egr_exp_preserves_sub_pr_step: forall d,
  egr_exp_preserves_sub_pr d -> egr_exp_preserves_sub_pr (d + 1).
Proof.
  intros d E. unfold egr_exp_preserves_sub_pr in *.
Abort. not what we need! *)

Lemma putting_it_together: forall g d,
  egr_exp_preserves_sub_pr g d /\ egr_narrowing g d.
Proof.
  intros g d. remember (g + d) as k eqn: Eqk. gen g. induction d; introv Eqk.
  + clear k Eqk. split.
    - apply (@egr_exp_preserves_sub_pr_0 g).
    - apply (@egr_narrowing_proof g).
      * left; reflexivity.
      * apply (@egr_exp_preserves_sub_pr_0 g).
  + assert (Eqk': k = S g + d) by omega.
    specialize (IHd (S g) Eqk').
    destruct IHd as [E0 N].
    lets E1: (egr_narrowing_to_exp_preserves_sub_pr_step N).
    apply (conj E1).
    apply egr_narrowing_proof.
    - right. exists d. apply (conj eq_refl N).
    - exact E1.
Qed.
*)

Lemma exp_preserves_sub_pr: forall G T1 T2 Ds1 Ds2 n1,
  subtyp pr oktrans G T1 T2 n1 ->
  exp pr G T1 (bdecs_decs Ds1) ->
  exp pr G T2 (bdecs_decs Ds2) ->
  exists L n2, forall z, z \notin L ->
    subdecs pr (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2) n2.
Admitted.
(*
Proof.
  introv St Exp1 Exp2.
  destruct (putting_it_together (ctx_size G) n1) as [E _].
  unfold egr_exp_preserves_sub_pr in E.
  specialize (E oktrans _ _ _ _ _ _ St eq_refl eq_refl Exp1 Exp2).
  destruct E as [L Sds]. exists L (pred n1).
  exact Sds.
Qed.
*)

Lemma ip2pr:
   (forall m G T Ds2', exp m G T Ds2' -> forall s Ds2,
      m = ip ->
      Ds2' = (bdecs_decs Ds2) ->
      wf_sto s G ->
      exists L Ds1 n,
        exp pr G T (bdecs_decs Ds1) /\
        forall z, z \notin L ->
                  subdecs pr (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2) n)
/\ (forall m G t L D2, has m G t L D2 -> forall s v,
      m = ip ->
      wf_sto s G ->
      t = (trm_var (avar_f v)) ->
      exists D1 n, has pr G (trm_var (avar_f v)) L D1 /\
                   subdec pr G D1 D2 n)
/\ (forall m1 m2 G T1 T2 n1, subtyp m1 m2 G T1 T2 n1 -> forall s,
      m1 = ip ->
      wf_sto s G ->
      exists n2, subtyp pr oktrans G T1 T2 n2)
/\ (forall m G D1 D2 n1, subdec m G D1 D2 n1 -> forall s,
      m = ip ->
      wf_sto s G ->
      exists n2, subdec pr G D1 D2 n2)
/\ (forall m G Ds1 Ds2 n1, subdecs m G Ds1 Ds2 n1 -> forall s,
      m = ip ->
      wf_sto s G ->
      exists n2, subdecs pr G Ds1 Ds2 n2)
/\ (forall G t T2, ty_trm G t T2 -> forall s v,
      wf_sto s G ->
      t = (trm_var (avar_f v)) ->
      exists T1 n, binds v T1 G /\
                   subtyp pr oktrans G T1 T2 n).
Proof.
  apply mutind6; try (intros; discriminate).
Admitted. (*
  + (* case exp_top *)
    intros. subst. exists vars_empty decs_nil.
    apply (conj (exp_top _ _)).
    intros. apply subdecs_empty.
  + (* case exp_bind *)
    intros m G Ds s Eq Wf. subst.
    exists vars_empty Ds.
    apply (conj (exp_bind _ _ _)).
    intros. apply subdecs_refl.
  + (* case exp_sel *)
    intros m G v L Lo2 Hi2 Ds2 Has IHHas Exp IHExp s Eq Wf. subst.
    lets Ok: (wf_sto_to_ok_G Wf).
    specialize (IHHas _ _ eq_refl Wf eq_refl). destruct IHHas as [D1 [IHHas IHSd]].
    specialize (IHExp _ eq_refl Wf).
    destruct IHExp as [L0 [Ds1 [ExpHi2 Sds12]]].
    apply invert_subdec_typ_sync_left in IHSd.
    destruct IHSd as [Lo1 [Hi1 [Eq [StLo [_ StHi]]]]]. subst.
    assert (E: exists Ds0, exp pr G Hi1 Ds0) by admit. (* hopefully by wf_sto... *)
    destruct E as [Ds0 ExpHi1].
    assert (Cb: cbounds_ctx G) by admit. (* <------- TODO *)
    lets Sds01: (exp_preserves_sub_pr Cb StHi ExpHi1 ExpHi2).
    destruct Sds01 as [L1 Sds01].
    exists (L0 \u L1) Ds0. split.
    - apply (exp_sel IHHas ExpHi1).
    - intros z Fr.
      assert (zL1: z \notin L1) by auto. specialize (Sds01 z zL1).
      assert (zL0: z \notin L0) by auto. specialize (Sds12 z zL0).
      apply (subdecs_trans Sds01).
      destruct pr_narrowing as [_ [_ [_ [_ N]]]].
      specialize (N pr _ _ _ Sds12 G empty z Ds0 Ds1 eq_refl).
      do 2 rewrite concat_empty_r in N.
      refine (N _ eq_refl _ _ Sds01).
      * admit. (* ok-stuff *)
      * admit. (* !! does `cbounds_decs Ds1` hold ?? *)
      * admit. (* !! does `cbounds_decs Ds0` hold ?? *)

  + (* case has_trm *)
    intros G t X2 Ds2 l D2 Ty IHTy Exp2 IHExp Ds2Has Clo s v _ Wf Eq. subst.
    lets Ok: (wf_sto_to_ok_G Wf).
    specialize (IHExp s eq_refl Wf). destruct IHExp as [L2 [Dsm [Expm Sds2]]].
    specialize (IHTy s v Wf eq_refl). destruct IHTy as [X1 [BiG St]].
    assert (E: exists Ds1, exp pr G X1 Ds1) by admit. (* hopefully by wf_sto... *)
    destruct E as [Ds1 Exp1].
    lets Cb: (wf_sto_to_cbounds_ctx Wf).
    lets Sds1: (exp_preserves_sub_pr Cb St Exp1 Expm).
    destruct Sds1 as [L1 Sds1].
    assert (Sds: forall z, z \notin L1 -> z \notin L2 ->
      subdecs pr (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2)). {
      intros z zL1 zL2. specialize (Sds1 z zL1). specialize (Sds2 z zL2).
      apply (subdecs_trans Sds1).
      destruct pr_narrowing as [_ [_ [_ [_ N]]]].
      specialize (N pr _ _ _ Sds2 G empty z Ds1 Dsm eq_refl).
      do 2 rewrite concat_empty_r in N.
      refine (N _ eq_refl _ _ Sds1).
      * admit. (* ok-stuff *)
      * admit. (* !! does `cbounds_decs Dsm` hold ?? *)
      * admit. (* !! does `cbounds_decs Ds1` hold ?? *)
   }
   pick_fresh z. assert (zL1: z \notin L1) by auto. assert (zL2: z \notin L2) by auto.
   specialize (Sds z zL1 zL2).
   (* T appears in env, and suppose env only typ_bind: *)
   assert (Eq: X1 = typ_bind Ds1) by admit. (* <------ *)
   subst.
   (* precise substitution with BiG and Sds: *)
   assert (Sds12: subdecs pr G (open_decs v Ds1) (open_decs v Ds2)) by admit.
   apply (decs_has_open v) in Ds2Has.
   lets Sd: (decs_has_preserves_sub Ds2Has Sds12).
   destruct Sd as [D1' [Ds1Has Sd]].
   assert (exists D1, open_dec v D1 = D1') by admit.
   destruct H as [D1 Eq]. subst.
   rename D2 into D2'.
   assert (exists D2, open_dec v D2 = D2') by admit.
   destruct H as [D2 Eq]. subst.
   exists (open_dec v D1).
   lets P: (@pr_subst_subdec v (typ_bind Ds1) (open_dec z D1) (open_dec z D2) G empty z).
   unfold subst_ctx in P. rewrite map_empty in P.
   repeat (progress rewrite -> concat_empty_r in P).
   assert (Ok': ok (G & z ~ typ_bind Ds1)) by auto.
   assert (Sd': subdec pr (G & z ~ typ_bind Ds1) (open_dec z D1) (open_dec z D2)) by admit.
   specialize (P Sd' BiG Ok').
   assert (Impl1: z \notin fv_decs Ds1 -> z \notin fv_dec D1) by admit.
   assert (Impl2: z \notin fv_decs Ds2 -> z \notin fv_dec D2) by admit.
   assert (FrD1: z \notin fv_dec D1) by auto.
   assert (FrD2: z \notin fv_dec D2) by auto.
   rewrite <- (@subst_intro_dec z v D1 FrD1) in P.
   rewrite <- (@subst_intro_dec z v D2 FrD2) in P.
   refine (conj _ P).
   apply has_pr with (typ_bind Ds1) Ds1.
   * exact BiG.
   * apply exp_bind.
   * apply (decs_has_close_admitted Ds1 D1 v Ds1Has).
  + (* case has_var *)
    intros G x0 X2 Ds2 l D2 Ty IHTy Exp2 IHExp Ds2Has s x _ Wf Eq. inversions Eq.
    lets Ok: (wf_sto_to_ok_G Wf).
    specialize (IHExp s eq_refl Wf x Ty). destruct IHExp as [Dsm [Expm Sds2]].
    specialize (IHTy s x Wf eq_refl). destruct IHTy as [X1 [BiG St]].
    assert (E: exists Ds1, exp pr G X1 Ds1) by admit. (* hopefully by wf_sto... *)
    destruct E as [Ds1 Exp1].
    lets Sds1: (exp_preserves_sub_pr Wf St Exp1 Expm).
    specialize (Sds1 x (ty_var BiG)).
    lets Sds: (subdecs_trans Sds1 Sds2).
    apply (decs_has_open x) in Ds2Has.
    lets P: (decs_has_preserves_sub Ds2Has Sds).
    destruct P as [D1o [Ds1Has Sd]].
    assert (E: exists D1, D1o = (open_dec x D1)) by admit.
    destruct E as [D1 Eq]. subst D1o.
    exists (open_dec x D1).
    refine (conj _ Sd).
    apply (has_pr BiG Exp1).
    assert (decs_has (open_decs x Ds1) l (open_dec x D1)
         -> decs_has Ds1 l D1) by admit. (* TODO does not hold! *) auto.

  + (* case subtyp_refl *)
    intros m G v L Lo2 Hi2 Has2 IHHas2 s Eq Wf. subst.
    specialize (IHHas2 _ _ eq_refl Wf eq_refl).
    destruct IHHas2 as [D1 [Has1 Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo StHi]]]]. subst D1.
    apply subtyp_tmode. apply (subtyp_refl Has1).
  + (* case subtyp_top *)
    intros. apply subtyp_tmode. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. apply subtyp_tmode. apply subtyp_bot.
  + (* case subtyp_bind *)
    intros L m G Ds1 Ds2 Sds IH s Eq Wf. subst.
    apply subtyp_tmode. apply subtyp_bind with L.
    intros z zL.
    specialize (Sds z zL).
    (* TODO: what if these Ds1 are not realizable?? Then we don't have hyp for IH! *)
    refine (IH z zL _ eq_refl _).
    assert (wf_sto empty (G & z ~ typ_bind Ds1)) by admit. (* <---- *)
    eassumption.
  + (* case subtyp_sel_l *)
    intros m G x L Lo2 Hi2 T Has2 IHHas2 St IHSt s Eq Wf. subst.
    specialize (IHHas2 _ _ eq_refl Wf eq_refl).
    specialize (IHSt _ eq_refl Wf).
    destruct IHHas2 as [D1 [Has1 Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo [_ StHi]]]]]. subst D1.
    apply subtyp_tmode.
    lets StHi1T: (subtyp_trans StHi IHSt).
    apply (subtyp_sel_l Has1 StHi1T).
  + (* case subtyp_sel_r *)
    intros m G x L Lo2 Hi2 T Has2 IHHas StLo2Hi2 IHStLo2Hi2 StTLo2 IHStTLo2 s Eq Wf. subst.
    specialize (IHHas _ _ eq_refl  Wf eq_refl).
    specialize (IHStLo2Hi2 s eq_refl Wf).
    specialize (IHStTLo2 s eq_refl Wf).
    destruct IHHas as [D1 [Has1 Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo2Lo1 [StLo1Hi1 StHi1Hi2]]]]]. subst D1.
    apply subtyp_tmode.
    lets StTLo1: (subtyp_trans IHStTLo2 StLo2Lo1).
    apply (subtyp_sel_r Has1 StLo1Hi1 StTLo1).
  + (* case subtyp_tmode *)
    introv St IHSt Eq Wf. subst. apply* IHSt.
  + (* case subtyp_trans *)
    introv St12 IH12 St23 IH23 Eq Wf. subst.
    apply subtyp_trans with T2; auto_star.

  + (* case subdec_typ *)
    intros. subst. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. subst. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. subst. apply* subdec_mtd.

  + (* case subdecs_empty *)
    intros. subst. apply* subdecs_empty.
  + (* case subdecs_push *)
    intros. subst. apply* subdecs_push.

  + (* case ty_var *)
    intros G x' T BiG s x Wf Eq. inversions Eq. exists T.
    apply (conj BiG).
    apply subtyp_refl_all.
  + (* case ty_sbsm *)
    intros G t T2 T3 Ty IHTy St23 IHSt23 s x Wf Eq. subst.
    specialize (IHTy s x Wf eq_refl). destruct IHTy as [T1 [BiG St12]].
    specialize (IHSt23 s eq_refl Wf).
    exists T1. apply (conj BiG). apply (subtyp_trans St12 IHSt23).
Qed.
*)
Print Assumptions ip2pr.

Lemma ip2pr_has: forall s G v L D2,
  wf_sto s G ->
  has ip G (trm_var (avar_f v)) L D2 ->
  exists D1 n, has pr G (trm_var (avar_f v)) L D1 /\ subdec pr G D1 D2 n.
Proof.
  introv Wf Has.
  destruct ip2pr as [_ [P _]]. apply* P.
Qed.

Lemma pr2ip:
   (forall m G T Ds, exp m G T Ds -> exp ip G T Ds)
/\ (forall m G t L D, has m G t L D -> has ip G t L D)
/\ (forall m1 m2 G T1 T2 n, subtyp m1 m2 G T1 T2 n -> subtyp ip m2 G T1 T2 n)
/\ (forall m G D1 D2 n, subdec m G D1 D2 n -> subdec ip G D1 D2 n)
/\ (forall m G Ds1 Ds2 n, subdecs m G Ds1 Ds2 n -> subdecs ip G Ds1 Ds2 n).
Admitted.

(* Not needed because it's simpler to use exp_preserves_sub directly
Lemma invert_subtyp_bind_oktrans: forall s G Ds1 Ds2 n1,
  wf_sto s G ->
  subtyp ip oktrans G (typ_bind Ds1) (typ_bind Ds2) n1 ->
  exists L n2, forall z, z \notin L ->
              subdecs ip (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2) n2.
Proof.
  introv Wf St. destruct ip2pr as [_ [_ [P _]]].
  specialize (P _ _ _ _ _ _ St _ eq_refl Wf).
  destruct P as [n2 P].
  lets Exp1: (exp_bind pr G Ds1).
  lets Exp2: (exp_bind pr G Ds2).
  lets Cb: (wf_sto_to_cbounds_ctx Wf).
  lets Q: (exp_preserves_sub_pr P Exp1 Exp2).
          (********************)
  destruct Q as [L [n3 Q]]. exists L n3. intros z zL. specialize (Q z zL). apply* pr2ip.
Qed.

Print Assumptions invert_subtyp_bind_oktrans.
*)


(* ###################################################################### *)
(** ** Soundness helper lemmas *)

Lemma has_sound_pr: forall s G x Ds ds l D,
  wf_sto s G ->
  binds x (object Ds ds) s ->
  has pr G (trm_var (avar_f x)) l D ->
  ty_defs G (open_defs x ds) (open_decs x Ds) /\ decs_has (open_decs x Ds) l D.
Proof.
  introv Wf Bis Has.
  apply invert_has_pr in Has. rename D into D'.
  destruct Has as [X' [Ds' [D [BiG' [Exp' [Ds2Has Eq]]]]]]. subst.
  lets BiG: (sto_binds_to_ctx_binds Wf Bis).
  lets Eq: (binds_func BiG BiG'). subst. clear BiG'.
  inversions Exp'.
  inversions Ds2Has. rename H0 into Ds2Has.
  lets P: (invert_wf_sto Wf Bis BiG). destruct P as [_ [G1 [G2 [Eq [Tyds Cb]]]]]. subst.
  lets Ok: (wf_sto_to_ok_G Wf).
  split.
  - apply (weaken_ty_defs_end Ok Tyds).
  - apply (decs_has_open _ Ds2Has).
Qed.

Lemma has_sound: forall s G x Ds1 ds l D2,
  wf_sto s G ->
  binds x (object Ds1 ds) s ->
  has ip G (trm_var (avar_f x)) l D2 ->
  exists D1 n,
    ty_defs G (open_defs x ds) (open_decs x Ds1) /\
    decs_has (open_decs x Ds1) l D1 /\
    subdec ip G D1 D2 n.
Proof.
  introv Wf Bis Has.
  apply (ip2pr_has Wf) in Has. destruct Has as [D1 [n [Has Sd]]].
  lets P: (has_sound_pr Wf Bis Has). destruct P as [Tyds DsHas].
  exists D1 n. repeat split; auto. apply* pr2ip.
Qed.

Print Assumptions has_sound.

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
    specialize (P eq_refl (tyvar_ip Tyy) Okyx).
    unfold subst_ctx in P. rewrite map_empty in P. rewrite concat_empty_r in P.
    exact P.
Qed.


(* ###################################################################### *)
(** ** Progress *)

Theorem progress_result: progress.
Proof.
  introv Wf Ty. gen G e T Ty s Wf.
  set (progress_for := fun s e =>
                         (exists e' s', red e s e' s') \/
                         (exists x o, e = (trm_var (avar_f x)) /\ binds x o s)).
  apply (ty_has_mutind
    (fun m G e l d Has => forall s, wf_sto s G -> m = ip -> progress_for s e)
    (fun G e T Ty      => forall s, wf_sto s G ->           progress_for s e));
    unfold progress_for; clear progress_for.
  (* case has_trm *)
  + intros. auto.
  (* case has_var *)
  + intros G v T Ds l D Ty IH Exp Has s Wf.
    right. apply invert_ty_var in Ty. destruct Ty as [T' [n [St BiG]]].
    destruct (ctx_binds_to_sto_binds Wf BiG) as [o Bis].
    exists v o. auto.
  (* case has_pr *)
  + intros. discriminate.
  (* case ty_var *)
  + intros G x T BiG s Wf.
    right. destruct (ctx_binds_to_sto_binds Wf BiG) as [o Bis].
    exists x o. auto.
  (* case ty_sel *)
  + intros G t l T Has IH s Wf.
    left. specialize (IH s Wf eq_refl). destruct IH as [IH | IH].
    (* receiver is an expression *)
    - destruct IH as [s' [e' IH]]. do 2 eexists. apply (red_sel1 l IH).
    (* receiver is a var *)
    - destruct IH as [x [[X1 ds] [Eq Bis]]]. subst.
      lets P: (has_sound Wf Bis Has).
              (*********)
      destruct P as [Ds1 [D1 [Tyds [Ds1Has Sd]]]].
      destruct (decs_has_to_defs_has Tyds Ds1Has) as [d dsHas].
      destruct (defs_has_fld_sync dsHas) as [r Eqd]. subst.
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
    destruct TyCall as [T2 [U2 [n [Has [StU23 Tyy]]]]].
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
