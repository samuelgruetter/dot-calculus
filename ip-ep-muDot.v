
(*
In trm_new and in object, we only allow Ds, not any type, because that's the
simplest thing which has a stable expansion under narrowing.
Thus, expansion is only needed as a "helper" for has.
We allow subsumption in all judgments, including expansion and has.

The mode "tmode" (notrans or oktrans) controls if transitivity at the top level
is accepted.

The mode "pmode" (imprecise or "env-precise") controls if the "has"
judgments inside the subtyping judgments are allowed to have subsumption (= imprecise)
or not in the following way:
- in imprecise mode (ip), subsumption is allowed everywhere
- in env-precise mode (ep), all sub-proofs with the same environment must not use
  subsumption, but as soon as the environment grows, subsumption is allowed.
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

(* pmode = "do the "has" judgments needed in subtyping have to be precise?"
- in imprecise mode (ip), subsumption is allowed everywhere
- in env-precise mode (ep), all sub-proofs with the same environment must not use
  subsumption, but as soon as the environment grows, subsumption is allowed.*)
Inductive pmode : Type := ip | ep.

(* expansion returns a set of decs without opening them *)
Inductive exp : pmode -> ctx -> typ -> decs -> Prop :=
  | exp_top : forall m G, 
      exp m G typ_top decs_nil
(*| exp_bot : typ_bot has no expansion *)
  | exp_bind : forall m G Ds,
      exp m G (typ_bind Ds) Ds
  | exp_sel : forall m G x L Lo Hi Ds,
      has m G (trm_var (avar_f x)) L (dec_typ Lo Hi) ->
      exp m G Hi Ds ->
      exp m G (typ_sel (pth_var (avar_f x)) L) Ds
with has : pmode -> ctx -> trm -> label -> dec -> Prop :=
  | has_trm : forall G t T Ds l D,
      ty_trm G t T ->
      exp ip G T Ds ->
      decs_has Ds l D ->
      (forall z, (open_dec z D) = D) ->
      has ip G t l D
  | has_var : forall G v T Ds l D,
      ty_trm G (trm_var (avar_f v)) T ->
      exp ip G T Ds ->
      decs_has Ds l D ->
      has ip G (trm_var (avar_f v)) l (open_dec v D)
  | has_ep : forall G v T Ds l D,
      binds v T G ->
      exp ep G T Ds ->
      decs_has Ds l D ->
      has ep G (trm_var (avar_f v)) l (open_dec v D)
with subtyp : pmode -> tmode -> ctx -> typ -> typ -> Prop :=
  | subtyp_refl : forall m G x L Lo Hi,
      has m G (trm_var (avar_f x)) L (dec_typ Lo Hi) ->
      subtyp m notrans G (typ_sel (pth_var (avar_f x)) L) (typ_sel (pth_var (avar_f x)) L)
  | subtyp_top : forall m G T,
      subtyp m notrans G T typ_top
  | subtyp_bot : forall m G T,
      subtyp m notrans G typ_bot T
  (* m1 in hyp, m2 in conclusion, all 4 possibilities are allowed *)
  | subtyp_bind : forall L m1 m2 G Ds1 Ds2,
      (forall z, z \notin L -> 
         subdecs m1 (G & z ~ (typ_bind Ds1))
                   (open_decs z Ds1) 
                   (open_decs z Ds2)) ->
      subtyp m2 notrans G (typ_bind Ds1) (typ_bind Ds2)
  | subtyp_sel_l : forall m G x L S U T,
      has m G (trm_var (avar_f x)) L (dec_typ S U) ->
      subtyp m oktrans G U T ->
      subtyp m notrans G (typ_sel (pth_var (avar_f x)) L) T
  | subtyp_sel_r : forall m G x L S U T,
      has m G (trm_var (avar_f x)) L (dec_typ S U) ->
      subtyp m oktrans G S U -> (* <--- makes proofs a lot easier!! *)
      subtyp m oktrans G T S ->
      subtyp m notrans G T (typ_sel (pth_var (avar_f x)) L)
  | subtyp_tmode : forall m G T1 T2,
      subtyp m notrans G T1 T2 ->
      subtyp m oktrans G T1 T2
  | subtyp_trans : forall m G T1 T2 T3,
      subtyp m oktrans G T1 T2 ->
      subtyp m oktrans G T2 T3 ->
      subtyp m oktrans G T1 T3
with subdec : pmode -> ctx -> dec -> dec -> Prop :=
  | subdec_typ : forall m G Lo1 Hi1 Lo2 Hi2,
      (* only allow implementable decl *)
      subtyp m oktrans G Lo1 Hi1 ->
      subtyp m oktrans G Lo2 Hi2 ->
      (* lhs narrower range than rhs *)
      subtyp m oktrans G Lo2 Lo1 ->
      subtyp m oktrans G Hi1 Hi2 ->
      (* conclusion *)
      subdec m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2)
  | subdec_fld : forall m G T1 T2,
      subtyp m oktrans G T1 T2 ->
      subdec m G (dec_fld T1) (dec_fld T2)
  | subdec_mtd : forall m G S1 T1 S2 T2,
      subtyp m oktrans G S2 S1 ->
      subtyp m oktrans G T1 T2 ->
      subdec m G (dec_mtd S1 T1) (dec_mtd S2 T2)
with subdecs : pmode -> ctx -> decs -> decs -> Prop :=
  | subdecs_empty : forall m G Ds,
      subdecs m G Ds decs_nil
  | subdecs_push : forall m G n Ds1 Ds2 D1 D2,
      decs_has Ds1 (label_for_dec n D2) D1 ->
      subdec  m G D1 D2 ->
      subdecs m G Ds1 Ds2 ->
      subdecs m G Ds1 (decs_cons n D2 Ds2)
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
      (forall x, x \notin L ->
                 forall M S U, decs_has (open_decs x Ds) M (dec_typ S U) -> 
                               subtyp ip oktrans (G & x ~ typ_bind Ds) S U) ->
      ty_trm G (trm_new Ds ds) (typ_bind Ds)
  | ty_sbsm : forall G t T U,
      ty_trm G t T ->
      subtyp ip oktrans G T U ->
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
      (forall L S U, decs_has (open_decs x Ds) L (dec_typ S U) -> 
                     subtyp ip oktrans (G & x ~ typ_bind Ds) S U) ->
      wf_sto (s & x ~ (object Ds ds)) (G & x ~ typ_bind Ds).

(*
ty_trm_new does not check for good bounds recursively inside the types, but that's
not a problem because when creating an object x which has (L: S..U), we have two cases:
Case 1: The object x has a field x.f = y of type x.L: Then y has a type
        Y <: x.L, and when checking the creation of y, we checked that
        the type members of Y are good, so the those of S and U are good as well,
        because S and U are supertypes of Y.
Case 2: The object x has no field of type x.L: Then we can only refer to the
        type x.L, but not to possibly bad type members of the type x.L.
*)


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

Scheme exp_mut6     := Induction for exp     Sort Prop
with   has_mut6     := Induction for has     Sort Prop
with   subtyp_mut6  := Induction for subtyp  Sort Prop
with   subdec_mut6  := Induction for subdec  Sort Prop
with   subdecs_mut6 := Induction for subdecs Sort Prop
with   ty_trm_mut6  := Induction for ty_trm  Sort Prop.
Combined Scheme mutind6 from exp_mut6, has_mut6,
                             subtyp_mut6, subdec_mut6, subdecs_mut6,
                             ty_trm_mut6.


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
  let C := gather_vars_with (fun x : ctx       => dom x     ) in
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
(** ** Trivial inversion lemmas *)

Lemma invert_subdec_typ_sync_left: forall m G D Lo2 Hi2,
   subdec m G D (dec_typ Lo2 Hi2) ->
   exists Lo1 Hi1, D = (dec_typ Lo1 Hi1) /\
                   subtyp m oktrans G Lo2 Lo1 /\
                   subtyp m oktrans G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. exists Lo1 Hi1. auto.
Qed.

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

Lemma invert_subdecs: forall m G Ds1 Ds2,
  subdecs m G Ds1 Ds2 -> 
  forall l D2, decs_has Ds2 l D2 -> 
               (exists D1, decs_has Ds1 l D1 /\ subdec m G D1 D2).
Proof.
  introv Sds. induction Ds2; introv Has.
  + inversion Has.
  + inversions Sds.
    unfold decs_has, get_dec in Has. case_if.
    - inversions Has.
      exists D1. split; assumption.
    - fold get_dec in Has. apply IHDs2; assumption.
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
        (forall L S U, decs_has (open_decs x Ds) L (dec_typ S U) -> 
                       subtyp ip oktrans (G1 & x ~ typ_bind Ds) S U).
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

Lemma invert_subdecs_push: forall m G Ds1 Ds2 n D2,
  subdecs m G Ds1 (decs_cons n D2 Ds2) -> 
    exists D1, decs_has Ds1 (label_for_dec n D2) D1
            /\ subdec m G D1 D2
            /\ subdecs m G Ds1 Ds2.
Proof.
  intros. inversions H. eauto.
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


(* ###################################################################### *)
(** ** Uniqueness *)

Lemma exp_has_unique:
  (forall m G T Ds1, exp m G T Ds1 -> m = ep ->
     forall Ds2, exp ep G T Ds2 -> Ds1 = Ds2) /\ 
  (forall m G v l D1, has m G v l D1 -> m = ep ->
     forall D2, has ep G v l D2 -> D1 = D2).
Proof.
  apply exp_has_mutind; intros.
  + inversions H0. reflexivity.
  + inversions H0. reflexivity.
  + inversions H2. specialize (H eq_refl _ H7). inversions H. apply* (H0 eq_refl).
  + discriminate.
  + discriminate.
  + inversions H1. unfold decs_has in *.
    lets Eq: (binds_func b H3). subst.
    specialize (H eq_refl _ H4). subst.
    rewrite d in H5.
    inversion H5. reflexivity.
Qed.

Lemma exp_unique: forall G T Ds1 Ds2,
  exp ep G T Ds1 -> exp ep G T Ds2 -> Ds1 = Ds2.
Proof. intros. apply* exp_has_unique. Qed.

Lemma has_unique: forall G v l D1 D2,
  has ep G v l D1 -> has ep G v l D2 -> D1 = D2.
Proof. intros. apply* exp_has_unique. Qed.


(* ###################################################################### *)
(** ** Weakening *)

Lemma weakening:
   (forall m G T Ds, exp m G T Ds -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      exp m (G1 & G2 & G3) T Ds)
/\ (forall m G t l d, has m G t l d -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      has m (G1 & G2 & G3) t l d)
/\ (forall m1 m2 G T1 T2, subtyp m1 m2 G T1 T2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subtyp m1 m2 (G1 & G2 & G3) T1 T2)
/\ (forall m G D1 D2, subdec m G D1 D2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdec m (G1 & G2 & G3) D1 D2)
/\ (forall m G Ds1 Ds2, subdecs m G Ds1 Ds2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdecs m (G1 & G2 & G3) Ds1 Ds2)
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
  + (* case exp_bind *)
    intros. apply exp_bind.
  + (* case exp_sel *)
    intros. apply* exp_sel.
  + (* case has_trm *)
    intros. apply* has_trm.
  + (* case has_var *)
    intros. apply* has_var.
  + (* case has_pr *)
    intros. subst. apply has_ep with T Ds.
    - apply* binds_weaken.
    - apply* H. 
    - assumption.
  + (* case subtyp_refl *)
    introv Has IHHas Ok Eq. subst.
    apply* subtyp_refl.
  + (* case subtyp_top *)
    introv Hok123 Heq; subst.
    apply (subtyp_top _ _).
  + (* case subtyp_bot *)
    introv Hok123 Heq; subst.
    apply (subtyp_bot _ _).
  + (* case subtyp_bind *)
    introv Hc IH Hok123 Heq; subst.
    apply_fresh subtyp_bind as z.
    rewrite <- concat_assoc.
    refine (IH z _ G1 G2 (G3 & z ~ typ_bind Ds1) _ _).
    - auto.
    - rewrite <- concat_assoc. reflexivity.
    - rewrite concat_assoc. auto.
  + (* case subtyp_asel_l *)
    intros. subst. apply* subtyp_sel_l.
  + (* case subtyp_asel_r *)
    intros. subst. apply* subtyp_sel_r.
  + (* case subtyp_tmode *)
    introv Hst IH Hok Heq. apply subtyp_tmode. apply* IH.
  + (* case subtyp_trans *)
    intros. subst. apply* subtyp_trans.
  + (* case subdec_typ *)
    intros.
    apply subdec_typ; gen G1 G2 G3; assumption.
  + (* case subdec_fld *)
    intros.
    apply subdec_fld; gen G1 G2 G3; assumption.
  + (* case subdec_mtd *)
    intros.
    apply subdec_mtd; gen G1 G2 G3; assumption.
  + (* case subdecs_empty *)
    intros.
    apply subdecs_empty.
  + (* case subdecs_push *)
    introv Hb Hsd IHsd Hsds IHsds Hok123 Heq.
    apply (subdecs_push n Hb).
    apply (IHsd _ _ _ Hok123 Heq).
    apply (IHsds _ _ _ Hok123 Heq).
  + (* case ty_var *)
    intros. subst. apply ty_var. apply* binds_weaken.
  + (* case ty_sel *)
    intros. subst. apply* ty_sel.
  + (* case ty_call *)
    intros. subst. apply* ty_call.
  + (* case ty_new *)
    intros L G ds Ds Tyds IHTyds F IHF G1 G2 G3 Eq Ok. subst.
    apply_fresh ty_new as x; assert (xL: x \notin L) by auto.
    - specialize (IHTyds x xL G1 G2 (G3 & x ~ typ_bind Ds)).
      rewrite <- concat_assoc. apply IHTyds.
      * rewrite concat_assoc. reflexivity.
      * rewrite concat_assoc. auto.
    - introv Has. specialize (IHF x xL M S U). rewrite <- concat_assoc. apply IHF.
      * auto.
      * rewrite concat_assoc. reflexivity.
      * rewrite concat_assoc. auto.
  + (* case ty_sbsm *)
    intros. apply ty_sbsm with T.
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

Lemma weaken_subtyp_middle: forall m1 m2 G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp m1 m2 (G1      & G3) S U ->
  subtyp m1 m2 (G1 & G2 & G3) S U.
Proof.
  destruct weakening as [_ [_ [W _]]].
  introv Hok123 Hst.
  specialize (W m1 m2 (G1 & G3) S U Hst).
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

Lemma subst_binds: forall x y v T G,
  binds v T G ->
  binds v (subst_typ x y T) (subst_ctx x y G).
Proof.
  introv Bi. unfold subst_ctx. apply binds_map. exact Bi.
Qed.

Lemma subst_principles: forall y S,
   (forall m G T Ds, exp m G T Ds -> forall G1 G2 x,
     G = G1 & x ~ S & G2 ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & x ~ S & G2) ->
     exp ip (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_decs x y Ds))
/\ (forall m G t l D, has m G t l D -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     has ip (G1 & (subst_ctx x y G2)) (subst_trm x y t) l (subst_dec x y D))
/\ (forall m1 m2 G T U, subtyp m1 m2 G T U -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     subtyp ip m2 (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U))
/\ (forall m G D1 D2, subdec m G D1 D2 -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     subdec ip (G1 & (subst_ctx x y G2)) (subst_dec x y D1) (subst_dec x y D2))
/\ (forall m G Ds1 Ds2, subdecs m G Ds1 Ds2 -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     subdecs ip (G1 & (subst_ctx x y G2)) (subst_decs x y Ds1) (subst_decs x y Ds2))
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
/\ (forall G ds Ds, ty_defs G ds Ds -> forall G1 G2 x,
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     ty_defs (G1 & (subst_ctx x y G2)) (subst_defs x y ds) (subst_decs x y Ds)).
Proof.
  intros y S. apply ty_mutind.
  (* case exp_top *)
  + intros. simpl. apply exp_top.
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
    apply has_trm with (subst_typ x y T) (subst_decs x y Ds).
    - exact IHTy.
    - apply* IHExp.
    - apply* subst_decs_has.
    - intro z. specialize (Clo z). admit.
  + (* case has_var *)
    intros G z T Ds l D Ty IHTy Exp IHExp Has G1 G2 x EqG Bi Ok.
    subst. specialize (IHTy _ _ _ eq_refl Bi Ok). simpl in *. case_if.
    - (* case z = x *)
      rewrite (subst_open_commute_dec x y x D). unfold subst_fvar. case_if.
      apply has_var with (subst_typ x y T) (subst_decs x y Ds).
      * exact IHTy.
      * apply* IHExp.
      * apply (subst_decs_has x y Has).
    - (* case z <> x *)
      rewrite (subst_open_commute_dec x y z D). unfold subst_fvar. case_if.
      apply has_var with (subst_typ x y T) (subst_decs x y Ds).
      * exact IHTy.
      * apply* IHExp.
      * apply (subst_decs_has x y Has).
  + (* case has_ep *)
    intros G z T Ds l D Bi Exp IHExp Has G1 G2 x EqG Ty Ok.
    subst. simpl in *. case_if.
    - (* case z = x *)
      rewrite (subst_open_commute_dec x y x D). unfold subst_fvar. case_if.
      lets Eq: (binds_middle_eq_inv Bi Ok). subst.
      apply has_var with S (subst_decs x y Ds).
      * assert (Ok': ok (G1 & subst_ctx x y G2)) by admit. (* <--- TODO *)
        apply (weaken_ty_trm_end Ok' Ty).
      * (* because x after G1 and S types in G1: *)
        assert (Eq: S = (subst_typ x y S)) by admit. rewrite Eq.
        apply* IHExp.
      * apply (subst_decs_has x y Has).
    - (* case z <> x *)
      rewrite (subst_open_commute_dec x y z D). unfold subst_fvar. case_if.
      apply has_var with (subst_typ x y T) (subst_decs x y Ds).
      * admit. (* TODO should follow from Bi *)
      * apply* IHExp.
      * apply (subst_decs_has x y Has).
  + (* case subtyp_refl *)
    intros m G v L Lo Hi Has IHHas G1 G2 x EqG Tyy Ok. subst.
    specialize (IHHas _ _ _ eq_refl Tyy Ok).
    unfold subst_dec in IHHas. fold subst_typ in IHHas.
    unfold subst_trm, subst_avar in IHHas.
    simpl. case_if; apply (subtyp_refl IHHas).
  + (* case subtyp_top *)
    intros. simpl. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. simpl. apply subtyp_bot.
  + (* case subtyp_bind *)
    intros L m1 m2 G Ds1 Ds2 Sds IH G1 G2 x EqG Bi Ok. subst.
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
    unfold subst_ctx. apply IH. admit.
  + (* case subtyp_sel_l *)
    intros m G v L Lo Hi T Has IHHas St IHSt G1 G2 x EqG Bi Ok. subst.
    specialize (IHSt _ _ _ eq_refl Bi Ok).
    specialize (IHHas _ _ _ eq_refl Bi Ok).
    simpl in *.
    case_if; apply (subtyp_sel_l IHHas IHSt).
  + (* case subtyp_sel_r *)
    intros m G v L Lo Hi T Has IHHas St1 IHSt1 St2 IHSt2 G1 G2 x EqG Bi Ok. subst.
    specialize (IHSt1 _ _ _ eq_refl Bi Ok).
    specialize (IHSt2 _ _ _ eq_refl Bi Ok).
    specialize (IHHas _ _ _ eq_refl Bi Ok).
    simpl in *.
    case_if; apply (subtyp_sel_r IHHas IHSt1 IHSt2).
  + (* case subtyp_tmode *)
    intros m G T1 T2 St IH G1 G2 x EqG Bi Ok. subst.
    specialize (IH _ _ _ eq_refl Bi Ok).
    apply (subtyp_tmode IH).
  + (* case subtyp_trans *)
    intros m G T1 T2 T3 St12 IH12 St23 IH23 G1 G2 x EqG Bi Ok. subst.
    apply* subtyp_trans.
  + (* case subdec_typ *)
    intros. apply* subdec_typ.
  + (* case subdec_fld *)
    intros. apply* subdec_fld.
  + (* case subdec_mtd *)
    intros. apply* subdec_mtd.
  + (* case subdecs_empty *)
    intros. apply subdecs_empty.
  + (* case subdecs_push *)
    intros m G n Ds1 Ds2 D1 D2 Has Sd IH1 Sds IH2 G1 G2 x Eq1 Bi Ok. subst.
    specialize (IH1 _ _ _ eq_refl Bi Ok).
    specialize (IH2 _ _ _ eq_refl Bi Ok).
    apply (subst_decs_has x y) in Has.
    rewrite <- (subst_label_for_dec n x y D2) in Has.
    apply subdecs_push with (subst_dec x y D1); 
      fold subst_dec; fold subst_decs; assumption.
  + (* case ty_var *)
    intros G z T Biz G1 G2 x EqG Biy Ok.
    subst G. unfold subst_trm, subst_avar. case_var.
    - (* case z = x *)
      assert (EqST: T = S) by apply (binds_middle_eq_inv Biz Ok). subst.
      assert (yG2: y # (subst_ctx x y G2)) by admit.
      assert (xG1: x # G1) by admit.
      assert (Eq: (subst_typ x y S) = S) by admit.
      rewrite Eq. 
      apply weaken_ty_trm_end.
      * unfold subst_ctx. auto.
      * assumption.
    - (* case z <> x *)
      apply ty_var. admit. (* TODO! *)
  (* case ty_sel *)
  + intros G t l T Has IH G1 G2 x Eq Bi Ok. apply* ty_sel.
  (* case ty_call *)
  + intros G t m U V u Has IHt Tyu IHu G1 G2 x Eq Bi Ok. apply* ty_call.
  (* case ty_new *)
  + intros L G ds Ds Tyds IHTyds F IHF G1 G2 x Eq Bi Ok. subst G.
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
    - intros M Lo Hi Has.
      assert (zL: z \notin L) by auto. specialize (F z zL M Lo Hi).
      admit. (* TODO! *)
  (* case ty_sbsm *)
  + intros G t T U Ty IHTy St IHSt G1 G2 x Eq Bi Ok. subst.
    apply ty_sbsm with (subst_typ x y T).
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
  apply* P.
Qed.

Lemma subdecs_subst_principle: forall G x y S Ds1 Ds2,
  ok (G & x ~ S) ->
  subdecs ip (G & x ~ S) Ds1 Ds2 ->
  ty_trm G (trm_var (avar_f y)) S ->
  subdecs ip G (subst_decs x y Ds1) (subst_decs x y Ds2).
Proof.
  introv Hok Sds yTy. destruct (subst_principles y S) as [_ [_ [_ [_ [P _]]]]].
  specialize (P _ _ Ds1 Ds2 Sds G empty x).
  unfold subst_ctx in P. rewrite map_empty in P.
  repeat (progress (rewrite concat_empty_r in P)).
  apply* P.
Qed.


(* ###################################################################### *)
(** ** Narrowing *)

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

Lemma narrow_subdec: forall G y T1 T2 D1 D2,
  ok (G & y ~ T2) ->
  subtyp ip oktrans G T1 T2 ->
  subdec ip (G & y ~ T2) D1 D2 ->
  subdec ip (G & y ~ T1) D1 D2.
Admitted.

Lemma narrow_subdecs: forall G y T1 T2 Ds1 Ds2,
  ok (G & y ~ T2) ->
  subtyp ip oktrans G T1 T2 ->
  subdecs ip (G & y ~ T2) Ds1 Ds2 ->
  subdecs ip (G & y ~ T1) Ds1 Ds2.
Admitted.


(* ###################################################################### *)
(** ** More inversion lemmas *)

Lemma invert_var_has_dec: forall G x l D,
  has ip G (trm_var (avar_f x)) l D ->
  exists T Ds D', ty_trm G (trm_var (avar_f x)) T /\
                  exp ip G T Ds /\
                  decs_has Ds l D' /\
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

Lemma invert_var_has_dec_typ: forall G x l S U,
  has ip G (trm_var (avar_f x)) l (dec_typ S U) ->
  exists X Ds S' U', ty_trm G (trm_var (avar_f x)) X /\
                     exp ip G X Ds /\
                     decs_has Ds l (dec_typ S' U') /\
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

Lemma invert_has_ep: forall G x l D,
  has ep G (trm_var (avar_f x)) l D ->
  exists T Ds D', binds x T G /\
                  exp ep G T Ds /\
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

Lemma subtyp_refl_all: forall m1 m2 G T, subtyp m1 m2 G T T.
Admitted.

Lemma invert_ty_var: forall G x T,
  ty_trm G (trm_var (avar_f x)) T ->
  exists T', subtyp ip oktrans G T' T /\ binds x T' G.
Proof.
  introv Ty. gen_eq t: (trm_var (avar_f x)). gen x.
  induction Ty; intros x' Eq; try (solve [ discriminate ]).
  + inversions Eq. exists T. apply (conj (subtyp_refl_all _ _ _ _)). auto.
  + subst. specialize (IHTy _ eq_refl). destruct IHTy as [T' [St Bi]].
    exists T'. split.
    - apply subtyp_trans with T; assumption.
    - exact Bi.
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

(*
Lemma invert_ty_sel: forall G t l T,
  ty_trm G (trm_sel t l) T ->
  has ip G t (label_fld l) (dec_fld T).
Proof.
  introv Ty. gen_eq t0: (trm_sel t l). gen t l.
  induction Ty; intros t' l' Eq; try (solve [ discriminate ]).
  + inversions Eq. assumption.
  + subst. rename t' into t, l' into l. specialize (IHTy _ _ eq_refl).
    apply invert_has in IHTy.
    destruct IHTy as [IHTy | IHTy].
    (* case has_trm *)
    - destruct IHTy as [X [Ds [Tyt [Exp [DsHas CloT]]]]].
      (* U occurs in a subtype judgment, so it's closed: *)
      assert (CloU: forall z, open_typ z U = U) by admit.
      lets St1: (exp_to_subtyp Exp).
      assert (St2: subtyp G (typ_bind Ds) (typ_bind (decs_cons l (dec_fld U) decs_nil))). {
        apply_fresh subtyp_bind as z.
        apply subdecs_push with (dec_fld T); fold open_rec_typ; simpl.
        * rewrite <- (CloT z). apply (decs_has_open z DsHas).
        * unfold open_dec, open_rec_dec. fold open_rec_typ. apply subdec_fld.
          rewrite -> CloU. refine (weaken_subtyp_end _ H). admit.
        * apply subdecs_empty.
      }
      apply has_trm with (typ_bind (decs_cons l (dec_fld U) decs_nil))
                                   (decs_cons l (dec_fld U) decs_nil).
      * refine (ty_sbsm _ St2). apply (ty_sbsm Tyt St1).
      * apply exp_bind.
      * unfold decs_has, get_dec. simpl. case_if. reflexivity.
      * intro z. specialize (CloU z). unfold open_dec, open_rec_dec. 
        fold open_rec_typ. f_equal. apply CloU.
    (* case has_var *)
    - admit. (* probably similar *)
Qed.
*)

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

(*
Lemma invert_ty_call: forall G t m V u,
  ty_trm G (trm_call t m u) V ->
  exists U, has ip G t (label_mtd m) (dec_mtd U V) /\ ty_trm G u U.
Proof.
  introv Ty. gen_eq e: (trm_call t m u). gen t m u.
  induction Ty; intros t0 m0 u0 Eq; try solve [ discriminate ]; symmetry in Eq.
  + (* case ty_call *)
    inversions Eq. exists U. auto.
  + (* case ty_sbsm *)
    subst t. specialize (IHTy _ _ _ eq_refl). rename t0 into t, m0 into m, u0 into u.
    destruct IHTy as [V [Has Tyu]].
    exists V. refine (conj _ Tyu).
    apply invert_has in Has.
    destruct Has as [IHTy | IHTy].

    (* need to turn (dec_mtd U0 T) into (dec_mtd U0 U) using T <: U, but there's
       no subsumption in has, so we would need to do the subsumption when
       typing t0 --> tricky *)
Abort.
*)

Lemma invert_ty_call: forall G t m V u,
  ty_trm G (trm_call t m u) V ->
  exists U, has ip G t (label_mtd m) (dec_mtd U V) /\ ty_trm G u U.
Proof.
  intros. inversions H.
  + eauto.
  + admit. (* subsumption case *)
Abort.

Lemma invert_ty_call: forall G t m V2 u,
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

Lemma invert_ty_new: forall G ds Ds T2,
  ty_trm G (trm_new Ds ds) T2 ->
  subtyp ip oktrans G (typ_bind Ds) T2 /\
  exists L, (forall x, x \notin L ->
               ty_defs (G & x ~ typ_bind Ds) (open_defs x ds) (open_decs x Ds)) /\
            (forall x, x \notin L ->
               forall M S U, decs_has (open_decs x Ds) M (dec_typ S U) ->
                             subtyp ip oktrans (G & x ~ typ_bind Ds) S U).
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
            subdecs ip (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Proof.
  introv St. inversions St. exists L.
  intros z zL. specialize (H3 z zL).
  destruct m1.
  - assumption.
  - admit. (* TODO ep=>ip *)
Qed.

Lemma invert_wf_sto_with_weakening: forall s G,
  wf_sto s G ->
  forall x ds Ds T,
    binds x (object Ds ds) s -> 
    binds x T G 
    -> T = (typ_bind Ds) 
    /\ ty_defs G (open_defs x ds) (open_decs x Ds)
    /\ (forall L S U, decs_has (open_decs x Ds) L (dec_typ S U) -> subtyp ip oktrans G S U).
Proof.
  introv Wf Bs BG.
  lets P: (invert_wf_sto Wf).
  specialize (P x ds Ds T Bs BG).
  destruct P as [EqT [G1 [G2 [EqG [Ty F]]]]]. subst.
  apply (conj eq_refl).
  lets Ok: (wf_sto_to_ok_G Wf).
  split.
  + apply (weaken_ty_defs_end Ok Ty).
  + intros L S U Has. specialize (F L S U Has). apply (weaken_subtyp_end Ok F).
Qed.

Lemma invert_wf_sto_with_sbsm: forall s G,
  wf_sto s G ->
  forall x ds Ds T, 
    binds x (object Ds ds) s ->
    ty_trm G (trm_var (avar_f x)) T (* <- instead of binds *)
    -> subtyp ip oktrans G (typ_bind Ds) T
    /\ ty_defs G (open_defs x ds) (open_decs x Ds)
    /\ (forall L S U, decs_has (open_decs x Ds) L (dec_typ S U) -> subtyp ip oktrans G S U).
Proof.
  introv Wf Bis Tyx.
  apply invert_ty_var in Tyx. destruct Tyx as [T'' [St BiG]].
  destruct (invert_wf_sto_with_weakening Wf Bis BiG) as [EqT [Tyds F]].
  subst T''.
  lets Ok: (wf_sto_to_ok_G Wf).
  apply (conj St).
  auto.
Qed.


(* ###################################################################### *)
(** ** Soundness helper lemmas *)

(* subdecs_refl does not hold, because subdecs requires that for each dec in rhs
   (including hidden ones), there is an unhidden one in lhs *)
(* or that there are no hidden decs in rhs *)
Lemma subdecs_refl: forall m G Ds,
  subdecs m G Ds Ds.
Proof.
Admitted. (* TODO does not hold!! *)

Lemma decs_has_preserves_sub: forall m G Ds1 Ds2 l D2,
  decs_has Ds2 l D2 ->
  subdecs m G Ds1 Ds2 ->
  exists D1, decs_has Ds1 l D1 /\ subdec m G D1 D2.
Proof.
  introv Has Sds. induction Ds2.
  + inversion Has.
  + unfold decs_has, get_dec in Has. inversions Sds. case_if.
    - inversions Has. exists D1. auto.
    - fold get_dec in Has. apply* IHDs2.
Qed.

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

(* This is the big fat TODO of the proof ;-) 
   So far we know how to do it in precise mode, but we don't know how to do it
   in imprecise mode. *)
Axiom oktrans_to_notrans: forall G T1 T2,
  subtyp ip oktrans G T1 T2 -> subtyp ip notrans G T1 T2.

Lemma has_sound: forall s G x Ds1 ds l D2,
  wf_sto s G ->
  binds x (object Ds1 ds) s ->
  has ip G (trm_var (avar_f x)) l D2 ->
  exists Ds1 D1,
    ty_defs G (open_defs x ds) (open_decs x Ds1) /\
    decs_has (open_decs x Ds1) l D1 /\
    subdec ip G D1 D2.
Proof.
  introv Wf Bis Has.
  apply invert_var_has_dec in Has.
  destruct Has as [X2 [Ds2 [T [Tyx [Exp2 [Ds2Has Eq]]]]]]. subst.
  destruct (invert_wf_sto_with_sbsm Wf Bis Tyx) as [St [Tyds _]].
  lets St': (exp_to_subtyp Exp2).
  lets Sds: (invert_subtyp_bind (oktrans_to_notrans (subtyp_trans St St'))).
  destruct Sds as [L Sds].
  pick_fresh z. assert (zL: z \notin L) by auto. specialize (Sds z zL).
  lets BiG: (sto_binds_to_ctx_binds Wf Bis).
  lets Tyx1: (ty_var BiG).
  lets Ok: (wf_sto_to_ok_G Wf).
  assert (Ok': ok (G & z ~ typ_bind Ds1)) by auto.
  lets Sds': (@subdecs_subst_principle _ z x (typ_bind Ds1)
              (open_decs z Ds1) (open_decs z Ds2) Ok' Sds Tyx1).
  assert (zDs1: z \notin fv_decs Ds1) by auto.
  assert (zDs2: z \notin fv_decs Ds2) by auto.
  rewrite <- (@subst_intro_decs z x Ds1 zDs1) in Sds'.
  rewrite <- (@subst_intro_decs z x Ds2 zDs2) in Sds'.
  apply (decs_has_open x) in Ds2Has.
  destruct (decs_has_preserves_sub Ds2Has Sds') as [D1 [Ds1Has Sd]].
  exists Ds1 D1.
  apply (conj Tyds (conj Ds1Has Sd)).
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
    specialize (P _ _ _ Ty' (G & y ~ S) empty x).
    rewrite concat_empty_r in P.
    specialize (P eq_refl Tyy Okyx).
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
    right. apply invert_ty_var in Ty. destruct Ty as [T' [St BiG]].
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
      (* arg is an expression *)
      * destruct IHarg as [s' [e' IHarg]]. do 2 eexists. apply (red_call2 x m IHarg).
      (* arg is a var *)
      * destruct IHarg as [y [o [Eq Bisy]]]. subst.
        lets P: (has_sound Wf Bis Has).
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
  (exists H, wf_sto s' (G & H) /\ ty_trm (G & H) e' T).
Proof.
  intros s e s' e' Red. induction Red.
  (* red_call *)
  + intros G U3 Wf TyCall. rename H into Bis, H0 into dsHas, T into X1.
    exists (@empty typ). rewrite concat_empty_r. apply (conj Wf).
    apply invert_ty_call in TyCall.
    destruct TyCall as [T2 [U2 [Has [StU23 Tyy]]]].
    lets P: (has_sound Wf Bis Has).
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
    destruct P as [Ds1 [D1 [Tyds [Ds1Has Sd]]]].
    apply invert_subdec_fld_sync_left in Sd.
    destruct Sd as [T1 [Eq StT12]]. subst D1.
    refine (ty_sbsm _ StT23).
    refine (ty_sbsm _ StT12).
    apply (invert_ty_fld_inside_ty_defs Tyds dsHas Ds1Has).
  (* red_new *)
  + rename T into Ds1. intros G T2 Wf Ty.
    apply invert_ty_new in Ty.
    destruct Ty as [StT12 [L [Tyds F]]].
    exists (x ~ (typ_bind Ds1)).
    pick_fresh x'. assert (Frx': x' \notin L) by auto.
    specialize (Tyds x' Frx').
    specialize (F x' Frx').
    assert (xG: x # G) by apply* sto_unbound_to_ctx_unbound.
    split.
    - apply (wf_sto_push _ Wf H xG).
      * apply* (@ty_open_defs_change_var x').
      * intros M S U dsHas. specialize (F M S U). admit. (* meh TODO *)
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

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(* ... transitivity in notrans mode, but no p.L in middle ... *)

Inductive notsel: typ -> Prop :=
  | notsel_top  : notsel typ_top
  | notsel_bot  : notsel typ_bot
  | notsel_bind : forall Ds, notsel (typ_bind Ds).

Hint Constructors notsel.

Lemma subdec_trans: forall m G D1 D2 D3,
  subdec m G D1 D2 -> subdec m G D2 D3 -> subdec m G D1 D3.
Proof.
  introv H12 H23. inversions H12; inversions H23; constructor;
  solve [ assumption | (eapply subtyp_trans; eassumption)].
Qed.

Lemma subdecs_trans: forall m G Ds1 Ds2 Ds3,
  subdecs m G Ds1 Ds2 ->
  subdecs m G Ds2 Ds3 ->
  subdecs m G Ds1 Ds3.
Proof.
  introv H12 H23.
  induction Ds3.
  + apply subdecs_empty.
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

Lemma subtyp_trans_notrans: forall G T1 T2 T3,
  ok G -> notsel T2 -> subtyp ip notrans G T1 T2 -> subtyp ip notrans G T2 T3 -> 
  subtyp ip notrans G T1 T3.
Proof.
  introv Hok Hnotsel H12 H23.

  inversion Hnotsel; subst.
  (* case top *)
  + inversion H23; subst.
    - apply (subtyp_top ip G T1).
    - apply (subtyp_sel_r H H0 (subtyp_trans (subtyp_tmode H12) H1)).
  (* case bot *)
  + inversion H12; subst.
    - apply (subtyp_bot ip G T3).
    - apply (subtyp_sel_l H (subtyp_trans H0 (subtyp_tmode H23))).
  (* case bind *)
  + inversion H12; inversion H23; subst; (
      assumption ||
      apply subtyp_refl ||
      apply subtyp_top ||
      apply subtyp_bot ||
      idtac
    ).
    (* bind <: bind <: bind *)
    - rename Ds into Ds2.
      apply_fresh subtyp_bind as z.
      assert (zL: z \notin L) by auto.
      assert (zL0: z \notin L0) by auto.
      rename H1 into Sds12, H6 into Sds23.
      specialize (Sds12 z zL).
      specialize (Sds23 z zL0).
      assert (Hok' : ok (G & z ~ typ_bind Ds1)) by auto.
      assert (Hok'': ok (G & z ~ typ_bind Ds2)) by auto.
      lets Sds23' : (narrow_subdecs Hok'' (subtyp_tmode H12) Sds23).
      apply (subdecs_trans Sds12 Sds23').
    - (* bind <: bind <: sel  *)
      assert (H1S: subtyp ip oktrans G (typ_bind Ds1) S) by
        apply (subtyp_trans (subtyp_tmode H12) H6).
      apply (subtyp_sel_r H4 H5 H1S).
    - (* sel  <: bind <: bind *)
      assert (HU2: subtyp ip oktrans G U (typ_bind Ds2))
        by apply (subtyp_trans H0 (subtyp_tmode H23)).
      apply (subtyp_sel_l H HU2). 
    - (* sel  <: bind <: sel  *)
      apply (subtyp_sel_r H2 H6).
      apply (subtyp_trans (subtyp_tmode H12) H7).
Qed.

Print Assumptions subtyp_trans_notrans.

(**
(follow_ub G p1.X1 T) means that there exists a chain

    (p1.X1: _ .. p2.X2), (p2.X2: _ .. p3.X3), ... (pN.XN: _ .. T)

which takes us from p1.X1 to T
*)
Inductive follow_ub : ctx -> typ -> typ -> Prop :=
  | follow_ub_nil : forall G T,
      follow_ub G T T
  | follow_ub_cons : forall G v X Lo Hi T,
      has pr G (trm_var (avar_f v)) X (dec_typ Lo Hi) ->
      follow_ub G Hi T ->
      follow_ub G (typ_sel (pth_var (avar_f v)) X) T.

(**
(follow_lb G T pN.XN) means that there exists a chain

    (p1.X1: T .. _), (p2.X2: p1.X1 .. _), (p3.X3: p2.X2 .. _),  (pN.XN: pN-1.XN-1 .. _)

which takes us from T to pN.XN
*)
Inductive follow_lb: ctx -> typ -> typ -> Prop :=
  | follow_lb_nil : forall G T,
      follow_lb G T T
  | follow_lb_cons : forall G v X Lo Hi U,
      has pr G (trm_var (avar_f v)) X (dec_typ Lo Hi) ->
      subtyp ip oktrans G Lo Hi -> (* <-- realizable bounds *)
      follow_lb G (typ_sel (pth_var (avar_f v)) X) U ->
      follow_lb G Lo U.

Hint Constructors follow_ub.
Hint Constructors follow_lb.

Lemma invert_follow_lb: forall G T1 T2,
  follow_lb G T1 T2 -> 
  T1 = T2 \/ 
    exists v1 X1 v2 X2 Hi, (typ_sel (pth_var (avar_f v2)) X2) = T2 /\
      has pr G (trm_var (avar_f v1)) X1 (dec_typ T1 Hi) /\
      subtyp ip oktrans G T1 Hi /\
      follow_lb G (typ_sel (pth_var (avar_f v1)) X1) (typ_sel (pth_var (avar_f v2)) X2).
Proof.
  intros.
  induction H.
  auto.
  destruct IHfollow_lb as [IH | IH].
  subst.
  right. exists v X v X Hi. auto.
  right.
  destruct IH as [p1 [X1 [p2 [X2 [Hi' [Heq [IH1 [IH2 IH3]]]]]]]].
  subst.  
  exists v X p2 X2 Hi.
  auto.
Qed.

(* Note: No need for a invert_follow_ub lemma because inversion is smart enough. *)

Definition st_middle (G: ctx) (B C: typ): Prop :=
  B = C \/
  subtyp ip notrans G typ_top C \/
  (notsel B /\ subtyp ip notrans G B C). (* TODO can we replace this subtyp by a subdecs? *)

(* linearize a derivation that uses transitivity *)

Definition chain (G: ctx) (A D: typ): Prop :=
   (exists B C, follow_ub G A B /\ st_middle G B C /\ follow_lb G C D).

Lemma empty_chain: forall G T, chain G T T.
Proof.
  intros.
  unfold chain. unfold st_middle.
  exists T T.
  auto.
Qed.

Lemma exp_and_has_pr2ip:
   (forall m G T Ds , exp m G T Ds  -> exp ip G T Ds )
/\ (forall m G t l D, has m G t l D -> has ip G t l D).
Proof.
  apply exp_has_mutind.
  + intros. apply exp_top.
  + intros. apply exp_bind.
  + introv mHas ipHas mExp ipExp. destruct m; apply* exp_sel.
  + introv Ty Exp _ DsHas Clo. apply* has_trm.
  + introv Ty Exp _ DsHas. apply* has_var.
  + introv Bi prExp ipExp DsHas. apply has_var with T Ds.
    - apply (ty_var Bi).
    - assumption.
    - assumption.
Qed.

Definition exp_pr2ip := proj1 exp_and_has_pr2ip.
Definition has_pr2ip := proj2 exp_and_has_pr2ip.

Lemma chain3subtyp: forall G C1 C2 D, 
  subtyp ip notrans G C1 C2 ->
  follow_lb G C2 D -> 
  subtyp ip notrans G C1 D.
Proof.
  introv Hst Hflb.
  induction Hflb.
  assumption.
  apply IHHflb.
  apply (subtyp_sel_r (has_pr2ip H) H0 (subtyp_tmode Hst)).
Qed.

Lemma chain2subtyp: forall G B1 B2 C D,
  ok G ->
  subtyp ip notrans G B1 B2 ->
  st_middle G B2 C ->
  follow_lb G C D ->
  subtyp ip notrans G B1 D.
Proof.
  introv Hok Hst Hm Hflb.
  unfold st_middle in Hm.
  destruct Hm as [Hm | [Hm | [Hm1 Hm2]]]; subst.
  apply (chain3subtyp Hst Hflb).
  apply (chain3subtyp (subtyp_trans_notrans Hok notsel_top (subtyp_top ip G B1) Hm) Hflb).
  apply (chain3subtyp (subtyp_trans_notrans Hok Hm1 Hst Hm2) Hflb).
Qed.

Lemma chain1subtyp: forall G A D,
  ok G ->
  chain G A D ->
  subtyp ip notrans G A D.
Proof.
  introv Hok Hch. destruct Hch as [B [C [Hfub [Hm Hflb]]]].
  induction Hfub.
  apply (chain2subtyp Hok (subtyp_refl_all ip notrans G T) Hm Hflb).
  apply (subtyp_sel_l (has_pr2ip H)).
  apply subtyp_tmode.
  apply (IHHfub Hok Hm Hflb).
Qed.

Print Assumptions chain1subtyp.

(*
Lemma exp_preserves_sub_ADMITTED: forall m G T1 T2 Ds1 Ds2,
  ok G ->
  subtyp ip m G T1 T2 ->
  exp pr G T1 Ds1 -> (* <-- note: precise *)
  exp ip G T2 Ds2 -> (* <-- note: imprecise *)
  exists L, forall z, z \notin L -> 
            subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Admitted.
*)

(* Move imprecision in "has" into subtype transitivity: S2<:S1<:U1<:U2 *)
Lemma ip_has_to_trans: forall s G x L S2 U2,
  wf_sto s G ->
  has ip G (trm_var (avar_f x)) L (dec_typ S2 U2) ->
  (* I can give you all this: *)
  exists X1 X2 DsX1 DsX2,
    binds x X1 G /\
    ty_trm G (trm_var (avar_f x)) X2 /\
    subtyp ip oktrans G X1 X2 /\
    exp pr G X1 DsX1 /\
    exp ip G X2 DsX2 /\
    ((* But you have to give me the conclusion of exp_preserves_sub: *)
     (exists L, forall z, z \notin L -> 
        subdecs ip (G & z ~ typ_bind DsX1) (open_decs z DsX1) (open_decs z DsX2)) ->
     (* So that I can give you the result: *)
     (exists S1 U1,
        has pr G (trm_var (avar_f x)) L (dec_typ S1 U1) /\
        subtyp ip oktrans G S2 S1 /\
        subtyp ip oktrans G S1 U1 /\
        subtyp ip oktrans G U1 U2)).
Proof.
  introv Wf Has2.
  (* Step 1: Destruct hypotheses to instantiate existentials *)
  lets Ok: (wf_sto_to_ok_G Wf).
  apply invert_var_has_dec_typ in Has2.
  destruct Has2 as [X2 [DsX2 [S2' [U2' [Ty [ExpX2 [DsX2Has [EqS EqU]]]]]]]].
  destruct (invert_ty_var Ty) as [X1 [StX BiG]].
  destruct (ctx_binds_to_sto_binds Wf BiG) as [[DsX1 ds] Bis].
  lets I: (invert_wf_sto_with_weakening Wf Bis BiG). destruct I as [Eq [_ F]]. subst X1.
  exists (typ_bind DsX1) X2 DsX1 DsX2.
  lets ExpX1: (exp_bind pr G DsX1).
  refine (conj BiG (conj Ty (conj StX (conj ExpX1 (conj ExpX2 _))))).
  (* Step 2: Get S2 <: S1 and U1 <: U2 *)
  intro Sds.
  (* doesn't hold, need some substitution ...*)
  assert (Impl: (exists L0, 
      forall z : var, z \notin L0 ->
      subdecs ip (G & z ~ typ_bind DsX1) (open_decs z DsX1) (open_decs z DsX2))
   -> subdecs ip G                       (open_decs x DsX1) (open_decs x DsX2)) by admit.
  apply Impl in Sds. clear Impl.
  apply (decs_has_open x) in DsX2Has.
  unfold open_dec, open_rec_dec in DsX2Has. fold open_rec_typ in DsX2Has.
  unfold open_typ in EqS, EqU.
  rewrite EqS in DsX2Has.
  rewrite EqU in DsX2Has.
  lets Sd: (decs_has_preserves_sub DsX2Has Sds).
  destruct Sd as [D1 [DsX1Has Sd]].
  apply invert_subdec_typ_sync_left in Sd. destruct Sd as [S1 [U1 [Eq [StS StU]]]].
  (* Step 3: Get S1 <: U1 *)
  subst D1. specialize (F L S1 U1 DsX1Has).
  (* Step 4: Combine *)
  exists S1 U1.
  refine (conj _ (conj StS (conj F StU))).
  assert (Eq: exists D1, open_dec x D1 = (dec_typ S1 U1)) by admit.
  destruct Eq as [D1 Eq]. rewrite <- Eq.
  apply has_pr with (typ_bind DsX1) DsX1.
  + apply BiG.
  + apply ExpX1.
  + rewrite <- Eq in DsX1Has.
    (* substitution hassle (does not hold): *)
    assert (Impl: decs_has (open_decs x DsX1) L (open_dec x D1)
                  -> decs_has DsX1 L D1) by admit.
    apply (Impl DsX1Has).
Qed.

Inductive ilevel: ctx -> typ -> nat -> Prop :=
| ilevel_top: forall G,
    ilevel G typ_top 0
| ilevel_bot: forall G,
    ilevel G typ_bot 0
| ilevel_bind: forall G Ds,
    ilevel G (typ_bind Ds) 0
| ilevel_sel: forall G x L S U n1 n2 n3,
    has pr G (trm_var x) L (dec_typ S U) ->
    ilevel G S n1 ->
    ilevel G U n2 ->
    n1 < n3 ->
    n2 < n3 ->
    ilevel G (typ_sel (pth_var x) L) n3.

(* prepend an oktrans to a chain *)
Lemma prepend_chain: forall s G A1 A2 D,
  wf_sto s G ->
  subtyp ip oktrans G A1 A2 ->
  chain G A2 D ->
  chain G A1 D
with exp_preserves_sub: forall s G T1 T2 Ds1 Ds2,
  wf_sto s G ->
  subtyp ip notrans G T1 T2 -> (* <-- TODO: is notrans sufficient ?? *)
  exp pr G T1 Ds1 -> (* <-- note: precise *)
  exp ip G T2 Ds2 -> (* <-- note: imprecise *)
  exists L, forall z, z \notin L -> 
            subdecs ip (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Proof.
(**** prepend_chain ****) {
  introv Wf St. unfold chain in *. unfold st_middle in *.
  lets Ok: (wf_sto_to_ok_G Wf).
  set (oktrans2notrans A D H := 
    (chain1subtyp Ok (prepend_chain s G A D D Wf H (empty_chain G D)))).
  intro Hch. inversions St; [ inversions H | idtac ].
  + (* case refl *)
    assumption.
  + (* case top *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]]; subst.
    - exists A1 typ_top. auto 10.
    - exists A1 C. auto 10.
    - exists A1 C. auto 10.
  + (* case bot *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    exists typ_bot C. auto 10.
  + (* case bind *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    exists (typ_bind Ds1) C.
    assert (subtyp ip notrans G (typ_bind Ds1) (typ_bind Ds2))
      by (apply subtyp_bind with L; assumption).
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
    - subst. auto 10.
    - auto 10.
    - lets Hst: (subtyp_trans_notrans Ok (notsel_bind _) H Hch2b). auto 10.
  + (* case sel_l *)
    rename H0 into Has2, H1 into St, S into S2, U into U2.
    lets I: (ip_has_to_trans Wf Has2).
    destruct I as [X1 [X2 [DsX1 [DsX2 [Bi [Ty [StX [ExpX1 [ExpX2 I]]]]]]]]].
    (* ExpX1 is contained in Exp1 --> decreasing *)
    lets IHX: (exp_preserves_sub s G X1 X2 DsX1 DsX2
                                 Wf (oktrans2notrans X1 X2 StX) ExpX1 ExpX2).
    specialize (I IHX). clear IHX.
    destruct I as [S1 [U1 [Has1 [StS [StSU StU]]]]].
    (* decreasing because [U2 <: A2] is contained in [p.L <: A2] *)
    lets IHSt: (prepend_chain s G U2 A2 D Wf St).
    specialize (IHSt Hch).
    lets IHStU: (prepend_chain s G U1 U2 D Wf StU).
    specialize (IHStU IHSt).
    destruct IHStU as [B [C [IH1 IH2]]].
    exists B C.
    apply (conj (follow_ub_cons Has1 IH1) IH2).
  + (* case sel_r *)
    rename H0 into Has2, S into S2, U into U2, H1 into StSU, H2 into StA1S2.
    set (Hch' := Hch).
    destruct Hch' as [B [C [Hch1 [Hch2 Hch3]]]].
    (*lets IHStSU: (prepend_chain s G S *)
    admit. (*


  + (* case sel_r *)
    rename H0 into Has2, H1 into StSU, H2 into StA1S.
    set (Hch' := Hch).
    destruct Hch' as [B [C [Hch1 [Hch2 Hch3]]]].
    lets IHStSU: (prepend_chain s G S 
    inversions Hch1.
    - (* case follow_ub_nil *)
      destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
      * subst.
        apply (IHSt2 Hok).
        exists S S. 
        set (Hflb := (follow_lb_cons H St1 Hch3)).
        auto.
      * exists T C.
        auto.
      * inversion Hch2a. (* contradiction *)
    - (* case follow_ub_cons *)
      apply (IHSt2 Hok). apply (IHSt1 Hok).
      assert (HdecEq: dec_typ Lo Hi = dec_typ S U) by admit (* has_var_unique *).
      injection HdecEq; intros; subst.
      exists B C. auto.
    *)
  + (* case trans *)
    lets IHSt1: (prepend_chain s G A1 T2 D Wf H).
    lets IHSt2: (prepend_chain s G T2 A2 D Wf H0).
    apply IHSt1. apply (IHSt2 Hch).
}
(**** exp_preserves_sub ****) {
  introv Wf St Exp1 Exp2.
  lets Ok: (wf_sto_to_ok_G Wf).
  set (oktrans2notrans A D H := 
    (chain1subtyp Ok (prepend_chain s G A D D Wf H (empty_chain G D)))).
  inversions St.
  + (* case subtyp_refl *)
    inversions Exp1. rename Lo0 into Lo1, Hi0 into Hi1, H4 into Has1, H6 into ExpHi1.
    inversions Exp2. rename Lo0 into Lo2, Hi0 into Hi2, H4 into Has2, H6 into ExpHi2.
    lets I: (ip_has_to_trans Wf Has2).
    destruct I as [X1 [X2 [DsX1 [DsX2 [Bi [Ty [StX [ExpX1 [ExpX2 I]]]]]]]]].
    (* ExpX1 is contained in Exp1 --> decreasing *)
    lets IHX: (exp_preserves_sub s G X1 X2 DsX1 DsX2
                                 Wf (oktrans2notrans X1 X2 StX) ExpX1 ExpX2).
    specialize (I IHX). clear IHX.
    destruct I as [Lo1' [Hi1' [Has1' [_ [_ StHi]]]]].
    (* since precise has is unique: *)
    assert (Lo1' = Lo1) by admit. subst Lo1'.
    assert (Hi1' = Hi1) by admit. subst Hi1'.
    (* Hi1 is the upper bound of x.L, so it's "simpler" than x.L 
       -> decreasing measure *)
    apply (exp_preserves_sub _ _ _ _ _ _ Wf (oktrans2notrans Hi1 Hi2 StHi) ExpHi1 ExpHi2).
  + (* case subtyp_top *)
    inversions Exp2.
    exists vars_empty. intros z zL. unfold open_decs, open_rec_decs. apply subdecs_empty.
  + (* case subtyp_bot *)
    inversions Exp1.
  + (* case subtyp_bind *)
    inversions Exp1. inversions Exp2.
    exists L. intros z zL. apply (H z zL).
  + (* case subtyp_sel_l *)
    rename H into Has2, H0 into StHiT2, S into Lo2, U into Hi2.
    lets I: (ip_has_to_trans Wf Has2).
    destruct I as [X1 [X2 [DsX1 [DsX2 [Bi [Ty [StX [ExpX1 [ExpX2 I]]]]]]]]].
    (* ExpX1 is contained in Exp1 --> decreasing *)
    lets IHX: (exp_preserves_sub s G X1 X2 DsX1 DsX2
                                 Wf (oktrans2notrans X1 X2 StX) ExpX1 ExpX2).
    specialize (I IHX). clear IHX.
    destruct I as [Lo1 [Hi1 [Has1 [_ [_ StHi]]]]].
    lets St: (subtyp_trans StHi StHiT2).
    apply invert_exp_sel in Exp1. destruct Exp1 as [Lo1' [Hi1' [Has1' ExpHi1]]].
    (* since precise has is unique: *)
    assert (Lo1' = Lo1) by admit. subst Lo1'.
    assert (Hi1' = Hi1) by admit. subst Hi1'.
    (* Hi1 is the upper bound of x.L, so it's "simpler" than x.L 
       -> decreasing measure *)
    refine (exp_preserves_sub _ _ _ _ _ _ Wf _ ExpHi1 Exp2).
    apply (oktrans2notrans Hi1 T2 St).
  + (* case subtyp_sel_r *)
    rename H into Has2, H0 into StLo2Hi2, H1 into StLo2T1, S into Lo2, U into Hi2.
    lets I: (ip_has_to_trans Wf Has2).
    destruct I as [X1 [X2 [DsX1 [DsX2 [Bi [Ty [StX [ExpX1 [ExpX2 I]]]]]]]]].
    (* ExpX1 is contained in Exp1 --> decreasing *)
    lets IHX: (exp_preserves_sub s G X1 X2 DsX1 DsX2
                                 Wf (oktrans2notrans X1 X2 StX) ExpX1 ExpX2).
    specialize (I IHX). clear IHX.
    destruct I as [Lo1 [Hi1 [Has1 [StLo2L1 [StLo1Hi1 StHi1Hi2]]]]].
    (* TODO difficult *)

     (*   T1 <: p.L (Lo..Hi)

         Ds1 <:         Ds2
     *)
    admit.
  (* if the exp_preserves_sub statement is only for notrans, no need for these 2 cases:
  + (* case subtyp_mode *)
    (* H (notrans) is contained in oktrans judgment *)
    apply (exp_preserves_sub _ _ _ _ _ _ _ Wf H Exp1 Exp2).
  + (* case subtyp_trans *)
    rename Ds2 into Ds3, T3 into Temp, T2 into T3. rename Temp into T2.
    rename H into St12, H0 into St23, Exp2 into Exp3.
    assert (Exp2: exists Ds2, exp pr G T2 Ds2) by admit. (* <----- *)
    destruct Exp2 as [Ds2 Exp2].
    (* now apply exp_preserves_sub on St12 and St23, then subdecs_trans *)
    *)
}
(*Qed.*)Abort.

Lemma oktrans_to_chain: forall G T1 T2,
  subtyp ip oktrans G T1 T2 ->
  chain G T1 T2.
Admitted.

Lemma oktrans2notrans: forall G T1 T3,
  ok G -> subtyp ip oktrans G T1 T3 -> subtyp ip notrans G T1 T3.
Proof.
  introv Hok Hst. apply (chain1subtyp Hok (oktrans_to_chain Hst)).
Qed.

Print Assumptions oktrans2notrans.

(* ###################################################################### *)
(* ###################################################################### *)
(* ###################################################################### *)
(** Exploring helper lemmas for ip->pr and oktrans->notrans *)


Lemma pr2ip:
   (forall m G T Ds,   exp m G T Ds  -> exp ip G T Ds)
/\ (forall m G t L D,  has m G t L D -> has ip G t L D)
/\ (forall m1 m2 G T1 T2, subtyp m1 m2 G T1 T2 -> subtyp ip m2 G T1 T2)
/\ (forall m G D1 D2, subdec m G D1 D2 -> subdec ip G D1 D2)
/\ (forall m G Ds1 Ds2, subdecs m G Ds1 Ds2 -> subdecs ip G Ds1 Ds2).
Admitted.

(*
Note:
 - Proving it for notrans only doesn't work, because the IH needs to accept oktrans,
   because that's what comes out of subtyp_sel_l/r.
*)

Lemma exp_preserves_sub_pr: forall m2 s G T1 T2 Ds1 Ds2,
  wf_sto s G ->
  subtyp pr m2 G T1 T2 ->
  exp pr G T1 Ds1 ->
  exp pr G T2 Ds2 ->
  forall z, ty_trm G (trm_var (avar_f z)) T1 -> 
            subdecs pr G (open_decs z Ds1) (open_decs z Ds2).
Proof.
  (* We don't use the [induction] tactic because we want to intro everything ourselves: *)
  intros m2 s G T1 T2 Ds1 Ds2 Wf St.
  gen_eq m1: pr. gen m1 m2 G T1 T2 St Ds1 Ds2 s Wf.
  apply (subtyp_ind (fun m1 m2 G T1 T2 => forall Ds1 Ds2 s,
    wf_sto s G ->
    m1 = pr ->
    exp m1 G T1 Ds1 ->
    exp m1 G T2 Ds2 ->
    forall z, _ -> subdecs m1 G (open_decs z Ds1) (open_decs z Ds2))).
  + (* case subtyp_refl *)
    intros m G x L Lo Hi Has Ds1 Ds2 s Wf Eq Exp1 Exp2. subst.
    lets Eq: (exp_unique Exp1 Exp2).
    subst. intros z Bi. apply subdecs_refl.
  + (* case subtyp_top *)
    intros m G T Ds1 Ds2 s Wf Eq Exp1 Exp2. subst.
    inversions Exp2.
    intros z Bi. unfold open_decs, open_rec_decs. apply subdecs_empty.
  + (* case subtyp_bot *)
    intros m G T Ds1 Ds2 s Wf Eq Exp1 Exp2. subst.
    inversions Exp1.
  + (* case subtyp_bind *)
    intros L m G Ds1' Ds2' Sds Ds1 Ds2 s Wf Eq Exp1 Exp2.
    inversions Exp1. inversions Exp2.
    intros x Ty. pick_fresh z. assert (zL: z \notin L) by auto. specialize (Sds z zL).
    admit. (* TODO requires env-precise substitution!! *)
  + (* case subtyp_sel_l *)
    (* This case does not need subdecs_trans, because Exp1 is precise, so the expansion
       of x.L is the same as the expansion of its upper bound Hi1, and we can just apply
       the IH for Hi1<:T *)
    intros m G x L Lo2 Hi2 T Has2 St IHSt Ds1 Ds2 s Wf Eq Exp1 Exp2. subst.
    apply invert_exp_sel in Exp1. destruct Exp1 as [Lo1 [Hi1 [Has1 Exp1]]].
    lets Eq: (has_unique Has2 Has1).
    inversions Eq.
    intros z Ty.
    apply* IHSt.
    apply (@ty_sbsm G _ (typ_sel (pth_var (avar_f x)) L) Hi1 Ty).
    apply subtyp_tmode.
    assert (Has1': has ip G (trm_var (avar_f x)) L (dec_typ Lo1 Hi1)) by apply* pr2ip.
    apply (subtyp_sel_l Has1').
    apply subtyp_refl_all.
  + (* case subtyp_sel_r *)
    (* This case needs subdecs_trans: Ds1 <: DsLo <: Ds2 *)
    intros m G x L Lo Hi T Has St1 IHSt1 St2 IHSt2 Ds1 Ds2 s Wf Eq Exp1 Exp2. subst.
    apply invert_exp_sel in Exp2. destruct Exp2 as [Lo' [Hi' [Has' Exp2]]].
    lets Eq: (has_unique Has' Has).
    inversions Eq.
    assert (ExpLo: exists DsLo, exp pr G Lo DsLo) by admit. (* <----- *)
    destruct ExpLo as [DsLo ExpLo].
    intros y Ty.
    specialize (IHSt1 DsLo Ds2 s Wf eq_refl ExpLo Exp2).
    assert (Ty': ty_trm G (trm_var (avar_f y)) Lo). {
      apply (ty_sbsm Ty). apply* pr2ip.
    }
    specialize (IHSt1 y Ty').
    specialize (IHSt2 Ds1 DsLo s Wf eq_refl Exp1 ExpLo y Ty).
    (* since y is in G instead of appended after G, no need for narrowing (which would
       have to be precise!) before applying subdecs_trans *)
    apply (subdecs_trans IHSt2 IHSt1).
  + (* case subtyp_mode *)
    intros. apply* H0.
  + (* case subtyp_trans *)
    intros m G T1 T2 T3 St12 IH12 St23 IH23 Ds1 Ds3 s Wf Eq Exp1 Exp3. subst.
    assert (Exp2: exists Ds2, exp pr G T2 Ds2) by admit. (* <----- *)
    destruct Exp2 as [Ds2 Exp2].
    intros y Ty.
    specialize (IH12 _ _ s Wf eq_refl Exp1 Exp2 y Ty).
    assert (Ty': ty_trm G (trm_var (avar_f y)) T2). {
      apply (ty_sbsm Ty). apply* pr2ip.
    }
    specialize (IH23 _ _ s Wf eq_refl Exp2 Exp3 y Ty').
    apply (subdecs_trans IH12 IH23).
Qed.

Print Assumptions exp_preserves_sub_pr.

(* note: conclusion is precise
Lemma exp_preserves_sub_pr: forall m2 G T1 T2 Ds1 Ds2,
  ok G ->
  subtyp pr m2 G T1 T2 ->
  exp pr G T1 Ds1 ->
  exp pr G T2 Ds2 ->
  exists L, forall z, z \notin L -> 
            subdecs pr (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Admitted.

(* In ip mode, this holds, but does it also hold in pr mode??? *)
Lemma pr_narrow_subdecs: forall G z DsA DsB Ds1 Ds2,
  subdecs pr (G & z ~ typ_bind DsA) (open_decs z DsA) (open_decs z DsB) ->
  subdecs pr (G & z ~ typ_bind DsB) Ds1 Ds2 ->
  subdecs pr (G & z ~ typ_bind DsA) Ds1 Ds2.
Admitted.*)

Lemma ip2pr:
   (forall m G T Ds2, exp m G T Ds2 -> forall s,
      m = ip ->
      wf_sto s G ->
      forall z, ty_trm G (trm_var (avar_f z)) T ->
                exists Ds1, exp pr G T Ds1 /\
                            subdecs pr G (open_decs z Ds1) (open_decs z Ds2))
/\ (forall m G t L D2, has m G t L D2 -> forall s v,
      m = ip ->
      wf_sto s G ->
      t = (trm_var (avar_f v)) ->
      exists D1, has pr G (trm_var (avar_f v)) L D1 /\
                 subdec pr G D1 D2)
/\ (forall m1 m2 G T1 T2, subtyp m1 m2 G T1 T2 -> forall s,
      m1 = ip ->
      wf_sto s G ->
      subtyp pr oktrans G T1 T2)
/\ (forall m G D1 D2, subdec m G D1 D2 -> forall s,
      m = ip ->
      wf_sto s G ->
      subdec pr G D1 D2)
/\ (forall m G Ds1 Ds2, subdecs m G Ds1 Ds2 -> forall s,
      m = ip ->
      wf_sto s G ->
      subdecs pr G Ds1 Ds2)
/\ (forall G t T2, ty_trm G t T2 -> forall s v,
      wf_sto s G ->
      t = (trm_var (avar_f v)) ->
      exists T1, binds v T1 G /\
                 subtyp pr oktrans G T1 T2).
Proof.
  apply mutind6; try (intros; discriminate).
  + (* case exp_top *)
    intros. exists decs_nil.
    apply (conj (exp_top _ _)).
    intros. apply subdecs_empty.
  + (* case exp_bind *)
    intros m G Ds s Wf.
    exists Ds.
    apply (conj (exp_bind _ _ _)).
    intros. apply subdecs_refl.
  + (* case exp_sel *)
    intros m G v L Lo2 Hi2 Ds2 Has IHHas Exp IHExp s Eq Wf z Ty. subst.
    lets Ok: (wf_sto_to_ok_G Wf).
    specialize (IHHas _ _ eq_refl Wf eq_refl). destruct IHHas as [D1 [IHHas IHSd]].
    specialize (IHExp _ eq_refl Wf).
    assert (Ty': ty_trm G (trm_var (avar_f z)) Hi2). {
      apply (ty_sbsm Ty). apply subtyp_tmode.
      apply (subtyp_sel_l Has). apply subtyp_refl_all.
    }
    specialize (IHExp z Ty').
    destruct IHExp as [Ds1 [ExpHi2 Sds12]].
    apply invert_subdec_typ_sync_left in IHSd.
    destruct IHSd as [Lo1 [Hi1 [Eq [StLo StHi]]]]. subst.
    assert (E: exists Ds0, exp pr G Hi1 Ds0) by admit. (* hopefully by wf_sto... *)
    destruct E as [Ds0 ExpHi1].
    lets Sds01: (exp_preserves_sub_pr Wf StHi ExpHi1 ExpHi2).
    assert (Ty'': ty_trm G (trm_var (avar_f z)) Hi1). {
      apply (ty_sbsm Ty). apply subtyp_tmode.
      assert (IHHas': has ip G (trm_var (avar_f v)) L (dec_typ Lo1 Hi1)) by apply* pr2ip.
      apply (subtyp_sel_l IHHas' (subtyp_refl_all _ _ _ _)).
    }
    specialize (Sds01 z Ty'').
    exists Ds0. split.
    - apply (exp_sel IHHas ExpHi1).
    - apply (subdecs_trans Sds01 Sds12).

  + (* case has_trm *)
    intros G t X2 Ds2 l D2 Ty IHTy Exp2 IHExp Ds2Has Clo s v _ Wf Eq. subst.
    lets Ok: (wf_sto_to_ok_G Wf).
    specialize (IHExp s eq_refl Wf v Ty). destruct IHExp as [Dsm [Expm Sds2]].
    specialize (IHTy s v Wf eq_refl). destruct IHTy as [X1 [BiG St]].
    assert (E: exists Ds1, exp pr G X1 Ds1) by admit. (* hopefully by wf_sto... *)
    destruct E as [Ds1 Exp1].
    lets Sds1: (exp_preserves_sub_pr Wf St Exp1 Expm).
    specialize (Sds1 v (ty_var BiG)).
    lets Sds: (subdecs_trans Sds1 Sds2).
    apply (decs_has_open v) in Ds2Has.
    rewrite Clo in Ds2Has.
    lets P: (decs_has_preserves_sub Ds2Has Sds).
    destruct P as [D1o [Ds1Has Sd]].
    assert (E: exists D1, D1o = (open_dec v D1)) by admit.
    destruct E as [D1 Eq]. subst D1o.
    exists (open_dec v D1).
    refine (conj _ Sd).
    apply (has_pr BiG Exp1).
    assert (decs_has (open_decs v Ds1) l (open_dec v D1)
         -> decs_has Ds1 l D1) by admit. (* TODO does not hold! *) auto.
  + (* case has_var *)
    admit.

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
    destruct Sd as [Lo1 [Hi1 [Eq [StLo StHi]]]]. subst D1.
    apply subtyp_tmode.
    lets StHi1T: (subtyp_trans StHi IHSt).
    apply (subtyp_sel_l Has1 StHi1T).
  + (* case subtyp_sel_r *)
    admit.
  + (* case subtyp_tmode *)
    admit.
  + (* case subtyp_trans *)
    admit.

  + (* case subdec_typ *)
    admit.
  + (* case subdec_fld *)
    admit.
  + (* case subdec_mtd *)
    admit.

  + (* case subdecs_empty *)
    admit.
  + (* case subdecs_push *)
    admit.

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

Lemma invert_subtyp_bind_oktrans: forall s G Ds1 Ds2,
  wf_sto s G ->
  subtyp ip oktrans G (typ_bind Ds1) (typ_bind Ds2) ->
  exists L, forall z, z \notin L ->
            subdecs ip (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Proof.
  introv Wf St. destruct ip2pr as [_ [_ [P _]]].
  specialize (P _ _ _ _ _ St _ eq_refl Wf).
  lets Exp1: (exp_bind pr G Ds1).
  lets Exp2: (exp_bind pr G Ds2).
  lets Q: (exp_preserves_sub_pr Wf P Exp1 Exp2).
Qed.

(* so probably we won't even need the transitivity push-back *)

Stop here.


(* note: if second Exp is ip, the subtyp_refl case is as hard as the whole lemma,
   but we don't have any IH *)

Lemma exp_preserves_sub_ip: forall m G T1 T2 Ds1 Ds2,
  ok G ->
  subtyp ip m G T1 T2 ->
  exp pr G T1 Ds1 ->
  exp pr G T2 Ds2 ->
  exists L, forall z, z \notin L -> 
            subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Proof.
  (* We don't use the [induction] tactic because we want to intro everything ourselves: *)
  intros m2 G T1 T2 Ds1 Ds2 Ok St. gen_eq m1: ip. gen m1 m2 G T1 T2 St Ds1 Ds2 Ok.
  apply (subtyp_ind (fun m1 m2 G T1 T2 => forall Ds1 Ds2,
    ok G ->
    m1 = ip ->
    exp pr G T1 Ds1 ->
    exp pr G T2 Ds2 ->
    exists L, forall z : var, z \notin L ->
              subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2))).
  + (* case subtyp_refl *)
    intros m G x L Lo Hi Has Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    assert (Eq: Ds1 = Ds2) by admit. (* precise is unique *)
    exists vars_empty. intros z zL. subst. apply subdecs_refl.
  + (* case subtyp_top *)
    intros m G T Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    inversions Exp2.
    exists vars_empty. intros z zL. unfold open_decs, open_rec_decs. apply subdecs_empty.
  + (* case subtyp_bot *)
    intros m G T Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    inversions Exp1.
  + (* case subtyp_bind *)
    intros L m G Ds1' Ds2' Sds Ds1 Ds2 Ok Eq Exp1 Exp2. inversions Exp1. inversions Exp2.
    exists L. intros z zL. apply (Sds z zL).
  + (* case subtyp_sel_l *)
    intros m G x L Lo2 Hi2 T Has2 St IHSt Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    apply invert_exp_sel in Exp1. destruct Exp1 as [Lo1 [Hi1 [Has1 Exp1]]].
    assert (Exp21: exists Ds21, exp pr G Hi2 Ds21) by admit. (* <-- *)
    destruct Exp21 as [Ds21 Exp21].
    lets IH': (IHSt Ds21 Ds2 Ok eq_refl Exp21 Exp2).
    specialize (IHSt Ds1 Ds21 Ok eq_refl).
    (* We need an IH to go from Ds1 to Ds21, i.e. an IH for Hi1 <: Hi2, i.e. one
       which takes an [Exp1: exp pr G Hi1 Ds1] and [Exp21: exp pr G Hi2 Ds21]. 
       But again, Has1 (pr) and Has2 (ip) might be related through a subtyp_bind
       in ty_sbsm, and we would have to invert the subtyp_bind to relate Hi1 and Hi2.
    *)
Abort.

(* exp_preserves_sub is approx the same as invert_subtyp_bind *)
Lemma exp_preserves_sub: forall G T1 T2 Ds1 Ds2,
  subtyp ip oktrans G T1 T2 ->
  exp pr G T1 Ds1 ->
  exp ip G T2 Ds2 ->
  exists L, forall z, z \notin L -> 
            subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Admitted.

(*
Definition exists_precise_exp G T Ds2 :=
  exists L Ds1, exp pr G T Ds1 /\
                forall z, z \notin L ->
                subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).

Definition exists_precise_has G v L D2 :=
  exists D1, has pr G (trm_var (avar_f v)) L D1 /\ subdec G D1 D2.

Definition exists_notrans_subtyp m1 G T1 T2 :=
  subtyp m1 notrans G T1 T2.

Definition exists_precise_ty_path := ...
*)

Lemma ip2pr_old:
   (forall m G T Ds2, exp m G T Ds2 -> forall s,
      m = ip ->
      wf_sto s G ->
      exists L Ds1, exp pr G T Ds1 /\
                    forall z, z \notin L ->
                    subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2))
/\ (forall m G t L D2, has m G t L D2 -> forall s v,
      m = ip ->
      wf_sto s G ->
      t = (trm_var (avar_f v)) ->
      exists D1, has pr G (trm_var (avar_f v)) L D1 /\
                 subdec G D1 D2)
/\ (forall m1 m2 G T1 T2, subtyp m1 m2 G T1 T2 -> forall s,
      m1 = ip ->
      wf_sto s G ->
      subtyp pr oktrans G T1 T2)
/\ (forall G t T2, ty_trm G t T2 -> forall s v,
      wf_sto s G ->
      t = (trm_var (avar_f v)) ->
      exists T1, binds v T1 G /\
                 subtyp pr oktrans G T1 T2).
Proof.
  apply exp_has_subtyp_ty_mutind; try (intros; discriminate).
  + (* case exp_top *)
    intros. exists vars_empty decs_nil.
    apply (conj (exp_top _ _)).
    intros. apply subdecs_empty.
  + (* case exp_bind *)
    intros m G Ds s Wf.
    exists vars_empty Ds.
    apply (conj (exp_bind _ _ _)).
    intros. apply subdecs_refl.
  + (* case exp_sel *)
    intros m G v L Lo2 Hi2 Ds2 Has IHHas Exp IHExp s Eq Wf. subst.
    specialize (IHHas _ _ eq_refl Wf eq_refl). destruct IHHas as [D1 [IHHas IHSd]].
    specialize (IHExp _ eq_refl Wf). destruct IHExp as [L0 [Ds1 [ExpHi2 Sds12]]].
    apply invert_subdec_typ_sync_left in IHSd.
    destruct IHSd as [Lo1 [Hi1 [Eq [StLo StHi]]]]. subst.
    assert (E: exists Ds0, exp pr G Hi1 Ds0) by admit. (* hopefully by wf_sto... *)
    destruct E as [Ds0 ExpHi1].
    assert (Sds01: forall z : var, z \notin L0 ->
      subdecs (G & z ~ typ_bind Ds0) (open_decs z Ds0) (open_decs z Ds1)) by admit.
    exists L0 Ds0. split.
    - apply (exp_sel IHHas ExpHi1).
    - intros z zL0.
      lets Sds01': Sds01.
      specialize (Sds01 z zL0).
      specialize (Sds12 z zL0).
      lets Ok: (wf_sto_to_ok_G Wf).
      assert (Ok' : ok (G & z ~ typ_bind Ds1)) by admit. (* TODO L0 \u dom G stuff *)
      lets Sds12' : (narrow_subdecs Ok' (subtyp_tmode (subtyp_bind ip _ Sds01')) Sds12).
      apply (subdecs_trans Sds01 Sds12').
  + (* case has_trm *)
    intros G t V2 Ds22 l D22 Ty IHTy Exp2 IHExp Ds22Has Clo s v _ Wf Eq. subst.
    specialize (IHExp s eq_refl Wf). destruct IHExp as [L [Ds21 [Exp21 Sds]]].
    specialize (IHTy s v Wf eq_refl). destruct IHTy as [V1 [BiG St]].
    pick_fresh z. assert (zL: z \notin L) by auto.
    specialize (Sds z zL).
    apply (decs_has_open z) in Ds22Has.
    lets P: (decs_has_preserves_sub Ds22Has Sds).
    destruct P as [D21 [Ds21Has Sd]].
    destruct (ctx_binds_to_sto_binds Wf BiG) as [[Ds1 ds] Bis].
    lets P: (invert_wf_sto_with_weakening Wf Bis BiG).
    destruct P as [Eq _]. subst.
(*
Some more thoughts about the idea to first prove a "make_subtyp_precise" lemma,
which removes all subsumption steps in a subtyping judgment, and then just feed this
precise subtyping judgment to the transitivity push-back proof:

Let's prove make_subtyp_precise by simple induction on the subtyping judgment. But
then, in the subtyp_sel_l/r cases, we have a "has" judgment which we must make precise,
but we only have IHs for subtype judgments, not for "has" judgments, so that doesn't work.

So we have to do mutual induction on "has" and subtyp, and we also have to include
expansion and type assignment for vars, because they are used by "has".
The statement we want to prove then looks like this (simplifying boring details):

  (forall G T Ds2,
      exp ip G T Ds2 ->
      exists Ds1, exp pr G T Ds1 /\ subdecs G Ds1 Ds2)
/\ (forall G v L D2,
      has ip G v L D2 ->
      exists D1, has pr G v L D1 /\ subdec G D1 D2)
/\ (forall G T1 T2, 
      subtyp ip G T1 T2 ->
      subtyp pr G T1 T2)
/\ (forall G v T2,
      ty_trm G v T2 ->
      exists T1, (v: T1) in G /\ subtyp pr G T1 T2).

where pr means precise, and ip means imprecise.

Now consider the case has_var: We get a ...

So the hope we had this afternoon, that we get a precise "has" for free by induction,
is gone...

*)
(*
Point was: don't prove make_has_precise, but deal with the "has" inside subtyp_sel_l/r
in a more ad-hoc way.
*)

    (* We have

      (typ_bind Ds1) <: V2 <z Ds21 <: Ds22

      and given Ds21Has, we need to get a D1 s.t. Ds1Has, but between Ds21 and Ds1,
      there's a subtype gap which we can only bridge using invert_subtyp_bind, but
      we do not yet have invert_subtyp_bind available!! 

      The problem is always the same: We need to "project" a
      (typ_bind Ds1) <: (typ_bind Ds2) into a D1 <: D2,
      without knowing D1, and without using invert_subtyp_bind.

      Want to apply oktrans2notrans IH on St, but St is a conclusion obtained
      by applying IHTy and thus might be bigger...

      Suppose we have a height measure (ok).
      And suppose oktrans2notrans preserves height (probably not ok!).
      *)
    admit.
  + (* case has_var *)
    admit.

  + (* case subtyp_refl *)
    intros m G v L Lo Hi Has2 _ s Eq Wf. subst.
    apply invert_var_has_dec_typ in Has2.
    destruct Has2 as [X2 [DsX2 [Lo2' [Hi2' [Ty [ExpX2 [DsX2Has [Eq2Lo Eq2Hi]]]]]]]].
    apply invert_ty_var in Ty.
    destruct Ty as [X1 [StX Bi]].
    assert (P: exists DsX1, X1 = typ_bind DsX1) by admit. (* since wf_sto only typ_bind *)
    destruct P as [DsX1 P]. subst X1.
    (* now how can we guess the precise Lo1/Hi1 s.t. 
       decs_has DsX1 L (dec_typ Lo1 Hi1)
       ???
    *)
    admit.
  + (* case subtyp_top *)
    admit.
  + (* case subtyp_bot *)
    admit.
  + (* case subtyp_bind *)
    admit.
  + (* case subtyp_sel_l *)
    intros m G x L Lo2 Hi2 T Has2 _ St IHSt s Eq Wf. subst.
    specialize (IHSt s eq_refl Wf).
    apply invert_var_has_dec_typ in Has2.
    destruct Has2 as [X2 [DsX2 [Lo2' [Hi2' [Ty [ExpX2 [DsX2Has [Eq2Lo Eq2Hi]]]]]]]].
    apply invert_ty_var in Ty.
    destruct Ty as [X1 [StX Bi]].
    refine (subtyp_trans _ IHSt).
    (* now we need to guess the precise Lo1/Hi1 s.t. 
       decs_has DsX1 L (dec_typ Lo1 Hi1)

       We would need
          X1 <: X2     <-- what if it contains middle p.L??
          X1 < DsX1
          X2 < DsX2
          ------------ exp_preserves_sub
          DsX1 <: DsX2

      Or actually even harder than exp_preserves_sub because we have to guess
      Lo1/Hi1 inside DsX1, so include the DsX2Has in lemma...
    *)
    assert (P: exists DsX1, X1 = typ_bind DsX1) by admit. (* since wf_sto only typ_bind *)
    destruct P as [DsX1 P]. subst X1.





     
    admit.
  + (* case subtyp_sel_r *)
    admit.
  + (* case subtyp_tmode *)
    admit.
  + (* case subtyp_trans *)
    admit.

  + (* case ty_var *)
    admit.
  + (* case ty_sbsm *)
    admit.
Qed.

Lemma many_ihs_we_need:
   (forall m G T Ds2, exp m G T Ds2 -> forall s Ds1,
      wf_sto s G ->
      m = ip ->
      (*T = (typ_sel (pth_var (avar_f v)) L) -> 
               bad idea, but removes exp_top/exp_bind cases *)
      exp pr G T Ds1 ->
      exists L, forall z, z \notin L ->
                subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2))
/\ (forall m G t L D2, has m G t L D2 -> forall s v D1,
      wf_sto s G ->
      m = ip ->
      t = (trm_var (avar_f v)) ->
      has pr G (trm_var (avar_f v)) L D1 ->
      subdec G D1 D2)
/\ (forall m1 m2 G T1 T2, subtyp m1 m2 G T1 T2 -> forall s Ds1 Ds2,
      wf_sto s G ->
      m1 = ip ->
      exp pr G T1 Ds1 ->
      exp pr G T2 Ds2 ->
      exists L, forall z, z \notin L -> 
                subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2))
/\ (forall G t T2, ty_trm G t T2 -> forall s v T1 Ds1 Ds2,
      wf_sto s G ->
      t = (trm_var (avar_f v)) ->
      binds v T1 G ->
      exp pr G T1 Ds1 ->
      exp pr G T2 Ds2 ->
      exists L, forall z, z \notin L -> 
                subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2)).
Proof.
  apply exp_has_subtyp_ty_mutind; try (intros; discriminate).
  + (* case exp_top *)
    intros. exists vars_empty.
    intros z zL. unfold open_decs, open_rec_decs. apply subdecs_empty.
  + (* case exp_bind *)
    intros m G Ds2 s Ds1 Wf Eq Exp. inversions Exp.
    exists vars_empty.
    intros. apply subdecs_refl.
  + (* case exp_sel *)
    intros m G v L Lo2 Hi2 Ds2 Has2 IHHas Exp2 IHExp s Ds1 Wf Eqm Exp1. subst.
    assert (Lo1: typ) by admit. assert (Hi1: typ) by admit.
    specialize (IHHas _ _ (dec_typ Lo1 Hi1) Wf eq_refl eq_refl). (*can't get precise has*)
    apply (IHExp s Ds1 Wf eq_refl). (* Hi2 doesn't expand to Ds1! *)
    admit. (* ??? *)
  + (* case has_trm *)
    admit.
  + (* case has_var *)
    admit.
  + (* case subtyp_refl *)
    admit.
  + (* case subtyp_top *)
    admit.
  + (* case subtyp_bot *)
    admit.
  + (* case subtyp_bind *)
    admit.
  + (* case subtyp_sel_l *)
    admit.
  + (* case subtyp_sel_r *)
    admit.
  + (* case subtyp_tmode *)
    admit.
  + (* case subtyp_trans *)
    admit.
  + (* case ty_var *)
    admit.
  + (* case ty_sbsm *)
    admit.
Qed.

Lemma ty_def_sbsm: forall G d D1 D2,
  ok G ->
  ty_def G d D1 ->
  subdec G D1 D2 ->
  ty_def G d D2.
Proof.
  introv Ok Ty Sd. destruct Ty; inversion Sd; try discriminate; subst; clear Sd.
  + apply ty_typ.
  + apply (ty_fld (ty_sbsm H H2)).
  + apply ty_mtd with (L \u dom G).
    intros x Fr. assert (xL: x \notin L) by auto. specialize (H x xL).
    assert (Okx: ok (G & x ~ S2)) by auto.
    apply (weaken_subtyp_end Okx) in H5.
    refine (ty_sbsm _ H5).
    refine (narrow_ty_trm _ H3 H).
    auto.
Qed.

(*
Lemma ty_defs_sbsm: forall L G ds Ds1 Ds2,
  ok G ->
  ty_defs G ds Ds1 ->
  (forall x, x \notin L -> 
     subdecs (G & x ~ typ_bind Ds1) (open_decs x Ds1) (open_decs x Ds2)) ->
  ty_defs G ds Ds2.
Admitted.
*)

(*
Lemma subtyp_expands_same: forall G T1 T2 Ds,
  exp G T2 Ds ->
  subtyp G T1 T2 ->
  exp G T1 Ds.
Proof.
  introv Exp. gen T1. induction Exp; introv St.
  (* case exp_top *)
  + destruct T1.
    (* case T1 = typ_top *)
    - apply exp_top.
    (* case T1 = typ_bot *)
    -z inversions St.

Qed.
*)

(*
Lemma precise_decs_subdecs_of_imprecise_decs: forall s G x ds X2 Ds1 Ds2, 
  wf_sto s G ->
  binds x (object Ds1 ds) s ->
  ty_trm G (trm_var (avar_f x)) X2 ->
  exp G X2 Ds2 ->
  subdecs G (open_decs x Ds1) (open_decs x Ds2).
Proof.
  introv Wf Bis Tyx Exp2.
  lets Ok: (wf_sto_to_ok_G Wf).
  destruct (invert_wf_sto_with_sbsm Wf Bis Tyx) as [St _]. 
     (* invert_wf_sto_with_sbsm should return hyp. of subtyp_bind! *)
  lets Sds: (exp_preserves_sub St Wf Exp1 Exp2).
  destruct Sds as [L Sds].
  pick_fresh z. assert (zL: z \notin L) by auto. specialize (Sds z zL).
  lets BiG: (sto_binds_to_ctx_binds Wf Bis).
  assert (Sds': subdecs oktrans (G & z ~ X1) (open_decs z Ds1) (open_decs z Ds2))
    by admit. (* narrowing to type X1 (which expands) *)
  assert (Ok': ok (G & z ~ X1)) by auto.
  lets P: (@subdecs_subst_principle oktrans _ z x X1 
              (open_decs z Ds1) (open_decs z Ds2) Ok' Sds' BiG).
  assert (zDs1: z \notin fv_decs Ds1) by auto.
  assert (zDs2: z \notin fv_decs Ds2) by auto.
  rewrite <- (@subst_intro_decs z x Ds1 zDs1) in P.
  rewrite <- (@subst_intro_decs z x Ds2 zDs2) in P.
  exact P.
Qed.
*)
