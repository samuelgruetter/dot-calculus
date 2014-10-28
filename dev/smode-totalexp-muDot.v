
(*

Idea: Make expansion a total function, so that expansion cannot be lost by
narrowing, and we can have precise narrowing.

In trm_new and in object, we only allow Ds, not any type, because that's the
simplest thing which has a stable expansion under narrowing.
Thus, expansion is only needed as a "helper" for has.
We allow subsumption in all judgments, including expansion and has.
The mode "tmode" (notrans or oktrans) controls if transitivity at the top level
is accepted, and the mode "pmode" (precise or imprecise) controls if the "has"
judgments inside the subtyping judgments (deeply) must be precise (i.e. without
subsumption.
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
  | decs_cons : nat -> dec -> decs -> decs
  | decs_bot : decs.

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
| decs_bot => match l with
  | label_typ n => Some (dec_typ typ_top typ_bot)
  | label_fld n => Some (dec_fld typ_bot)
  | label_mtd n => Some (dec_mtd typ_top typ_bot)
  end
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
  | decs_bot          => decs_bot
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
  | decs_bot          => \{}
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

(* pmode = "do the 'has' judgments needed in subtyping have to be precise?"
Inductive pmode : Type := pr | ip. *)

(* smode = "do the 'has' and 'exp' judgments need to be stable under narrowing?" 
  For 'has G x l D', the case where the binding for x is narrowed is excluded. *)
Inductive smode : Type := stable | unstable.

(* h: list (path * nat) is the history of all visited p.L *)

(* "simple has": precise "has" which does not depend on expansion
Inductive shas : ctx -> trm -> label -> dec -> Prop :=
  | shas_var : forall G v Ds l D,
      binds v (typ_bind Ds) G ->
      decs_has Ds l D ->
      shas G (trm_var (avar_f v)) l (open_dec v D).
"has" and "exp" are not needed on type level any more, only "shas" is used *)

(* expansion returns a set of decs without opening them *)
Inductive exp : smode -> ctx -> typ -> list (pth * label) -> decs -> Prop :=
  | exp_top : forall G h,
      exp stable G typ_top h decs_nil
  | exp_bot : forall G h,
      exp stable G typ_bot h decs_bot
  | exp_bind : forall G h Ds,
      exp stable G (typ_bind Ds) h Ds
  | exp_sel : forall G x L h Lo Hi Ds,
      has unstable G (trm_var (avar_f x)) L (dec_typ Lo Hi) ->
      ~ List.In (pth_var (avar_f x), L) h ->
      exp unstable G Hi (cons ((pth_var (avar_f x)), L) h) Ds ->
      exp unstable G (typ_sel (pth_var (avar_f x)) L) h Ds
  (* if we encounter a p.L that we've already seen, we just say it expands to {} *)
  | exp_loop : forall G x L h,
      List.In (pth_var (avar_f x), L) h ->
      exp unstable G (typ_sel (pth_var (avar_f x)) L) h decs_nil
  | exp_smode : forall G T h Ds,
      exp stable G T h Ds ->
      exp unstable G T h Ds
with has : smode -> ctx -> trm -> label -> dec -> Prop :=
  | has_trm : forall G t T Ds l D,
      ty_trm G t T ->
      exp unstable G T nil Ds ->
      decs_has Ds l D ->
      (forall z, (open_dec z D) = D) ->
      has unstable G t l D
(*
  | has_var : forall m G v T Ds l D,
      binds v T G ->
      exp m G T nil Ds ->
      decs_has Ds l D ->
      has m G (trm_var (avar_f v)) l (open_dec v D)
*)
  | has_var : forall m G v T Ds l D,
      binds v T G ->
      exp m G T nil Ds ->
      decs_has (open_decs v Ds) l D ->
      has m G (trm_var (avar_f v)) l D
with subtyp : tmode -> ctx -> typ -> typ -> Prop :=
  | subtyp_refl : forall G T,
      subtyp notrans G T T
  | subtyp_top : forall G T,
      subtyp notrans G T typ_top
  | subtyp_bot : forall G T,
      subtyp notrans G typ_bot T
  | subtyp_bind : forall L G Ds1 Ds2,
      (forall z, z \notin L -> 
         subdecs (G & z ~ (typ_bind Ds1))
                 (open_decs z Ds1) 
                 (open_decs z Ds2)) ->
      subtyp notrans G (typ_bind Ds1) (typ_bind Ds2)
  | subtyp_sel_l : forall G x L S U T,
      has stable G (trm_var (avar_f x)) L (dec_typ S U) ->
      subtyp oktrans G U T ->
      subtyp notrans G (typ_sel (pth_var (avar_f x)) L) T
  | subtyp_sel_r : forall G x L S U T,
      has stable G (trm_var (avar_f x)) L (dec_typ S U) ->
      subtyp oktrans G S U -> (* <--- makes proofs a lot easier!! *)
      subtyp oktrans G T S ->
      subtyp notrans G T (typ_sel (pth_var (avar_f x)) L)
  | subtyp_tmode : forall G T1 T2,
      subtyp notrans G T1 T2 ->
      subtyp oktrans G T1 T2
  | subtyp_trans : forall G T1 T2 T3,
      subtyp oktrans G T1 T2 ->
      subtyp oktrans G T2 T3 ->
      subtyp oktrans G T1 T3
with subdec : ctx -> dec -> dec -> Prop :=
  | subdec_typ : forall G Lo1 Hi1 Lo2 Hi2,
      (* only allow implementable decl *)
      (*
      subtyp oktrans G Lo1 Hi1 ->
      subtyp oktrans G Lo2 Hi2 ->
      *)
      (* lhs narrower range than rhs *)
      subtyp oktrans G Lo2 Lo1 ->
      subtyp oktrans G Hi1 Hi2 ->
      (* conclusion *)
      subdec G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2)
  | subdec_fld : forall G T1 T2,
      subtyp oktrans G T1 T2 ->
      subdec G (dec_fld T1) (dec_fld T2)
  | subdec_mtd : forall G S1 T1 S2 T2,
      subtyp oktrans G S2 S1 ->
      subtyp oktrans G T1 T2 ->
      subdec G (dec_mtd S1 T1) (dec_mtd S2 T2)
with subdecs : ctx -> decs -> decs -> Prop :=
  | subdecs_empty : forall G Ds,
      subdecs G Ds decs_nil
  | subdecs_push : forall G n Ds1 Ds2 D1 D2,
      decs_has Ds1 (label_for_dec n D2) D1 ->
      subdec  G D1 D2 ->
      subdecs G Ds1 Ds2 ->
      subdecs G Ds1 (decs_cons n D2 Ds2)
  | subdecs_bot : forall G Ds,
      subdecs G decs_bot Ds
with ty_trm : ctx -> trm -> typ -> Prop :=
  | ty_var : forall G x T,
      binds x T G ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_sel : forall m G t l T,
      has m G t (label_fld l) (dec_fld T) ->
      ty_trm G (trm_sel t l) T
  | ty_call : forall m1 G t m U1 U2 V u,
      has m1 G t (label_mtd m) (dec_mtd U2 V) ->
      ty_trm G u U1 ->
      subtyp oktrans G U1 U2 -> (* <-- built-in subsumption *)
      ty_trm G (trm_call t m u) V
  | ty_new : forall L G ds Ds,
      (forall x, x \notin L ->
                 ty_defs (G & x ~ typ_bind Ds) (open_defs x ds) (open_decs x Ds)) ->
      (forall x, x \notin L ->
                 forall M S U, decs_has (open_decs x Ds) M (dec_typ S U) -> 
                               subtyp oktrans (G & x ~ typ_bind Ds) S U) ->
      ty_trm G (trm_new Ds ds) (typ_bind Ds)
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
                     subtyp oktrans (G & x ~ typ_bind Ds) S U) ->
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

Hint Constructors exp has subtyp subdec subdecs ty_trm ty_def ty_defs.


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

Scheme subtyp_mut3  := Induction for subtyp  Sort Prop
with   subdec_mut3  := Induction for subdec  Sort Prop
with   subdecs_mut3 := Induction for subdecs Sort Prop.
Combined Scheme subtyp_mutind from subtyp_mut3, subdec_mut3, subdecs_mut3.

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

Scheme exp_mut5     := Induction for exp     Sort Prop
with   has_mut5     := Induction for has     Sort Prop
with   subtyp_mut5  := Induction for subtyp  Sort Prop
with   subdec_mut5  := Induction for subdec  Sort Prop
with   subdecs_mut5 := Induction for subdecs Sort Prop
with   ty_trm_mut5  := Induction for ty_trm  Sort Prop.
Combined Scheme mutind5 from exp_mut5, has_mut5,
                             subtyp_mut5, subdec_mut5, subdecs_mut5.

Lemma induction_skeleton:
   (forall m G T H Ds, exp m G T H Ds -> exp m G T H Ds)
/\ (forall m G t l d, has m G t l d -> has m G t l d)
/\ (forall m G T1 T2, subtyp m G T1 T2 -> subtyp m G T1 T2)
/\ (forall G D1 D2, subdec G D1 D2 -> subdec G D1 D2)
/\ (forall G Ds1 Ds2, subdecs G Ds1 Ds2 -> subdecs G Ds1 Ds2)
/\ (forall G t T, ty_trm G t T -> ty_trm G t T)
/\ (forall G d D, ty_def G d D -> ty_def G d D)
/\ (forall G ds Ds, ty_defs G ds Ds -> ty_defs G ds Ds).
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
  + (* case exp_loop *)
    intros. apply* exp_loop.
  + (* case exp_smode *)
    intros. apply* exp_smode.
  + (* case has_trm *)
    intros. apply* has_trm.
  + (* case has_var *)
    intros. apply* has_var.
  + (* case subtyp_refl *)
    intros. apply* subtyp_refl.
  + (* case subtyp_top *)
    intros. apply (subtyp_top _ _).
  + (* case subtyp_bot *)
    intros. apply (subtyp_bot _ _).
  + (* case subtyp_bind *)
    intros. apply_fresh subtyp_bind as z. auto.
  + (* case subtyp_asel_l *)
    intros. apply* subtyp_sel_l.
  + (* case subtyp_asel_r *)
    intros. apply* subtyp_sel_r.
  + (* case subtyp_tmode *)
    intros. apply* subtyp_tmode.
  + (* case subtyp_trans *)
    intros. admit.
  + (* case subdec_typ *)
    intros. admit.
  + (* case subdec_fld *)
    intros. admit.
  + (* case subdec_mtd *)
    intros. admit.
  + (* case subdecs_empty *)
    intros. apply subdecs_empty.
  + (* case subdecs_push *)
    intros. admit.
  + (* case subdecs_bot *)
    intros. apply subdecs_bot.
  + (* case ty_var *)
    intros. apply* ty_var.
  + (* case ty_sel *)
    intros. apply* ty_sel.
  + (* case ty_call *)
    intros. apply* ty_call.
  + (* case ty_new *)
    intros. apply* ty_new.
  + (* case ty_typ *)
    intros. apply ty_typ.
  + (* case ty_fld *)
    intros. apply* ty_fld.
  + (* case ty_mtd *)
    intros. apply* ty_mtd.
  + (* case ty_dsnil *)
    intros. apply ty_dsnil.
  + (* case ty_dscons *) 
    intros. apply* ty_dscons.
Qed.


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
  | decs_bot          => decs_bot
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

(*
Lemma subdecs_bot: forall m G Ds,
  subdecs m G decs_bot Ds.
Proof.
  intros. induction Ds.
  + apply subdecs_empty.
  + destruct d.
    - apply subdecs_push with (dec_typ typ_top typ_bot).
      * simpl. unfold decs_has, get_dec. reflexivity.
      * apply subdec_typ. (* t <: t0 might not work!! *)
  (* also need subdecs m G decs_bot decs_bot *)
  (* easiest: just add decs_bot <: everything *)
Qed.
*)

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
  + inversions Hhas. exists typ_top typ_bot. reflexivity.
Qed.

Lemma decs_has_fld_sync: forall n d ds,
  decs_has ds (label_fld n) d -> exists x, d = (dec_fld x).
Proof.
  introv Hhas. induction ds; unfolds decs_has, get_dec. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_dec in H. destruct* d; discriminate.
    - apply* IHds.
  + inversions Hhas. exists typ_bot. reflexivity.
Qed.

Lemma decs_has_mtd_sync: forall n d ds,
  decs_has ds (label_mtd n) d -> exists T U, d = (dec_mtd T U).
Proof.
  introv Hhas. induction ds; unfolds decs_has, get_dec. 
  + discriminate.
  + case_if.
    - inversions Hhas. unfold label_for_dec in H. destruct* d; discriminate.
    - apply* IHds.
  + inversions Hhas. exists typ_top typ_bot. reflexivity.
Qed.

Lemma decs_has_show_label_for_dec: forall Ds l D, decs_has Ds l D ->
  exists n, l = (label_for_dec n D).
Proof.
  intros. destruct l; exists n.
  + apply decs_has_typ_sync in H. destruct H as [Lo [Hi Eq]]. subst. reflexivity.
  + apply decs_has_fld_sync in H. destruct H as [T      Eq ]. subst. reflexivity.
  + apply decs_has_mtd_sync in H. destruct H as [T  [U  Eq]]. subst. reflexivity.
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

(*
Lemma smode_to_unstable:
   (forall m G T h Ds, exp m G T h Ds -> exp unstable G T h Ds)
/\ (forall m G t l D, has m G t l D -> has unstable G t l D).
Proof.
  apply exp_has_mutind; try solve [intros; auto].
  + introv Has IHHas NIn Exp IHExp.
    apply (exp_sel IHHas NIn IHExp).
  + introv Ty Exp IHExp DsHas Cl.
    apply (has_trm Ty IHExp DsHas Cl).
  + introv Bi Exp IHExp DsHas.
    apply (has_var Bi IHExp DsHas).
Qed.

Lemma exp_smode: forall m G T h Ds,
  exp m G T h Ds -> exp unstable G T h Ds.
Proof. intros. apply* smode_to_unstable. Qed.

Lemma has_smode: forall m G t l D,
  has m G t l D -> has unstable G t l D.
Proof. intros. apply* smode_to_unstable. Qed.
*)

(* ###################################################################### *)
(** ** Reflexivity TODO *)

Lemma subtyp_refl_all: forall m G T, subtyp m G T T.
Admitted.

Lemma subdec_refl: forall G D, subdec G D D. Admitted.

(* subdecs_refl does not hold, because subdecs requires that for each dec in rhs
   (including hidden ones), there is an unhidden one in lhs *)
(* or that there are no hidden decs in rhs *)
Lemma subdecs_refl: forall G Ds,
  subdecs G Ds Ds.
Proof.
Admitted. (* TODO does not hold!! *)


(* ###################################################################### *)
(** ** Inversion lemmas *)

Lemma invert_subdec_typ_sync_left: forall G D Lo2 Hi2,
   subdec G D (dec_typ Lo2 Hi2) ->
   exists Lo1 Hi1, D = (dec_typ Lo1 Hi1) /\
                   subtyp oktrans G Lo2 Lo1 /\
                   subtyp oktrans G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. exists Lo1 Hi1. auto.
Qed.

Lemma invert_subdec_fld_sync_left: forall G D T2,
   subdec G D (dec_fld T2) ->
   exists T1, D = (dec_fld T1) /\
              subtyp oktrans G T1 T2.
Proof.
  introv Sd. inversions Sd. exists T1. auto.
Qed.

Lemma invert_subdec_mtd_sync_left: forall G D T2 U2,
   subdec G D (dec_mtd T2 U2) ->
   exists T1 U1, D = (dec_mtd T1 U1) /\
                 subtyp oktrans G T2 T1 /\
                 subtyp oktrans G U1 U2.
Proof.
  introv Sd. inversions Sd. exists S1 T1. auto.
Qed.

Lemma invert_subdec_typ: forall G Lo1 Hi1 Lo2 Hi2,
  subdec G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2) ->
  subtyp oktrans G Lo2 Lo1 /\ subtyp oktrans G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. auto.
Qed.

Lemma decs_bot_has_subdec: forall G n D2,
  exists D1, decs_has decs_bot (label_for_dec n D2) D1 /\
             subdec G D1 D2.
Proof.
  intros. destruct D2 as [Lo Hi | T | T1 T2].
  - exists (dec_typ typ_top typ_bot). split.
    * unfold decs_has, get_dec. reflexivity.
    * apply subdec_typ; auto.
  - exists (dec_fld typ_bot). split.
    * unfold decs_has, get_dec. reflexivity.
    * apply subdec_fld; auto.
  - exists (dec_mtd typ_top typ_bot). split.
    * unfold decs_has, get_dec. reflexivity.
    * apply subdec_mtd; auto.
Qed.

Lemma invert_subdecs: forall G Ds1 Ds2,
  subdecs G Ds1 Ds2 -> 
  forall l D2, decs_has Ds2 l D2 -> 
               (exists D1, decs_has Ds1 l D1 /\ subdec G D1 D2).
Proof.
  introv Sds. induction Sds; introv DsHas.
  + inversions DsHas.
  + unfold decs_has, get_dec in DsHas. case_if.
    - inversions DsHas.
      exists D1. split; assumption.
    - fold get_dec in DsHas. apply IHSds; assumption.
  + destruct l.
    - exists (dec_typ typ_top typ_bot).
      destruct (decs_has_typ_sync DsHas) as [Lo [Hi Eq]]. subst. split.
      * unfold decs_has, get_dec. reflexivity.
      * apply subdec_typ; auto.
    - exists (dec_fld typ_bot).
      destruct (decs_has_fld_sync DsHas) as [T Eq]. subst. split.
      * unfold decs_has, get_dec. reflexivity.
      * apply subdec_fld; auto.
    - exists (dec_mtd typ_top typ_bot).
      destruct (decs_has_mtd_sync DsHas) as [T1 [T2 Eq]]. subst. split.
      * unfold decs_has, get_dec. reflexivity.
      * apply subdec_mtd; auto.
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
                       subtyp oktrans (G1 & x ~ typ_bind Ds) S U).
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

Lemma subdec_sync: forall G D1 D2,
   subdec G D1 D2 ->
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

Lemma subdec_to_label_for_eq: forall G D1 D2 n,
  subdec G D1 D2 ->
  (label_for_dec n D1) = (label_for_dec n D2).
Proof.
  introv Sd. subdec_sync_for Sd; subst; reflexivity.
Qed.

Lemma invert_subdecs_push: forall G Ds1 Ds2 n D2,
  subdecs G Ds1 (decs_cons n D2 Ds2) -> 
    exists D1, decs_has Ds1 (label_for_dec n D2) D1
            /\ subdec G D1 D2
            /\ subdecs G Ds1 Ds2.
Proof.
  intros. inversions H.
  - eauto.
  - lets P: (decs_bot_has_subdec G n D2).
    destruct P as [D1 [H1 H2]].
    exists D1. refine (conj H1 (conj H2 (subdecs_bot _ _))).
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

(*
Lemma invert_var_has_dec: forall m G x l D,
  has m G (trm_var (avar_f x)) l D ->
  exists T Ds D', ty_trm G (trm_var (avar_f x)) T /\
                  exp m G T nil Ds /\
                  decs_has Ds l D' /\
                  open_dec x D' = D.
Proof.
  introv Has. inversions Has.
  (* case has_trm *)
  + exists T Ds D. auto.
  (* case has_var *)
  + exists T Ds D0. auto.
Qed.
*)

Lemma invert_has: forall m G t l D,
   has m G t l D ->
   (exists T Ds,      ty_trm G t T /\
                      exp m G T nil Ds /\
                      decs_has Ds l D /\
                      (forall z : var, open_dec z D = D))
\/ (exists x T Ds,    t = (trm_var (avar_f x)) /\
                      ty_trm G (trm_var (avar_f x)) T /\
                      exp m G T nil Ds /\
                      decs_has (open_decs x Ds) l D).
Proof.
  introv Has. inversions Has.
  (* case has_trm *)
  + subst. left. exists T Ds. auto.
  (* case has_var *)
  + right. exists v T Ds. auto.
Qed.

(*
Lemma invert_has: forall m G t l D,
   has m G t l D ->
   (exists T Ds,      ty_trm G t T /\
                      exp m G T nil Ds /\
                      decs_has Ds l D /\
                      (forall z : var, open_dec z D = D))
\/ (exists x T Ds D', t = (trm_var (avar_f x)) /\
                      ty_trm G (trm_var (avar_f x)) T /\
                      exp m G T nil Ds /\
                      decs_has Ds l D' /\
                      open_dec x D' = D).
Proof.
  introv Has. inversions Has.
  (* case has_trm *)
  + subst. left. exists T Ds. auto.
  (* case has_var *)
  + right. exists v T Ds D0. auto.
Qed.*)

(*
Lemma invert_var_has_dec_typ: forall m G x l S U,
  has m G (trm_var (avar_f x)) l (dec_typ S U) ->
  exists X Ds S' U', ty_trm G (trm_var (avar_f x)) X /\
                     exp m G X nil Ds /\
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

Lemma invert_var_has_dec_fld: forall m G x l T,
  has m G (trm_var (avar_f x)) l (dec_fld T) ->
  exists X Ds T', ty_trm G (trm_var (avar_f x)) X /\
                  exp m G X nil Ds /\
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

Lemma invert_var_has_dec_mtd: forall m G x l S U,
  has m G (trm_var (avar_f x)) l (dec_mtd S U) ->
  exists X Ds S' U', ty_trm G (trm_var (avar_f x)) X /\
                     exp m G X nil Ds /\
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
*)

(*
Lemma invert_exp_sel: forall m G v L Ds,
  exp m G (typ_sel (pth_var (avar_f v)) L) nil Ds ->
  exists Lo Hi, has m G (trm_var (avar_f v)) L (dec_typ Lo Hi) /\
                exp m G Hi ((pth_var (avar_f v), L) :: nil) Ds.
Proof.
  introv Exp. induction Exp.
  + exists Lo Hi. auto.
  + false H2.
  + 
Qed.
*)

Lemma invert_ty_var: forall G x T,
  ty_trm G (trm_var (avar_f x)) T -> binds x T G.
Proof.
  introv Ty. inversions Ty. assumption.
Qed.

(*
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
*)

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
  + unfold open_decs, open_rec_decs. admit. (* TODO holds *)
Qed.

Lemma decs_has_preserves_sub: forall G Ds1 Ds2 l D2,
  decs_has Ds2 l D2 ->
  subdecs G Ds1 Ds2 ->
  exists D1, decs_has Ds1 l D1 /\ subdec G D1 D2.
Proof.
  introv Has Sds. gen l D2 Has. induction Sds; introv Has.
  + inversion Has.
  + unfold decs_has, get_dec in Has. case_if.
    - inversions Has. exists D1. auto.
    - fold get_dec in Has. apply* IHSds.
  + destruct (decs_has_show_label_for_dec Has) as [n Eq]. subst.
    apply decs_bot_has_subdec.
Qed.

Print Assumptions decs_has_preserves_sub.

(*************************


l : label
D : dec
G1 : env typ
G2 : env typ
x : var
DsA : decs
NIn : x # G2
Sds : subdecs (G1 & x ~ typ_bind DsA) (open_decs x DsA) (open_decs x Ds)
Ok : ok (G1 & x ~ typ_bind Ds & G2)
IHExp : exp stable (G1 & x ~ typ_bind DsA & G2) (typ_bind Ds) nil Ds
DsHas : decs_has (open_decs x Ds) l (open_dec x D)
*)

Lemma open_decs_cons: forall x DsC n DsOH DsOT,
  decs_cons n DsOH DsOT = open_decs x DsC ->
  exists DsCH DsCT, DsC = decs_cons n DsCH DsCT
                 /\ open_dec  x DsCH = DsOH
                 /\ open_decs x DsCT = DsOT.
Proof.
  introv Eq. destruct DsC.
  + unfold open_decs, open_rec_decs in Eq. discriminate Eq.
  + unfold open_decs, open_rec_decs in Eq.
    fold open_rec_dec in Eq. fold open_rec_decs in Eq. inversions Eq.
    exists d DsC. auto.
  + discriminate Eq.
Qed.

Lemma decs_has_preserves_sub_open: forall x G Ds1 Ds2 l D2,
  decs_has (open_decs x Ds2) l (open_dec x D2) ->
  subdecs G (open_decs x Ds1) (open_decs x Ds2) ->
  exists D1, decs_has (open_decs x Ds1) l D1
          /\ subdec G D1 (open_dec x D2).
Proof.
  introv Has Sds.
  gen_eq Ds2': (open_decs x Ds2).
  gen_eq Ds1': (open_decs x Ds1).
  gen x l Ds1 Ds2 D2 Has. induction Sds; introv Has Eq1 Eq2.
  + inversion Has.
  + rename Ds0 into Ds1AllClosed, Ds3 into Ds2AllClosed, D0 into DBClosed, D1 into DAOpen.
    subst Ds1.
    apply open_decs_cons in Eq2.
    destruct Eq2 as [Ds2HeadOpen [Ds2TailOpen [Eq3 [Eq4 Eq5]]]]. subst.
    unfold decs_has, get_dec in Has. case_if.
    - inversions Has. exists DAOpen. auto.
    - fold get_dec in Has. apply* IHSds.
  + destruct (decs_has_show_label_for_dec Has) as [n Eq]. subst.
    apply decs_bot_has_subdec.
Qed.

Lemma decs_has_preserves_sub_D1_known: forall G Ds1 Ds2 l D1 D2,
  decs_has Ds1 l D1 ->
  decs_has Ds2 l D2 ->
  subdecs G Ds1 Ds2 ->
  subdec G D1 D2.
Proof.
  introv Has1 Has2 Sds. gen l D1 D2 Has1 Has2. induction Sds; introv Has1 Has2.
  + inversion Has2.
  + unfold decs_has, get_dec in Has2. case_if.
    - inversions Has2. rename H into Has1'.
      unfold decs_has in Has1, Has1'.
      rewrite Has1' in Has1. inversions Has1. assumption.
    - fold get_dec in Has2. apply* IHSds.
  + destruct (decs_has_show_label_for_dec Has2) as [n Eq]. subst.
    lets P: (@decs_bot_has_subdec G n D2). destruct P as [D1' [Has1' Sd]].
    unfold decs_has in Has1, Has1'.
    rewrite Has1' in Has1. inversions Has1. exact Sd.
Qed.

Print Assumptions decs_has_preserves_sub_D1_known.


(* ###################################################################### *)
(** ** Uniqueness *)

Lemma stable_exp_has_unique:
  (forall m G T H Ds1, exp m G T H Ds1 -> m = stable ->
     forall Ds2, exp stable G T H Ds2 -> Ds1 = Ds2) /\ 
  (forall m G v l D1, has m G v l D1 -> m = stable ->
     forall D2, has stable G v l D2 -> D1 = D2).
Proof.
  apply exp_has_mutind.
  + (* exp_top *)
    introv Eq Exp. inversions Exp. reflexivity.
  + (* exp_bot *)
    introv Eq Exp. inversions Exp. reflexivity.
  + (* exp_bind *)
    introv Eq Exp. inversions Exp. reflexivity.
  + (* exp_sel *)
    intros. discriminate.
  + (* case exp_loop *)
    intros. discriminate.
  + (* case exp_smode *)
    introv Exp1 IHExp1 Eq Exp2. apply (IHExp1 eq_refl _ Exp2).
  + (* case has_trm *)
    intros. discriminate.
  + (* case has_var *)
    introv Bi Exp IHExp DsHas Eq Has. subst. specialize (IHExp eq_refl).
    apply invert_has in Has. destruct Has as [Has | Has].
    - destruct Has as [T' [Ds' [Ty' [Exp' [DsHas' Cl]]]]].
      apply invert_ty_var in Ty'.
      lets Eq: (binds_func Bi Ty'). subst T'.
      specialize (IHExp _ Exp'). subst Ds'.
      apply (decs_has_open v) in DsHas'.
      unfold decs_has in *. rewrite DsHas' in DsHas. inversions DsHas.
      apply Cl.
    - destruct Has as [v' [T' [Ds' [Eq [Ty' [Exp' DsHas']]]]]].
      symmetry in Eq. inversions Eq.
      apply invert_ty_var in Ty'.
      lets Eq: (binds_func Bi Ty'). subst T'.
      specialize (IHExp _ Exp'). subst Ds'.
      unfold decs_has in *. rewrite DsHas' in DsHas. inversions DsHas.
      reflexivity.
Qed.

Print Assumptions stable_exp_has_unique.

Lemma stable_exp_unique: forall G T Ds1 Ds2,
  exp stable G T nil Ds1 -> exp stable G T nil Ds2 -> Ds1 = Ds2.
Proof. intros. apply ((proj1 stable_exp_has_unique) _ _ _ _ _ H eq_refl _ H0). Qed.

Lemma stable_has_unique: forall G v l D1 D2,
  has stable G v l D1 -> has stable G v l D2 -> D1 = D2.
Proof. intros. apply* stable_exp_has_unique. Qed.


(* ###################################################################### *)
(** ** Weakening *)

Lemma weakening:
   (forall m G T H Ds, exp m G T H Ds -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      exp m (G1 & G2 & G3) T H Ds)
/\ (forall m G t l d, has m G t l d -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      has m (G1 & G2 & G3) t l d)
/\ (forall m G T1 T2, subtyp m G T1 T2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subtyp m (G1 & G2 & G3) T1 T2)
/\ (forall G D1 D2, subdec G D1 D2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdec (G1 & G2 & G3) D1 D2)
/\ (forall G Ds1 Ds2, subdecs G Ds1 Ds2 -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      subdecs (G1 & G2 & G3) Ds1 Ds2)
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
  + (* case exp_loop *)
    intros. apply* exp_loop.
  + (* case exp_smode *)
    intros. apply* exp_smode.
  + (* case has_trm *)
    intros. apply* has_trm.
  + (* case has_var *)
    intros. subst. apply has_var with T Ds.
    - apply* binds_weaken.
    - apply* H.
    - assumption.
  + (* case subtyp_refl *)
    intros. apply* subtyp_refl.
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
    intros. subst. apply subtyp_sel_l with S U.
    - admit. (* holds *)
    - auto.
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
  + (* case subdecs_bot *)
    intros. apply subdecs_bot.
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
  ok (G1 & G2 & G3) -> exp m (G1 & G3) T nil Ds -> exp m (G1 & G2 & G3) T nil Ds.
Proof.
  intros. apply* weakening.
Qed.

Lemma weaken_exp_end: forall m G1 G2 T Ds,
  ok (G1 & G2) -> exp m G1 T nil Ds -> exp m (G1 & G2) T nil Ds.
Proof.
  introv Ok Exp.
  assert (Eq1: G1 = G1 & empty) by (rewrite concat_empty_r; reflexivity).
  assert (Eq2: G1 & G2 = G1 & G2 & empty) by (rewrite concat_empty_r; reflexivity).
  rewrite Eq1 in Exp. rewrite Eq2 in Ok. rewrite Eq2.
  apply (weaken_exp_middle Ok Exp).
Qed.

Lemma weaken_subtyp_middle: forall m G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp m (G1      & G3) S U ->
  subtyp m (G1 & G2 & G3) S U.
Proof.
  destruct weakening as [_ [_ [W _]]].
  introv Hok123 Hst.
  specialize (W m (G1 & G3) S U Hst).
  specialize (W G1 G2 G3 eq_refl Hok123).
  apply W.
Qed.

Lemma weaken_subdec_middle: forall G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subdec (G1      & G3) S U ->
  subdec (G1 & G2 & G3) S U.
Proof.
  destruct weakening as [_ [_ [_ [W _]]]].
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

Lemma weaken_subtyp_end: forall m G1 G2 S U,
  ok (G1 & G2) -> 
  subtyp m G1        S U ->
  subtyp m (G1 & G2) S U.
Proof.
  introv Hok Hst.
  apply (env_remove_empty (fun G0 => subtyp m G0 S U) (G1 & G2)).
  apply weaken_subtyp_middle.
  apply (env_add_empty (fun G0 => ok G0) (G1 & G2) Hok).
  apply (env_add_empty (fun G0 => subtyp m G0 S U) G1 Hst).
Qed.

Lemma weaken_subdec_end: forall G1 G2 D1 D2,
  ok (G1 & G2) -> 
  subdec G1        D1 D2 ->
  subdec (G1 & G2) D1 D2.
Proof.
  introv Hok Hsd.
  apply (env_remove_empty (fun G0 => subdec G0 D1 D2) (G1 & G2)).
  apply weaken_subdec_middle.
  apply (env_add_empty (fun G0 => ok G0) (G1 & G2) Hok).
  apply (env_add_empty (fun G0 => subdec G0 D1 D2) G1 Hsd).
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
  + simpl. unfold decs_has, get_dec in *. destruct l; inversions Has; reflexivity.
Qed.

Lemma subst_binds: forall x y v T G,
  binds v T G ->
  binds v (subst_typ x y T) (subst_ctx x y G).
Proof.
  introv Bi. unfold subst_ctx. apply binds_map. exact Bi.
Qed.

(*
Lemma subst_principles: forall y S,
   (forall m G T H Ds, exp m G T H Ds -> forall G1 G2 x,
     m = ip ->
     G = G1 & x ~ S & G2 ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & x ~ S & G2) ->
     exp ip (G1 & (subst_ctx x y G2)) (subst_typ x y T) H (subst_decs x y Ds))
/\ (forall m G t l D, has m G t l D -> forall G1 G2 x,
     m = ip ->
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     has ip (G1 & (subst_ctx x y G2)) (subst_trm x y t) l (subst_dec x y D))
/\ (forall m1 m2 G T U, subtyp m1 m2 G T U -> forall G1 G2 x,
     m1 = ip ->
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     subtyp ip m2 (G1 & (subst_ctx x y G2)) (subst_typ x y T) (subst_typ x y U))
/\ (forall m G D1 D2, subdec m G D1 D2 -> forall G1 G2 x,
     m = ip ->
     G = (G1 & (x ~ S) & G2) ->
     ty_trm G1 (trm_var (avar_f y)) S ->
     ok (G1 & (x ~ S) & G2) ->
     subdec ip (G1 & (subst_ctx x y G2)) (subst_dec x y D1) (subst_dec x y D2))
/\ (forall m G Ds1 Ds2, subdecs m G Ds1 Ds2 -> forall G1 G2 x,
     m = ip ->
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
Admitted. (* TODO *)
(*
Proof.
  intros y S. apply ty_mutind.
  (* case exp_top *)
  + intros. simpl. apply exp_top.
  (* case exp_bot *)
  + intros. simpl. apply exp_bot.
  (* case exp_bind *)
  + intros. simpl. apply exp_bind.
  (* case exp_sel *)
  + intros m G v L Lo Hi H Ds Has IHHas Exp IHExp G1 G2 x Eqm EqG Tyy Ok. subst.
    specialize (IHHas _ _ _ eq_refl eq_refl Tyy Ok).
    specialize (IHExp _ _ _ eq_refl eq_refl Tyy Ok).
    unfold subst_typ. unfold subst_pth. unfold subst_avar. case_if.
    - simpl in IHHas. case_if.
      apply (exp_sel IHHas IHExp).
    - simpl in IHHas. case_if.
      apply (exp_sel IHHas IHExp).
  + (* case has_trm *)
    intros G t T Ds l D Ty IHTy Exp IHExp Has Clo G1 G2 x Eqm EqG Bi Ok.
    subst. specialize (IHTy _ _ _ eq_refl Bi Ok).
    apply has_trm with (subst_typ x y T) (subst_decs x y Ds).
    - exact IHTy.
    - apply* IHExp.
    - apply* subst_decs_has.
    - intro z. specialize (Clo z). admit.
  + (* case has_var *)
    intros G z T Ds l D Ty IHTy Exp IHExp Has G1 G2 x Eqm EqG Bi Ok.
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
  + (* case has_pr *)
    intros. discriminate.
  + (* case subtyp_refl *)
    intros m G v L Lo Hi Has IHHas G1 G2 x Eqm EqG Tyy Ok. subst.
    specialize (IHHas _ _ _ eq_refl eq_refl Tyy Ok).
    unfold subst_dec in IHHas. fold subst_typ in IHHas.
    unfold subst_trm, subst_avar in IHHas.
    simpl. case_if; apply (subtyp_refl IHHas).
  + (* case subtyp_top *)
    intros. simpl. apply subtyp_top.
  + (* case subtyp_bot *)
    intros. simpl. apply subtyp_bot.
  + (* case subtyp_bind *)
    intros L m G Ds1 Ds2 Sds IH G1 G2 x Eqm EqG Bi Ok. subst.
    apply_fresh subtyp_bind as z. fold subst_decs.
    assert (zL: z \notin L) by auto.
    specialize (IH z zL G1 (G2 & z ~ typ_bind Ds1) x).
    rewrite concat_assoc in IH.
    specialize (IH eq_refl eq_refl Bi).
    unfold subst_ctx in IH. rewrite map_push in IH. simpl in IH.
    rewrite concat_assoc in IH.
    rewrite (subst_open_commute_decs x y z Ds1) in IH.
    rewrite (subst_open_commute_decs x y z Ds2) in IH.
    unfold subst_fvar in IH.
    assert (x <> z) by auto. case_if.
    unfold subst_ctx. apply IH. admit.
  + (* case subtyp_sel_l *)
    intros m G v L Lo Hi T Has IHHas St IHSt G1 G2 x Eqm EqG Bi Ok. subst.
    specialize (IHSt _ _ _ eq_refl eq_refl Bi Ok).
    specialize (IHHas _ _ _ eq_refl eq_refl Bi Ok).
    simpl in *.
    case_if; apply (subtyp_sel_l IHHas IHSt).
  + (* case subtyp_sel_r *)
    intros m G v L Lo Hi T Has IHHas St1 IHSt1 St2 IHSt2 G1 G2 x Eqm EqG Bi Ok. subst.
    specialize (IHSt1 _ _ _ eq_refl eq_refl Bi Ok).
    specialize (IHSt2 _ _ _ eq_refl eq_refl Bi Ok).
    specialize (IHHas _ _ _ eq_refl eq_refl Bi Ok).
    simpl in *.
    case_if; apply (subtyp_sel_r IHHas IHSt1 IHSt2).
  + (* case subtyp_tmode *)
    intros m G T1 T2 St IH G1 G2 x Eqm EqG Bi Ok. subst.
    specialize (IH _ _ _ eq_refl eq_refl Bi Ok).
    apply (subtyp_tmode IH).
  + (* case subtyp_trans *)
    intros m G T1 T2 T3 St12 IH12 St23 IH23 G1 G2 x Eqm EqG Bi Ok. subst.
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
    intros m G n Ds1 Ds2 D1 D2 Has Sd IH1 Sds IH2 G1 G2 x Eq1 Eq2 Bi Ok. subst.
    specialize (IH1 _ _ _ eq_refl eq_refl Bi Ok).
    specialize (IH2 _ _ _ eq_refl eq_refl Bi Ok).
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
*)
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
*)

(* ###################################################################### *)
(** ** A weak form of narrowing, only on type-level *)

Axiom okadmit: forall G: ctx, ok G.

Lemma pr_narrow_subdecs: forall G z DsA DsB Ds1 Ds2,
  subdecs (G & z ~ typ_bind DsA) (open_decs z DsA) (open_decs z DsB) ->
  subdecs (G & z ~ typ_bind DsB) Ds1 Ds2 ->
  subdecs (G & z ~ typ_bind DsA) Ds1 Ds2.
Admitted.

Lemma simple_narrow_exp_has:
   (forall m G T h Ds, exp m G T h Ds -> forall G1 G2 x DsA DsB,
    m = stable ->
    ok G ->
    G = G1 & x ~ (typ_bind DsB) & G2 ->
    subdecs (G1 & x ~ (typ_bind DsA)) (open_decs x DsA) (open_decs x DsB) ->
    exp m (G1 & x ~ (typ_bind DsA) & G2) T h Ds)
/\ (forall m G t l D2, has m G t l D2 -> forall G1 G2 x DsA DsB,
    m = stable ->
    ok G ->
    G = G1 & x ~ (typ_bind DsB) & G2 ->
    subdecs (G1 & x ~ (typ_bind DsA)) (open_decs x DsA) (open_decs x DsB) ->
    exists D1, has m  (G1 & x ~ (typ_bind DsA) & G2) t l D1
            /\ subdec (G1 & x ~ (typ_bind DsA) & G2) D1 D2).
Proof.
  apply exp_has_mutind; try solve [(intros; discriminate) || (intros; auto)].
  (* case has_var *)
  + introv Bi Exp IHExp DsHas Eq1 Ok Eq2 Sds. subst.
    specialize (IHExp _ _ _ _ _ eq_refl Ok eq_refl Sds).
    apply binds_middle_inv in Bi.
    destruct Bi as [Bi | [[NIn [Eq1 Eq2]] | [NIn [Ne Bi]]]].
    - (* v is in G2 *)
      exists D.
      refine (conj _ (subdec_refl _ _)).
      refine (has_var _ IHExp DsHas).
      apply (binds_concat_right _ Bi).
    - (* v = x *)
      subst. inversions Exp. (* Ds = DsB *)
      lets Sd: (decs_has_preserves_sub DsHas Sds).
      destruct Sd as [D1 [DsAHas Sd]].
      exists D1. split.
      * refine (@has_var _ _ _  (typ_bind DsA) DsA l D1 _ _ DsAHas); auto.
      * apply* weaken_subdec_end. apply okadmit.
    - (* v is in G1 *)
      exists D.
      refine (conj _ (subdec_refl _ _)).
      refine (has_var _ IHExp DsHas). auto.
Qed.

Print Assumptions simple_narrow_exp_has.

Definition simple_narrow_exp := proj1 simple_narrow_exp_has.
Definition simple_narrow_has := proj2 simple_narrow_exp_has.

Lemma simple_narrow_sub:
   (forall m G T1 T2 (Hst : subtyp m G T1 T2), forall G1 G2 z DsA DsB, 
     ok              (G1 & z ~ typ_bind DsB & G2) ->
     G       =       (G1 & z ~ typ_bind DsB & G2) ->
     subdecs         (G1 & z ~ typ_bind DsA     ) (open_decs z DsA) (open_decs z DsB) ->
     subtyp  oktrans (G1 & z ~ typ_bind DsA & G2) T1 T2)
/\ (forall   G D1 D2 (Hsd : subdec G D1 D2), forall G1 G2 z DsA DsB, 
     ok              (G1 & z ~ typ_bind DsB & G2) ->
     G       =       (G1 & z ~ typ_bind DsB & G2) ->
     subdecs         (G1 & z ~ typ_bind DsA     ) (open_decs z DsA) (open_decs z  DsB) ->
     subdec          (G1 & z ~ typ_bind DsA & G2) D1 D2)
/\ (forall G Ds1 Ds2 (Hsds : subdecs G Ds1 Ds2), forall G1 G2 z DsA DsB, 
     ok              (G1 & z ~ typ_bind DsB & G2) ->
     G       =       (G1 & z ~ typ_bind DsB & G2) ->
     subdecs         (G1 & z ~ typ_bind DsA     ) (open_decs z DsA) (open_decs z DsB) ->
     subdecs         (G1 & z ~ typ_bind DsA & G2) Ds1 Ds2).
Proof.
  apply subtyp_mutind; try (intros; solve [auto]).

  (* subtyp *)
  (* cases refl, top, bot: auto *)
  + (* case bind *)
    introv Sds12 IH Ok Eq SdsAB. subst. apply subtyp_tmode.
    apply_fresh subtyp_bind as z0.
    rewrite <- concat_assoc.
    refine (IH z0 _ G1 (G2 & z0 ~ typ_bind Ds1) _ DsA DsB _ _ _ ); clear IH.
    - auto.
    - rewrite concat_assoc. auto.
    - rewrite <- concat_assoc. reflexivity. 
    - assumption.
  + (* case sel_l *)
    introv Has St IHSt Ok Eq SdsAB. subst.
    apply subtyp_tmode.
    lets Hn: (simple_narrow_has Has).
    specialize (Hn G1 G2 z DsA DsB eq_refl Ok eq_refl SdsAB).
    destruct Hn as [DA [DAHas Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [St1 St2]]]]. subst.
    apply subtyp_sel_l with Lo1 Hi1.
    * assumption.
    * assert (Hok': ok (G1 & z ~ (typ_bind DsA) & G2)). {
        apply (ok_middle_change _ Ok).
      }
      refine (subtyp_trans St2 _).
      apply IHSt with (DsB0 := DsB); auto.
  + (* case asel_r *)
    introv Has St1 IH1 St2 IH2 Ok Eq SdsAB. subst.
    apply subtyp_tmode.
    assert (Hok': ok (G1 & z ~ (typ_bind DsA) & G2)).
    apply (ok_middle_change _ Ok).
    lets Hn: (simple_narrow_has Has).
    specialize (Hn G1 G2 z DsA DsB eq_refl Ok eq_refl SdsAB).
    destruct Hn as [DA [DAHas Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [St1' St2']]]]. subst.
    apply subtyp_sel_r with S U.
    * admit. (**  <---------- TODO can that work??? *)
    * apply (IH1 _ _ _ _ _ Ok eq_refl SdsAB).
    * apply (IH2 _ _ _ _ _ Ok eq_refl SdsAB).
  (* case trans *)
  + introv St IH Ok Eq SdsAB.
    apply subtyp_trans with T2.
    - apply IH with (DsB := DsB); auto.
    - apply (subtyp_tmode (subtyp_refl _ T2)).
  (* case mode *)
  + introv Hst12 IH12 Hst23 IH23 Hok123 Heq HAB.
    specialize (IH12 G1 G2 z DsA DsB Hok123 Heq HAB).
    specialize (IH23 G1 G2 z DsA DsB Hok123 Heq HAB).
    apply (subtyp_trans IH12 IH23).

  (* subdec *)
  (* case subdec_typ *)
  + intros. apply* subdec_typ.
  (* case subdec_fld *)
  + intros. apply* subdec_fld.
  (* case subdec_mtd *)
  + intros. apply* subdec_mtd.

  (* subdecs *)
  (* case subdecs_empty: auto *)
  (* case subdecs_push *)
  + introv Hb Hsd IHsd Hsds IHsds Hok123 Heq HAB.
    apply (subdecs_push n Hb).
    apply (IHsd  _ _ _ _ _ Hok123 Heq HAB).
    apply (IHsds _ _ _ _ _ Hok123 Heq HAB).
Qed.


(* ###################################################################### *)
(** ** Transitivity push-back *)

(* ... transitivity in notrans mode, but no p.L in middle ... *)

Inductive notsel: typ -> Prop :=
  | notsel_top  : notsel typ_top
  | notsel_bot  : notsel typ_bot
  | notsel_bind : forall Ds, notsel (typ_bind Ds).

Hint Constructors notsel.

Lemma subdec_trans: forall G D1 D2 D3,
  subdec G D1 D2 -> subdec G D2 D3 -> subdec G D1 D3.
Proof.
  introv H12 H23. inversions H12; inversions H23; constructor;
  solve [ assumption | (eapply subtyp_trans; eassumption)].
Qed.

Lemma subdecs_trans: forall G Ds1 Ds2 Ds3,
  subdecs G Ds1 Ds2 ->
  subdecs G Ds2 Ds3 ->
  subdecs G Ds1 Ds3.
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
  + inversions H23. inversions H12. apply subdecs_bot.
Qed.

Lemma subtyp_trans_notrans: forall G T1 T2 T3,
  ok G -> notsel T2 -> subtyp notrans G T1 T2 -> subtyp notrans G T2 T3 -> 
  subtyp notrans G T1 T3.
Proof.
  introv Hok Hnotsel H12 H23.

  inversion Hnotsel; subst.
  (* case top *)
  + inversion H23; subst.
    - apply (subtyp_top G T1).
    - apply (subtyp_top G T1).
    - apply (subtyp_sel_r H H0 (subtyp_trans (subtyp_tmode H12) H1)).
  (* case bot *)
  + inversion H12; subst.
    - apply (subtyp_bot G T3).
    - apply (subtyp_bot G T3).
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
      rename H0 into Sds12, H4 into Sds23.
      specialize (Sds12 z zL).
      specialize (Sds23 z zL0).
      assert (Hok' : ok (G & z ~ typ_bind Ds1)) by auto.
      assert (Hok'': ok (G & z ~ typ_bind Ds2)) by auto.
      lets Sds23' : (pr_narrow_subdecs Sds12 Sds23).
      apply (subdecs_trans Sds12 Sds23').
    - (* bind <: bind <: sel  *)
      assert (H1S: subtyp oktrans G (typ_bind Ds1) S) by
        apply (subtyp_trans (subtyp_tmode H12) H5).
      apply (subtyp_sel_r H3 H4 H1S).
    - (* sel  <: bind <: bind *)
      assert (HU2: subtyp oktrans G U (typ_bind Ds2))
        by apply (subtyp_trans H0 (subtyp_tmode H23)).
      apply (subtyp_sel_l H HU2). 
    - (* sel  <: bind <: sel  *)
      apply (subtyp_sel_r H1 H5).
      apply (subtyp_trans (subtyp_tmode H12) H6).
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
      has stable G (trm_var (avar_f v)) X (dec_typ Lo Hi) ->
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
      has stable G (trm_var (avar_f v)) X (dec_typ Lo Hi) ->
      subtyp oktrans G Lo Hi -> (* <-- realizable bounds *)
      follow_lb G (typ_sel (pth_var (avar_f v)) X) U ->
      follow_lb G Lo U.

Hint Constructors follow_ub.
Hint Constructors follow_lb.

Lemma invert_follow_lb: forall G T1 T2,
  follow_lb G T1 T2 -> 
  T1 = T2 \/ 
    exists v1 X1 v2 X2 Hi, (typ_sel (pth_var (avar_f v2)) X2) = T2 /\
      has stable G (trm_var (avar_f v1)) X1 (dec_typ T1 Hi) /\
      subtyp oktrans G T1 Hi /\
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
  subtyp notrans G typ_top C \/
  (notsel B /\ subtyp notrans G B C). (* TODO can we replace this subtyp by a subdecs? *)

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

Lemma chain3subtyp: forall G C1 C2 D, 
  subtyp notrans G C1 C2 ->
  follow_lb G C2 D -> 
  subtyp notrans G C1 D.
Proof.
  introv Hst Hflb.
  induction Hflb.
  + assumption.
  + apply IHHflb.
  apply (subtyp_sel_r H H0 (subtyp_tmode Hst)).
Qed.

Lemma chain2subtyp: forall G B1 B2 C D,
  ok G ->
  subtyp notrans G B1 B2 ->
  st_middle G B2 C ->
  follow_lb G C D ->
  subtyp notrans G B1 D.
Proof.
  introv Hok Hst Hm Hflb.
  unfold st_middle in Hm.
  destruct Hm as [Hm | [Hm | [Hm1 Hm2]]]; subst.
  apply (chain3subtyp Hst Hflb).
  apply (chain3subtyp (subtyp_trans_notrans Hok notsel_top (subtyp_top G B1) Hm) Hflb).
  apply (chain3subtyp (subtyp_trans_notrans Hok Hm1 Hst Hm2) Hflb).
Qed.

Lemma chain1subtyp: forall G A D,
  ok G ->
  chain G A D ->
  subtyp notrans G A D.
Proof.
  introv Hok Hch. destruct Hch as [B [C [Hfub [Hm Hflb]]]].
  induction Hfub.
  apply (chain2subtyp Hok (subtyp_refl_all notrans G T) Hm Hflb).
  apply (subtyp_sel_l H).
  apply subtyp_tmode.
  apply (IHHfub Hok Hm Hflb).
Qed.

Print Assumptions chain1subtyp.

(* prepend an oktrans to chain ("utrans0*") *)
Lemma prepend_chain: forall G A1 A2 D,
  ok G ->
  subtyp oktrans G A1 A2 ->
  chain G A2 D ->
  chain G A1 D.
Proof.
  introv Hok St. unfold chain in *. unfold st_middle in *. 
  induction St; intro Hch.
  + (* case refl *)
    assumption.
  + (* case top *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]]; subst.
    exists T typ_top.
    auto 10.
    exists T C.
    auto 10.
    exists T C.
    auto 10.
  + (* case bot *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    exists typ_bot C.
    auto 10.
  + (* case bind *)
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
    exists (typ_bind Ds1) C.
    assert (subtyp notrans G (typ_bind Ds1) (typ_bind Ds2)). {
      apply subtyp_bind with L. assumption.
    }
    destruct Hch2 as [Hch2 | [Hch2 | [Hch2a Hch2b]]].
    - subst. auto 10.
    - auto 10.
    - set (Hst := (subtyp_trans_notrans Hok (notsel_bind _) H0 Hch2b)). auto 10.
  + (* case asel_l *)
    specialize (IHSt Hok Hch).
    destruct IHSt as [B [C [IH1 [IH2 IH3]]]].
    exists B C.
    split.
    apply (follow_ub_cons H IH1).
    split; assumption.
  (*
  + (* case asel_r *) 
    apply (IHSt2 Hok). apply (IHSt1 Hok).
    destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
    exists B C.
    inversions Hch1. (* oops, cannot prove follow_ub G U (typ_sel (pth_var (avar_f x)) L)*)
  *)
  + (* case asel_r *) 
    set (Hch' := Hch).
    destruct Hch' as [B [C [Hch1 [Hch2 Hch3]]]].
    inversion Hch1; subst.
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
  + (* case mode *)
    apply (IHSt Hok Hch).
  + (* case trans *)
    apply (IHSt1 Hok). apply (IHSt2 Hok Hch).
Qed.

Lemma oktrans2notrans: forall G T1 T3,
  ok G -> subtyp oktrans G T1 T3 -> subtyp notrans G T1 T3.
Proof.
  introv Hok Hst.
  assert (Hch: chain G T1 T3).
  apply (prepend_chain Hok Hst (empty_chain _ _)).
  apply (chain1subtyp Hok Hch).
Qed.

Print Assumptions oktrans2notrans.


(* ###################################################################### *)
(** ** exp_preserves_sub *)

Lemma open_decs_nil: forall z, (open_decs z decs_nil) = decs_nil.
Proof.
  intro z. reflexivity.
Qed.

Lemma open_decs_bot: forall z, (open_decs z decs_bot) = decs_bot.
Proof.
  intro z. reflexivity.
Qed.

Inductive decs_nonempty: decs -> Prop :=
  | decs_nonempty_cons: forall n D Ds,
      decs_nonempty (decs_cons n D Ds)
  | decs_nonempty_bot:
      decs_nonempty (decs_bot).

Definition notin_hist(T: typ)(h: list (pth * label)): Prop :=
   (exists p L, T = typ_sel p L /\ ~List.In (p, L) h)
\/ notsel T.

Hypothesis pL_eq_dec : forall x y : (pth*label), {x = y}+{x <> y}.

Definition remove := List.remove pL_eq_dec.

Lemma remove_notin_id: forall l x,
  ~ List.In x l -> remove x l = l.
Proof.
  intro l. induction l; intros.
  + reflexivity.
  + unfold remove, List.remove. destruct (pL_eq_dec x a) as [Eq | Ne].
    * subst. false H. unfold List.In. auto.
    * f_equal. apply IHl. intro. apply H. unfold List.In. right. exact H0.
Qed.

Lemma remove_preserves_notin: forall l x y,
  ~ List.In x l -> ~ List.In x (remove y l).
Admitted.

Lemma nonempty_exp_shrink_history: forall m G T h Ds,
  exp m G T h Ds ->
  decs_nonempty Ds ->
  forall p L, exp m G T (remove (p, L) h) Ds.
Proof.
  introv Exp. induction Exp; intros.
  + apply exp_top.
  + apply exp_bot.
  + apply exp_bind.
  + destruct H1 as [n D Ds|].
    - specialize (IHExp (decs_nonempty_cons n D Ds) p L0).
      simpl in IHExp. destruct (pL_eq_dec (p, L0) (pth_var (avar_f x), L)) as [Eq | Ne].
      { inversions Eq. apply (exp_sel H).
        * apply List.remove_In.
        * rewrite (remove_notin_id _ _ H0). exact Exp. }
      { refine (exp_sel H _ IHExp). apply remove_preserves_notin. apply H0. }
    - specialize (IHExp decs_nonempty_bot p L0).
      simpl in IHExp. destruct (pL_eq_dec (p, L0) (pth_var (avar_f x), L)) as [Eq | Ne].
      { inversions Eq. apply (exp_sel H).
        * apply List.remove_In.
        * rewrite (remove_notin_id _ _ H0). exact Exp. }
      { refine (exp_sel H _ IHExp). apply remove_preserves_notin. apply H0. }
  + inversion H0. (* contradiction *)
  + apply exp_smode. apply* IHExp.
Qed.

Lemma remove_head: forall l x, l = remove x (List.cons x l). Admitted.

Lemma nonempty_exp_doesnt_need_history: forall h m G T Ds,
  exp m G T h Ds ->
  decs_nonempty Ds ->
  exp m G T nil Ds.
Proof.
  intro h. induction h; introv Exp Nem.
  + exact Exp.
  + apply* IHh. rewrite (remove_head h a). destruct a as [p L].
    apply (nonempty_exp_shrink_history Exp Nem).
Qed.

Print Assumptions nonempty_exp_doesnt_need_history.


Lemma supertype_of_top_expands_to_decs_nil: forall G m1 m2 T2,
  ok G ->
  subtyp m2 G typ_top T2 ->
  exp m1 G T2 nil decs_nil.
Proof.
Admitted.

Lemma invert_empty_expansion: forall m G T h,
   exp m G T h decs_nil ->
   (subtyp oktrans G typ_top T)
\/ (exists p L, T = typ_sel p L /\ List.In (p, L) h).
Proof.
Admitted.

(* TODO this only holds if T is well-formed, but we first need such a jugment... *)
Lemma exp_total: forall G T h,
  exists Ds, exp unstable G T h Ds.
Admitted.

Lemma exp_preserves_sub_pr: forall m2 G T1 T2 Ds1 Ds2,
  ok G ->
  subtyp m2 G T1 T2 ->
  exp unstable G T1 nil Ds1 ->
  exp unstable G T2 nil Ds2 ->
  exists L, forall z, z \notin L -> 
            subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2).
Proof.
  (* We don't use the [induction] tactic because we want to intro everything ourselves: *)
  intros m2 G T1 T2 Ds1 Ds2 Ok St. gen_eq m1: unstable.
  gen m2 G T1 T2 St m1 Ds1 Ds2 Ok.
  apply (subtyp_ind (fun m2 G T1 T2 => forall m1 Ds1 Ds2,
    ok G ->
    m1 = unstable ->
    exp m1 G T1 nil Ds1 ->
    exp m1 G T2 nil Ds2 ->
    exists L, forall z : var, z \notin L ->
              subdecs (G & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2))).
  + (* case subtyp_refl *)
    introv Ok Eq Exp1 Exp2. subst.
    lets Eq: (exp_unique Exp1 Exp2).
    exists vars_empty. intros z zL. subst. apply subdecs_refl.
  + (* case subtyp_top *)
    intros m G T Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    inversions Exp2. inversions H.
    exists vars_empty. intros z zL. unfold open_decs, open_rec_decs. apply subdecs_empty.
  + (* case subtyp_bot *)
    intros m G T Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    inversions Exp1. inversions H.
    exists vars_empty. intros z zL. apply subdecs_bot.
  + (* case subtyp_bind *)
    intros L G Ds1' Ds2' Sds m1 Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    inversions Exp1. inversions H. inversions Exp2. inversions H.
    exists L. intros z zL. apply (Sds z zL).
  + (* case subtyp_sel_l *)
    intros G x L Lo2 Hi2 T Has2 St IHSt m Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    apply invert_exp_sel in Exp1. destruct Exp1 as [Lo1 [Hi1 [Has1 Exp1]]].
    lets Eq: (has_unique Has2 Has1).
    inversions Eq.
    specialize (IHSt Ds1 Ds2 Ok eq_refl).
    (* If exp didn't have history, we could now just apply (IHSt Exp1 Exp2),
       but since it does, we have to modify it before applying IHSt (2nd and 3rd case),
       or do something else without using IHSt (1st case) *)
    destruct Ds1 as [|n D1 Ds1|].
    - apply invert_empty_expansion in Exp1. destruct Exp1 as [St' | [p0 [L0 [Eq HIn]]]].
      * lets St'': (subtyp_trans St' St).
        lets Exp2': (supertype_of_top_expands_to_decs_nil Ok St'').
        lets Eq: (exp_unique Exp2 Exp2'). subst Ds2. 
        exists vars_empty. intros z zL. unfold open_decs, open_rec_decs. 
        apply subdecs_empty.
      * subst Hi1.
        lets HIn': HIn.
        unfold List.In in HIn. destruct HIn as [Eq | F]; try false F.
        inversions Eq. (* Has1 shows that we have have an upper-bound loop of length 1 *)
        apply* IHSt. apply* exp_sel. apply exp_loop. exact HIn'.
    - apply* IHSt.
      apply (nonempty_exp_doesnt_need_history Exp1 (decs_nonempty_cons n D1 Ds1)).
    - apply* IHSt.
      apply (nonempty_exp_doesnt_need_history Exp1 decs_nonempty_bot).
  + (* case subtyp_sel_r *)
    intros m G x L Lo Hi T Has St1 IHSt1 St2 IHSt2 Ds1 Ds2 Ok Eq Exp1 Exp2. subst.
    apply invert_exp_sel in Exp2. destruct Exp2 as [Lo' [Hi' [Has' Exp2]]].
    lets Eq: (has_unique Has' Has).
    inversions Eq.
    assert (ExpLo: exists DsLo, exp pr G Lo nil DsLo) by apply exp_total.
    destruct ExpLo as [DsLo ExpLo].
    specialize (IHSt2 Ds1 DsLo Ok eq_refl Exp1 ExpLo). destruct IHSt2 as [L2 IHSt2].
    (* cannot yet specialize IHSt1 with Exp2, because Exp2 has non-empty history *)
    destruct Ds2 as [|n Ds2h Ds2t|] eqn: Eq.
    - exists vars_empty. intros z zL. unfold open_decs, open_rec_decs. apply subdecs_empty.
    - lets Exp2': (nonempty_exp_doesnt_need_history Exp2 (decs_nonempty_cons n Ds2h Ds2t)).
      rewrite <- Eq in *.
      specialize (IHSt1 DsLo Ds2 Ok eq_refl ExpLo Exp2'). destruct IHSt1 as [L1 IHSt1].
      exists (L1 \u L2 \u dom G). intros z zL1L2.
      auto_specialize.
      assert (Ok': ok (G & z ~ typ_bind DsLo)) by auto.
      lets IHSt1': (pr_narrow_subdecs IHSt2 IHSt1). (* <-------- NARROWING *)
      apply (subdecs_trans IHSt2 IHSt1').
    - lets Exp2': (nonempty_exp_doesnt_need_history Exp2 decs_nonempty_bot). subst.
      specialize (IHSt1 DsLo decs_bot Ok eq_refl ExpLo Exp2'). destruct IHSt1 as [L1 IHSt1].
      exists (L1 \u L2 \u dom G). intros z zL1L2.
      auto_specialize.
      assert (Ok': ok (G & z ~ typ_bind DsLo)) by auto.
      lets IHSt1': (pr_narrow_subdecs IHSt2 IHSt1). (* <-------- NARROWING *)
      apply (subdecs_trans IHSt2 IHSt1').
  + (* case subtyp_mode *)
    intros. apply* H0.
  + (* case subtyp_trans *)
    intros m G T1 T2 T3 St12 IH12 St23 IH23 Ds1 Ds3 Ok Eq Exp1 Exp3. subst.
    assert (Exp2: exists Ds2, exp pr G T2 nil Ds2) by apply exp_total.
    destruct Exp2 as [Ds2 Exp2].
    specialize (IH12 _ _ Ok eq_refl Exp1 Exp2). destruct IH12 as [L1 IH12].
    specialize (IH23 _ _ Ok eq_refl Exp2 Exp3). destruct IH23 as [L2 IH23].
    exists (L1 \u L2 \u dom G). intros z zL1L2.
    auto_specialize.
    assert (Ok': ok (G & z ~ typ_bind Ds2)) by auto.
    lets IHS23': (pr_narrow_subdecs IH12 IH23).  (* <-------- NARROWING *)
    apply (subdecs_trans IH12 IHS23').
Qed.

Print Assumptions exp_preserves_sub_pr.


(* ###################################################################### *)
(** ** Full-fledged narrowing *)

Lemma narrowing:
   (forall m G T h Ds2, exp m G T h Ds2 -> forall G1 G2 x S1 S2,
    m = pr ->
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    exists L Ds1,
    exp pr (G1 & x ~ S1 & G2) T h Ds1 /\ 
    forall z, z \notin L ->
    subdecs pr (G1 & x ~ S1 & G2 & z ~ typ_bind Ds1) (open_decs z Ds1) (open_decs z Ds2))
/\ (forall m G t l D2, has m G t l D2 ->  forall G1 G2 x S1 S2,
    m = pr ->
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    exists D1, has pr (G1 & x ~ S1 & G2) t l D1 /\ subdec pr (G1 & x ~ S1 & G2) D1 D2)
/\ (forall m1 m2 G T1 T2, subtyp m1 m2 G T1 T2 ->  forall G1 G2 x S1 S2,
    m1 = pr ->
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    subtyp pr oktrans (G1 & x ~ S1 & G2) T1 T2)
/\ (forall m G D1 D2, subdec m G D1 D2 ->  forall G1 G2 x S1 S2,
    m = pr ->
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    subdec pr (G1 & x ~ S1 & G2) D1 D2)
/\ (forall m G Ds1 Ds2, subdecs m G Ds1 Ds2 ->  forall G1 G2 x S1 S2,
    m = pr ->
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    subdecs pr (G1 & x ~ S1 & G2) Ds1 Ds2)
/\ (forall G t T2, ty_trm G t T2 ->  forall G1 G2 x S1 S2,
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    exists T1, ty_trm (G1 & x ~ S1 & G2) t T1 /\ subtyp pr oktrans (G1 & x ~ S1 & G2) T1 T2)
/\ (forall G d D2, ty_def G d D2 ->  forall G1 G2 x S1 S2,
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    exists D1, ty_def (G1 & x ~ S1 & G2) d D1 /\ subdec pr (G1 & x ~ S1 & G2) D1 D2)
/\ (forall G ds Ds2, ty_defs G ds Ds2 ->  forall G1 G2 x S1 S2,
    ok G ->
    G = G1 & x ~ S2 & G2 ->
    subtyp pr oktrans G1 S1 S2 ->
    exists Ds1, ty_defs (G1 & x ~ S1 & G2) ds Ds1 /\ subdecs pr (G1 & x ~ S1 & G2) Ds1 Ds2).
Proof.
  apply ty_mutind.
  + (* case exp_top *)
    intros. exists vars_empty decs_nil. split.
    - apply exp_top.
    - intros. rewrite open_decs_nil. apply subdecs_empty.
  + (* case exp_bot *)
    intros. exists vars_empty decs_bot. split.
    - apply exp_bot.
    - intros. rewrite open_decs_bot. apply subdecs_bot.
  + (* case exp_bind *)
    intros. subst. exists vars_empty Ds. split.
    - apply exp_bind.
    - intros. apply subdecs_refl.
  + (* case exp_sel *)
    intros m G z L h Lo2 Hi2 Ds2 Has IHHas NIn Exp IHExp G1 G2 x S1 S2 E1 Ok2 E2 St. subst.
    specialize (IHHas _ _ _ _ _ eq_refl Ok2 eq_refl St).
    specialize (IHExp _ _ _ _ _ eq_refl Ok2 eq_refl St).
    destruct IHHas as [D1 [IHHas Sd]].
    destruct IHExp as [L0 [Dsm [IHExp Sds2]]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo21 StHi12]]]]. subst D1.
    destruct (exp_total (G1 & x ~ S1 & G2) Hi1 ((pth_var (avar_f z), L) :: h))
      as [Ds1 Exp1].
    exists L0 Ds1. apply (conj (exp_sel IHHas NIn Exp1)).
    intros y yL0. specialize (Sds2 y yL0).
    assert (Ok1: ok (G1 & x ~ S1 & G2)) by apply okadmit.
    destruct Dsm as [|n Dsmh Dsmt|] eqn: Eq.
    - lets Sds1: (subdecs_empty pr (G1 & x ~ S1 & G2 & y ~ typ_bind Ds1) (open_decs y Ds1)).
      rewrite open_decs_nil in Sds2.
      rewrite <- (open_decs_nil y) in Sds1.
      apply (pr_narrow_subdecs Sds1) in Sds2. (* <---- narrowing in conclusion of IH!!! *)
      apply (subdecs_trans Sds1 Sds2).
      (* Note: for the "weak" form of narrowing (currently called pr_narrow_subdecs),
         which is only for exp/has/subtyp/subdec/subdecs, we'd still have this exact same
         case, where we have to apply narrowing on the conclusion of the IH! *)
    - lets IHExp':(nonempty_exp_doesnt_need_history IHExp (decs_nonempty_cons n Dsmh Dsmt)).
      rewrite <- Eq in *.
    
  + (* case exp_loop *)
    intros. apply* exp_loop.
  + (* case has_trm *)
    intros. apply* has_trm.
  + (* case has_var *)
    intros. apply* has_var.
  + (* case has_pr *)
    intros. apply* has_pr.
  + (* case subtyp_refl *)
    intros. apply* subtyp_refl.
  + (* case subtyp_top *)
    intros. apply (subtyp_top _ _).
  + (* case subtyp_bot *)
    intros. apply (subtyp_bot _ _).
  + (* case subtyp_bind *)
    intros. apply_fresh subtyp_bind as z. auto.
  + (* case subtyp_asel_l *)
    intros. apply* subtyp_sel_l.
  + (* case subtyp_asel_r *)
    intros. apply* subtyp_sel_r.
  + (* case subtyp_tmode *)
    intros. apply* subtyp_tmode.
  + (* case subtyp_trans *)
    intros. admit.
  + (* case subdec_typ *)
    intros. admit.
  + (* case subdec_fld *)
    intros. admit.
  + (* case subdec_mtd *)
    intros. admit.
  + (* case subdecs_empty *)
    intros. apply subdecs_empty.
  + (* case subdecs_push *)
    intros. admit.
  + (* case subdecs_bot *)
    intros. apply subdecs_bot.
  + (* case ty_var *)
    intros. apply* ty_var.
  + (* case ty_sel *)
    intros. apply* ty_sel.
  + (* case ty_call *)
    intros. apply* ty_call.
  + (* case ty_new *)
    intros. apply* ty_new.
  + (* case ty_sbsm *)
    intros. apply ty_sbsm with T; auto.
  + (* case ty_typ *)
    intros. apply ty_typ.
  + (* case ty_fld *)
    intros. apply* ty_fld.
  + (* case ty_mtd *)
    intros. apply* ty_mtd.
  + (* case ty_dsnil *)
    intros. apply ty_dsnil.
  + (* case ty_dscons *) 
    intros. apply* ty_dscons.
Qed.


(* ###################################################################### *)
(** ** More inversion lemmas *)

(* TODO does not hold currently! *)
Axiom top_subtyp_of_empty_bind: forall m1 m2 G, 
  subtyp m1 m2 G typ_top (typ_bind decs_nil).

Lemma exp_to_subtyp: forall G T Ds,
  exp ip G T nil Ds ->
  subtyp ip oktrans G T (typ_bind Ds).
Proof.
  introv Exp. gen_eq m: ip. induction Exp; intro Eq; subst.
  + apply top_subtyp_of_empty_bind.
  + apply subtyp_tmode. apply subtyp_bot.
  + apply subtyp_refl_all.
  + specialize (IHExp eq_refl). apply subtyp_tmode. apply (subtyp_sel_l H IHExp).
  + apply subtyp_trans with typ_top. 
    - apply subtyp_tmode, subtyp_top.
    - apply top_subtyp_of_empty_bind.
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

Lemma ty_def_sbsm: forall G d D1 D2,
  ok G ->
  ty_def G d D1 ->
  subdec ip G D1 D2 ->
  ty_def G d D2.
Proof.
  introv Ok Ty Sd. destruct Ty; inversion Sd; try discriminate; subst; clear Sd.
  + apply ty_typ.
  + apply (ty_fld (ty_sbsm H H3)).
  + apply ty_mtd with (L \u dom G).
    intros x Fr. assert (xL: x \notin L) by auto. specialize (H x xL).
    assert (Okx: ok (G & x ~ S2)) by auto.
    apply (weaken_subtyp_end Okx) in H6.
    refine (ty_sbsm _ H6).
    (*
    refine (narrow_ty_trm _ H4 H).
    auto.
    *)
    admit.
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
