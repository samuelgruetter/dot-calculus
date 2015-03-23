
(*
lambda-DOT:
Lambda calculus with records, abstract type members, union and intersection types,
but without self references in types, and thus without recursive types nor recursive
functions.

nohas = no "has" judgment, but use type assignment instead
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

Module labels.
  Parameter L: typ_label.
  Parameter l: fld_label.
  Parameter m: mtd_label.
  Parameter apply: mtd_label.
End labels.

Inductive avar : Set :=
  | avar_b : nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f : var -> avar. (* free var ("name"), refers to store or ctx *)

Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ (* {D}, no self reference for the moment *)
  | typ_sel  : avar -> typ_label -> typ (* p.L *)
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



(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k) 
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar) : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top       => typ_top
  | typ_bot       => typ_bot
  | typ_rcd D     => typ_rcd (open_rec_dec k u D)
  | typ_sel a L   => typ_sel (open_rec_avar k u a) L
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

Fixpoint fv_typ (T: typ) { struct T } : vars :=
  match T with
  | typ_top       => \{}
  | typ_bot       => \{}
  | typ_rcd D     => (fv_dec D)
  | typ_sel a L   => (fv_avar a)
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

(* Don't try out these:
   - allow transitivity only with a no-path-type in the middle (simp),
     add mode where path type in the middle is allowed (full)
     simp is not strong enough for what we need in invert_ty_var
     simp <=> full should hold, but is very hard to prove because imprecision
     on middle p.L
   - require that p.L in the middle of transitivity rule has good bounds
     doesnt' work because of imprecision (see below)
   *)

(*
Inductive trans_middle_ok: ctx -> typ -> Prop :=
| trans_middle_ok_top: forall G, trans_middle_ok G typ_top
| trans_middle_ok_bot: forall G, trans_middle_ok G typ_bot
| trans_middle_ok_rcd: forall G D, trans_middle_ok G (typ_rcd D)
| trans_middle_ok_sel: forall G p L, 
    ty_trm G (pth2trm p) X ->
    subtyp G X (dec_typ L Lo Hi) -> (* imprecise and thus useless !! *)
    trans_middle_ok G (typ_sel p L)
| trans_middle_ok_and: forall G T1 T2, trans_middle_ok G (typ_and T1 T2)
| trans_middle_ok_or:  forall G T1 T2, trans_middle_ok G (typ_or  T1 T2).
*)

Inductive subtyp: ctx -> typ -> typ -> Prop :=
  | subtyp_refl: forall G T,
      subtyp G T T
  | subtyp_top: forall G T,
      subtyp G T typ_top
  | subtyp_bot: forall G T,
      subtyp G typ_bot T
  | subtyp_rcd: forall G D1 D2,
      subdec G D1 D2 ->
      subtyp G (typ_rcd D1) (typ_rcd D2)
  | subtyp_sel_l: forall G a L Lo Hi,
      ty_trm G (trm_var a) (typ_rcd (dec_typ L Lo Hi)) ->
      subtyp G (typ_sel a L) Hi
  | subtyp_sel_r: forall G a L Lo Hi,
      ty_trm G (trm_var a) (typ_rcd (dec_typ L Lo Hi)) ->
      subtyp G Lo (typ_sel a L)
  | subtyp_and: forall G S T1 T2,
      subtyp G S T1 ->
      subtyp G S T2 ->
      subtyp G S (typ_and T1 T2)
  | subtyp_and_l: forall G T1 T2 U,
      subtyp G T1 U ->
      subtyp G (typ_and T1 T2) U
  | subtyp_and_r: forall G T1 T2 U,
      subtyp G T2 U ->
      subtyp G (typ_and T1 T2) U
  | subtyp_or: forall G T1 T2 S,
      subtyp G T1 S ->
      subtyp G T2 S ->
      subtyp G (typ_or T1 T2) S
  | subtyp_or_l: forall G U T1 T2,
      subtyp G U T1 ->
      subtyp G U (typ_or T1 T2)
  | subtyp_or_r: forall G U T1 T2,
      subtyp G U T2 ->
      subtyp G U (typ_or T1 T2)
(* needed?
  ! subtyp_and_rcd: forall G D1 D2 D3,
      D1 && D2 == D3 ->
      subtyp G (typ_and (typ_rcd D1) (typ_rcd D2)) (typ_rcd D3)

  ! subtyp_or_rcd: forall G D1 D2 D3,
      D1 || D2 == D0 ->
      subtyp G (typ_rcd D0) (typ_or (typ_rcd D1) (typ_rcd D2))
  ! subtyp_trans: forall G T1 T2 T3,
      subtyp G T1 T2 ->
      subtyp G T2 T3 ->
      subtyp G T1 T3
*)
with subdec: ctx -> dec -> dec -> Prop :=
  | subdec_typ: forall G L Lo1 Hi1 Lo2 Hi2,
      subtyp G Lo2 Lo1 ->
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
      subtyp G T (typ_rcd (dec_fld l U)) ->
      ty_trm G (trm_sel t l) U
  | ty_call: forall G t T m U V u,
      ty_trm G t T ->
      subtyp G T (typ_rcd (dec_mtd m U V)) ->
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

Scheme subtyp_mut  := Induction for subtyp  Sort Prop
with   subdec_mut  := Induction for subdec  Sort Prop
with   ty_trm_mut  := Induction for ty_trm  Sort Prop
with   ty_def_mut  := Induction for ty_def  Sort Prop
with   ty_defs_mut := Induction for ty_defs Sort Prop
with   can_add_mut := Induction for can_add Sort Prop.
Combined Scheme ty_mutind from subtyp_mut, subdec_mut,
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

Hint Constructors subtyp subdec ty_trm ty_def ty_defs can_add.
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

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top     => typ_top
  | typ_bot     => typ_bot
  | typ_rcd D   => typ_rcd (subst_dec z u D)
  | typ_sel a L => typ_sel (subst_avar z u a) L
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

Lemma subst_fresh_typ_dec_decs: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ) /\
  (forall d : dec , x \notin fv_dec  d  -> subst_dec  x y d  = d ).
Proof.
  intros x y. apply typ_mutind; intros; simpls; f_equal*. apply* subst_fresh_avar.
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

(* "open and then substitute" = "substitute and then open" *)
Lemma subst_open_commute_typ_dec_decs: forall x y u,
  (forall t : typ, forall n: Datatypes.nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) /\
  (forall d : dec , forall n: Datatypes.nat, 
     subst_dec x y (open_rec_dec n u d)
     = open_rec_dec n (subst_fvar x y u) (subst_dec x y d)).
Proof.
  intros. apply typ_mutind; intros; simpl; f_equal*. apply subst_open_commute_avar.
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

Lemma subst_undo_typ_dec_decs: forall x y,
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

(* TODO needs subtyping transitivity
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
*)

(* ###################################################################### *)
(** ** Weakening *)

Lemma weakening:
   (forall G T1 T2, subtyp G T1 T2 -> forall G1 G2 G3,
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
  apply ty_mutind; intros; subst; auto.
  apply* subtyp_sel_l.
  apply* subtyp_sel_r.
  apply ty_var. apply* binds_weaken.
  apply* ty_sel.
  apply* ty_call.
  apply ty_sbsm with T; auto.
  { apply_fresh ty_mtd as x.
    rewrite <- concat_assoc.
    refine (H x _ G1 G2 (G3 & x ~ S) _ _).
    - auto.
    - symmetry. apply concat_assoc.
    - rewrite concat_assoc. auto.
  }
  apply* can_refine_typ.
Qed.

Lemma weaken_subtyp_middle: forall G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp (G1      & G3) S U ->
  subtyp (G1 & G2 & G3) S U.
Proof.
  destruct weakening as [W _].
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
  destruct weakening as [_ [W _]].
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
  destruct weakening as [_ [W _]].
  rewrite <- (concat_empty_r G1) in Sd.
  specialize (W (G1 & empty) D1 D2 Sd G1 G2 empty).
  repeat progress rewrite concat_empty_r in *.
  apply (W eq_refl Ok).
Qed.

Lemma weaken_ty_trm_end: forall G1 G2 e T,
  ok (G1 & G2) -> ty_trm G1 e T -> ty_trm (G1 & G2) e T.
Proof.
  intros.
  destruct weakening as [_ [_ [W _]]].
  rewrite <- (concat_empty_r (G1 & G2)).
  apply (W (G1 & empty)); rewrite* concat_empty_r.
Qed.

Lemma weaken_ty_defs_end: forall G1 G2 is Ds,
  ok (G1 & G2) -> ty_defs G1 is Ds -> ty_defs (G1 & G2) is Ds.
Proof.
  intros.
  destruct weakening as [_ [_ [_ [_ [W _]]]]].
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


(* ###################################################################### *)

Lemma impossible_subtyping_first_try: forall G T1 T2,
  subtyp G T1 T2 ->
  (T1 = typ_top -> T2 = typ_bot \/
                   (exists D2, T2 = typ_rcd D2) -> False) /\
  ((exists D1, T1 = typ_rcd D1) -> T2 = typ_bot -> False).
Proof.
  introv St. induction St; (split;
  [ (intros Eq1 Eqs; destruct Eqs as [Eq2 | [D2' Eq2]])
  | (intros Eq1 Eq2; destruct Eq1 as [D1' Eq1])]);
  subst; try discriminate.
  + (* case subtyp_trans:  top <: T2 <: bot *)
    destruct IHSt1 as [IH1 IH2]. destruct IHSt2 as [IH3 IH4].
    specialize (IH1 eq_refl).
    destruct T2; eauto.
    - (* case top <: p.L <: bot *)
      rename t into L.
      (* exclude because we will require that path types not in middle of subtyp_trans *)
      admit.
    - (* case top <: U & V <: bot *)
      (* IHs not strong enough!! *)
      admit.
    - (* case top <: U | V <: bot *)
      (* IHs not strong enough!! *)
      admit.
  + (* case subtyp_trans: top <: T2 <: (typ_rcd D2) *)
    rename D2' into D2.
    destruct IHSt1 as [IH1 IH2]. destruct IHSt2 as [IH3 IH4].
    specialize (IH1 eq_refl).
    admit. (* basically the same story as above *)
  + (* case subtyp_trans: (typ_rcd D1) <: T2 <: typ_bot *)
    rename D1' into D1.
    destruct IHSt1 as [IH1 IH2]. destruct IHSt2 as [IH3 IH4].
    admit. (* basically the same story as above *)
Qed.

(* So instead of "T = typ_bot", "T = typ_top" and "exists D, T = typ_rcd D", 
   we have to use more general propositions: *)

Inductive is_bot: typ -> Prop :=
| is_bot_bot: is_bot typ_bot
| is_bot_and_l: forall T1 T2, is_bot T1 -> is_bot (typ_and T1 T2)
| is_bot_and_r: forall T1 T2, is_bot T2 -> is_bot (typ_and T1 T2)
| is_bot_or: forall T1 T2, is_bot T1 -> is_bot T2 -> is_bot (typ_or T1 T2).

Inductive is_top: typ -> Prop :=
| is_top_top: is_top typ_top
| is_top_and: forall T1 T2, is_top T1 -> is_top T2 -> is_top (typ_and T1 T2)
| is_top_or_l: forall T1 T2, is_top T1 -> is_top (typ_or T1 T2)
| is_top_or_r: forall T1 T2, is_top T2 -> is_top (typ_or T1 T2).

Inductive is_rcd: typ -> Prop :=
| is_rcd_rcd:   forall D, is_rcd (typ_rcd D)
| is_rcd_and:   forall T1 T2, is_rcd T1 -> is_rcd T2 -> is_rcd (typ_and T1 T2)
| is_rcd_and_l: forall T1 T2, is_rcd T1 -> is_top T2 -> is_rcd (typ_and T1 T2)
| is_rcd_and_r: forall T1 T2, is_top T1 -> is_rcd T2 -> is_rcd (typ_and T1 T2)
| is_rcd_or:    forall T1 T2, is_rcd T1 -> is_rcd T2 -> is_rcd (typ_or  T1 T2)
| is_rcd_or_l:  forall T1 T2, is_rcd T1 -> is_bot T2 -> is_rcd (typ_or  T1 T2)
| is_rcd_or_r:  forall T1 T2, is_bot T1 -> is_rcd T2 -> is_rcd (typ_or  T1 T2).

Hint Constructors is_bot is_top is_rcd.

Lemma is_top_is_bot_mutex: forall T, is_top T -> is_bot T -> False.
Proof.
  intro T. induction T; intros It Ib; inversions It; inversions Ib; auto.
Qed.

Lemma is_top_is_rcd_mutex: forall T, is_top T -> is_rcd T -> False.
Proof.
  intro T. induction T; intros It Ir; inversions It; inversions Ir; auto.
  apply* is_top_is_bot_mutex.
  apply* is_top_is_bot_mutex.
Qed.

Lemma is_rcd_is_bot_mutex: forall T, is_rcd T -> is_bot T -> False.
  intro T. induction T; intros Ir Ib; inversions Ir; inversions Ib; auto.
  apply* is_top_is_bot_mutex.
  apply* is_top_is_bot_mutex.
Qed.

(* "no_path_types T" means that T contains no path types (but T's members can) *)
Inductive no_path_types: typ -> Prop :=
| no_path_types_top: no_path_types typ_top
| no_path_types_bot: no_path_types typ_bot
| no_path_types_rcd: forall D, no_path_types (typ_rcd D)
| no_path_types_and: forall T1 T2,
    no_path_types T1 -> no_path_types T2 -> no_path_types (typ_and T1 T2)
| no_path_types_or: forall T1 T2,
    no_path_types T1 -> no_path_types T2 -> no_path_types (typ_or T1 T2).

Lemma no_path_types_cases: forall T, no_path_types T ->
  is_top T \/ is_bot T \/ is_rcd T.
Proof.
  intro T. induction T; intro Np; inversions* Np.
Qed.

Lemma impossible_subtyping: forall G T1 T2,
  subtyp G T1 T2 ->
  (is_top T1 -> is_bot T2 \/ is_rcd T2 -> False) /\
  (is_rcd T1 -> is_bot T2 -> False).
Proof.
  introv St. induction St; (split;
  [ (intros It P; destruct P as [Ib | Ir])
  | (intros Ir Ib)]);
  match goal with
  | H: is_top (typ_and ?A ?B) |- _ => inversions H
  | H: is_top (typ_or  ?A ?B) |- _ => inversions H
  | H: is_bot (typ_and ?A ?B) |- _ => inversions H
  | H: is_bot (typ_or  ?A ?B) |- _ => inversions H
  | H: is_rcd (typ_and ?A ?B) |- _ => inversions H
  | H: is_rcd (typ_or  ?A ?B) |- _ => inversions H
  | _ => idtac
  end;
  match goal with
  | H1: is_top ?A, H2: is_bot ?A |- _ => apply (is_top_is_bot_mutex H1 H2)
  | H1: is_top ?A, H2: is_rcd ?A |- _ => apply (is_top_is_rcd_mutex H1 H2)
  | H1: is_rcd ?A, H2: is_bot ?A |- _ => apply (is_rcd_is_bot_mutex H1 H2)
  | _ => idtac
  end;
  try solve [inversions* Ib];
  try solve [inversions* Ir];
  try solve [inversions* It];
  try (destruct IHSt1 as [IH1 IH2]; destruct IHSt2 as [IH3 IH4]);
  try (inversions H; inversions H2);
  assert (Np: no_path_types T2) by admit; (* <----------- *)
  apply no_path_types_cases in Np;
  destruct Np as [Np | [Np | Np]]; auto.
Qed.

