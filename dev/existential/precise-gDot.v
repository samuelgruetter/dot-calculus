
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
  | typ_tdec : typ_label -> typ -> typ -> typ (* { L: S..U } *)
  | typ_mdec : mtd_label -> typ -> typ -> typ (* { m: S->U } *)
  | typ_sel  : avar -> typ_label -> typ (* x.L *)
  | typ_and  : typ -> typ -> typ
  | typ_or   : typ -> typ -> typ.

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
  | typ_tdec L T U => typ_tdec L (open_rec_typ k u T) (open_rec_typ k u U)
  | typ_mdec m T U => typ_mdec m (open_rec_typ k u T) (open_rec_typ k u U)
  | typ_sel x L    => typ_sel (open_rec_avar k u x) L
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1) (open_rec_typ k u T2)
  | typ_or  T1 T2  => typ_or  (open_rec_typ k u T1) (open_rec_typ k u T2)
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
  | typ_tdec L T U => (fv_typ T) \u (fv_typ U)
  | typ_mdec m T U => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv_avar x)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_or  T U    => (fv_typ T) \u (fv_typ U)
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

(* "optimization" of typ_and (makes some proofs simpler). *)
Definition intersect_typ(T1 T2: typ): typ := match T1, T2 with
| typ_top, _ => T2
| _, typ_top => T1
| typ_bot, _ => typ_bot
| _, typ_bot => typ_bot
| _, _       => typ_and T1 T2
end.

Definition union_typ(T1 T2: typ): typ := match T1, T2 with
| typ_top, _ => typ_top
| _, typ_top => typ_top
| typ_bot, _ => T2
| _, typ_bot => T1
| _, _       => typ_or T1 T2
end.

(* If we run out of fuel or something goes wrong, we just return (typ_bot, typ_top).
   This should be sound because with such an {L: Bot..Top}, nothing useful can be done. *)
Fixpoint lookup_tdec(fuel1: nat)(G: ctx)(T: typ)(L: typ_label): (typ * typ) :=
match fuel1 with
| 0 => (typ_bot, typ_top)
| S fuel => match T with
  | typ_top => (typ_bot, typ_top)
  | typ_bot => (typ_top, typ_bot)
  | typ_tdec L1 T1 U1 => If L1 = L then (T1, U1) else (typ_bot, typ_top)
  | typ_mdec _ _ _ => (typ_bot, typ_top)
  | typ_sel a L1 => match a with
     | avar_f x =>
         match get x G with
         | Some X => let (Lo, Hi) := lookup_tdec fuel G X L1 in lookup_tdec fuel G Hi L
         | None => (typ_bot, typ_top)
         end
     | avar_b _ => (typ_bot, typ_top) (* T is not wf! *)
     end
  | typ_and T1 T2 =>
    let (Lo1, Hi1) := (lookup_tdec fuel G T1 L) in
    let (Lo2, Hi2) := (lookup_tdec fuel G T2 L) in
    ((union_typ Lo1 Lo2), (intersect_typ Hi1 Hi2))
  | typ_or T1 T2 =>
    let (Lo1, Hi1) := (lookup_tdec fuel G T1 L) in
    let (Lo2, Hi2) := (lookup_tdec fuel G T2 L) in
    ((intersect_typ Lo1 Lo2), (union_typ Hi1 Hi2))
  end
end.

(* For method member lookup, we have to be more careful than for type member lookup,
   because it has to agree with defs_has, so we can't just return {m: Bot->Top} if
   we don't find m or if something goes wrong, but we have to return None. *)
Fixpoint lookup_mdec(fuel1: nat)(G: ctx)(T: typ)(m: mtd_label): option (typ * typ) :=
match fuel1 with
| 0 => None
| S fuel => match T with
  | typ_top => None
  | typ_bot => Some (typ_top, typ_bot)
  | typ_tdec _ _ _ => None
  | typ_mdec m1 A1 R1 => If m1 = m then Some (A1, R1) else None
  | typ_sel a L => match a with
    | avar_f x => match get x G with
      | Some X => let (Lo, Hi) := (lookup_tdec fuel G X L) in lookup_mdec fuel G Hi m
      | None => None 
      end
    | avar_b _ => None  (* T is not wf *)
    end
  | typ_and T1 T2 => match (lookup_mdec fuel G T1 m), (lookup_mdec fuel G T2 m) with
    | None, o2 => o2
    | o1, None => o1
    | Some (A1, R1), Some (A2, R2) => Some ((union_typ A1 A2), (intersect_typ R1 R2))
    end
  | typ_or T1 T2 => match (lookup_mdec fuel G T1 m), (lookup_mdec fuel G T2 m) with
    | None, o2 => None
    | o1, None => None
    | Some (A1, R1), Some (A2, R2) => Some ((intersect_typ A1 A2), (union_typ R1 R2))
    end
  end
end.

Inductive subtyp: ctx -> typ -> typ -> Prop :=
  | subtyp_refl: forall G T,
      subtyp G T T
  | subtyp_top: forall G T,
      subtyp G T typ_top
  | subtyp_bot: forall G T,
      subtyp G typ_bot T
  | subtyp_tdec: forall G L T1 U1 T2 U2,
      subtyp G T2 T1 ->
      subtyp G U1 U2 ->
      subtyp G (typ_tdec L T1 U1) (typ_tdec L T2 U2)
  | subtyp_mdec: forall G m T1 U1 T2 U2,
      subtyp G T2 T1 ->
      subtyp G U1 U2 ->
      subtyp G (typ_mdec m T1 U1) (typ_mdec m T2 U2)
  | subtyp_sel_l: forall G x X L T U fuel,
      binds x X G ->
      lookup_tdec fuel G X L = (T, U) ->
      subtyp G T U -> (* <-- probably not needed, but keep for symmetry with subtyp_sel_r *)
      subtyp G (typ_sel (avar_f x) L) U
  | subtyp_sel_r: forall G x X L T U fuel,
      binds x X G ->
      lookup_tdec fuel G X L = (T, U) ->
      subtyp G T U -> (* <-- makes proofs a lot easier!! *)
      subtyp G T (typ_sel (avar_f x) L)
  | subtyp_and: forall G S T1 T2,
      subtyp G S T1 ->
      subtyp G S T2 ->
      subtyp G S (typ_and T1 T2)
  | subtyp_and_l: forall G T1 T2,
      subtyp G (typ_and T1 T2) T1
  | subtyp_and_r: forall G T1 T2,
      subtyp G (typ_and T1 T2) T2
  | subtyp_or: forall G T1 T2 S,
      subtyp G T1 S ->
      subtyp G T2 S ->
      subtyp G (typ_or T1 T2) S
  | subtyp_or_l: forall G T1 T2,
      subtyp G T1 (typ_or T1 T2)
  | subtyp_or_r: forall G T1 T2,
      subtyp G T2 (typ_or T1 T2)
  | subtyp_trans: forall G T1 T2 T3,
      subtyp G T1 T2 ->
      subtyp G T2 T3 ->
      subtyp G T1 T3.

Inductive ty_trm: ctx -> trm -> typ -> Prop :=
  | ty_var: forall G x T,
      binds x T G ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_call: forall G t T m U1 U2 V u fuel,
      ty_trm G t T ->
      lookup_mdec fuel G T m = Some (U2, V) ->
      ty_trm G u U1 ->
      subtyp G U1 U2 -> (* <-- explicit subsumption *)
      ty_trm G (trm_call t m u) V
  | ty_new: forall L G ds T u U,
      (forall x, x \notin L ->
         ty_defs (G & x ~ T) (open_defs x ds) T) ->
      (forall x, x \notin L ->
         ty_trm (G & x ~ T) (open_trm x u) U) ->
      ty_trm G (trm_new ds u) U
with ty_def: ctx -> def -> typ -> Prop :=
  | ty_tdef: forall G L T U,
      subtyp G T U -> (* <-- only allow realizable bounds *)
      ty_def G (def_typ L T U) (typ_tdec L T U)
  | ty_mdef: forall L m G T U1 U2 u,
      (forall x, x \notin L -> ty_trm (G & x ~ T) (open_trm x u) U1) ->
      subtyp G U1 U2 ->  (* <-- explicit subsumption *)
      ty_def G (def_mtd m T U2 u) (typ_mdec m T U2)
with ty_defs: ctx -> defs -> typ -> Prop :=
  | ty_defs_nil: forall G,
      ty_defs G defs_nil typ_top
  | ty_defs_cons: forall G ds d T1 T2,
      ty_defs G ds T1 ->
      ty_def G d T2 ->
      defs_hasnt ds (label_of_def d) -> (* <-- no duplicates *)
      ty_defs G (defs_cons ds d) (typ_and T1 T2).


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

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors subtyp ty_trm ty_def ty_defs.

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
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_tdec L T U => typ_tdec L (subst_typ z u T) (subst_typ z u U)
  | typ_mdec m T U => typ_mdec m (subst_typ z u T) (subst_typ z u U)
  | typ_sel x L    => typ_sel (subst_avar z u x) L
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_or  T1 T2  => typ_or  (subst_typ z u T1) (subst_typ z u T2)
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

Lemma subst_fresh_typ: forall x y,
  (forall T : typ , x \notin fv_typ  T  -> subst_typ  x y T  = T ).
Proof.
  intros x y T. induction T; intros; simpls; f_equal*. apply* subst_fresh_avar.
Qed.

Lemma subst_fresh_trm_def_defs: forall x y,
  (forall t : trm , x \notin fv_trm  t  -> subst_trm  x y t  = t ) /\
  (forall d : def , x \notin fv_def  d  -> subst_def  x y d  = d ) /\
  (forall ds: defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind; intros; simpls; f_equal*;
    (apply* subst_fresh_avar || apply* subst_fresh_typ).
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
Lemma subst_open_commute_typ: forall x y u,
  (forall t : typ, forall n: nat,
     subst_typ x y (open_rec_typ n u t)
     = open_rec_typ n (subst_fvar x y u) (subst_typ x y t)).
Proof.
  intros. induction t; intros; simpl; f_equal*. apply subst_open_commute_avar.
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
    (apply* subst_open_commute_avar || apply* subst_open_commute_typ).
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
  lets Q: (@subst_fresh_typ x u). rewrite* (Q T).
  unfold subst_fvar. case_var*.
Qed.

Lemma subst_undo_avar: forall x y,
  (forall a, y \notin fv_avar a -> (subst_avar y x (subst_avar x y a)) = a).
Proof.
  intros. unfold subst_avar, subst_fvar, open_avar, open_rec_avar; destruct a.
  + reflexivity.
  + unfold fv_avar in H. assert (y <> v) by auto. repeat case_if; reflexivity.
Qed.

Lemma subst_undo_typ: forall x y,
   (forall T , y \notin fv_typ  T  -> (subst_typ  y x (subst_typ  x y T )) = T ).
Proof.
  intros.
  induction T; intros; simpl; unfold fv_typ in *; f_equal*.
  apply* subst_undo_avar.
Qed.

Lemma subst_undo_trm_def_defs: forall x y,
   (forall t , y \notin fv_trm  t  -> (subst_trm  y x (subst_trm  x y t )) = t )
/\ (forall d , y \notin fv_def  d  -> (subst_def  y x (subst_def  x y d )) = d )
/\ (forall ds, y \notin fv_defs ds -> (subst_defs y x (subst_defs x y ds)) = ds).
Proof.
  intros.
  apply trm_mutind; intros; simpl; unfold fv_trm, fv_def, fv_defs in *; f_equal*;
    (apply* subst_undo_avar || apply* subst_undo_typ).
Qed.

Lemma subst_undo_trm: forall x y t,
  y \notin fv_trm t -> (subst_trm y x (subst_trm x y t)) = t.
Proof.
  apply* subst_undo_trm_def_defs.
Qed.


(* ###################################################################### *)
(** ** subtyp-and-then-lookup_tdec to lookup_tdec-and-then-subdec *)

Lemma more_fuel_increases_precision: forall G T L fuel2 Lo2 Hi2 fuel1 Lo1 Hi1,
  fuel2 <= fuel1 ->
  lookup_tdec fuel2 G T L = (Lo2, Hi2) ->
  lookup_tdec fuel1 G T L = (Lo1, Hi1) ->
  subtyp G Lo2 Lo1 /\ subtyp G Hi1 Hi2.
Admitted.

Lemma swap_sub_and_lookup_tdec: forall G T1 T2 fuel2 L Lo2 Hi2,
  subtyp G T1 T2 ->
  lookup_tdec fuel2 G T2 L = (Lo2, Hi2) ->
  exists fuel1 Lo1 Hi1,
    lookup_tdec fuel1 G T1 L = (Lo1, Hi1) /\
    subtyp G Lo2 Lo1 /\
    subtyp G Hi1 Hi2.
Proof.
  introv St. gen fuel2 L Lo2 Hi2. induction St; introv Eq2.
  + (* case subtyp_refl *)
    do 3 eexists. apply (conj Eq2). auto.
  + (* case subtyp_top *)
    exists 0 typ_bot typ_top.
    repeat split; destruct fuel2; unfold lookup_tdec in Eq2; inversions Eq2; auto.
  + (* case subtyp_bot *)
    exists 1 typ_top typ_bot. auto.
  + (* case subtyp_tdec *)
    destruct fuel2 as [|fuel2].
    - exists 0 typ_bot typ_top.
      repeat split; unfold lookup_tdec in Eq2; inversions Eq2; auto.
    - unfold lookup_tdec in Eq2. case_if.
      * inversions Eq2. exists 1 T1 U1.
        repeat split; auto. unfold lookup_tdec. case_if. reflexivity.
      * inversions Eq2. exists 0 typ_bot typ_top. auto.
  + (* case subtyp_mdec *)
    destruct fuel2 as [|fuel2]; unfold lookup_tdec in Eq2; inversions Eq2;
    exists 0 typ_bot typ_top; auto.
(*+ (* case subtyp_sel_l *)
    exists (S fuel) Lo2 Hi2.
    unfold lookup_tdec. fold lookup_tdec. rewrite H. rewrite H0.
    repeat split; auto.
    apply Eq2. (* doesn't work because maybe fuel <> fuel2 *) *)
  + (* case subtyp_sel_l *)
    (* Note: We have two different amounts of fuel:
       'fuel' comes from the lookup_tdec in the subtyp_sel_l, and
       'fuel2' comes from the lookup_tdec given as a hypothesis. *)
    exists (S (max fuel fuel2)).
    lets Le1: (Max.le_max_l fuel fuel2).
    lets Le2: (Max.le_max_r fuel fuel2).
    remember (lookup_tdec (max fuel fuel2) G X L) as p eqn: Eq1. destruct p as [T' U'].
    symmetry in Eq1.
    lets E1: (more_fuel_increases_precision _ _ _ Le1 H0 Eq1). destruct E1 as [StT StU].
    remember (lookup_tdec (max fuel fuel2) G U' L0) as p eqn: Eq3. destruct p as [Lo1 Hi1].
    symmetry in Eq3.
    exists Lo1 Hi1. repeat split.
    - unfold lookup_tdec. fold lookup_tdec. rewrite H. rewrite Eq1. exact Eq3.
    - admit. (* TODO kind of follows from StU, Eq2, Eq3, but harder than the whole
       lemma we're about to prove... *)
    - admit. (* ditto *)
  + (* case subtyp_sel_r *)
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
    rename Lo2 into Lo3, Hi2 into Hi3, Eq2 into Eq3, fuel2 into fuel3.
    specialize (IHSt2 _ _ _ _ Eq3).
    destruct IHSt2 as [fuel2 [Lo2 [Hi2 [Eq2 [StLo23 StHi23]]]]].
    specialize (IHSt1 _ _ _ _ Eq2).
    destruct IHSt1 as [fuel1 [Lo1 [Hi1 [Eq1 [StLo12 StHi12]]]]].
    exists fuel1 Lo1 Hi1. apply (conj Eq1). split.
    - apply (subtyp_trans StLo23 StLo12).
    - apply (subtyp_trans StHi12 StHi23).
Qed.


