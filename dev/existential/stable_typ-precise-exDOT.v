
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
  | typ_self : avar -> typ (* x.type *)
  | typ_ex   : typ -> typ -> typ (* ex(x: T)U
                                    both T and U can refer to the locally nameless x *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec (* L: S..U *)
  | dec_mtd  : mtd_label -> typ -> typ -> dec (* m: S->U *).

Inductive trm: Set :=                            (* x is locally nameless  *)
  | trm_new : defs -> trm -> trm                 (* val x = new {ds} in t  *)
  | trm_let : trm -> trm -> trm                  (* val x = t1 in t2       *)
  | trm_call: avar -> mtd_label -> avar -> trm   (* y.m(z)                 *)
  | trm_var : avar -> trm
with def : Set :=
  | def_typ : typ_label -> typ -> def (* only type aliases allowed here *)
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
| def_typ L _ => label_typ L
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
  | typ_self x     => typ_self (open_rec_avar k u x)
  | typ_ex T U     => typ_ex (open_rec_typ (S k) u T) (open_rec_typ (S k) u U)
  end
with open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_mtd m T U => dec_mtd m (open_rec_typ k u T) (open_rec_typ k u U)
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_new ds t2  => trm_new (open_rec_defs (S k) u ds) (open_rec_trm (S k) u t2)
  | trm_let t1 t2  => trm_let (open_rec_trm     k  u t1) (open_rec_trm (S k) u t2)
  | trm_call y m z => trm_call (open_rec_avar k u y) m (open_rec_avar k u z)
  | trm_var x      => trm_var (open_rec_avar k u x)
  end
with open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec_typ k u T)
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
  | typ_self x     => (fv_avar x)
  | typ_ex T U     => (fv_typ T) \u (fv_typ U)
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
  | trm_new ds t2  => (fv_defs ds) \u (fv_trm t2)
  | trm_let t1 t2  => (fv_trm t1) \u (fv_trm t2)
  | trm_call y m z => (fv_avar y) \u (fv_avar z)
  | trm_var x      => (fv_avar x)
  end
with fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv_typ T)
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
      red (trm_call (avar_f x) m (avar_f y)) s
          (open_trm y body) s
  | red_new: forall s ds t x,
      x # s ->
      red (trm_new ds t) s
          (open_trm x t) (s & x ~ (open_defs x ds))
  | red_let_2: forall y t s,
      red (trm_let (trm_var (avar_f y)) t) s
          (open_trm y t) s
  (* congruence rule *)
  | red_let_1: forall t1 t1' t2 s s',
      red t1 s t1' s' ->
      red (trm_let t1  t2) s
          (trm_let t1' t2) s'.


(* ###################################################################### *)
(** ** Typing *)

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

Notation "D1 && D2 == D3" := (intersect_dec D1 D2 = Some D3) (at level 40).
Notation "D1 || D2 == D3" := (union_dec D1 D2 = Some D3) (at level 40).

Definition dec_bot(l: label): dec := match l with
  | label_typ L => dec_typ L typ_top typ_bot
  | label_mtd m => dec_mtd m typ_top typ_bot
end.

(* Note: There are no typ_has/hasnt rules for existential types, but you first have to
   apply the skolemization rule.
   This also means that typ_has/hasnt is total only if the type is not an existential
   and the ctx contains no existentials. *)
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
  | typ_self_has: forall G x T D,
      binds x T G ->
      typ_has G T D ->
      typ_has G (typ_self (avar_f x)) D
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
      typ_hasnt G (typ_or T1 T2) l
  | typ_self_hasnt: forall G x T l,
      binds x T G ->
      typ_hasnt G T l ->
      typ_hasnt G (typ_self (avar_f x)) l.


(* [stable_typ T] means that T's members don't change under narrowing.
   TODO this can be extended to include "class types", and aliases to stable types. *)
Inductive stable_typ: typ -> Prop :=
| stable_top: stable_typ typ_top
| stable_bot: stable_typ typ_bot
| stable_rcd: forall D, stable_typ (typ_rcd D)
| stable_and: forall T1 T2, stable_typ T1 -> stable_typ T2 -> stable_typ (typ_and T1 T2)
| stable_or : forall T1 T2, stable_typ T1 -> stable_typ T2 -> stable_typ (typ_or  T1 T2).
(* Note: typ_sel and typ_self are not stable, and typ_ex could be considered stable
   with the following rule:
   
   forall T U, stable_typ U -> stable_typ (typ_ex T U)

   But since there's no typ_ex_has rules, there's no point in doing this.
*)

(*
Inductive stable_typ: ctx -> typ -> Prop :=
  | stable_top: forall G,
      stable_typ G typ_top
  | stable_bot: forall G,
      stable_typ G typ_bot
  | stable_rcd: forall G D,
      stable_typ G (typ_rcd D)
(*| stable_sel: typ_sel is not stable (that's the whole point) *)
  | stable_and: forall G T1 T2,
      stable_typ G T1 -> stable_typ G T2 -> stable_typ G (typ_and T1 T2)
  | stable_or: forall G T1 T2,
      stable_typ G T1 -> stable_typ G T2 -> stable_typ G (typ_or T1 T2).
*)

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
  | wf_self: forall G A x X,
      binds x X G ->
      wf_typ_impl G A X ->
      wf_typ_impl G A (typ_self (avar_f x))
  | wf_ex: forall L G A T U,
      (forall x, x \notin L -> wf_typ_impl (G & x ~ (open_typ x T)) A (open_typ x T)) ->
      (forall x, x \notin L -> wf_typ_impl (G & x ~ (open_typ x T)) A (open_typ x U)) ->
      wf_typ_impl G A (typ_ex T U)
  | wf_skolem: forall L G1 G2 x A S T U,
      (forall y, y \notin L ->
         wf_typ_impl (G1 & x ~ (open_typ y U) & y ~ (open_typ y S) & G2) A T) ->
      fv_typ T \c (dom (G1 & x ~ typ_ex S U & G2)) -> (* instead of "y \notin fv_typ T" *)
      wf_typ_impl (G1 & x ~ typ_ex S U & G2) A T
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

Inductive hmode: Set := okhyp | nohyp.

Inductive subtyp: hmode -> ctx -> typ -> typ -> Prop :=
  | subtyp_refl: forall hm G T,
      wf_typ G T ->
      subtyp hm G T T
  | subtyp_top: forall hm G T,
      wf_typ G T ->
      subtyp hm G T typ_top
  | subtyp_bot: forall hm G T,
      wf_typ G T ->
      subtyp hm G typ_bot T
  | subtyp_rcd: forall hm G D1 D2,
      subdec hm G D1 D2 ->
      subtyp hm G (typ_rcd D1) (typ_rcd D2)
  | subtyp_sel_l: forall hm G x X L T U,
      binds x X G ->
      wf_typ G X ->
      stable_typ X -> (* <-- important restriction *)
      typ_has G X (dec_typ L T U) ->
      subtyp hm G T U -> (* <-- probably not needed, just for symmetry with subtyp_sel_r *)
      subtyp hm G (typ_sel (avar_f x) L) U
  | subtyp_sel_r: forall hm G x X L T U,
      binds x X G ->
      wf_typ G X ->
      stable_typ X -> (* <-- important restriction *)
      typ_has G X (dec_typ L T U) ->
      subtyp hm G T U -> (* <-- makes proofs a lot easier!! *)
      subtyp hm G T (typ_sel (avar_f x) L)
  | subtyp_and: forall hm G T U1 U2,
      subtyp hm G T U1 ->
      subtyp hm G T U2 ->
      subtyp hm G T (typ_and U1 U2)
  | subtyp_and_l: forall hm G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp hm G (typ_and T1 T2) T1
  | subtyp_and_r: forall hm G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp hm G (typ_and T1 T2) T2
  | subtyp_or: forall hm G T1 T2 U,
      subtyp hm G T1 U ->
      subtyp hm G T2 U ->
      subtyp hm G (typ_or T1 T2) U
  | subtyp_or_l: forall hm G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp hm G T1 (typ_or T1 T2)
  | subtyp_or_r: forall hm G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      subtyp hm G T2 (typ_or T1 T2)
  | subtyp_self_l: forall hm G x T,
      binds x T G ->
      wf_typ G T ->
      subtyp hm G (typ_self (avar_f x)) T
  | subtyp_self_r: forall hm x y G,
      binds x (typ_self (avar_f y)) G ->
      wf_typ G (typ_self (avar_f y)) ->
      wf_typ G (typ_self (avar_f x)) ->
      subtyp hm G (typ_self (avar_f y)) (typ_self (avar_f x))
  | subtyp_ex_l: forall L hm G S T U,
      (forall x, x \notin L -> wf_typ (G & x ~ (open_typ x S)) (open_typ x S)) ->
      (forall x, x \notin L -> subtyp hm (G & x ~ (open_typ x S)) (open_typ x T) U) ->
      wf_typ G U ->
      subtyp hm G (typ_ex S T) U
  | subtyp_ex_r: forall hm G x S' S T U,
      binds x S' G ->
      subtyp hm G S' (open_typ x S) -> (* <-- explicit subsumption *)
      subtyp hm G T (open_typ x U) ->
      subtyp hm G T (typ_ex S U)
  | subtyp_trans: forall hm G T1 T2 T3,
      subtyp hm G T1 T2 ->
      subtyp hm G T2 T3 ->
      subtyp hm G T1 T3
  | subtyp_hyp: forall x X G L Lo Hi,
      binds x X G ->
      typ_has G X (dec_typ L Lo Hi) ->
      stable_typ X ->
      wf_typ G X ->
      wf_typ G Lo ->
      wf_typ G Hi ->
      subtyp okhyp G Lo Hi
with subdec: hmode -> ctx -> dec -> dec -> Prop :=
  | subdec_typ: forall hm G L Lo1 Hi1 Lo2 Hi2,
      subtyp hm G Lo2 Lo1 ->
      subtyp hm G Hi1 Hi2 ->
      subdec hm G (dec_typ L Lo1 Hi1) (dec_typ L Lo2 Hi2)
  | subdec_mtd: forall hm m G S1 T1 S2 T2,
      subtyp hm G S2 S1 ->
      subtyp hm G T1 T2 ->
      subdec hm G (dec_mtd m S1 T1) (dec_mtd m S2 T2).

(* TODO do we also need these? (from papers/dot/exdot/simple-rules.txt)

                G |- x.type <: y.type    G |- x.M <: T
                --------------------------------------
                            G |- y.M <: T

                G |- x.type <: y.type    G |- T <: x.M
                --------------------------------------
                            G |- T <: y.M
*)

(* typing on term level is always imprecise (can use subsumption) *)
Inductive ty_trm: ctx -> trm -> typ -> Prop :=
  | ty_var: forall G x T,
      binds x T G ->
      wf_typ G T ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_call: forall G y T m U V z,
      ty_trm G (trm_var (avar_f y)) T ->
      typ_has G T (dec_mtd m U V) ->
      ty_trm G (trm_var (avar_f z)) U -> (* <-- allows subsumption *)
      wf_typ G V ->
      ty_trm G (trm_call (avar_f y) m (avar_f z)) V
  | ty_new: forall L G ds T u U,
      (forall x, x \notin L ->
         ty_defs (G & x ~ (open_typ x T)) (open_defs x ds) (open_typ x T)) ->
      (forall x, x \notin L ->
         ty_trm (G & x ~ (open_typ x T)) (open_trm x u) U) ->
      wf_typ G U -> (* <-- even stronger than x \notin fv_typ U *)
      ty_trm G (trm_new ds u) U
  | ty_let: forall L G t1 T1 t2 T2,
      ty_trm G t1 T1 ->
      (forall x, x \notin L -> ty_trm (G & x ~ T1) (open_trm x t2) T2) ->
      wf_typ G T2 -> (* <-- even stronger than x \notin fv_typ T2 *)
      ty_trm G (trm_let t1 t2) T2
  | ty_skolem: forall L G1 G2 x t S T U,
      (forall y, y \notin L ->
         ty_trm (G1 & x ~ (open_typ y U) & y ~ (open_typ y S) & G2) t T) ->
      wf_typ (G1 & x ~ typ_ex S U & G2) T ->
      ty_trm (G1 & x ~ typ_ex S U & G2) t T
(* imprecise typing: subsumption allowed *)
  | ty_sbsm: forall G t T1 T2,
      ty_trm G t T1 ->
      subtyp okhyp G T1 T2 ->
      ty_trm G t T2
with ty_def: ctx -> def -> dec -> Prop :=
  | ty_tdef: forall G L T,
      wf_typ G T ->
      ty_def G (def_typ L T) (dec_typ L T T)
  | ty_mdef: forall L m G T U u,
      (* These wf checks ensure that x does not appear in T and U.
         But note that it is allowed to occur in the precise type of u. *)
      wf_typ G T ->
      wf_typ G U ->
      (forall x, x \notin L ->
         ty_trm (G & x ~ T) (open_trm x u) U) -> (* <-- allows subsumption *)
      ty_def G (def_mtd m T U u) (dec_mtd m T U)
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
  (def_typ E typ_top))
  (def_typ Stream (typ_and
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
  eapply ty_new with \{} (typ_and (typ_and typ_top
    (typ_rcd (dec_typ E typ_top typ_top)))
    (typ_rcd (dec_typ Stream
       (typ_and
          (typ_rcd (dec_mtd head typ_top (typ_sel (avar_b 0) E)))
          (typ_rcd (dec_mtd tail typ_top (typ_sel (avar_b 0) Stream))))
       (typ_and
          (typ_rcd (dec_mtd head typ_top (typ_sel (avar_b 0) E)))
          (typ_rcd (dec_mtd tail typ_top (typ_sel (avar_b 0) Stream))))))).
  { intros glob _. do_open.
    remember (typ_and
               (typ_rcd (dec_mtd head typ_top (typ_sel (avar_f glob) E)))
               (typ_rcd (dec_mtd tail typ_top (typ_sel (avar_f glob) Stream))))
    as TStream eqn: EqTStream.
    split_ty_defs.
    { auto. }
    { apply ty_tdef.
      rewrite concat_empty_l in *.
      rewrite EqTStream at 3.
      apply wf_and.
      { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
        eapply (wf_sel ((binds_single_eq _ _))).
        { eauto. }
        { eauto. }
        { repeat apply wf_and.
          { apply wf_top. }
          { auto. }
          { apply wf_rcd. apply wf_tmem.
            { rewrite EqTStream at 5.
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
                    { rewrite EqTStream at 7.
                      apply wf_and.
                      { apply wf_hyp. prove_in_fset. }
                      { apply wf_hyp. prove_in_fset. }
                    }
                    { rewrite EqTStream at 7.
                      apply wf_and.
                      { apply wf_hyp. prove_in_fset. }
                      { apply wf_hyp. prove_in_fset. }
                    }
                  }
                }
                { rewrite EqTStream at 5.
                  apply wf_and.
                  { apply wf_hyp. prove_in_fset. }
                  { apply wf_hyp. prove_in_fset. }
                }
                { rewrite EqTStream at 5.
                  apply wf_and.
                  { apply wf_hyp. prove_in_fset. }
                  { apply wf_hyp. prove_in_fset. }
                }
              }
            }
            { rewrite EqTStream at 5.
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
                    { rewrite EqTStream at 7.
                      apply wf_and.
                      { apply wf_hyp. prove_in_fset. }
                      { apply wf_hyp. prove_in_fset. }
                    }
                    { rewrite EqTStream at 7.
                      apply wf_and.
                      { apply wf_hyp. prove_in_fset. }
                      { apply wf_hyp. prove_in_fset. }
                    }
                  }
                }
                { rewrite EqTStream at 5.
                  apply wf_and.
                  { apply wf_hyp. prove_in_fset. }
                  { apply wf_hyp. prove_in_fset. }
                }
                { rewrite EqTStream at 5.
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
            { rewrite EqTStream at 5.
              apply wf_and.
              { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                eapply (wf_sel ((binds_single_eq _ _))).
                { eauto. }
                { eauto. }
                { repeat apply wf_and.
                  { apply wf_top. }
                  { auto. }
                  { apply wf_rcd. apply wf_tmem.
                    { rewrite EqTStream at 7.
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
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_hyp. prove_in_fset. }
                        }
                        { rewrite EqTStream at 7.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_hyp. prove_in_fset. }
                        }
                      }
                    }
                    { rewrite EqTStream at 7.
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
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_hyp. prove_in_fset. }
                        }
                        { rewrite EqTStream at 7.
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
            { rewrite EqTStream at 5.
              apply wf_and.
              { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                eapply (wf_sel ((binds_single_eq _ _))).
                { eauto. }
                { eauto. }
                { repeat apply wf_and.
                  { apply wf_top. }
                  { auto. }
                  { apply wf_rcd. apply wf_tmem.
                    { rewrite EqTStream at 7.
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
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_hyp. prove_in_fset. }
                        }
                        { rewrite EqTStream at 7.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_hyp. prove_in_fset. }
                        }
                      }
                    }
                    { rewrite EqTStream at 7.
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
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 9.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
                          apply wf_and.
                          { apply wf_hyp. prove_in_fset. }
                          { apply wf_hyp. prove_in_fset. }
                        }
                        { rewrite EqTStream at 7.
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
                { rewrite EqTStream at 5.
                  apply wf_and.
                  { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                    eapply (wf_sel ((binds_single_eq _ _))).
                    { eauto. }
                    { eauto. }
                    { repeat apply wf_and.
                      { apply wf_top. }
                      { auto. }
                      { apply wf_rcd. apply wf_tmem.
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
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
                { rewrite EqTStream at 5.
                  apply wf_and.
                  { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                    eapply (wf_sel ((binds_single_eq _ _))).
                    { eauto. }
                    { eauto. }
                    { repeat apply wf_and.
                      { apply wf_top. }
                      { auto. }
                      { apply wf_rcd. apply wf_tmem.
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
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
                { rewrite EqTStream at 5.
                  apply wf_and.
                  { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                    eapply (wf_sel ((binds_single_eq _ _))).
                    { eauto. }
                    { eauto. }
                    { repeat apply wf_and.
                      { apply wf_top. }
                      { auto. }
                      { apply wf_rcd. apply wf_tmem.
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
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
                { rewrite EqTStream at 5.
                  apply wf_and.
                  { apply wf_rcd. apply (wf_mtd _ (wf_top _ _)).
                    eapply (wf_sel ((binds_single_eq _ _))).
                    { eauto. }
                    { eauto. }
                    { repeat apply wf_and.
                      { apply wf_top. }
                      { auto. }
                      { apply wf_rcd. apply wf_tmem.
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                          }
                        }
                        { rewrite EqTStream at 7.
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
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                                { rewrite EqTStream at 9.
                                  apply wf_and.
                                  { apply wf_hyp. prove_in_fset. }
                                  { apply wf_hyp. prove_in_fset. }
                                }
                              }
                            }
                            { rewrite EqTStream at 7.
                              apply wf_and.
                              { apply wf_hyp. prove_in_fset. }
                              { apply wf_hyp. prove_in_fset. }
                            }
                            { rewrite EqTStream at 7.
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
    { intros unit N. do_open. apply ty_var.
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
  | typ_self x     => typ_self (subst_avar z u x)
  | typ_ex T U     => typ_ex (subst_typ z u T) (subst_typ z u U)
  end
with subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_mtd m T U => dec_mtd m (subst_typ z u T) (subst_typ z u U)
  end.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_new ds t2  => trm_new (subst_defs z u ds) (subst_trm z u t2)
  | trm_let t1 t2  => trm_let (subst_trm z u t1) (subst_trm z u t2)
  | trm_call a m b => trm_call (subst_avar z u a) m (subst_avar z u b)
  | trm_var x      => trm_var (subst_avar z u x)
  end
with subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (subst_typ z u T)
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
  intros x y. apply typ_mutind; intros; simpls; f_equal*; apply* subst_fresh_avar.
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

Definition subst_fresh_trm (x y: var) := proj31 (subst_fresh_trm_def_defs x y).
Definition subst_fresh_def (x y: var) := proj32 (subst_fresh_trm_def_defs x y).
Definition subst_fresh_defs(x y: var) := proj33 (subst_fresh_trm_def_defs x y).

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
  intros. apply typ_mutind; intros; simpl; f_equal*; apply subst_open_commute_avar.
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
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*;
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
  apply typ_mutind; intros; simpl; unfold fv_typ, fv_dec in *; f_equal*;
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

Lemma subst_ctx_idempotent: forall x y G,
  subst_ctx x y (subst_ctx x y G) = subst_ctx x y G.
Admitted.


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


(* ###################################################################### *)
(** ** Regularity of Typing *)

(* If a type is involved in a subtyping judgment, it is (deeply) well-formed. *)
Lemma subtyping_regular:
   (forall hm G T1 T2, subtyp hm G T1 T2 -> wf_typ G T1 /\ wf_typ G T2)
/\ (forall hm G D1 D2, subdec hm G D1 D2 -> wf_dec G D1 /\ wf_dec G D2).
Proof.
  apply subtyp_mutind; try solve [intros; split; subst; destruct_wf; eauto].
  (* case subtyp_rcd *)
  introv Sd Wf. destruct Wf as [Wf1 Wf2].
  split; apply wf_rcd; apply add_hyps_to_wf_dec; assumption.
Qed.

Definition subtyp_regular := proj1 subtyping_regular.
Definition subdec_regular := proj2 subtyping_regular.

Definition subtyp_regular_1(hm: hmode)(G: ctx)(T1 T2: typ)(St: subtyp hm G T1 T2) :=
  (proj1 (subtyp_regular St)).
Definition subtyp_regular_2(hm: hmode)(G: ctx)(T1 T2: typ)(St: subtyp hm G T1 T2) :=
  (proj2 (subtyp_regular St)).
Definition subdec_regular_1(hm: hmode)(G: ctx)(D1 D2: dec)(Sd: subdec hm G D1 D2) :=
  (proj1 (subdec_regular Sd)).
Definition subdec_regular_2(hm: hmode)(G: ctx)(D1 D2: dec)(Sd: subdec hm G D1 D2) :=
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
  (* case ty_defs_cons *)
  introv Tyds WfT TyD WfD Hasnt.
  apply (wf_and WfT). apply wf_rcd. apply add_hyps_to_wf_dec; assumption.
  Grab Existential Variables. constructor. constructor.
Qed.

Definition ty_trm_regular  := proj31 typing_regular.
Definition ty_def_regular  := proj32 typing_regular.
Definition ty_defs_regular := proj33 typing_regular.

Hint Resolve ty_trm_regular ty_def_regular ty_defs_regular.


(* ###################################################################### *)
(** ** Looks like rules, but follows from the rules *)

Lemma subdec_refl: forall hm G D,
  wf_dec G D ->
  subdec hm G D D.
Proof.
  introv Wf. inversions Wf; eauto.
Qed.

Lemma subdec_bot: forall hm G D,
  wf_dec G D ->
  subdec hm G (dec_bot (label_of_dec D)) D.
Proof.
  introv Wf. inversions Wf; simpl; eauto.
Qed.

Hint Resolve subdec_refl subdec_bot.

Lemma subdec_intersect: forall hm G D0 D1 D2 D12,
  subdec hm G D0 D1 ->
  subdec hm G D0 D2 ->
  D1 && D2 == D12 ->
  subdec hm G D0 D12.
Proof.
  introv Sd01 Sd02 I. inversions Sd01; inversions Sd02;
  unfold intersect_dec in I; case_if; inversions I; auto.
Qed.

Lemma subdec_union: forall hm G D D1 D2 D12,
  subdec hm G D1 D ->
  subdec hm G D2 D ->
  D1 || D2 == D12 ->
  subdec hm G D12 D.
Proof.
  introv Sd01 Sd02 I. inversions Sd01; inversions Sd02;
  unfold union_dec in I; case_if; inversions I; auto.
Qed.

Lemma subdec_intersect_l: forall hm G D1 D2 D12,
  D1 && D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec hm G D12 D1.
Proof.
  introv Eq WfD1 WfD2. unfold intersect_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  destruct_wf;
  try in_empty_contradiction;
  eauto.
Qed.

Lemma subdec_intersect_r: forall hm G D1 D2 D12,
  D1 && D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec hm G D12 D2.
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

Lemma subdec_union_l: forall hm G D1 D2 D12,
  D1 || D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec hm G D1 D12.
Proof.
  introv Eq Wf1 Wf2. unfold union_dec in Eq. case_if.
  destruct D1 as [L1 S1 U1 | m1 S1 U1];
  destruct D2 as [L2 S2 U2 | m2 S2 U2];
  inversions Eq;
  inversions H;
  destruct_wf;
  eauto.
Qed.

Lemma subdec_union_r: forall hm G D1 D2 D12,
  D1 || D2 == D12 ->
  wf_dec G D1 ->
  wf_dec G D2 ->
  subdec hm G D2 D12.
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

Lemma subdec_to_label_of_dec_eq: forall hm G D1 D2,
  subdec hm G D1 D2 -> label_of_dec D1 = label_of_dec D2.
Proof.
  introv Sd. inversions Sd; reflexivity.
Qed.

Lemma invert_subdec_typ_sync_left: forall hm G D L Lo2 Hi2,
   subdec hm G D (dec_typ L Lo2 Hi2) ->
   exists Lo1 Hi1, D = (dec_typ L Lo1 Hi1) /\
                   subtyp hm G Lo2 Lo1 /\
                   subtyp hm G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. exists Lo1 Hi1. auto.
Qed.

Lemma invert_subdec_mtd_sync_left: forall hm G D m T2 U2,
   subdec hm G D (dec_mtd m T2 U2) ->
   exists T1 U1, D = (dec_mtd m T1 U1) /\
                 subtyp hm G T2 T1 /\
                 subtyp hm G U1 U2.
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
  Grab Existential Variables. constructor. constructor.
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
  Grab Existential Variables. constructor. constructor.
Qed.

Lemma subdec_trans: forall hm G D1 D2 D3,
  subdec hm G D1 D2 -> subdec hm G D2 D3 -> subdec hm G D1 D3.
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
  Grab Existential Variables. constructor. constructor.
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
(** ** More definitions (not part of spec) *)

Definition subenv(G1 G2: ctx) :=
  forall x T2, binds x T2 G2 -> 
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ subtyp nohyp G1 T1 T2 /\ stable_typ T1.

Definition memberwise_subtyp(G: ctx)(T1 T2: typ) := 
  (forall D2, typ_has G T2 D2 -> exists D1, typ_has G T1 D1 /\ subdec nohyp G D1 D2)
  /\ wf_typ G T1 /\ wf_typ G T2.


(* ###################################################################### *)
(** ** Weakening for subtyping *)

Ltac chicken := constructor.

Lemma weaken_subtyp_subdec:
   (forall hm G T1 T2, subtyp hm G T1 T2 -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subtyp hm (G1 & G2 & G3) T1 T2)
/\ (forall hm G D1 D2, subdec hm G D1 D2 -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2 & G3) ->
    subdec hm (G1 & G2 & G3) D1 D2).
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
  + (* case subtyp_hyp   *)
    introv Bix Has SbX WfX WfLo WfHi Eq Ok.
    apply subtyp_hyp with x X L; ((subst; apply (binds_weaken Bix Ok)) || eauto).
  + (* case subdec_typ   *) eauto.
  + (* case subdec_mtd   *) eauto.
  (* See
     Zongker, D. (2006). Chicken chicken chicken: Chicken chicken.
     Annals of Improbable Research, 12(5), 16-21.
     https://isotropic.org/papers/chicken.pdf *)
  Grab Existential Variables.
  chicken.
  chicken. chicken. chicken.
  chicken. chicken. chicken. chicken.
Qed.

Lemma weaken_subtyp_middle: forall hm G1 G2 G3 S U,
  ok (G1 & G2 & G3) -> 
  subtyp hm (G1 &     G3) S U ->
  subtyp hm (G1 & G2 & G3) S U.
Proof.
  introv Ok St. destruct weaken_subtyp_subdec as [P _]. apply* P.
Qed.

Lemma weaken_subtyp_end: forall hm G1 G2 S U,
  ok (G1 & G2) -> 
  subtyp hm G1        S U ->
  subtyp hm (G1 & G2) S U.
Proof.
  introv Ok St. destruct weaken_subtyp_subdec as [P _].
  specialize (P _ G1 S U St G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.

Lemma weaken_subdec_end: forall hm G1 G2 D1 D2,
  ok (G1 & G2) -> 
  subdec hm G1        D1 D2 ->
  subdec hm (G1 & G2) D1 D2.
Proof.
  introv Ok St. destruct weaken_subtyp_subdec as [_ P].
  specialize (P _ G1 D1 D2 St G1 G2 empty). repeat rewrite concat_empty_r in P. auto.
Qed.


(* ###################################################################### *)
(** ** Strengthening typ_has (needed to weaken good_bounds and memberwise_subtyp) *)

Lemma ok_concat_indom: forall (A: Type) (G1 G2: env A) (x: var),
  ok (G1 & G2) ->
  x \in dom G1 ->
  x \in dom G2 ->
  False.
Proof.
  introv Ok. gen x. gen_eq G: (G1 & G2). gen G1 G2. induction Ok; introv Eq xG1 xG2; subst.
  - apply empty_concat_inv in Eq. destruct Eq. subst. rewrite dom_empty in xG1.
    in_empty_contradiction.
  - destruct (env_case G2) as [? | [x' [v' [G2' ?]]]].
    * subst. rewrite concat_empty_r in *.
      rewrite dom_empty in xG2. in_empty_contradiction.
    * subst. rewrite concat_assoc in Eq.
      apply eq_push_inv in Eq. destruct Eq as [? [? Eq]]. symmetry in H0, H1. subst.
      rewrite dom_push in xG2. rewrite in_union in xG2. destruct xG2 as [Eq | xG2].
      + rewrite in_singleton in Eq. subst.
        rewrite dom_concat in H. unfold notin in H. apply H. rewrite in_union.
        left. exact xG1.
      + apply (IHOk _ _ eq_refl _ xG1 xG2).
Qed.

Lemma strengthened_binds_unique: forall (T: Type) G1 G2 G3 x (X X': T),
  ok (G1 & G2 & G3) ->
  binds x X (G1 & G2 & G3) ->
  binds x X' (G1 & G3) ->
  X = X'.
Proof.
  introv Ok Bi Bi'.
  assert (xG2: x # G2). {
    apply get_some_inv in Bi'. rewrite dom_concat in Bi'. rewrite in_union in Bi'.
    unfold notin. intro xG2.
    destruct Bi' as [xG1 | xG3].
    - refine (ok_concat_indom _ xG1 xG2). auto.
    - refine (ok_concat_indom _ xG2 xG3). rewrite <- concat_assoc in Ok. auto.
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

Definition good_bounds_typ(G: ctx)(T: typ) :=
  wf_typ G T /\ (forall L Lo Hi, typ_has G T (dec_typ L Lo Hi) -> subtyp nohyp G Lo Hi).

Definition good_bounds(G: ctx) :=
  forall x X, binds x X G -> good_bounds_typ G X.

Lemma ty_defs_to_good_bounds_typ: forall G ds T,
  ty_defs G ds T ->
  good_bounds_typ G T.
Proof.
  unfold good_bounds_typ. introv Tyds. split; [eauto | idtac].
  introv THas.
  destruct (invert_ty_defs Tyds THas) as [d [dsHas Tyd]].
  inversions Tyd. eauto.
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

Lemma weaken_memberwise_subtyp_end: forall G1 G2 S U,
  ok (G1 & G2) -> 
  memberwise_subtyp G1        S U ->
  memberwise_subtyp (G1 & G2) S U.
Proof.
  unfold memberwise_subtyp. introv Ok MSt. destruct MSt as [MSt [WfS WfU]]. repeat split.
  - introv UHas. specialize (MSt _ (strengthen_has_end Ok WfU UHas)).
    destruct MSt as [D1 [SHas Sd]]. exists D1. split.
    * apply (weaken_typ_has_end Ok SHas).
    * apply (weaken_subdec_end Ok Sd).
  - apply (weaken_wf_typ_end WfS Ok).
  - apply (weaken_wf_typ_end WfU Ok).
Qed.


(* ###################################################################### *)
(** ** Well-formed store *)


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
  unfold good_bounds. introv Wf BiG.
  destruct (ctx_binds_to_sto_binds_raw Wf BiG) as [G1 [G2 [ds [Eq [Bis Tyds]]]]]. subst.
  lets Gb: (ty_defs_to_good_bounds_typ Tyds).
  refine (weaken_good_bounds_typ_end _ Gb).
  apply (wf_sto_to_ok_G Wf).
Qed.

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


(* ###################################################################### *)
(** ** subtyp-and-then-lookup to lookup-and-then-subdec *)

Lemma subtyp_to_memberwise: forall G T1 T2,
  subtyp nohyp G T1 T2 ->
  memberwise_subtyp G T1 T2.
Proof.
  introv St. unfold memberwise_subtyp.
  destruct (subtyp_regular St) as [Wf1 Wf2].
  refine (conj _ (conj Wf1 Wf2)). clear Wf1 Wf2.
  gen_eq hm: nohyp.
  induction St; unfold memberwise_subtyp in *; introv Eq T2Has; subst.
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
    apply (IHSt eq_refl). clear IHSt.
    lets Eq: (typ_has_unique H3 XHas eq_refl). inversions Eq.
    exact H5.
  + (* case subtyp_and *)
    inversions T2Has.
    - eauto.
    - eauto.
    - rename H1 into U1Has, H3 into U2Has, H5 into Eq, D1 into DU1, D0 into DU2.
      specialize (IHSt1 eq_refl _ U1Has). destruct IHSt1 as [D1 [THas Sd1]].
      specialize (IHSt2 eq_refl _ U2Has). destruct IHSt2 as [D1' [THas' Sd2]].
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
        apply (subdec_intersect_l _ Eq12 WfD1 WfD2).
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
        apply (subdec_intersect_r _ Eq12 WfD1 WfD2).
  + (* case subtyp_or *)
    rename T2Has into UHas.
    specialize (IHSt1 eq_refl _ UHas). destruct IHSt1 as [D01 [T1Has Sd1]].
    specialize (IHSt2 eq_refl _ UHas). destruct IHSt2 as [D02 [T2Has Sd2]].
    lets Eql1: (subdec_to_label_of_dec_eq Sd1).
    lets Eql2: (subdec_to_label_of_dec_eq Sd2).
    rewrite <- Eql2 in Eql1.
    destruct (union_dec_total _ _ Eql1) as [D12 Eq12]. exists D12. split.
    - apply (typ_or_has T1Has T2Has Eq12).
    - apply (subdec_union Sd1 Sd2 Eq12).
  + (* case subtyp_or_l *)
    inversions T2Has. rename H3 into T1Has, H5 into T2Has, D2 into D12, D0 into D2.
    exists D1. apply (conj T1Has). apply (subdec_union_l _ H7).
    - apply (typ_has_preserves_wf T1Has H).
    - apply (typ_has_preserves_wf T2Has H0).
  + (* case subtyp_or_r *)
    inversions T2Has. rename H3 into T1Has, H5 into T2Has, D2 into D12, D0 into D2.
    exists D2. apply (conj T2Has). apply (subdec_union_r _ H7).
    - apply (typ_has_preserves_wf T1Has H).
    - apply (typ_has_preserves_wf T2Has H0).
  + (* case subtyp_trans *)
    rename D2 into D3, T2Has into T3Has.
    specialize (IHSt2 eq_refl _ T3Has).
    destruct IHSt2 as [D2 [T2Has Sd23]].
    specialize (IHSt1 eq_refl _ T2Has).
    destruct IHSt1 as [D1 [T1Has Sd12]].
    exists D1. apply (conj T1Has). apply (subdec_trans Sd12 Sd23).
  + (* case subtyp_hyp *)
    discriminate.
Qed.

Print Assumptions subtyp_to_memberwise.


(* ###################################################################### *)
(** ** Properties of good_bounds *)

Lemma distribute_and: forall (P1 P2 Q1 Q2: Prop),
  (P1 /\ P2 -> Q1 /\ Q2) -> ((P1 /\ P2 -> Q1) /\ (P1 /\ P2 -> Q2)).
Proof.
  intros. split; intro H0; specialize (H H0); destruct H; auto.
Qed.

(*
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
*)

(* ###################################################################### *)
(** ** okhyp/nohyp *)

(* the trivial direction *)
Lemma anyhyp_to_okhyp: 
   (forall hm G T1 T2, subtyp hm G T1 T2 -> subtyp okhyp G T1 T2)
/\ (forall hm G D1 D2, subdec hm G D1 D2 -> subdec okhyp G D1 D2).
Proof.
  apply subtyp_mutind; intros; eauto.
Qed.

Definition subtyp_to_okhyp := proj1 anyhyp_to_okhyp.
Definition subdec_to_okhyp := proj2 anyhyp_to_okhyp.


(* ###################################################################### *)
(** ** Narrowing on type level *)

Lemma narrow_binds_3: forall G1 G2 x T2,
  subenv G1 G2 ->
  binds x T2 G2 ->
  binds x T2 G1
  \/ exists T1, 
  binds x T1 G1 /\ subtyp nohyp G1 T1 T2 /\ stable_typ T1.
Proof.
  introv Se Bi. unfold subenv in Se. (* destruct Se as [Ok1 [Ok2 Se]]. *) apply (Se _ _ Bi).
Qed.

Lemma memberwise_subtyp_refl: forall G T,
  wf_typ G T ->
  memberwise_subtyp G T T.
Proof.
  unfold memberwise_subtyp. introv Wf. simpl in *. refine (conj _ (conj Wf Wf)).
  introv Has. exists D2. apply (conj Has).
  apply subdec_refl.
  apply (typ_has_preserves_wf Has Wf).
Qed.

Lemma narrow_binds_4: forall G1 G2 x T1 T2,
  wf_typ G1 T1 ->
  binds x T2 G2 ->
  binds x T1 G1 ->
  subenv G1 G2 ->
  subtyp nohyp G1 T1 T2.
Proof.
  introv WfT1 Bi2 Bi1 Se.
  lets P: (narrow_binds_3 Se Bi2). 
  destruct P as [Bi1' | [T0 [Bi1' [St Sb]]]].
  - rewrite (binds_func Bi1' Bi1). apply (subtyp_refl _ WfT1).
  - lets Eq: (binds_func Bi1' Bi1). subst. assumption.
Qed.

Lemma narrow_binds_5: forall G1 G2 x T2,
  wf_typ G1 T2 ->
  binds x T2 G2 ->
  subenv G1 G2 ->
  exists T1, binds x T1 G1 /\ subtyp nohyp G1 T1 T2.
Proof.
  introv WfT2 Bi2 Se.
  lets P: (narrow_binds_3 Se Bi2). destruct P as [Bi1' | [T0 [Bi1' [St Sb]]]].
  - exists T2. auto.
  - exists T0. auto.
Qed.

Lemma narrow_has_hasnt_stable:
   (forall G T D, typ_has G T D -> forall G',
    stable_typ T ->
    subenv G' G ->
    typ_has G' T D)
/\ (forall G T l, typ_hasnt G T l -> forall G',
    stable_typ T ->
    subenv G' G ->
    typ_hasnt G' T l).
Proof.
  apply typ_has_mutind; intros; subst;
  match goal with
  | H: stable_typ _ |- _ => inversions H
  end;
  eauto.
Qed.

Definition narrow_has_stable := proj1 narrow_has_hasnt_stable.
Definition narrow_hasnt_stable := proj2 narrow_has_hasnt_stable.

(* Needed by narrow_ty *)
Lemma narrow_has_hasnt:
   (forall G T D2, typ_has G T D2 -> forall G',
    subenv G' G ->
    wf_typ G' T -> (* G' !! *)
    exists D1,
      typ_has G' T D1 /\
      subdec nohyp G' D1 D2)
/\ (forall G T l, typ_hasnt G T l -> forall G',
    subenv G' G ->
    wf_typ G' T -> (* G' !! *)
    typ_hasnt G' T l 
    \/ exists D, label_of_dec D = l /\ typ_has G' T D).
Proof.
  apply typ_has_mutind.
  + (* case typ_bot_has *)
    intros. exists (dec_bot l). split; [eauto | destruct l; simpl; eauto].
  + (* case typ_rcd_has *)
    intros. subst. apply invert_wf_rcd in H0. exists D. eauto.
  + (* case typ_sel_has *)
    intros G x X2 L Lo2 Hi2 D2 Bix2 _ IH1 _ IH2 G' Se Wf. subst.
    apply invert_wf_sel in Wf. destruct Wf as [X1 [T [U [Bix1 [X1Has [WfX1 [WfT WfU]]]]]]].
    lets StX: (narrow_binds_4 WfX1 Bix2 Bix1 Se).
    lets WfX2: (proj2 (subtyp_regular StX)).
    specialize (IH1 _ Se WfX2). destruct IH1 as [D0 [X2Has Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo1 [Hi1 [Eq [StLo12 StHi12]]]]. subst D0.
    lets WfHi2: (proj2 (subtyp_regular StHi12)).
    specialize (IH2 _ Se WfHi2). destruct IH2 as [D1 [Hi2Has Sd12]].
    lets P: (subtyp_to_memberwise StX). destruct P as [P _]. specialize (P _ X2Has).
            (********************)
    destruct P as [D0 [X1Has' Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo0 [Hi0 [Eq [StLo01 StHi01]]]]. subst D0.
    lets StLo: (subtyp_trans StLo12 StLo01).
    lets StHi: (subtyp_trans StHi01 StHi12).
    lets P: (subtyp_to_memberwise StHi). destruct P as [P _]. specialize (P _ Hi2Has).
            (********************)
    destruct P as [D0 [Hi0Has Sd01]].
    exists D0. split.
    - apply (typ_sel_has Bix1 X1Has' Hi0Has).
    - apply (subdec_trans Sd01 Sd12).
  + (* case typ_and_has_1 *)
    introv _ IH1 _ IH2. introv Se Wf. rename D into D1.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
        apply (subdec_intersect_l _ Eq WfD1 WfD2).
  + (* case typ_and_has_2 *)
    introv _ IH1 _ IH2. introv Se Wf. rename D into D1.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
        apply (subdec_intersect_r _ Eq WfD1 WfD2).
  + (* case typ_and_has_12 *)
    introv _ IH1 _ IH2 Eq. introv Se Wf. subst.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
      * refine (subdec_trans _ Sd1). apply (subdec_intersect_l _ Eq' WfD1' WfD2').
      * refine (subdec_trans _ Sd2). apply (subdec_intersect_r _ Eq' WfD1' WfD2').
  + (* case typ_or_has *)
    introv _ IH1 _ IH2 Eq. introv Se Wf. subst.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
      * refine (subdec_trans Sd1 _). apply (subdec_union_l _ Eq WfD1 WfD2).
      * refine (subdec_trans Sd2 _). apply (subdec_union_r _ Eq WfD1 WfD2).
  + (* case typ_top_hasnt *)
    eauto.
  + (* case typ_rcd_hasnt *)
    eauto.
  + (* case typ_sel_hasnt *)
    intros G x X2 L Lo2 Hi2 l Bix2 X2Has' IH1 Hi2Hasnt' IH2. introv Se Wf.
    apply invert_wf_sel in Wf. destruct Wf as [X1 [T [U [Bix1 [X1Has [WfX1 [WfT WfU]]]]]]].
    lets StX: (narrow_binds_4 WfX1 Bix2 Bix1 Se).
    lets WfX2: (proj2 (subtyp_regular StX)).
    specialize (IH1 _ Se WfX2). destruct IH1 as [D0 [X2Has Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo1 [Hi1 [Eq [StLo12 StHi12]]]]. subst D0.
    lets P: (subtyp_to_memberwise StX). destruct P as [P _]. specialize (P _ X2Has).
            (********************)
    destruct P as [D0 [X1Has' Sd0]].
    apply invert_subdec_typ_sync_left in Sd0.
    destruct Sd0 as [Lo0 [Hi0 [Eq [StLo01 StHi01]]]]. subst D0.
    lets StLo: (subtyp_trans StLo12 StLo01).
    lets StHi: (subtyp_trans StHi01 StHi12).
    destruct (subtyp_regular StHi) as [WfHi0 _].
    lets P: (typ_has_total WfHi0 l). destruct P as [Hasnt | Has].
            (*************)
    - left. apply (typ_sel_hasnt Bix1 X1Has' Hasnt).
    - right. destruct Has as [D [Eq Has]]. exists D. eauto.
  + (* case typ_and_hasnt *)
    introv _ IH1 _ IH2. introv Se Wf.
    apply invert_wf_and in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
    introv Hasnt1 IH1 Has2 IH2. introv Se Wf.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
    introv Has1 IH1 Hasnt2 IH2. introv Se Wf. subst.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
    introv _ IH1 _ IH2 Se Wf. subst.
    apply invert_wf_or in Wf. destruct Wf as [Wf1 Wf2].
    specialize (IH1 _ Se Wf1).
    specialize (IH2 _ Se Wf2).
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
  Grab Existential Variables. constructor. constructor.
Qed.

Print Assumptions narrow_has_hasnt.

Definition narrow_has := proj1 narrow_has_hasnt.
Definition narrow_hasnt := proj2 narrow_has_hasnt.

Lemma narrow_wf:
   (forall G A T, wf_typ_impl G A T -> forall G',
    subenv G' G ->
    wf_typ_impl G' A T)
/\ (forall G A D, wf_dec_impl G A D -> forall G',
    subenv G' G ->
    wf_dec_impl G' A D).
Proof.
  apply wf_mutind.
  + (* case wf_top *) eauto.
  + (* case wf_bot *) eauto.
  + (* case wf_hyp *) eauto.
  + (* case wf_rcd *) eauto.
  + (* case wf_sel *)
    introv Bix SbX XHas WfX IHX WfT IHT WfU IHU. introv Se. subst.
    lets XHas': (narrow_has_stable XHas SbX Se).
    specialize (IHX _ Se).
    specialize (IHT _ Se).
    specialize (IHU _ Se).
    destruct (narrow_binds_3 Se Bix) as [Bix' | [X' [Bix' [St SbX']]]].
    - (* case "type of x remained unchanged" *)
      apply (wf_sel Bix' SbX XHas' IHX IHT IHU).
    - (* case "type of x changed from X to X'" *)
      lets P: (subtyp_to_memberwise St). destruct P as [P _]. specialize (P _ XHas').
              (********************)
      destruct P as [D1 [S1Has Sd]].
      apply invert_subdec_typ_sync_left in Sd. destruct Sd as [T' [U' [Eq [StT2 StU2]]]].
      subst D1.
      apply (wf_sel Bix' SbX' S1Has);
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

Definition narrow_wf_typ := proj1 narrow_wf.
Definition narrow_wf_dec := proj2 narrow_wf.

Lemma narrow_subtyp_subdec:
   (forall hm G T1 T2, subtyp hm G T1 T2 -> forall G',
    subenv G' G ->
    subtyp okhyp G' T1 T2)
/\ (forall hm G D1 D2, subdec hm G D1 D2 -> forall G',
    subenv G' G ->
    subdec okhyp G' D1 D2).
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
    introv Bi2 WfX SbX XHas St IHSt. introv Se.
    lets WfX': (narrow_wf_typ WfX Se).
    specialize (IHSt _ Se).
    lets XHas': (narrow_has_stable XHas SbX Se).
    lets P: (narrow_binds_3 Se Bi2).
    destruct P as [Bi1 | [X' [Bi1 [StX SbX']]]].
    - (* case "type of x remained unchanged" *)
      apply (subtyp_sel_l Bi1 WfX' SbX XHas' IHSt).
    - (* case "type of x changed from X to X'" *)
      lets P: (subtyp_to_memberwise StX). destruct P as [P _]. specialize (P _ XHas').
              (********************)
      destruct P as [D1 [X'Has Sd]].
      apply invert_subdec_typ_sync_left in Sd. destruct Sd as [T' [U' [Eq [StT StU]]]].
      subst D1.
      refine (subtyp_trans _ (subtyp_to_okhyp StU)).
      apply (subtyp_sel_l Bi1 (proj1 (subtyp_regular StX)) SbX' X'Has).
      apply (subtyp_hyp Bi1 X'Has SbX' (proj1 (subtyp_regular StX))
            (**********)               (proj2 (subtyp_regular StT))
                                       (proj1 (subtyp_regular StU))).
  + (* case subtyp_sel_r *)
    introv Bi2 WfX SbX XHas St IHSt. introv Se.
    lets WfX': (narrow_wf_typ WfX Se).
    specialize (IHSt _ Se).
    lets XHas': (narrow_has_stable XHas SbX Se).
    lets P: (narrow_binds_3 Se Bi2).
    destruct P as [Bi1 | [X' [Bi1 [StX SbX']]]].
    - (* case "type of x remained unchanged" *)
      apply (subtyp_sel_r Bi1 WfX' SbX XHas' IHSt).
    - (* case "type of x changed from X to X'" *)
      lets P: (subtyp_to_memberwise StX). destruct P as [P _]. specialize (P _ XHas').
              (********************)
      destruct P as [D1 [X'Has Sd]].
      apply invert_subdec_typ_sync_left in Sd. destruct Sd as [T' [U' [Eq [StT StU]]]].
      subst D1.
      refine (subtyp_trans (subtyp_to_okhyp StT) _).
      apply (subtyp_sel_r Bi1 (proj1 (subtyp_regular StX)) SbX' X'Has).
      apply (subtyp_hyp Bi1 X'Has SbX' (proj1 (subtyp_regular StX))
            (**********)               (proj2 (subtyp_regular StT))
                                       (proj1 (subtyp_regular StU))).
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
    intros. apply subtyp_trans with T2; eauto.
  + (* case subtyp_hyp *)
    introv Bi2 XHas SbX WfX WfLo WfHi Se.
    lets WfX': (narrow_wf_typ WfX Se).
    lets XHas': (narrow_has_stable XHas SbX Se).
    lets P: (narrow_binds_3 Se Bi2).
    destruct P as [Bi1 | [X' [Bi1 [StX SbX']]]].
    - (* case "type of x remained unchanged" *)
      apply (subtyp_hyp Bi1 XHas' SbX WfX' (narrow_wf_typ WfLo Se) (narrow_wf_typ WfHi Se)).
    - (* case "type of x changed from X to X'" *)
      lets P: (subtyp_to_memberwise StX). destruct P as [P _]. specialize (P _ XHas').
              (********************)
      destruct P as [D1 [X'Has Sd]].
      apply invert_subdec_typ_sync_left in Sd. destruct Sd as [T' [U' [Eq [StT StU]]]].
      subst D1.
      refine (subtyp_trans (subtyp_to_okhyp StT) _).
      refine (subtyp_trans _ (subtyp_to_okhyp StU)).
      lets WfX'': (proj1 (subtyp_regular StX)).
      lets WfD: (typ_has_preserves_wf X'Has WfX''). inversions WfD.
      apply (subtyp_hyp Bi1 X'Has SbX'); assumption.
  + (* case subdec_typ *) eauto.
  + (* case subdec_mtd *) eauto.
Qed.

Print Assumptions narrow_subtyp_subdec.

Definition narrow_subtyp := proj1 narrow_subtyp_subdec.
Definition narrow_subdec := proj2 narrow_subtyp_subdec.

(*
Lemma narrow_memberwise_subtyp: forall G G' T1 T2,
  memberwise_subtyp G T1 T2 ->
  good_bounds G' ->
  subenv G' G ->
  memberwise_subtyp G' T1 T2.
Proof.
  unfold memberwise_subtyp. introv MSt Gb Se. repeat split.
  - introv T2Has. (* Oh no! This needs un-narrowing for typ_has! *)
Abort.
*)


(* ###################################################################### *)
(** ** subenv *)

Lemma subenv_refl: forall G,
  subenv G G.
Proof.
  intro G. unfold subenv. intros. left. assumption.
Qed.

Lemma subenv_trans: forall G1 G2 G3,
  subenv G1 G2 ->
  subenv G2 G3 ->
  subenv G1 G3.
Proof.
Abort.
(* Does not hold because narrow_memberwise_subtyp does not hold!
  introv Gb Se12 Se23. intros x T3 Bi3.
  destruct (Se23 _ _ Bi3) as [Bi2 | [T2 [Bi2 [St23 [MSt23 Sb2]]]]];
  destruct (Se12 _ _ Bi2) as [Bi1 | [T1 [Bi1 [St12 [MSt12 Sb1]]]]].
  + left. exact Bi1.
  + right. exists T1. auto.
  + right. exists T2. repeat split; try assumption.
    apply (narrow_subtyp St23 Gb Se12).
          (*************)    (**)
  + right. exists T1. repeat split; try assumption.
    refine (subtyp_trans St12 _).
    apply (narrow_subtyp St23 Gb Se12).
          (*************)    (**)
Qed.
*)

Lemma subenv_sub: forall G1 G2 x T1 T2,
  subenv G1 G2 ->
  stable_typ T1 ->
  ok (G1 & x ~ T1) ->
  subtyp nohyp (G1 & x ~ T1) T1 T2 ->
  subenv (G1 & x ~ T1) (G2 & x ~ T2).
Proof.
  introv Se Sb Ok St. unfold subenv in *. intros v V Bi.
  apply binds_push_inv in Bi. destruct Bi as [[? ?] | [Ne Bi]].
  - subst. right. exists T1. auto.
  - specialize (Se _ _ Bi). destruct Se as [Bi' | Se].
    * left. auto.
    * right. destruct Se as [V' [Bi' [StV Sb']]]. exists V'.
      refine (conj _ (conj _ Sb')).
      + auto.
      + apply (weaken_subtyp_end Ok StV).
Qed.

Lemma subenv_push: forall G1 G2 x T,
  ok (G1 & x ~ T) ->
  subenv G1 G2 ->
  subenv (G1 & x ~ T) (G2 & x ~ T).
Proof.
  unfold subenv. introv Ok Se. intros v V Bi.
  apply binds_push_inv in Bi. destruct Bi as [[? ?] | [Ne Bi]].
  - subst. auto.
  - specialize (Se _ _ Bi). destruct Se as [Bi' | Se].
    * left. auto.
    * right. destruct Se as [V' [Bi' [StV Sb']]]. exists V'.
      refine (conj _ (conj _ Sb')).
      + auto.
      + apply (weaken_subtyp_end Ok StV).
Qed.

Lemma subenv_skip: forall G1 G2 x T,
  ok (G1 & x ~ T) ->
  subenv G1 G2 ->
  subenv (G1 & x ~ T) G2.
Proof.
  introv Ok Se. unfold subenv in *. intros v V Bi.
  assert (Ne: v <> x). {
    intro Eq. subst. specialize (Se _ _ Bi).
    assert (E: exists V', binds x V' G1). {
      destruct Se as [Bi' | [V' [Bi' _]]]; eauto.
    }
    destruct E as [V' Bi'].
    apply ok_push_inv in Ok. destruct Ok as [_ xG1]. apply (binds_fresh_inv Bi' xG1).
  }
  specialize (Se _ _ Bi). destruct Se as [Bi' | Se].
  * left. apply* binds_push_neq.
  * right. destruct Se as [V' [Bi' [StV Sb']]]. exists V'.
    refine (conj _ (conj _ Sb')).
    + auto.
    + apply (weaken_subtyp_end Ok StV).
Qed.


(* ###################################################################### *)
(** ** Narrowing on term level *)

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
    lets WfT': (narrow_wf_typ WfT Se).
    lets P: (narrow_binds_5 WfT' Bi2 Se). destruct P as [T1 [Bi1 St]].
    lets WfT1: (proj1 (subtyp_regular St)).
    apply subtyp_to_okhyp in St.
    apply ty_sbsm with T1; eauto.
  + (* case ty_call *)
    introv Tyt IH1 T2Has Tyu IH2 WfV2. introv Ok Se.
    subst. rename T into T2, V into V2.
    specialize (IH1 _ Ok Se).
    specialize (IH2 _ Ok Se).
    lets P: (narrow_has T2Has Se (ty_trm_regular IH1)).
    destruct P as [D [T2Has' Sd]]. apply invert_subdec_mtd_sync_left in Sd.
    destruct Sd as [U2' [V2' [Eq [StU2 StV2]]]]. subst D.
    refine (ty_sbsm _ (subtyp_to_okhyp StV2)).
    apply (ty_call IH1 T2Has').
    - apply (ty_sbsm IH2 (subtyp_to_okhyp StU2)).
    - apply (proj1 (subtyp_regular StV2)).
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Ok1 Se. subst.
    apply_fresh ty_new as y; try assert (yL: y \notin L) by auto.
    - refine (IH1 y yL (G' & y ~ open_typ y T) _ (subenv_push _ Se)); auto.
    - refine (IH2 y yL (G' & y ~ open_typ y T) _ (subenv_push _ Se)); auto.
    - apply* narrow_wf_typ.
  + (* case ty_let *)
    introv Ty1 IH1 Ty2 IH2 Wf2 Ok Se.
    apply_fresh ty_let as y; try assert (yL: y \notin L) by auto.
    - apply (IH1 _ Ok Se).
    - refine (IH2 y yL (G' & y ~ T1) _ (subenv_push _ Se)); auto.
    - apply* narrow_wf_typ.
  + (* case ty_sbsm *)
    introv Ty IH St Ok Se. subst.
    apply ty_sbsm with T1.
    * apply* IH.
    * apply* narrow_subtyp.
  + (* case ty_tdef *)
    introv St Ok Se. subst.
    apply ty_tdef. apply* narrow_wf.
  + (* case ty_mdef *)
    introv WfT WfU Tyu IH Ok Se. subst.
    apply_fresh ty_mdef as y.
    - apply* narrow_wf_typ.
    - apply* narrow_wf_typ.
    - assert (yL: y \notin L) by auto.
      refine (IH y yL (G' & y ~ T) _ (subenv_push _ Se)); auto.
  + (* case ty_defs_nil *) eauto.
  + (* case ty_defs_cons *)
    intros. subst. apply* ty_defs_cons.
Qed.

Lemma narrow_ty_end: forall G x S1 S2 t T,
  ty_trm (G & x ~ S2) t T ->
  ok (G & x ~ S1) ->
  stable_typ S1 ->
  subtyp nohyp (G & x ~ S1) S1 S2 ->
  ty_trm (G & x ~ S1) t T.
Proof.
  introv Ty Ok Sb St. destruct narrow_ty as [P _].
  refine (P _ _ _ Ty (G & x ~ S1) Ok _).
  refine (subenv_sub (@subenv_refl G) Sb _ St). auto.
Qed.

Print Assumptions narrow_ty_end.


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
    introv Bix THas IH1 HiHas IH2 Eq Ok Biy. subst.
    specialize (IH1 _ _ _ eq_refl Ok Biy).
    specialize (IH2 _ _ _ eq_refl Ok Biy).
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
    introv Bix THas IH1 HiHasnt IH2 Eq Ok Biy. subst.
    specialize (IH1 _ _ _ eq_refl Ok Biy).
    specialize (IH2 _ _ _ eq_refl Ok Biy).
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
   (forall hm G T1 T2, subtyp hm G T1 T2 -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    subtyp hm (subst_ctx x y (G1 & G2)) (subst_typ x y T1) (subst_typ x y T2))
/\ (forall hm G D1 D2, subdec hm G D1 D2 -> forall G1 G2 x,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    subdec hm (subst_ctx x y (G1 & G2)) (subst_dec x y D1) (subst_dec x y D2)).
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
  + (* case subtyp_hyp *)
    introv Bix XHas Sb WfX WfLo WfHi Eq Ok Biy. subst.
    lets Bix': (subst_binds Bix Ok Biy).
    apply subtyp_hyp with (subst_fvar x0 y x) (subst_typ x0 y X) L.
    * apply Bix'.
    * apply (subst_has XHas Ok Biy).
    * apply (subst_stable_typ _ _ Sb).
    * eauto.
    * eauto.
    * eauto.
  + (* case subdec_typ *)
    intros. subst. eq_specialize. apply subdec_typ; eauto.
  + (* case subdec_mtd *)
    intros. subst. eq_specialize. apply subdec_mtd; eauto.
  Grab Existential Variables.
  chicken. chicken. chicken.
  chicken. chicken. chicken. chicken. chicken.
  chicken. chicken.
  chicken. chicken. chicken.
Qed.

Print Assumptions subst_subtyp_subdec.

Lemma subst_subtyp: forall hm G1 x y S G2 T1 T2,
  subtyp hm (G1 & x ~ S & G2) T1 T2 ->
  ok (G1 & x ~ S & G2) ->
  binds y (subst_typ x y S) (G1 & G2) ->
  subtyp hm (subst_ctx x y (G1 & G2)) (subst_typ x y T1) (subst_typ x y T2).
Proof.
  intros. apply* subst_subtyp_subdec.
Qed.

Lemma subtyp_subst_principle: forall hm G x y S T1 T2,
  subtyp hm (G & x ~ S) T1 T2 ->
  ok (G & x ~ S) ->
  binds y (subst_typ x y S) G ->
  subtyp hm (subst_ctx x y G) (subst_typ x y T1) (subst_typ x y T2).
Proof.
  introv St Ok Biy.
  destruct (subst_subtyp_subdec y S) as [P _].
  specialize (P _ _ _ _ St G empty x). repeat rewrite concat_empty_r in P.
  apply (P eq_refl Ok Biy).
Qed.

Lemma subst_ctx_concat: forall x y G1 G2,
   subst_ctx x y (G1 & G2) = (subst_ctx x y G1) & (subst_ctx x y G2).
Proof.
  intros. unfold subst_ctx. apply map_concat.
Qed.

Lemma subst_ty:
   (forall G t T, ty_trm G t T -> forall G1 x y S G2,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    ty_trm (subst_ctx x y (G1 & G2)) (subst_trm x y t) (subst_typ x y T))
/\ (forall G d D, ty_def G d D -> forall G1 x y S G2,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    ty_def (subst_ctx x y (G1 & G2)) (subst_def x y d) (subst_dec x y D))
/\ (forall G ds T, ty_defs G ds T -> forall G1 x y S G2,
    G = G1 & x ~ S & G2  ->
    ok (G1 & x ~ S & G2) ->
    binds y (subst_typ x y S) (G1 & G2) ->
    ty_defs (subst_ctx x y (G1 & G2)) (subst_defs x y ds) (subst_typ x y T)).
Proof.
  apply ty_mutind.
  + (* case ty_var *)
    introv Bix WfT Eq Ok Biy. subst.
    lets Bix': (subst_binds Bix Ok Biy).
    simpl. rewrite if_hoist.
    apply (ty_var Bix'). eauto.
  + (* case ty_call *)
    introv Tyt IH1 THas Tyu IH2 WfV Eq Ok Biy. subst.
    lets THas': (subst_has THas Ok Biy). simpl.
    specialize (IH1 _ _ y0 _ _ eq_refl).
    specialize (IH2 _ _ y0 _ _ eq_refl).
    simpl in *. repeat rewrite if_hoist in *.
    apply ty_call with (subst_typ x y0 T) (subst_typ x y0 U); eauto.
  + (* case ty_new *)
    introv Tyds IH1 Tyu IH2 WfU Eq Ok Biy. subst.
    apply_fresh ty_new as x'; fold subst_defs subst_trm.
    - assert (x'L: x' \notin L) by auto. clear IH2.
      specialize (IH1 _ x'L G1 x y S (G2 & x' ~ open_typ x' T)).
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
      specialize (IH2 _ x'L G1 x y S (G2 & x' ~ open_typ x' T)).
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
  + (* case ty_let *)
    introv Ty1 IH1 Ty2 IH2 Wf2 Eq Ok Biy. subst. simpl.
    apply_fresh ty_let as z.
    - apply* IH1.
    - assert (zL: z \notin L) by auto.
      specialize (IH2 z zL G1 x y S (G2 & z ~ T1)).
      repeat rewrite concat_assoc in IH2.
      rewrite subst_ctx_concat in IH2. unfold subst_ctx in IH2 at 2.
      rewrite map_single in IH2.
      assert (Eqz: subst_fvar x y z = z) by (unfold subst_fvar; case_var* ).
      lets P: (@subst_open_commute_trm x y z t2). rewrite Eqz in P.
      rewrite P in IH2. clear P. apply* IH2.
    - apply* subst_wf_typ.
  + (* case ty_sbsm *)
    introv Ty IH St Eq Ok Biy. subst.
    lets St': (subst_subtyp St Ok Biy). apply ty_sbsm with (subst_typ x y T1); eauto.
  + (* case ty_tdef *)
    introv St Eq Ok Biy. subst.
    apply ty_tdef; eauto.
  + (* case ty_mdef *)
    introv WfT WfU2 Tyu IH Eq Ok Biy. subst.
    apply_fresh ty_mdef as x'.
    - eauto.
    - eauto.
    - fold subst_trm.
      assert (x'L: x' \notin L) by auto.
      specialize (IH x' x'L G1 x y S (G2 & x' ~ T)).
      repeat rewrite concat_assoc in IH.
      assert (Ok': ok (G1 & x ~ S & G2 & x' ~ T)) by auto.
      specialize (IH eq_refl Ok').
      assert (Eqz: subst_fvar x y x' = x') by (unfold subst_fvar; case_var*).
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
  Grab Existential Variables. constructor. constructor. constructor. constructor.
Qed.

Lemma trm_subst_principle: forall G x y t S T,
  ty_trm (G & x ~ S) t T ->
  ok (G & x ~ S) ->
  x \notin fv_ctx_types G ->
  binds y (subst_typ x y S) G ->
  ty_trm G (subst_trm x y t) (subst_typ x y T).
Proof.
  introv Ty Ok Fr Biy.
  destruct subst_ty as [P _].
  specialize (P _ _ _ Ty G x y S empty).
  repeat rewrite concat_empty_r in P.
  specialize (P eq_refl Ok Biy).
  rewrite (subst_fresh_ctx _ _ Fr) in P.
  exact P.
Qed.

Lemma defs_subst_principle: forall G x y ds S T,
  ty_defs (G & x ~ S) ds T ->
  ok (G & x ~ S) ->
  x \notin fv_ctx_types G ->
  binds y (subst_typ x y S) G ->
  ty_defs G (subst_defs x y ds) (subst_typ x y T).
Proof.
  introv Ty Ok Fr Biy.
  destruct subst_ty as [_ [_ P]].
  specialize (P _ _ _ Ty G x y S empty).
  repeat rewrite concat_empty_r in P.
  specialize (P eq_refl Ok Biy).
  rewrite (subst_fresh_ctx _ _ Fr) in P.
  exact P.
Qed.


(* ###################################################################### *)
(** ** Weakening corollaries of the general narrowing+weakening *)

Lemma subenv_concat: forall G1 G2,
  ok (G1 & G2) ->
  subenv (G1 & G2) G1.
Proof.
  intro G1. apply (env_ind (fun G2 => ok (G1 & G2) -> subenv (G1 & G2) G1)).
  - intro Ok. rewrite concat_empty_r. apply subenv_refl.
  - intros G2 x T IH Ok. rewrite concat_assoc in *. refine (subenv_skip Ok (IH _)). auto.
Qed.

Lemma weaken_ty_trm_end: forall G1 G2 t T,
  ok (G1 & G2) -> 
  ty_trm G1        t T ->
  ty_trm (G1 & G2) t T.
Proof.
  introv Ok Ty. lets Se: (subenv_concat Ok).
  apply ((proj31 narrow_ty) _ _ _ Ty _ Ok Se).
Qed.

Lemma weaken_ty_defs_end: forall G1 G2 ds T,
  ok (G1 & G2) -> ty_defs G1 ds T -> ty_defs (G1 & G2) ds T.
Proof.
  introv Ok Ty. lets Se: (subenv_concat Ok).
  apply ((proj33 narrow_ty) _ _ _ Ty _ Ok Se).
Qed.

Print Assumptions weaken_ty_defs_end.

Lemma subenv_weaken_middle: forall G1 G2 G3,
  ok (G1 & G2 & G3) ->
  subenv (G1 & G2 & G3) (G1 & G3).
Proof.
  intros G1 G2 G3. gen G3.
  apply (env_ind (fun G3 => ok (G1 & G2 & G3) -> subenv (G1 & G2 & G3) (G1 & G3))).
  - do 2 rewrite concat_empty_r. apply subenv_concat.
  - intros G3 x T IH Ok. repeat rewrite concat_assoc in *.
    refine (subenv_push Ok (IH _)). auto.
Qed.

Lemma weaken_ty_trm_middle: forall G1 G2 G3 t T,
  ok (G1 & G2 & G3) -> ty_trm (G1 & G3) t T -> ty_trm (G1 & G2 & G3) t T.
Proof.
  introv Ok Ty. lets Se: (subenv_weaken_middle Ok).
  apply ((proj31 narrow_ty) _ _ _ Ty _ Ok Se).
Qed.

Lemma weaken_ty_defs_middle: forall G1 G2 G3 ds T,
  ok (G1 & G2 & G3) -> ty_defs (G1 & G3) ds T -> ty_defs (G1 & G2 & G3) ds T.
Proof.
  introv Ok Ty. lets Se: (subenv_weaken_middle Ok).
  apply ((proj33 narrow_ty) _ _ _ Ty _ Ok Se).
Qed.


(* ###################################################################### *)
(** ** Helpers *)

Lemma invert_ty_var: forall G x T,
  ty_trm G (trm_var (avar_f x)) T ->
  exists T', binds x T' G /\ subtyp okhyp G T' T.
Proof.
  introv Ty. gen_eq t: (trm_var (avar_f x)). induction Ty; intro Eq; inversions Eq.
  - exists T. auto.
  - specialize (IHTy eq_refl). destruct IHTy as [T0 [Bi St]].
    exists T0. apply (conj Bi). apply (subtyp_trans St H).
Qed.

Lemma ctx_binds_to_sto_binds: forall s G x T,
  wf_sto s G ->
  binds x T G ->
  exists ds, binds x ds s /\ ty_defs G ds T.
Proof.
  introv Wf Bi.
  lets P: (ctx_binds_to_sto_binds_raw Wf Bi).
  destruct P as [G1 [G2 [ds [Eq [Bis Tyds]]]]]. subst.
  exists ds. apply (conj Bis). refine (weaken_ty_defs_end _ Tyds).
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
      exists U. apply (conj Bi'). refine (weaken_ty_defs_end _ Tyds).
      (* apply (wf_sto_to_good_bounds Wf). *)
      * apply wf_sto_to_ok_G in Wf. auto.
Qed.

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
(** ** okhyp to nohyp *)

Lemma anyhyp_to_nohyp:
   (forall hm G T1 T2, subtyp hm G T1 T2 -> good_bounds G -> subtyp nohyp G T1 T2)
/\ (forall hm G D1 D2, subdec hm G D1 D2 -> good_bounds G -> subdec nohyp G D1 D2).
Proof.
  apply subtyp_mutind.
  + (* case subtyp_refl *) auto.
  + (* case subtyp_top *) auto.
  + (* case subtyp_bot *) auto.
  + (* case subtyp_rcd *) auto.
  + (* case subtyp_sel_l *)
    introv Bix WfX Sb XHas St IH Gb. apply (subtyp_sel_l Bix WfX Sb XHas (IH Gb)).
  + (* case subtyp_sel_r *)
    introv Bix WfX Sb XHas St IH Gb. apply (subtyp_sel_r Bix WfX Sb XHas (IH Gb)).
  + (* case subtyp_and *) auto.
  + (* case subtyp_and_l *) auto.
  + (* case subtyp_and_r *) auto.
  + (* case subtyp_or *) auto.
  + (* case subtyp_or_l *) auto.
  + (* case subtyp_or_r *) auto.
  + (* case subtyp_trans *) eauto.
  + (* case subtyp_hyp *)
    introv Bix XHas Sb WfX WfLo WfHi Gb.
    unfold good_bounds, good_bounds_typ in Gb. specialize (Gb _ _ Bix).
    destruct Gb as [_ Gb]. apply (Gb _ _ _ XHas).
  + (* case subdec_typ *) auto.
  + (* case subdec_mtd *) auto.
Qed.

Definition subtyp_to_nohyp := proj1 anyhyp_to_nohyp.
Definition subdec_to_nohyp := proj2 anyhyp_to_nohyp.


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
      destruct IHrec as [s' [e' IHrec]].
      (* contradiction: vars don't step *)
      inversions IHrec.
    - (* case receiver is  a var *)
      destruct IHrec as [x [ds [Eq Bis]]]. inversions Eq.
      specialize (IHarg s Wfs). destruct IHarg as [IHarg | IHarg].
      * (* arg is an expression *)
        destruct IHarg as [s' [e' IHarg]].
        (* contradiction: vars don't step *)
        inversions IHarg.
      * (* arg is a var *)
        destruct IHarg as [z' [o [Eq Bisz]]]. symmetry in Eq. inversions Eq.
        apply invert_ty_var in Ty1.
        destruct Ty1 as [T' [BiG StT]].
        lets P: (subtyp_to_memberwise (subtyp_to_nohyp StT (wf_sto_to_good_bounds Wfs))).
        destruct P as [P _]. specialize (P _ THas). destruct P as [D1 [T'Has Sd]].
        apply invert_subdec_mtd_sync_left in Sd. destruct Sd as [U' [V' [Eq [StU StV]]]].
        subst.
        lets P: (typ_has_to_defs_has Wfs T'Has Bis BiG).
        destruct P as [d [dsHas Tyd]].
        inversions Tyd. rename H4 into WfU', H5 into WfV', H6 into Tybody.
        exists (open_trm z u) s.
        apply (red_call z Bis dsHas).
  + (* case ty_new *)
    introv Tyds Tyu IH WfU Wfs.
    left. pick_fresh x.
    exists (open_trm x u) (s & x ~ (open_defs x ds)).
    apply* red_new.
  + (* case ty_let *)
    introv Ty1 IH1 Ty2 IH2 Wf2 Wfs.
    specialize (IH1 s Wfs). destruct IH1 as [IH1 | IH1].
    - (* case t1 can step *)
      destruct IH1 as [t1' [s' IH1]].
      left. exists (trm_let t1' t2) s'. apply (red_let_1 _ IH1).
    - (* case t1 is a var *)
      destruct IH1 as [x [o [Eq Bix]]]. subst.
      left. exists (open_trm x t2) s. apply red_let_2.
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
    lets Ty': (weaken_ty_defs_middle Okyx Ty).
    rewrite* (@subst_intro_defs x y ds).
    lets P: (@defs_subst_principle _ x y _ _ _ Ty' Okyx).
    assert (FrT: x \notin (fv_typ T)) by auto.
    rewrite <- (@subst_intro_typ x y T FrT) in P.
    assert (FrS: x \notin (fv_typ S)) by auto.
    rewrite <- (@subst_intro_typ x y S FrS) in P.
    assert (Fr': (x \notin (fv_ctx_types (G & y ~ open_typ y S)))). {
      rewrite fv_ctx_types_push. rewrite notin_union. auto.
    }
    apply P.
    - assumption.
    - apply binds_push_eq.
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
    lets Ty': (weaken_ty_trm_middle Okyx Ty).
    rewrite* (@subst_intro_trm x y t).
    lets P: (@trm_subst_principle _ _ y _ _ _ Ty' Okyx).
    assert (FrS: x \notin (fv_typ S)) by auto.
    rewrite <- (@subst_intro_typ x y S FrS) in P.
    assert (FrT: x \notin (fv_typ T)) by auto.
    rewrite (@subst_fresh_typ x y T FrT) in P.
    assert (Fr': (x \notin (fv_ctx_types (G & y ~ open_typ y S)))). {
      rewrite fv_ctx_types_push. rewrite notin_union. auto.
    }
    apply P.
    - assumption.
    - apply binds_push_eq.
Qed.

Lemma defs_have_stable_typ: forall G ds T,
  ty_defs G ds T -> stable_typ T.
Proof.
  introv Tyds. induction Tyds; eauto.
Qed.

Lemma invert_ty_new: forall G ds u U,
  ok G ->
  ty_trm G (trm_new ds u) U ->
  exists L T,
     (forall x, x \notin L ->
        ty_defs (G & x ~ open_typ x T) (open_defs x ds) (open_typ x T))
  /\ (forall x, x \notin L ->
        ty_trm (G & x ~ open_typ x T) (open_trm x u) U)
  /\ (wf_typ G U).
Proof.
  introv Ok Ty. gen_eq t: (trm_new ds u). induction Ty; intro Eq; inversions Eq.
  - eauto.
  - specialize (IHTy Ok eq_refl).
    destruct IHTy as [L [T0 [Tyds [Tyu Wf]]]].
    subst. let L0 := gather_vars in exists L0 T0. repeat split.
    * intros x xFr. assert (xL: x \notin L) by auto. apply (Tyds x xL).
    * intros x xFr. assert (xL: x \notin L) by auto.
      apply (ty_sbsm (Tyu x xL)). refine (weaken_subtyp_end _ H). auto.
    * apply (proj2 (subtyp_regular H)).
Qed.

Lemma invert_ty_call: forall G y m V2 z,
  ty_trm G (trm_call y m z) V2 ->
  exists T U V1,
    ty_trm G (trm_var y) T /\
    typ_has G T (dec_mtd m U V1) /\
    ty_trm G (trm_var z) U /\
    subtyp okhyp G V1 V2.
Proof.
  introv Ty. gen_eq t0: (trm_call y m z). induction Ty; intro Eq; inversions Eq.
  - do 3 eexists. eauto.
  - specialize (IHTy eq_refl). destruct IHTy as [T [U [V [Tyt [THas [Tyu St]]]]]].
    exists T U V. repeat split; auto. apply (subtyp_trans St H).
Qed.

Lemma invert_ty_let: forall G t1 t2 T2,
  ok G ->
  ty_trm G (trm_let t1 t2) T2 ->
  exists L T1,
    ty_trm G t1 T1 /\
    (forall x, x \notin L -> ty_trm (G & x ~ T1) (open_trm x t2) T2) /\
    wf_typ G T2.
Proof.
  introv Ok Ty. gen_eq t: (trm_let t1 t2). gen t1 t2.
  induction Ty; introv Eq; try discriminate.
  - symmetry in Eq. inversions Eq. eauto.
  - subst. specialize (IHTy Ok _ _ eq_refl). destruct IHTy as [L [T0 [Ty1 [Ty2 Wf]]]].
    let L0 := gather_vars in exists L0 T0.
    apply (conj Ty1). refine (conj _ (subtyp_regular_2 H)).
    intros x xFr. assert (xL: x \notin L) by auto. specialize (Ty2 x xL).
    apply (ty_sbsm Ty2). refine (weaken_subtyp_end _ H). auto.
Qed.

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
      inversions Tyd. eauto.
  - specialize (Gb x X Bix). apply (weaken_good_bounds_typ_end Ok Gb).
Qed.

Print Assumptions good_bounds_push_ty_defs.


(* ###################################################################### *)
(** ** Preservation *)

Theorem preservation_result: preservation.
Proof.
  introv Wf Ty Red. gen G T Wf Ty. induction Red.
  + (* red_call *)
    intros G V Wf TyCall.
    rename H into Bis, H0 into dsHas, T into U2, U into V2, V into V2'.
    exists (@empty typ). rewrite concat_empty_r. apply (conj Wf).
    lets Gb: (wf_sto_to_good_bounds Wf).
    apply invert_ty_call in TyCall.
    destruct TyCall as [T [U2'' [V2'' [Tyx [THas [Tyy StV]]]]]].
    apply invert_ty_var in Tyx. destruct Tyx as [T' [BiGx StT]].
    apply invert_ty_var in Tyy. destruct Tyy as [U2''' [BiGy StU2]].
    lets P: (subtyp_to_memberwise (subtyp_to_nohyp StT (wf_sto_to_good_bounds Wf))).
    destruct P as [P _]. specialize (P _ THas). destruct P as [D1 [T'Has Sd]].
    apply invert_subdec_mtd_sync_left in Sd. destruct Sd as [U1 [V1 [Eq [StU1 StV']]]].
    subst D1.
    lets P: (typ_has_to_defs_has Wf T'Has Bis BiGx). destruct P as [d [dsHas' Tyd]].
    inversions Tyd.
    clear H4. rename H5 into WfV, H6 into Tybody, u into body'.
    assert (Eq: def_mtd m U1 V1 body' = def_mtd m U2 V2 body). {
      refine (defs_has_unique _ dsHas' dsHas). reflexivity.
    }
    inversions Eq. clear dsHas'.
    rename U2''' into U1.
    lets StU: (subtyp_trans StU2 (subtyp_to_okhyp StU1)).
    pick_fresh y'.
    assert (y'L: y' \notin L) by auto.
    specialize (Tybody y' y'L).
    lets Ok: (wf_sto_to_ok_G Wf).
    (* Before we can apply the substitution principle, we must narrow 
       y' ~ U2 to y' ~ U1 in Tybody. *)
    lets StU0: (subtyp_to_nohyp StU (wf_sto_to_good_bounds Wf)). clear StU.
    assert (Oky': ok (G & y' ~ U1)) by auto.
    lets StU: (weaken_subtyp_end Oky' StU0).
    destruct (ctx_binds_to_sto_binds Wf BiGy) as [dsy [Bisy Tydsy]].
    lets SbU1: (defs_have_stable_typ Tydsy).
    lets Tybody': (narrow_ty_end Tybody Oky' SbU1 StU).
                  (*****************)
    assert (y'G: y' \notin fv_ctx_types G) by auto.
    lets P: (@trm_subst_principle G y' y _ U1 V2 Tybody' Oky').
             (*******************)
    assert (y'U1: y' \notin (fv_typ U1)) by auto.
    rewrite (@subst_fresh_typ y' y U1 y'U1) in P.
    assert (y'body: y' \notin (fv_trm body)) by auto.
    rewrite <- (@subst_intro_trm y' y body y'body) in P.
    apply (ty_sbsm (P y'G BiGy)).
    assert (EqV2: (subst_typ y' y V2) = V2). { refine (@subst_fresh_typ y' y _ _). auto. }
    rewrite EqV2. apply (subtyp_trans (subtyp_to_okhyp StV') StV).
  + (* red_new *)
    introv Wf Ty.
    lets Gb: (wf_sto_to_good_bounds Wf).
    apply (invert_ty_new (wf_sto_to_ok_G Wf)) in Ty.
    destruct Ty as [L [Tds [Tyds [Tyt WfT]]]].
    exists (x ~ (open_typ x Tds)).
    assert (xG: x # G) by apply* sto_unbound_to_ctx_unbound.
    lets Ok: (wf_sto_to_ok_G Wf).
    assert (Okx: forall X, ok (G & x ~ X)) by auto.
    lets C1: (@ty_open_defs_change_var x G Tds ds Tds Ok xG). destruct C1 as [L1 C1].
    lets C2: (@ty_open_trm_change_var  x G Tds t  T   Ok xG). destruct C2 as [L2 C2].
    pick_fresh x'.
    assert (x'L: x' \notin L) by auto.
    assert (x'L1: x' \notin L1) by auto.
    assert (x'L2: x' \notin L2) by auto.
    specialize (Tyds x' x'L). specialize (Tyt x' x'L).
    split.
    - refine (wf_sto_push Wf H xG _). apply* C1.
      apply (good_bounds_push_ty_defs Gb Tyds). auto.
    - apply* C2.
      apply (good_bounds_push_ty_defs Gb Tyds). auto.
  + (* red_let_2 *)
    introv Wf Tyt. exists (@empty typ). rewrite concat_empty_r. apply (conj Wf).
    lets Ok: (wf_sto_to_ok_G Wf).
    apply (invert_ty_let Ok) in Tyt. rename T into T2, t into t2.
    destruct Tyt as [L [T1 [Ty1 [Ty2 Wf2]]]].
    apply invert_ty_var in Ty1. destruct Ty1 as [T1' [BiGy St1]].
    pick_fresh y'.
    assert (y'L: y' \notin L) by auto.
    specialize (Ty2 y' y'L).
    (* Before we can apply the substitution principle, we must narrow 
       y' ~ T1 to y' ~ T1' in Ty2. *)
    lets St10: (subtyp_to_nohyp St1 (wf_sto_to_good_bounds Wf)). clear St1.
    assert (Oky': ok (G & y' ~ T1')) by auto.
    lets St1: (weaken_subtyp_end Oky' St10).
    destruct (ctx_binds_to_sto_binds Wf BiGy) as [dsy [Bisy Tydsy]].
    lets SbT1': (defs_have_stable_typ Tydsy).
    lets Ty2': (narrow_ty_end Ty2 Oky' SbT1' St1).
               (*************)
    assert (y'G: y' \notin fv_ctx_types G) by auto.
    lets P: (@trm_subst_principle G y' y _ T1' T2 Ty2' Oky').
             (*******************)
    assert (y'T1': y' \notin (fv_typ T1')) by auto.
    rewrite (@subst_fresh_typ y' y _ y'T1') in P.
    assert (y't2: y' \notin (fv_trm t2)) by auto.
    rewrite <- (@subst_intro_trm y' y t2 y't2) in P.
    assert (Eq: (subst_typ y' y T2) = T2). { refine (@subst_fresh_typ y' y _ _). auto. }
    rewrite Eq in P. apply (P y'G BiGy).
  + (* red_let_1 *)
    introv Wf Ty.
    lets Ok: (wf_sto_to_ok_G Wf). rename T into T2.
    apply (invert_ty_let Ok) in Ty.
    destruct Ty as [L [T1 [Ty1 [Ty2 Wf2]]]].
    specialize (IHRed _ _ Wf Ty1). destruct IHRed as [G' [Wf' Ty1']].
    exists G'. apply (conj Wf'). apply ty_let with (L \u (dom G) \u (dom G')) T1.
    - exact Ty1'.
    - intros x xL. apply* weaken_ty_trm_middle.
    - apply* weaken_wf_typ_end.
Qed.

Check progress_result.
Print progress.
Print Assumptions progress_result.

Check preservation_result.
Print preservation.
Print Assumptions preservation_result.
