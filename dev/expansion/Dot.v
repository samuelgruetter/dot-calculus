Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.

(** Utilities **)
(* For some reason,
   the default map on env is opaque, and so
   it cannot be used in recursive definitions. *)
Definition envmap {A B: Type} (f: A -> B) (E: env A): env B :=
  List.map (fun p => (fst p, f (snd p))) E.
Definition EnvForall {A: Type} (P: A -> Prop) (E: env A): Prop :=
  List.Forall (fun p => P (snd p)) E.

(** Syntax **)

Definition label := var.

Inductive avar : Type :=
  | avar_b : nat -> avar
  | avar_f : var -> avar
.

Inductive pth : Type :=
  | pth_var : avar -> pth
  | pth_sel : pth -> label -> pth
.

Inductive typ : Type :=
  | typ_asel : pth -> label -> typ (* select abstract type *)
  | typ_csel : pth -> label -> typ (* select concrete type *)
  | typ_rfn  : typ -> env dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_or   : typ -> typ -> typ
  | typ_top  : typ
  | typ_bot  : typ
with cyp : Type := (* concrete/class type *)
  | cyp_csel : pth -> label -> cyp
  | cyp_rfn  : cyp -> env dec -> cyp
  | cyp_and  : cyp -> cyp -> cyp
  | cyp_top  : cyp
with dec : Type :=
  | dec_typ  : typ -> typ -> dec
  | dec_cyp  : cyp -> dec
  | dec_fld  : typ -> dec
  | dec_mtd  : typ -> typ -> dec
.

Inductive trm : Type :=
  | trm_var  : avar -> trm
  | trm_new  : cyp -> env def -> trm -> trm
  | trm_sel  : trm -> label -> trm
  | trm_cll  : trm -> label -> trm -> trm (* call *)
with def : Type :=
  | def_fld : avar -> def
  | def_mtd : trm -> def
  | def_non : def (* place holder for matching type declarations *)
.

(* ... opening ...
   replaces in some syntax a bound variable with dangling index (k) by a free variable x
*)

Fixpoint open_rec_avar (k: nat) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end
.

Fixpoint open_rec_pth (k: nat) (u: var) (p: pth) { struct p } : pth :=
  match p with
  | pth_var a => pth_var (open_rec_avar k u a)
  | pth_sel p l => pth_sel (open_rec_pth k u p) l
  end
.

Fixpoint open_rec_typ (k: nat) (u: var) (t: typ) { struct t } : typ :=
  match t with
  | typ_asel p l => typ_asel (open_rec_pth k u p) l
  | typ_csel p l => typ_csel (open_rec_pth k u p) l
  | typ_rfn  t ds => typ_rfn (open_rec_typ k u t) (envmap (open_rec_dec (S k) u) ds)
  | typ_and t1 t2 => typ_and (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_or t1 t2 => typ_or (open_rec_typ k u t1) (open_rec_typ k u t2)
  | typ_top => typ_top
  | typ_bot => typ_bot
  end
with open_rec_cyp (k: nat) (u: var) (c: cyp) { struct c } : cyp :=
  match c with
  | cyp_csel p l => cyp_csel (open_rec_pth k u p) l
  | cyp_rfn  c ds => cyp_rfn (open_rec_cyp k u c) (envmap (open_rec_dec (S k) u) ds)
  | cyp_and c1 c2 => cyp_and (open_rec_cyp k u c1) (open_rec_cyp k u c2)
  | cyp_top => cyp_top
  end
with open_rec_dec (k: nat) (u: var) (d: dec) { struct d } : dec :=
  match d with
  | dec_typ ts tu => dec_typ (open_rec_typ k u ts) (open_rec_typ k u tu)
  | dec_cyp c => dec_cyp (open_rec_cyp k u c)
  | dec_fld t => dec_fld (open_rec_typ k u t)
  | dec_mtd ts tu => dec_mtd (open_rec_typ k u ts) (open_rec_typ k u tu)
  end
.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t } : trm :=
  match t with
  | trm_var a => trm_var (open_rec_avar k u a)
  | trm_new  c ds t => trm_new (open_rec_cyp k u c) (envmap (open_rec_def (S k) u) ds) (open_rec_trm (S k) u t)
  | trm_sel t l => trm_sel (open_rec_trm k u t) l
  | trm_cll o m a => trm_cll (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: nat) (u: var) (d: def) { struct d } : def :=
  match d with
  | def_fld a => def_fld (open_rec_avar k u a)
  | def_mtd t => def_mtd (open_rec_trm (S k) u t)
  | def_non => def_non
  end
.

(* Question: why do we change the order of the args here? I'd like to use a partially
   applied (open_dec u) for envmap *)
Definition open_avar a u := open_rec_avar 0 u a.
Definition open_pth p u := open_rec_pth 0 u p.
Definition open_typ t u := open_rec_typ 0 u t.
Definition open_cyp c u := open_rec_cyp 0 u c.
Definition open_dec d u := open_rec_dec 0 u d.
Definition open_decs ds u := (envmap (open_rec_dec 0 u) ds).
Definition open_trm t u := open_rec_trm 0 u t.
Definition open_def d u := open_rec_def 0 u d.


Inductive fvar : avar -> Prop :=
  | fvar_f : forall x,
      fvar (avar_f x).

Inductive path : pth -> Prop :=
  | path_var : forall a,
      fvar a ->
      path (pth_var a)
  | path_sel : forall p l,
      path p ->
      path (pth_sel p l).

Inductive type : typ -> Prop :=
  | type_asel : forall p l,
      path p ->
      type (typ_asel p l)
  | type_csel : forall p l,
      path p ->
      type (typ_csel p l)
  | type_rfn : forall L t ds,
      type t ->
      (forall x, x \notin L -> EnvForall (fun d => decl (open_dec d x)) ds) ->
      type (typ_rfn t ds)
  | type_and : forall t1 t2,
      type t1 ->
      type t2 ->
      type (typ_and t1 t2)
  | type_or : forall t1 t2,
      type t1 ->
      type t2 ->
      type (typ_or t1 t2)
  | type_top : type (typ_top)
  | type_bot : type (typ_bot)
with cype : cyp -> Prop :=
  | cype_csel : forall p l,
      path p ->
      cype (cyp_csel p l)
  | cype_rfn : forall L c ds,
      cype c ->
      (forall x, x \notin L -> EnvForall (fun d => decl (open_dec d x)) ds) ->
      cype (cyp_rfn c ds)
  | cype_and : forall c1 c2,
      cype c1 ->
      cype c2 ->
      cype (cyp_and c1 c2)
  | cype_top : cype (cyp_top)
with decl : dec -> Prop :=
  | decl_typ  : forall ts tu,
      type ts ->
      type tu ->
      decl (dec_typ ts tu)
  | decl_cyp  : forall c,
      cype c ->
      decl (dec_cyp c)
  | decl_fld : forall t,
      type t ->
      decl (dec_fld t)
  | decl_mtd : forall ts tu,
      type ts ->
      type tu ->
      decl (dec_mtd ts tu)
.

Inductive term : trm -> Prop :=
  | term_var : forall a,
      fvar a ->
      term (trm_var a)
  | term_new : forall L c ds t,
      cype c ->
      (forall x, x \notin L ->
         EnvForall (fun d => defn (open_def d x)) ds /\
         term (open_trm t x)) ->
      term (trm_new c ds t)
  | term_sel : forall t l,
       term t ->
       term (trm_sel t l)
  | term_cll : forall o m a,
       term o ->
       term a ->
       term (trm_cll o m a)
with defn : def -> Prop :=
  | defn_fld : forall a,
       fvar a ->
       defn (def_fld a)
  | defn_mtd : forall L t,
       (forall x, x \notin L -> term (open_trm t x)) ->
       defn (def_mtd t)
  | defn_non : defn (def_non)
.

(** Operational Semantics **)

Definition cds := (cyp * env def) % type.
Definition sto := env cds.

Inductive red : sto -> trm -> sto -> trm -> Prop :=
  (* computation rules *)
  | red_cll : forall s x m y c ds t,
      binds x (c, ds) s ->
      binds m (def_mtd t) ds ->
      red s (trm_cll (trm_var (avar_f x)) m (trm_var (avar_f y))) s (open_trm t y)
  | red_sel : forall s x l c ds y,
      binds x (c, ds) s ->
      binds l (def_fld y) ds ->
      red s (trm_sel (trm_var (avar_f x)) l) s (trm_var y)
  | red_new : forall s c ds t x,
      x # s ->
      red s (trm_new c ds t) (s & x ~ (c, ds)) (open_trm t x)
  (* congruence rules *)
  | red_cll1 : forall s o m a s' o',
      red s o s' o' ->
      red s (trm_cll o m a) s' (trm_cll o' m a)
  | red_cll2 : forall s x m a s' a',
      red s a s' a' ->
      red s (trm_cll (trm_var (avar_f x)) m a) s' (trm_cll (trm_var (avar_f x)) m a')
  | red_sel1 : forall s o l s' o',
      red s o s' o' ->
      red s (trm_sel o l) s' (trm_sel o' l)
.


(** Infrastructure **)

Fixpoint pth2trm (p: pth) { struct p } : trm :=
  match p with
    | pth_var a => trm_var a
    | pth_sel p l => trm_sel (pth2trm p) l
  end.

Fixpoint cyp2typ (c: cyp) { struct c } : typ :=
  match c with
  | cyp_csel p k => typ_csel p k
  | cyp_rfn c ds => typ_rfn (cyp2typ c) ds
  | cyp_and c1 c2 => typ_and (cyp2typ c1) (cyp2typ c2)
  | cyp_top => typ_top
  end.

Fixpoint fv_avar (a: avar) { struct a } : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end
.

Fixpoint fv_pth (p: pth) { struct p } : vars :=
  match p with
  | pth_var a => fv_avar a
  | pth_sel p l => fv_pth p
  end
.

Fixpoint fv_typ (t: typ) { struct t } : vars :=
  match t with
  | typ_asel p l => fv_pth p
  | typ_csel p l => fv_pth p
  | typ_rfn  t ds => (fv_typ t) \u (fold_vars id (envmap fv_dec ds))
  | typ_and t1 t2 => (fv_typ t1) \u (fv_typ t2)
  | typ_or t1 t2 => (fv_typ t1) \u (fv_typ t2)
  | typ_top => \{}
  | typ_bot => \{}
  end
with fv_cyp (c: cyp) { struct c } : vars :=
  match c with
  | cyp_csel p l => fv_pth p
  | cyp_rfn  c ds => (fv_cyp c) \u (fold_vars id (envmap fv_dec ds))
  | cyp_and c1 c2 => (fv_cyp c1) \u (fv_cyp c2)
  | cyp_top => \{}
  end
with fv_dec (d: dec) { struct d } : vars :=
  match d with
  | dec_typ ts tu => (fv_typ ts) \u (fv_typ tu)
  | dec_cyp c => fv_cyp c
  | dec_fld t => fv_typ t
  | dec_mtd ts tu => (fv_typ ts) \u (fv_typ tu)
  end
.

Fixpoint fv_trm (t: trm) { struct t } : vars :=
  match t with
  | trm_var a => fv_avar a
  | trm_new  c ds t => (fv_cyp c) \u (fold_vars id (envmap fv_def ds)) \u (fv_trm t)
  | trm_sel t l => fv_trm t
  | trm_cll o m a => (fv_trm o) \u (fv_trm a)
  end
with fv_def (d: def) { struct d } : vars :=
  match d with
  | def_fld a => fv_avar a
  | def_mtd t => fv_trm t
  | def_non => \{}
  end
.

(** Typing **)

Definition ctx := env typ.

(* We want to use (env dec) for list of declarations
   => keys of declaration lists are label (=var)
   => no way to tell (get myLabel myEnv) what kind of declaration we want
   => all 4 kinds of declarations share the same namespace for their labels
   => there are invalid intersections
   => declaration intersection must be implemented as
      - functions returning option, or
      - Props
      Question: Which of these two is better?
      Question: Or should we choose a different data structure than (env dec),
                which also rejects duplicate names?
*)

(*
(* declaration intersection/union with functions returning option: not so nice *)

(* intersect two declarations if they're of the same kind, otherwise return None *)
Definition dec_dec_intersect(d1: dec)(d2: dec): option dec := 
  match d1 with
  | dec_typ Lo1 Hi1 => match d2 with
    | dec_typ Lo2 Hi2 => Some (dec_typ (typ_or Lo1 Lo2) (typ_and Hi1 Hi2))
    | _ => None
    end
  | dec_cyp U1 => match d2 with
    | dec_cyp U2 => Some(dec_cyp (cyp_and U1 U2))
    | _ => None
    end
  | dec_fld T1 => match d2 with
    | dec_fld T2 => Some(dec_fld (typ_and T1 T2))
    | _ => None
    end
  | dec_mtd S1 U1 => match d2 with
    | dec_mtd S2 U2 => Some(dec_mtd (typ_or S1 S2) (typ_and U1 U2))
    | _ => None
    end
  end.

(* union two declarations if possible, otherwise return None *)
Definition dec_dec_union(d1: dec)(d2: dec): option dec := 
  match d1 with
  | dec_typ Lo1 Hi1 => match d2 with
    | dec_typ Lo2 Hi2 => Some (dec_typ (typ_and Lo1 Lo2) (typ_or Hi1 Hi2))
    | _ => None
    end
  | dec_cyp U1 => None (* cyp has no union *)
  | dec_fld T1 => match d2 with
    | dec_fld T2 => Some(dec_fld (typ_or T1 T2))
    | _ => None
    end
  | dec_mtd S1 U1 => match d2 with
    | dec_mtd S2 U2 => Some(dec_mtd (typ_and S1 S2) (typ_or U1 U2))
    | _ => None
    end
  end.

(* intersect one dec with a set of decs *)
Definition decs_dec_intersect(D: env dec)(l: label)(d: dec): option (env dec) := 
  match get l D with
  | Some d' => match dec_dec_intersect d d' with
    | Some d'' => Some(D & l ~ d'') (* shadows previous binding for l *)
    | None => None (* d and d' are of different kinds *)
  end
  | None => Some D (* no change *)
end.
*)

(* declaration intersection/union using Props *)

Inductive dec_dec_intersect: dec -> dec -> dec -> Prop :=
  | dec_dec_intersect_typ : forall Lo1 Hi1 Lo2 Hi2,
      dec_dec_intersect (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2)
                        (dec_typ (typ_or Lo1 Lo2) (typ_and Hi1 Hi2))
  | dec_dec_intersect_cyp : forall U1 U2,
      dec_dec_intersect (dec_cyp U1) (dec_cyp U2)
                        (dec_cyp (cyp_and U1 U2))
  | dec_dec_intersect_fld : forall T1 T2,
      dec_dec_intersect (dec_fld T1) (dec_fld T2)
                        (dec_fld (typ_and T1 T2))
  | dec_dec_intersect_mtd : forall S1 U1 S2 U2,
      dec_dec_intersect (dec_mtd S1 U1) (dec_mtd S2 U2)
                        (dec_mtd (typ_or S1 S2) (typ_and U1 U2))
.

Inductive dec_dec_union: dec -> dec -> dec -> Prop :=
  | dec_dec_union_typ : forall Lo1 Hi1 Lo2 Hi2,
      dec_dec_union (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2)
                    (dec_typ (typ_and Lo1 Lo2) (typ_or Hi1 Hi2))
  (* note: no case for cyp *)
  | dec_dec_union_fld : forall T1 T2,
      dec_dec_union (dec_fld T1) (dec_fld T2)
                    (dec_fld (typ_or T1 T2))
  | dec_dec_union_mtd : forall S1 U1 S2 U2,
      dec_dec_union (dec_mtd S1 U1) (dec_mtd S2 U2)
                    (dec_mtd (typ_and S1 S2) (typ_or U1 U2))
.

(* TODO there are many ways to express this, is this the way we want it for the proofs? *)
Definition decs_intersect(D1 D2 D3: env dec): Prop :=
    dom D3 = (union (dom D1) (dom D2))
/\ (forall l d1 d2 d3, binds l d1 D1 /\ binds l d2 D2 /\ dec_dec_intersect d1 d2 d3
                      -> binds l d3 D3)
/\ (forall l d, binds l d D1 /\ l # D2 -> binds l d D3)
/\ (forall l d, l # D1 /\ binds l d D2 -> binds l d D3).

Definition decs_union(D1 D2 D3: env dec): Prop :=
    dom D3 = (inter (dom D1) (dom D2))
/\ (forall l d1 d2 d3, binds l d1 D1 /\ binds l d2 D2 /\ dec_dec_union d1 d2 d3
                      -> binds l d3 D3).

(* declaration D (taken from { z => Ds }) does not contain z *)
Definition dec_no_selfref(D: dec): Prop := forall (v: var), open_dec D v = D.

(* sub-declarations *)
Definition sub_decs(sub_dec: dec -> dec -> Prop)(D1 D2: env dec): Prop :=
  forall l d2, binds l d2 D2 -> (exists d1, binds l d1 D1 /\ sub_dec d1 d2).

(*
   ?question?:
   for now, just using # instead of cofinite quantification...
   ... we will see if it's enough
*)
(* Term typing *)
Inductive typing_trm : ctx -> trm -> typ -> Prop :=
  | typing_trm_var : forall G x T,
      binds x T G ->
      typing_trm G (trm_var (avar_f x)) T
  | typing_trm_sel : forall G t l T,
      weak_trm_mem G t l (dec_fld T) ->
      typing_trm G (trm_sel t l) T
  | typing_trm_app : forall G t m U T u,
      weak_trm_mem G t m (dec_mtd U T) ->
      typing_trm G u U ->
      typing_trm G (trm_cll t m u) T
  | typing_trm_new : forall G x c ds t T Tc Ds,
      Tc=(cyp2typ c) ->
      imp_typ G Tc ->
      strg_expand G Tc Ds ->
      x # G ->
      typing_defs (G & x ~ Tc) ds Ds ->
      typing_trm (G & x ~ Tc) (open_trm t x) T ->
      typing_trm G (trm_new c ds t) T
  | typing_trm_sub : forall G t T U,
      typing_trm G t T ->
      sub_typ G T U ->
      typing_trm G t U

(* Definition (implementation) typing *)
with typing_def : ctx -> def -> dec -> Prop :=
  | typing_def_fld : forall G v T,
      typing_trm G (trm_var v) T ->
      typing_def G (def_fld v) (dec_fld T)
  | typing_def_mtd : forall G x t S T,
      x # G ->
      x \notin fv_typ(T) ->
      typing_trm (G & x ~ S) (open_trm t x) T ->
      typing_def G (def_mtd t) (dec_mtd S T)
  | typing_def_typ : forall G S U,
      typing_def G def_non (dec_typ S U)
  | typing_def_cyp : forall G U,
      typing_def G def_non (dec_cyp U)
with typing_defs : ctx -> env def -> env dec -> Prop :=
  | typing_defs_all : forall G Defs Decs, 
      List.Forall2 (fun (p1: (label * def)) (p2: (label * dec)) => 
        (fst p1) = (fst p2) /\ typing_def G (snd p1) (snd p2)
      ) Defs Decs ->
      typing_defs G Defs Decs

(* Precise path typing *)
(* TODO: should accept a path instead of just a var *)
with typing_pth : ctx -> var -> typ -> Prop :=
  | typing_pth_var : forall G x T,
      binds x T G ->
      typing_pth G x T
(*| typing_pth_pth : TODO *)

(* Strong path membership *)
(* TODO: Should take a path instead of just a var => need to change open s.t. it
   also accepts a path instead of just a var. Question: Is this correct? *)
with strg_pth_mem : ctx -> var -> label -> dec -> Prop :=
  | strg_pth_mem_pth : forall G p l T Ds d,
      typing_pth G p T ->
      strg_expand G T Ds ->
      binds l d Ds ->
      strg_pth_mem G p l (open_dec d p)

(* Weak path membership *)
(* TODO allow any path *)
with weak_pth_mem : ctx -> var -> label -> dec -> Prop :=
  | weak_pth_mem_pth : forall G p T l Ds d,
      typing_trm G (trm_var (avar_f p)) T ->
      weak_expand G T Ds ->
      binds l d Ds ->
      weak_pth_mem G p l (open_dec d p)

(* Weak term membership *)
with weak_trm_mem : ctx -> trm -> label -> dec -> Prop :=
  | weak_trm_mem_trm : forall G t T l Ds d,
      typing_trm G t T ->
      weak_expand G T Ds ->
      binds l d Ds ->
      dec_no_selfref d ->   (* <---- Question: Is this ok? *) 
      weak_trm_mem G t l d

(* Implementable types *)
with imp_typ : ctx -> typ -> Prop :=
  | imp_typ_typ : forall G T Ds,
      wf_typ G T ->
      strg_expand G T Ds ->
      EnvForall (imp_dec G) Ds ->
      imp_typ G T

(* Implementable declarations *)
with imp_dec : ctx -> dec -> Prop :=
  | imp_dec_typ : forall G S U,
      sub_typ G S U ->
      imp_dec G (dec_typ S U)
  | imp_dec_cyp : forall G U,
      imp_typ G (cyp2typ U) ->
      imp_dec G (dec_cyp U)
  | imp_dec_fld : forall G T,
      imp_typ G T ->
      imp_dec G (dec_fld T)
  | imp_dec_mtd : forall G S U,
      (* note: no conditions here *)
      imp_dec G (dec_mtd S U)

(* Strong expansion *)
with strg_expand : ctx -> typ -> env dec -> Prop :=
  | strg_expand_rfn : forall G T Ds1 Ds2 Ds3,
      strg_expand G T Ds1 ->
      decs_intersect Ds1 Ds2 Ds3 ->
      strg_expand G (typ_rfn T Ds2) Ds3
  | strg_expand_asel : forall G p L S U Ds,
      strg_pth_mem G p L (dec_typ S U) ->
      strg_expand G U Ds ->
      (* TODO replace (path_var (avar_f p)) by just p *)
      strg_expand G (typ_asel (pth_var (avar_f p)) L) Ds
  | strg_expand_csel : forall G p K U Ds,
      strg_pth_mem G p K (dec_cyp U) ->
      strg_expand G (cyp2typ U) Ds ->
      (* TODO replace (path_var (avar_f p)) by just p *)
      strg_expand G (typ_csel (pth_var (avar_f p)) K) Ds
  | strg_expand_and : forall G T1 Ds1 T2 Ds2 Ds3,
      strg_expand G T1 Ds1 ->
      strg_expand G T2 Ds2 ->
      decs_intersect Ds1 Ds2 Ds3 ->
      strg_expand G (typ_and T1 T2) Ds3
  | strg_expand_or : forall G T1 Ds1 T2 Ds2 Ds3,
      strg_expand G T1 Ds1 ->
      strg_expand G T2 Ds2 ->
      decs_union Ds1 Ds2 Ds3 ->
      strg_expand G (typ_or T1 T2) Ds3
  | strg_expand_top : forall G,
      strg_expand G typ_top empty

(* Weak expansion (like strong expansion, but uses weak path membership) *)
with weak_expand : ctx -> typ -> env dec -> Prop :=
  | weak_expand_rfn : forall G T Ds1 Ds2 Ds3,
      weak_expand G T Ds1 ->
      decs_intersect Ds1 Ds2 Ds3 ->
      weak_expand G (typ_rfn T Ds2) Ds3
  | weak_expand_asel : forall G p L S U Ds,
      weak_pth_mem G p L (dec_typ S U) ->
      weak_expand G U Ds ->
      weak_expand G (typ_asel (pth_var (avar_f p)) L) Ds (* TODO allow any path *)
  | weak_expand_csel : forall G p K U Ds,
      weak_pth_mem G p K (dec_cyp U) ->
      weak_expand G (cyp2typ U) Ds ->
      weak_expand G (typ_csel (pth_var (avar_f p)) K) Ds (* TODO allow any path *)
  | weak_expand_and : forall G T1 Ds1 T2 Ds2 Ds3,
      weak_expand G T1 Ds1 ->
      weak_expand G T2 Ds2 ->
      decs_intersect Ds1 Ds2 Ds3 -> 
      weak_expand G (typ_and T1 T2) Ds3
  | weak_expand_or : forall G T1 Ds1 T2 Ds2 Ds3,
      weak_expand G T1 Ds1 ->
      weak_expand G T2 Ds2 ->
      decs_union Ds1 Ds2 Ds3 -> 
      weak_expand G (typ_or T1 T2) Ds3
  | weak_expand_top : forall G,
      weak_expand G typ_top empty

(* Well-formed types *)
with wf_typ : ctx -> typ -> Prop :=
  | wf_typ_bot : forall G,
      wf_typ G typ_bot
  | wf_typ_top : forall G,
      wf_typ G typ_top
  | wf_typ_asel : forall G p L S U,
      strg_pth_mem G p L (dec_typ S U) ->
      (* note: recursive wf checking of bounds *)
      wf_typ G S ->
      wf_typ G U ->
      wf_typ G (typ_asel (pth_var (avar_f p)) L) (* TODO allow any paths *)
  | wf_typ_csel : forall G p K U,
      strg_pth_mem G p K (dec_cyp U) ->
      (* note: no recursive wf checking of U *)
      wf_typ G (typ_csel (pth_var (avar_f p)) K) (* TODO allow any paths *)
  | wf_typ_rfn : forall G z T Ds,
      wf_typ G T ->
      z # G ->
      EnvForall (wf_dec (G & z ~ T)) (open_decs Ds z) ->
      wf_typ G (typ_rfn T Ds)
  | wf_typ_and : forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      wf_typ G (typ_and T1 T2)
  | wf_typ_or : forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      wf_typ G (typ_or T1 T2)

(* Well-formed declarations *)
with wf_dec : ctx -> dec -> Prop :=
  | wf_dec_typ : forall G S U,
      wf_typ G S ->
      wf_typ G U ->
      wf_dec G (dec_typ S U)
  | wf_dec_cyp : forall G U,
      wf_typ G (cyp2typ U) ->
      wf_dec G (dec_cyp U)
  | wf_dec_fld : forall G T,
      wf_typ G T ->
      wf_dec G (dec_fld T)
  | wf_dec_mtd : forall G S U,
      wf_typ G S ->
      wf_typ G U ->
      wf_dec G (dec_mtd S U)

(* Declaration subtyping *)
with sub_dec : ctx -> dec -> dec -> Prop :=
  | sub_dec_typ : forall G S1 U1 S2 U2,
      sub_typ G S2 S1 ->
      sub_typ G U1 U2 ->
      sub_dec G (dec_typ S1 U1) (dec_typ S2 U2)
  | sub_dec_cyp : forall G U,
      sub_dec G (dec_cyp U) (dec_cyp U)
  | sub_dec_fld : forall G T1 T2,
      sub_typ G T1 T2 ->
      sub_dec G (dec_fld T1) (dec_fld T2)
  | sub_dec_mtd : forall G S1 T1 S2 T2,
      sub_typ G S2 S2 ->
      sub_typ G T1 T2 ->
      sub_dec G (dec_mtd S1 T1) (dec_mtd S2 T2)  

(* Subtyping *)
with sub_typ : ctx -> typ -> typ -> Prop :=
  | sub_typ_refl : forall G T,
      sub_typ G T T
  | sub_typ_top : forall G T,
      sub_typ G T typ_top
  | sub_typ_bot : forall G T,
      sub_typ G typ_bot T
  | sub_typ_rfn_l : forall G T Ds S,
      sub_typ G T S ->
      sub_typ G (typ_rfn T Ds) S
  | sub_typ_rfn_r : forall G z S T DsS DsT,
      sub_typ G S T ->
      weak_expand G S DsS ->
      z # G ->
      sub_decs (sub_dec (G & z ~ T)) (open_decs DsS z) (open_decs DsT z) ->
      sub_typ G S (typ_rfn T DsT)
  | sub_typ_asel_l : forall G p L S U T,
      weak_pth_mem G p L (dec_typ S U) ->
      sub_typ G U T ->
      sub_typ G (typ_asel (pth_var (avar_f p)) L) T (* TODO allow any path *)
  | sub_typ_asel_r : forall G p L S U T,
      weak_pth_mem G p L (dec_typ S U) ->
      sub_typ G T S ->
      sub_typ G T (typ_asel (pth_var (avar_f p)) L) (* TODO allow any path *)
  | sub_typ_csel : forall G p K U T,
      weak_pth_mem G p K (dec_cyp U) ->
      sub_typ G (cyp2typ U) T ->
      sub_typ G (typ_csel (pth_var (avar_f p)) K) T (* TODO allow any path *)
  | sub_typ_and : forall G S T1 T2,
      sub_typ G S T1 ->
      sub_typ G S T2 ->
      sub_typ G S (typ_and T1 T2)
  | sub_typ_and_l : forall G T1 T2 S,
      sub_typ G T1 S ->
      sub_typ G (typ_and T1 T2) S
  | sub_typ_and_r : forall G T1 T2 S,
      sub_typ G T2 S ->
      sub_typ G (typ_and T1 T2) S
  | sub_typ_or : forall G T1 T2 S,
      sub_typ G T1 S ->
      sub_typ G T2 S ->
      sub_typ G (typ_or T1 T2) S
  | sub_typ_or_l : forall G S T1 T2,
      sub_typ G S T1 ->
      sub_typ G S (typ_or T1 T2)
  | sub_typ_or_r : forall G S T1 T2,
      sub_typ G S T2 ->
      sub_typ G S (typ_or T1 T2)
.


Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : ctx => dom x) in
  let D := gather_vars_with (fun x : trm => fv_trm x) in
  let E := gather_vars_with (fun x : typ => fv_typ x) in
  constr:(A \u B \u C \u D \u E).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Definition trm_example_1(l : label) := (trm_new
  (cyp_rfn cyp_top (l ~ (dec_fld typ_top)))
  (l ~ (def_fld (avar_b 0)))
  (trm_sel (trm_var (avar_b 0)) l)
).




Fact ex_1: exists l, 
  typing_trm nil (trm_example_1 l) (typ_rfn typ_top (l ~ (dec_fld typ_top))).
Proof.
  pick_fresh l.
  exists l.
  set (Ds := (l ~ (dec_fld typ_top))).
  set (c  := (cyp_rfn cyp_top Ds)).
  set (Tc := (typ_rfn typ_top Ds)).

  assert (Hse: strg_expand nil Tc Ds). (* used several times *)
  apply strg_expand_rfn with (Ds1 := empty) (Ds2 := Ds) (Ds3 := Ds).
  apply strg_expand_top.
  (* proving decs_intersect will need some automation, or a better definition *)
  unfold decs_intersect.
  split.
  rewrite -> dom_empty.
  rewrite -> union_empty_l.
  reflexivity.
  split.
  intros.
  destruct H as [H _].
  unfold binds in H.
  apply get_some_inv in H.
  rewrite -> dom_empty in H.
  apply notin_empty in H.
  contradiction.
  split.
  intros.
  destruct H as [H _].
  unfold binds in H.
  apply get_some_inv in H.
  rewrite -> dom_empty in H.
  apply notin_empty in H.
  contradiction.
  intros.
  destruct H as [_ H].
  assumption.
  (* end assert Hse *)

  pick_fresh x.  
  apply typing_trm_new with (x := x) (Tc := Tc) (Ds := Ds).
  reflexivity.
  apply imp_typ_typ with (Ds := Ds).
  pick_fresh z.
  apply wf_typ_rfn with (z := z).
  apply wf_typ_top.
  skip. (* how can I solve "z # nil" ??? *)
  skip. (* how to prove EnvForall by proving it for each entry in list? *)
  assumption.
  unfold EnvForall.
  skip. (* how to deal with Forall ?? *)
  assumption.
  skip. (* how can I solve "l # nil" ??? *)
  
  apply (typing_defs_all).
  skip. (* TODO somehow apply List.Forall2_cons *)
  unfold open_trm.
  unfold open_rec_trm.
  unfold open_rec_avar.
  case_if.
  apply typing_trm_sel.
  apply weak_trm_mem_trm with (T := Tc) (Ds := Ds).
  apply typing_trm_var.
  rewrite <- empty_def.
  rewrite -> concat_empty_l.
  apply binds_single_eq.

  apply weak_expand_rfn.



(* "old" way of getting a label: 
  assert (Inhab label) by apply var_inhab.
  destruct H as [[l _]].
  exists l.
*)

