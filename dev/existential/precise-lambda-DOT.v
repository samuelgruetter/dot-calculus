
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

(* There's only a finite number of typ/field/method labels. *)
Parameter number_of_typ_labels: nat.
Parameter number_of_fld_labels: nat.
Parameter number_of_mtd_labels: nat.

Inductive typ_label: Set :=
| mk_typ_label: forall n: nat, n < number_of_typ_labels -> typ_label.
Inductive fld_label: Set :=
| mk_fld_label: forall n: nat, n < number_of_fld_labels -> fld_label.
Inductive mtd_label: Set :=
| mk_mtd_label: forall n: nat, n < number_of_mtd_labels -> mtd_label.

Module labels.
  Parameter L: typ_label.
  Parameter l: fld_label.
  Parameter m: mtd_label.
  Parameter apply: mtd_label.
End labels.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_fld: fld_label -> label
| label_mtd: mtd_label -> label.

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

Definition dec_bot(l: label): dec := match l with
  | label_typ L => dec_typ L typ_top typ_bot
  | label_fld l => dec_fld l typ_bot
  | label_mtd m => dec_mtd m typ_top typ_bot
end.

Definition dec_top(l: label): dec := match l with
  | label_typ L => dec_typ L typ_bot typ_top
  | label_fld l => dec_fld l typ_top
  | label_mtd m => dec_mtd m typ_bot typ_top
end.

Inductive lookup_res: Set :=
  | found: dec -> lookup_res
  | notfound: lookup_res
  | notwf: lookup_res
  | timeout: lookup_res.

Definition wont_happen := timeout.

Fixpoint lookup(n1: nat)(h: fset (var * typ_label))(G: ctx)(T: typ)(l: label): lookup_res :=
match n1 with
| 0 => timeout
| S n => match T with
  | typ_top => notfound
  | typ_bot => found (dec_bot l)
  | typ_rcd D => If label_of_dec D = l then found D else notfound
  | typ_sel p L => let (a) := p in match a with
     | avar_f x => If (x, L) \in h then
         found (dec_typ L typ_top typ_bot) (* TODO make switch to return "cyclic" error *)
       else (* TODO let X = type of x in G...
         match (lookup n (h \u \{ (x, L) }) G X L) *)
       notwf
     | avar_b _ => notwf
     end
  | typ_and T1 T2 => match (lookup n h G T1 l), (lookup n h G T2 l) with
    | (found D1), (found D2) => match D1, D2 with
      | (dec_typ L S1 U1), (dec_typ _ S2 U2)
        => found (dec_typ L (typ_or S1 S2) (typ_and U1 U2))
      | (dec_fld f U1), (dec_fld _ U2)
        => found (dec_fld f (typ_and U1 U2))
      | (dec_mtd m S1 U1), (dec_mtd _ S2 U2)
        => found (dec_mtd m (typ_or S1 S2) (typ_and U1 U2))
      | _, _ => wont_happen
      end
    | (found D1), notfound => found D1
    | notfound, (found D2) => found D2
    | notfound, notfound => notfound
    | notwf, _ => notwf
    | _, notwf => notwf
    | timeout, _ => timeout
    | _, timeout => timeout
    end
  | typ_or T1 T2 => notwf
  end
end.

(* "typ_has" + "typ_hasnt" 
G |- T has D   (with history h)   <==>   lookup_impl h G T (label_of_dec D) (Some D)
G |- T hasnt l (with history h)   <==>   lookup_impl h G T l None

This is too much in-between function and relation...
Inductive lookup_impl:
  fset (var * typ_label) -> ctx -> typ -> label -> option dec -> Prop :=
  | lookup_top: forall h G l,
      lookup_impl h G typ_top l None
  | lookup_bot: forall h G l,
      lookup_impl h G typ_bot l (Some (dec_bot l))
  | lookup_rcd_found: forall h G l D,
      l = label_of_dec D ->
      lookup_impl h G (typ_rcd D) l (Some D)
  | lookup_rcd_notfound: forall h G l D,
      l <> label_of_dec D ->
      lookup_impl h G (typ_rcd D) l None
  | lookup_sel_break: forall h G x L l,
      (x, L) \in h ->
      lookup_impl h G (typ_sel (pth_var (avar_f x)) L) l (Some (dec_bot l))
  | lookup_sel: forall h G x T L Lo Hi l D,
      binds x T G ->
      lookup_impl (h \u \{(x,L)}) G T (label_typ L) (dec_typ L Lo Hi) ->
      lookup_impl (h \u \{(x,L)}) G Hi l D ->
      lookup_impl h G (typ_sel (pth_var (avar_f x)) L) l D
  | typ_and_has_1: forall h G T1 T2 D,
      typ_has_impl h G T1 D ->
      typ_hasnt_impl h G T2 (label_of_dec D) ->
      typ_has_impl h G (typ_and T1 T2) D
  | typ_and_has_2: forall h G T1 T2 D,
      typ_hasnt_impl h G T1 (label_of_dec D) ->
      typ_has_impl h G T2 D ->
      typ_has_impl h G (typ_and T1 T2) D
  | typ_and_has_12: forall h G T1 T2 D1 D2 D3,
      typ_has_impl h G T1 D1 ->
      typ_has_impl h G T2 D2 ->
      D1 && D2 == D3 ->
      typ_has_impl h G (typ_and T1 T2) D3
  | typ_or_has: forall h G T1 T2 D1 D2 D3,
      typ_has_impl h G T1 D1 ->
      typ_has_impl h G T2 D2 ->
      D1 || D2 == D3 ->
      typ_has_impl h G (typ_or T1 T2) D3
with typ_hasnt_impl: fset (var * typ_label) -> ctx -> typ -> label -> Prop :=
  | typ_top_hasnt: forall h G l,
      typ_hasnt_impl h G typ_top l
(*| typ_bot_hasnt: There's no label that typ_bot hasn't. *)
  | typ_rcd_hasnt: forall h G D l,
      l <> label_of_dec D ->
      typ_hasnt_impl h G (typ_rcd D) l
(*| typ_sel_hasnt_break: does not exist, because if cyclic, we return a bottom-dec *)
  | typ_sel_hasnt: forall h G x T L Lo Hi l,
      binds x T G ->
      typ_has_impl   (h \u \{(x,L)}) G T (dec_typ L Lo Hi) ->
      typ_hasnt_impl (h \u \{(x,L)}) G Hi l ->
      typ_hasnt_impl h G (typ_sel (pth_var (avar_f x)) L) l
  | typ_and_hasnt: forall h G T1 T2 l, 
      typ_hasnt_impl h G T1 l ->
      typ_hasnt_impl h G T2 l ->
      typ_hasnt_impl h G (typ_and T1 T2) l
  | typ_or_hasnt_1: forall h G T1 T2 l,
      typ_hasnt_impl h G T1 l ->
      typ_hasnt_impl h G (typ_or T1 T2) l
  | typ_or_hasnt_2: forall h G T1 T2 l,
      typ_hasnt_impl h G T2 l ->
      typ_hasnt_impl h G (typ_or T1 T2) l.
*)

(* typ_has_impl keeps history of already-seen path types
Inductive typ_has_impl: fset (var * typ_label) -> ctx -> typ -> dec -> Prop :=
(*| typ_top_has: typ_top has nothing *)
  | typ_bot_has: forall h G l,
      typ_has_impl h G typ_bot (dec_bot l)
  | typ_rcd_has: forall h G D,
      typ_has_impl h G (typ_rcd D) D
  | typ_sel_has_break: forall h G x L,
      (x, L) \in h ->
      typ_has_impl h G (typ_sel (pth_var (avar_f x)) L) (dec_typ L typ_top typ_bot)
  | typ_sel_has: forall h G x T L Lo Hi D,
      binds x T G ->
      typ_has_impl (h \u \{(x,L)}) G T (dec_typ L Lo Hi) ->
      typ_has_impl (h \u \{(x,L)}) G Hi D ->
      typ_has_impl h G (typ_sel (pth_var (avar_f x)) L) D
  | typ_and_has_1: forall h G T1 T2 D,
      typ_has_impl h G T1 D ->
      typ_hasnt_impl h G T2 (label_of_dec D) ->
      typ_has_impl h G (typ_and T1 T2) D
  | typ_and_has_2: forall h G T1 T2 D,
      typ_hasnt_impl h G T1 (label_of_dec D) ->
      typ_has_impl h G T2 D ->
      typ_has_impl h G (typ_and T1 T2) D
  | typ_and_has_12: forall h G T1 T2 D1 D2 D3,
      typ_has_impl h G T1 D1 ->
      typ_has_impl h G T2 D2 ->
      D1 && D2 == D3 ->
      typ_has_impl h G (typ_and T1 T2) D3
  | typ_or_has: forall h G T1 T2 D1 D2 D3,
      typ_has_impl h G T1 D1 ->
      typ_has_impl h G T2 D2 ->
      D1 || D2 == D3 ->
      typ_has_impl h G (typ_or T1 T2) D3
with typ_hasnt_impl: fset (var * typ_label) -> ctx -> typ -> label -> Prop :=
  | typ_top_hasnt: forall h G l,
      typ_hasnt_impl h G typ_top l
(*| typ_bot_hasnt: There's no label that typ_bot hasn't. *)
  | typ_rcd_hasnt: forall h G D l,
      l <> label_of_dec D ->
      typ_hasnt_impl h G (typ_rcd D) l
(*| typ_sel_hasnt_break: does not exist, because if cyclic, we return a bottom-dec *)
  | typ_sel_hasnt: forall h G x T L Lo Hi l,
      binds x T G ->
      typ_has_impl   (h \u \{(x,L)}) G T (dec_typ L Lo Hi) ->
      typ_hasnt_impl (h \u \{(x,L)}) G Hi l ->
      typ_hasnt_impl h G (typ_sel (pth_var (avar_f x)) L) l
  | typ_and_hasnt: forall h G T1 T2 l, 
      typ_hasnt_impl h G T1 l ->
      typ_hasnt_impl h G T2 l ->
      typ_hasnt_impl h G (typ_and T1 T2) l
  | typ_or_hasnt_1: forall h G T1 T2 l,
      typ_hasnt_impl h G T1 l ->
      typ_hasnt_impl h G (typ_or T1 T2) l
  | typ_or_hasnt_2: forall h G T1 T2 l,
      typ_hasnt_impl h G T2 l ->
      typ_hasnt_impl h G (typ_or T1 T2) l*)

Inductive wf_typ: ctx -> typ -> Prop :=
  | wf_top: forall G,
      wf_typ G typ_top
  | wf_bot: forall G,
      wf_typ G typ_bot
  | wf_rcd: forall G D,
      wf_dec G D ->
      wf_typ G (typ_rcd D)
  | wf_sel: forall G x T L,
      binds x T G ->  (* <- this is the whole point of wf: no dangling var names in types *)
      (* no check that T really has L, because typ_has is total anyways,
         and thus no checks on Lo and Hi either [might lead to cycles btw] *)
      wf_typ G (typ_sel (pth_var (avar_f x)) L)
  | wf_and: forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      wf_typ G (typ_and T1 T2)
  | wf_or: forall G T1 T2,
      wf_typ G T1 ->
      wf_typ G T2 ->
      wf_typ G (typ_or T1 T2)
with wf_dec: ctx -> dec -> Prop :=
  | wf_tmem: forall G L Lo Hi,
      wf_typ G Lo ->
      wf_typ G Hi ->
      wf_dec G (dec_typ L Lo Hi)
  | wf_fld: forall G l T,
      wf_typ G T ->
      wf_dec G (dec_fld l T)
  | wf_mtd: forall G m A R,
      wf_typ G A ->
      wf_typ G R ->
      wf_dec G (dec_mtd m A R).

(* typ_has_impl keeps history of already-seen path types *)
Inductive typ_has_impl: fset (var * typ_label) -> ctx -> typ -> dec -> Prop :=
  | typ_top_has: forall h G l,
      typ_has_impl h G typ_bot (dec_top l) (* instead of just no such rule *)
  | typ_bot_has: forall h G l,
      typ_has_impl h G typ_bot (dec_bot l)
  | typ_rcd_has: forall h G D,
      typ_has_impl h G (typ_rcd D) D
  | typ_sel_has_break: forall h G x L,
      (x, L) \in h ->
      typ_has_impl h G (typ_sel (pth_var (avar_f x)) L) (dec_typ L typ_top typ_bot)
  | typ_sel_has: forall h G x T L Lo Hi D,
      binds x T G ->
      typ_has_impl (h \u \{(x,L)}) G T (dec_typ L Lo Hi) ->
      typ_has_impl (h \u \{(x,L)}) G Hi D ->
      typ_has_impl h G (typ_sel (pth_var (avar_f x)) L) D
  | typ_and_has: forall h G T1 T2 D1 D2 D3,
      (* one or both hyps might return dec_top, because it does not really have
         a member (typ_top_has was applied) *)
      typ_has_impl h G T1 D1 ->
      typ_has_impl h G T2 D2 ->
      D1 && D2 == D3 ->
      typ_has_impl h G (typ_and T1 T2) D3
  | typ_or_has: forall h G T1 T2 D1 D2 D3,
      typ_has_impl h G T1 D1 ->
      typ_has_impl h G T2 D2 ->
      D1 || D2 == D3 ->
      typ_has_impl h G (typ_or T1 T2) D3
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
  | subtyp_sel_l: forall G x X L S U T,
      binds x X G ->
      typ_has_impl \{} G X (dec_typ L S U) ->
      (*subtyp G S U -> <--- not needed because if U has D, then p.L has D as well *)
      subtyp G U T ->
      subtyp G (typ_sel (pth_var (avar_f x)) L) T
  | subtyp_sel_r: forall G x X L S U T,
      binds x X G ->
      typ_has_impl \{} G X (dec_typ L S U) ->
      subtyp G S U -> (* <--- makes proofs a lot easier!! *)
      subtyp G T S ->
      subtyp G T (typ_sel (pth_var (avar_f x)) L)
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
      (* We would like Lo2 <: Lo1 <: Hi1 <: Hi2, but Lo1 <: Hi1 does not hold
         for the dec_typ of typ_bot, so drop it *)
      subtyp G Lo2 Lo1 ->
      (*subtyp G Lo1 Hi1 ->*)
      subtyp G Hi1 Hi2 ->
      subdec G (dec_typ L Lo1 Hi1) (dec_typ L Lo2 Hi2)
  | subdec_fld: forall G l T1 T2,
      subtyp G T1 T2 ->
      subdec G (dec_fld l T1) (dec_fld l T2)
  | subdec_mtd: forall G m S1 T1 S2 T2,
      subtyp G S2 S1 ->
      subtyp G T1 T2 ->
      subdec G (dec_mtd m S1 T1) (dec_mtd m S2 T2)
(* not needed because subdec_typ doesn't require Lo1<:Hi1
  | subdec_refl: forall G D,
      subdec G D D*)
with ty_trm: ctx -> trm -> typ -> Prop :=
  | ty_var: forall G x T,
      binds x T G ->
      ty_trm G (trm_var (avar_f x)) T
  | ty_sel: forall G t T l U,
      ty_trm G t T ->
      typ_has_impl \{} G T (dec_fld l U) ->
      ty_trm G (trm_sel t l) U
  | ty_call: forall G t T m U1 U2 V u,
      ty_trm G t T ->
      typ_has_impl \{} G T (dec_mtd m U2 V) ->
      ty_trm G u U1 ->
      subtyp G U1 U2 -> (* <- explicit subsumption *)
      ty_trm G (trm_call t m u) V
  | ty_new: forall G ds T, (* TODO enable self reference *)
      ty_defs G ds T ->
      ty_trm G (trm_new ds) T
(* no subsumption because precise:
  | ty_sbsm: forall G t T U,
      ty_trm G t T ->
      subtyp G T U ->
      ty_trm G t U *)
with ty_def: ctx -> def -> dec -> Prop :=
  | ty_typ: forall G L S T,
      subtyp G S T -> (* <----- only allow realizable bounds *)
      ty_def G (def_typ L S T) (dec_typ L S T)
  | ty_fld: forall G l v T1 T2,
      binds v T1 G ->
      subtyp G T1 T2 -> (* <- explicit subsumption *)
      ty_def G (def_fld l T2 (avar_f v)) (dec_fld l T2)
  | ty_mtd: forall L m G S T1 T2 t,
      (forall x, x \notin L -> ty_trm (G & x ~ S) (open_trm x t) T1) ->
      subtyp G T1 T2 ->  (* <- explicit subsumption *)
      ty_def G (def_mtd m S T2 t) (dec_mtd m S T2)
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

Notation typ_has G T D := (typ_has_impl \{} G T D).
(*Notation typ_hasnt G T l := (typ_hasnt_impl \{} G T l).*)

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

Scheme typ_has_mut   := Induction for typ_has_impl   Sort Prop
(*with   typ_hasnt_mut := Induction for typ_hasnt_impl Sort Prop*)
with   subtyp_mut    := Induction for subtyp    Sort Prop
with   subdec_mut    := Induction for subdec    Sort Prop
with   ty_trm_mut    := Induction for ty_trm    Sort Prop
with   ty_def_mut    := Induction for ty_def    Sort Prop
with   ty_defs_mut   := Induction for ty_defs   Sort Prop
with   can_add_mut   := Induction for can_add   Sort Prop.
Combined Scheme ty_mutind from typ_has_mut, (*typ_hasnt_mut,*)
                               subtyp_mut, subdec_mut,
                               ty_trm_mut, ty_def_mut, ty_defs_mut, can_add_mut.

Scheme subtyp_mut2  := Induction for subtyp  Sort Prop
with   subdec_mut2  := Induction for subdec  Sort Prop.
Combined Scheme subtyp_subdec_mut from subtyp_mut2, subdec_mut2.

(*
Scheme typ_has_mut2 := Induction for typ_has_impl Sort Prop
with typ_hasnt_mut2 := Induction for typ_hasnt_impl Sort Prop.
Combined Scheme typ_has_hasnt_mut from typ_has_mut2, typ_hasnt_mut2.
*)

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

Hint Constructors typ_has_impl (*typ_hasnt_impl*)
  subtyp subdec ty_trm ty_def ty_defs can_add.
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

Lemma subdec_to_label_of_dec_eq: forall G D1 D2,
  subdec G D1 D2 -> label_of_dec D1 = label_of_dec D2.
Proof.
  introv Sd. inversions Sd; reflexivity.
Qed.

Lemma invert_subdec_typ_sync_right: forall G D2 L Lo1 Hi1,
  subdec G (dec_typ L Lo1 Hi1) D2 ->
  exists Lo2 Hi2, D2 = (dec_typ L Lo2 Hi2) /\
                  subtyp G Lo2 Lo1 /\
                  subtyp G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. eauto.
Qed.

Lemma invert_subdec_typ_sync_left: forall G D1 L Lo2 Hi2,
   subdec G D1 (dec_typ L Lo2 Hi2) ->
   exists Lo1 Hi1, D1 = (dec_typ L Lo1 Hi1) /\
                   subtyp G Lo2 Lo1 /\
                   subtyp G Hi1 Hi2.
Proof.
  introv Sd. inversions Sd. eauto.
Qed.

Lemma invert_subdec_fld_sync_left: forall G D l T2,
   subdec G D (dec_fld l T2) ->
   exists T1, D = (dec_fld l T1) /\
              subtyp G T1 T2.
Proof.
  introv Sd. inversions Sd. eauto.
Qed.

Lemma invert_subdec_mtd_sync_left: forall G D m T2 U2,
   subdec G D (dec_mtd m T2 U2) ->
   exists T1 U1, D = (dec_mtd m T1 U1) /\
                 subtyp G T2 T1 /\
                 subtyp G U1 U2.
Proof.
  introv Sd. inversions Sd. eauto.
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
  ty_trm G (trm_var (avar_f x)) T -> binds x T G.
Proof.
  introv Ty. inversions Ty. assumption.
Qed.

(* ###################################################################### *)
(** ** Weakening *)

Lemma weakening:
   (forall h G T D, typ_has_impl h G T D -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      typ_has_impl h (G1 & G2 & G3) T D)
(*
/\ (forall h G T l, typ_hasnt_impl h G T l -> forall G1 G2 G3,
      G = G1 & G3 ->
      ok (G1 & G2 & G3) ->
      typ_hasnt_impl h (G1 & G2 & G3) T l) *)
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
  apply ty_mutind. Admitted. (*
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
Qed.*)

Lemma weaken_typ_has_end: forall G1 G2 T D,
  ok (G1 & G2) ->
  typ_has G1 T D ->
  typ_has (G1 & G2) T D.
Proof.
  introv Ok THas. destruct weakening as [W _].
  specialize (W \{} G1 T D THas G1 G2 empty). repeat rewrite concat_empty_r in W.
  apply (W eq_refl Ok).
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

Lemma subdec_refl: forall G D, subdec G D D.
Proof.
  intros. destruct D; eauto.
Qed.

Hint Resolve subdec_refl.

(* ###################################################################### *)
(** ** More inversion lemmas *)

Lemma invert_wf_sto: forall s G,
  wf_sto s G ->
  forall x T2,
  ty_trm G (trm_var (avar_f x)) T2 ->
  exists ds T1 s1 s2 G1 G2,
    s = s1 & x ~ ds & s2 /\
    G = G1 & x ~ T1 & G2 /\
    wf_sto s1 G1 /\ 
    ty_defs G1 ds T1.
Proof.
  intros s G Wf. induction Wf; intros.
  + exfalso. apply invert_ty_var in H. apply (binds_empty_inv H).
  + rename T into X, H2 into Tyy, x0 into y, T2 into Y2.
    apply invert_ty_var in Tyy. rename Tyy into BiG.
    unfold binds in BiG. rewrite get_push in BiG.
    case_if.
    - inversions BiG.
      exists ds Y2 s (@empty defs) G (@empty typ). do 2 rewrite concat_empty_r. auto.
    - specialize (IHWf y Y2 (ty_var BiG)).
      destruct IHWf as [dsY [Y' [s1 [s2 [G1 [G2 [Eqs [EqG [Wf1 TydsY]]]]]]]]]. subst.
      lets Eq: (binds_middle_eq_inv BiG (wf_sto_to_ok_G Wf)). subst Y'.
      exists dsY Y2 s1 (s2 & x ~ ds) G1 (G2 & x ~ X).
      do 2 rewrite concat_assoc. auto.
Qed.

(*
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
*)


(* ###################################################################### *)
(** ** Misc *)

(*
Lemma binds_middle_eq_cases: forall G1 y Y G2 x X,
  binds x X (G1 & y ~ Y & G2) ->
  x = y /\ X = Y \/ x # G2 /\ x <> x0 /\ binds x T G1
*)

Lemma subdec_trans: forall G D1 D2 D3,
  subdec G D1 D2 -> subdec G D2 D3 -> subdec G D1 D3.
Proof.
  introv H12 H23. inversions H12; inversions H23; constructor;
  solve [ assumption | (eapply subtyp_trans; eassumption)].
Qed.

Axiom okadmit: forall G: ctx, ok G.

Lemma intersect_dec_unique: forall D1 D2 D3 D4,
  D1 && D2 == D3 ->
  D1 && D2 == D4 ->
  D3 = D4.
Proof.
  introv Eq3 Eq4. inversions Eq3; inversions Eq4; reflexivity.
Qed.

Lemma union_dec_unique: forall D1 D2 D3 D4,
  D1 || D2 == D3 ->
  D1 || D2 == D4 ->
  D3 = D4.
Proof.
  introv Eq3 Eq4. inversions Eq3; inversions Eq4; reflexivity.
Qed.

(* need to prove the same things several times to make sure we always have an IH 
Lemma typ_has_unique_and_not_hasnt:
   (forall G T D1, typ_has G T D1 ->
        (forall D2, typ_has G T D2 -> label_of_dec D1 = label_of_dec D2 -> D1 = D2)
     /\ (typ_hasnt G T (label_of_dec D1) -> False))
/\ (forall G T l, typ_hasnt G T l ->
      forall D, l = label_of_dec D -> typ_has G T D -> False).
Proof.
  apply typ_has_hasnt_mut; try split.
  + (* case typ_bot_has_typ *)
    introv Has Eq. inversions Has; simpl in Eq; try discriminate.
    inversions Eq. reflexivity.
  + (* case typ_bot_has_typ *)
    introv Hasnt. inversions Hasnt. 
  + (* case typ_bot_has_fld *)
    introv Has Eq. inversions Has; simpl in Eq; try discriminate.
    inversions Eq. reflexivity.
  + (* case typ_bot_has_fld *)
    introv Hasnt. inversions Hasnt. 
  + (* case typ_bot_has_mtd *)
    introv Has Eq. inversions Has; simpl in Eq; try discriminate.
    inversions Eq. reflexivity.
  + (* case typ_bot_has_mtd *)
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
    - exfalso. refine (IH2 _ _ H3). inversions H5; simpl in *; rewrite Eq; reflexivity.
  + (* case typ_and_has_1 *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Hasnt. inversions T12Hasnt. destruct IH1 as [_ IH1]. apply (IH1 H2).
  + (* case typ_and_has_2 *)
    rename t into T1Hasnt, H into IH1, t0 into T2Has, H0 into IH2.
    introv Has' Eq. destruct IH2 as [IH2 _].
    inversions Has'.
    - exfalso. refine (IH1 _ Eq H2).
    - eauto.
    - exfalso. refine (IH1 _ _ H1). inversions H5; simpl in *; rewrite Eq; reflexivity.
  + (* case typ_and_has_2 *)
    rename t into T1Hasnt, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Hasnt. inversions T12Hasnt. destruct IH2 as [_ IH2]. apply (IH2 H4).
  + (* case typ_and_has_12 *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv Has' Eq.
    remember (label_of_dec D0) as l eqn: Eq0.
    symmetry in Eq. rename Eq into Eq3.
    assert (Eq1: l = label_of_dec D1) by (inversions i; simpl in *; assumption).
    assert (Eq2: l = label_of_dec D2) by (inversions i; simpl in *; assumption).
    rewrite <- Eq1, <- Eq2 in *.
    lets Eq: (conj Eq0 (conj Eq1 (conj Eq2 Eq3))). clear Eq0 Eq1 Eq2 Eq3.
    inversions Has'.
    - exfalso. rewrite <- (proj41 Eq) in H4. destruct IH2 as [_ IH2]. apply (IH2 H4).
    - exfalso. rewrite <- (proj41 Eq) in H2. destruct IH1 as [_ IH1]. apply (IH1 H2).
    - assert (Eq4: l = label_of_dec D4) by (inversions H5; simpl in *; auto_star).
      assert (Eq5: l = label_of_dec D5) by (inversions H5; simpl in *; auto_star).
      destruct IH1 as [IH1 _]. lets EqD: (IH1 _ H1 Eq4). subst D4.
      destruct IH2 as [IH2 _]. lets EqD: (IH2 _ H3 Eq5). subst D5.
      apply (intersect_dec_unique i H5).
  + (* case typ_or_has *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Hasnt. inversions T12Hasnt.
    remember (label_of_dec D3) as l eqn: Eq3.
    assert (Eq1: l = label_of_dec D1) by (inversions i; simpl in *; reflexivity).
    assert (Eq2: l = label_of_dec D2) by (inversions i; simpl in *; assumption).
    rewrite <- Eq1, <- Eq2 in *.
    apply ((proj2 IH2) H4).
  + (* case typ_or_has *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Has Eq. inversions T12Has.
    remember (label_of_dec D0) as l eqn: Eq0.
    symmetry in Eq. rename Eq into Eq3.
    assert (Eq1: l = label_of_dec D1) by (inversions u; simpl in *; assumption).
    assert (Eq2: l = label_of_dec D2) by (inversions u; simpl in *; assumption).
    rewrite <- Eq1, <- Eq2 in *.
    assert (Eq4: l = label_of_dec D4) by (inversions H5; simpl in *; assumption).
    assert (Eq5: l = label_of_dec D5) by (inversions H5; simpl in *; assumption).
    destruct IH1 as [IH1 _]. lets EqD: (IH1 _ H1 Eq4). subst D4.
    destruct IH2 as [IH2 _]. lets EqD: (IH2 _ H3 Eq5). subst D5.
    apply (union_dec_unique u H5).
  + (* case typ_or_has *)
    rename t into T1Has, H into IH1, t0 into T2Has, H0 into IH2.
    introv T12Hasnt. inversions T12Hasnt.
    - destruct IH1 as [_ IH1].
      assert (Eq: label_of_dec D1 = label_of_dec D3). {
        inversions u; simpl in *; reflexivity.
      }
      rewrite Eq in IH1. apply (IH1 H3).
    - destruct IH2 as [_ IH2].
      assert (Eq: label_of_dec D2 = label_of_dec D3). {
        inversions u; simpl in *; reflexivity.
      }
      rewrite Eq in IH2. apply (IH2 H3).
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
    - assert (Eq: label_of_dec D1 = label_of_dec D). {
        inversions H5; simpl in *; reflexivity.
      }
      rewrite <- Eq in *. apply (IH1 _ eq_refl H1).
  + (* case typ_or_hasnt_1 *)
    introv T1Hasnt IH Eq Has'. inversions Has'.
    assert (Eq: label_of_dec D1 = label_of_dec D). {
        inversions H5; simpl in *; reflexivity.
    }
    rewrite <- Eq in *. apply (IH _ eq_refl H1).
  + (* case typ_or_hasnt_2 *)
    introv T2Hasnt IH Eq Has'. inversions Has'.
    assert (Eq: label_of_dec D2 = label_of_dec D). {
        inversions H5; simpl in *; reflexivity.
    }
    rewrite <- Eq in *. apply (IH _ eq_refl H3).
Qed.

Print Assumptions typ_has_unique_and_not_hasnt.
*)
Lemma typ_has_unique: forall G T D1 D2,
  typ_has G T D1 ->
  typ_has G T D2 ->
  label_of_dec D1 = label_of_dec D2 ->
  D1 = D2.
Admitted. (*
Proof.
  introv H1 H2 Eq.
  destruct typ_has_unique_and_not_hasnt as [P _].
  specialize (P G T D1 H1). destruct P as [P _]. apply (P _ H2 Eq).
Qed.*)

(*
Lemma not_typ_has_and_hasnt: forall G T D,
  typ_has G T D -> typ_hasnt G T (label_of_dec D) -> False.
Admitted.
Proof.
  introv Has Hasnt.
  destruct typ_has_unique_and_not_hasnt as [_ P].
  apply (P G T (label_of_dec D) Hasnt D eq_refl Has).
Qed.*)


(* ###################################################################### *)
(** ** Getting a finite list of all type labels *)

Lemma get_typ_labels_list_impl: forall n (Hle1: n <= number_of_typ_labels),
  exists (ls: list typ_label), 
    forall n0 (Hle2: n0 < n), 
      LibList.Mem (mk_typ_label (Lt.lt_le_trans _ _ _ Hle2 Hle1)) ls.
Proof.
  intro n. induction n.
  - intro. exists (@nil typ_label). intros. inversions Hle2.
  - intro. assert (Hle1': n <= number_of_typ_labels) by omega.
    specialize (IHn Hle1'). destruct IHn as [ls IH].
    assert (Hlt1: n < number_of_typ_labels) by omega.
    exists (cons (mk_typ_label Hlt1) ls).
    intros.
    rewrite LibList.Mem_cons_eq. 
    destruct (classicT (n0 = n)) as [Eq | Ne].
    + left. subst. f_equal. apply proof_irrelevance. (* <-- rocks ;-) *)
    + right. assert (Hlt2: n0 < n) by omega. specialize (IH n0 Hlt2).
      rewrite (proof_irrelevance (Lt.lt_le_trans n0 (S n) number_of_typ_labels Hle2 Hle1)
                                 (Lt.lt_le_trans n0 n number_of_typ_labels Hlt2 Hle1')).
      exact IH.
Qed.

Lemma invert_typ_label: forall (l: typ_label),
  exists (n: nat) (Hlt: n < number_of_typ_labels), l = mk_typ_label Hlt.
Proof.
  intro l. destruct l as [n H]. exists n H. reflexivity.
Qed.

Lemma get_typ_labels_list:
  exists (ls: list typ_label), forall l: typ_label, LibList.Mem l ls.
Proof.
  destruct (get_typ_labels_list_impl (le_n number_of_typ_labels)) as [ls F].
  exists ls. intro l.
  destruct (invert_typ_label l) as [n [Hlt Eq]].
  specialize (F n Hlt).
  rewrite Eq.
  rewrite <- (proof_irrelevance Hlt
                 (Lt.lt_le_trans n number_of_typ_labels number_of_typ_labels 
                                 Hlt (le_n number_of_typ_labels))) in F.
  exact F.
Qed.


(* ###################################################################### *)
(** ** Looks like rules, but follows from the rules *)

(* subdec D0 D1
   subdec D0 D2
   --------------------
   subdec D0 (D1 /\ D2)
*)
Lemma subdec_and: forall G D0 D1 D2 D12,
  subdec G D0 D1 ->
  subdec G D0 D2 ->
  D1 && D2 == D12 ->
  subdec G D0 D12.
Proof.
  introv Sd01 Sd02 I. inversions I; inversions Sd01; inversions Sd02; eauto.
Qed.

(* subdec D1 D
   subdec D2 D
   -------------------
   subdec (D1 \/ D2) D
*)
Lemma subdec_or: forall G D D1 D2 D12,
  subdec G D1 D ->
  subdec G D2 D ->
  D1 || D2 == D12 ->
  subdec G D12 D.
Proof.
  introv Sd01 Sd02 I. inversions I; inversions Sd01; inversions Sd02; eauto.
Qed.

(* 
  subdec D0 D1
  --------------------
  subdec D0 (D1 \/ D2)
*)
Lemma subdec_or_l: forall G D0 D1 D2 D12,
  subdec G D0 D1 ->
  D1 || D2 == D12 ->
  subdec G D0 D12.
Proof.
  introv Sd u. inversions u; inversions Sd; eauto.
Qed.

(* 
  subdec D0 D2
  --------------------
  subdec D0 (D1 \/ D2)
*)
Lemma subdec_or_r: forall G D0 D1 D2 D12,
  subdec G D0 D2 ->
  D1 || D2 == D12 ->
  subdec G D0 D12.
Proof.
  introv Sd u. inversions u; inversions Sd; eauto.
Qed.


(* ###################################################################### *)
(** ** More stuff *)

Lemma intersect_dec_total: forall D1 D2,
  label_of_dec D1 = label_of_dec D2 ->
  exists D12, D1 && D2 == D12.
Proof.
  introv Eq. destruct D1; destruct D2; inversions Eq; eexists.
  - eapply intersect_dec_typ.
  - eapply intersect_dec_fld.
  - eapply intersect_dec_mtd.
Qed.

Lemma union_dec_total: forall D1 D2,
  label_of_dec D1 = label_of_dec D2 ->
  exists D12, D1 || D2 == D12.
Proof.
  introv Eq. destruct D1; destruct D2; inversions Eq; eexists.
  - eapply union_dec_typ.
  - eapply union_dec_fld.
  - eapply union_dec_mtd.
Qed.


(* ###################################################################### *)
(** ** Even more stuff *)

(* [needs_lookup T1 p.L] ==> in order to look up a member in T1, we also
                            have to lookup the member in p.L 
   The other direction does not hold.
   And note that this judgment does not do more recursion than the size of T1. *)
Inductive needs_lookup: typ -> typ -> Prop :=
| typ_self_needs_lookup: forall x L,
    needs_lookup (typ_sel (pth_var (avar_f x)) L) (typ_sel (pth_var (avar_f x)) L)
| typ_and_needs_lookup_1: forall T1 T2 U,
    needs_lookup T1 U ->
    needs_lookup (typ_and T1 T2) U
| typ_and_needs_lookup_2: forall T1 T2 U,
    needs_lookup T2 U ->
    needs_lookup (typ_and T1 T2) U
| typ_or_needs_lookup_1: forall T1 T2 U,
    needs_lookup T1 U ->
    needs_lookup (typ_or T1 T2) U
| typ_or_needs_lookup_2: forall T1 T2 U,
    needs_lookup T2 U ->
    needs_lookup (typ_or T1 T2) U.

Inductive notin_chain: var -> typ_label -> env typ_label -> Prop :=
| notin_chain_empty: forall x L,
    notin_chain x L empty
| notin_chain_push: forall x L x0 L0 c,
    notin_chain x L c ->
    (x <> x0 \/ L <> L0) ->
    notin_chain x L (c & x0 ~ L0).

(* [chain G (x1 ~ L1 & x2 ~ L2 & ... & xn ~ Ln)] means that in order to look up a member
   in x1.L1, we have to look up a member in x2.L2, for that, need to lookup in x3.L3, etc,
   until xn.Ln.
   Moreover, all xi.Li in the chain are guaranteed to be unique, and each xi is bound in G.
   This implies that chains are never longer than (size of G)*(number_of_typ_labels).
*)
Inductive chain: ctx -> env typ_label -> Prop :=
| chain_base: forall G x L T,
    binds x T G ->
    chain G (x ~ L)
| chain_step_1: forall G h x1 L1 x2 L2 X1,
    chain G (h & x1 ~ L1) ->
    binds x1 X1 G ->
    needs_lookup X1 (typ_sel (pth_var (avar_f x2)) L2) ->
    notin_chain x2 L2 h ->
    (x2 <> x1 \/ L2 <> L1) ->
    chain G (h & x1 ~ L1 & x2 ~ L2)
| chain_step_2: forall G h x1 L1 x2 L2 X1 Lo Hi,
    chain G (h & x1 ~ L1) ->
    binds x1 X1 G ->
    typ_has G X1 (dec_typ L1 Lo Hi) ->
    needs_lookup Hi (typ_sel (pth_var (avar_f x2)) L2) ->
    notin_chain x2 L2 h ->
    (x2 <> x1 \/ L2 <> L1) ->
    chain G (h & x1 ~ L1 & x2 ~ L2).

Definition cyclic(G: ctx)(T0: typ) := exists x1 L1 x2 L2 x3 L3 h12 h23,
  (* first, walk until we reach the cycle: *)
  needs_lookup T0 (typ_sel (pth_var (avar_f x1)) L1) /\
  (chain G (x1 ~ L1 & h12 & x2 ~ L2) \/ (x1 = x2 /\ L1 = L2)) /\
  (* cycle starts at p2.L2: *)
  (chain G (x2 ~ L2 & h23 & x3 ~ L3) \/ (x2 = x3 /\ L2 = L3)) /\
  needs_lookup (typ_sel (pth_var (avar_f x3)) L3) (typ_sel (pth_var (avar_f x2)) L2).

Lemma lookup_step: forall G x1 L1 x2 L2 l h,
  chain G (x1 ~ L1 & h & x2 ~ L2) ->
  (* done: *)
  (exists D, typ_has G (typ_sel (pth_var (avar_f x1)) L1) D /\ label_of_dec D = l) \/
  (* or can do a step: *)
  (exists x3 L3, chain G (x1 ~ L1 & h & x2 ~ L2 & x3 ~ L3)) \/
  (* or cycle detected: *)
  (cyclic G (typ_sel (pth_var (avar_f x1)) L1)).
Proof.
  (* If x2's type contains no path types at the surface (i.e. through typ_and/typ_or),
     we can find l in x2's type and return it (done).
     Otherwise, we have to lookup in that path type, so we're in case 2 (can do a step).
     but when do we need chain_step_2???
     might get a cycle (3rd case) 
  *)
Admitted.

Definition is_cartesian(T1: Type)(T2: Type)(A: fset T1)(B: fset T2)(C: fset (T1 * T2)) :=
  forall a b, mem a A -> mem b B -> mem (a,b) C.

Notation "A \x B == C" := (is_cartesian A B C) (at level 40).

(* B is a list instead of fset so that we can do induction on it *)
Lemma cartesian: forall (T1: Type)(T2: Type)(A: fset T1)(B: list T2),
  exists (C: fset (T1 * T2)), 
    forall (a: T1)(b: T2), mem a A -> LibList.Mem b B -> mem (a,b) C.
Proof.
  intros T1 T2 A B. induction B.
  - exists (@FsetImpl.empty (T1 * T2)). intros a b Ia Ib. inversions Ib.
  - destruct IHB as [C IH]. rename a into b.
    destruct (fset_finite A) as [A' Eq].
    exists (C \u (from_list (LibList.map (fun a => (a, b)) A'))).
    intros a0 b0 IA IB.
    rewrite LibList.Mem_cons_eq in IB. destruct IB as [Eq2 | IB].
    + subst. rewrite in_union. right.
      admit. (* TODO...*)
    + rewrite in_union. left. apply (IH _ _ IA IB).
Qed.

Lemma typ_has_total_or_cyclic: forall G T l,
  wf_typ G T ->
  (exists D, typ_has G T D /\ label_of_dec D = l) \/
  cyclic G T.
Proof.
  intros G T l Wf.
  destruct get_typ_labels_list as [typ_labels typ_labels_spec].
  assert (exists C, (dom G) \x (from_list typ_labels) == C) by admit.
  destruct H as [cart cart_spec].

  assert (Inner: forall
    (unseen: list (var * typ_label))
    (seen: list (var * typ_label)),
    (from_list unseen) \u (from_list seen) = cart ->
    forall x1 L1 h x2 L2,
      needs_lookup T (typ_sel (pth_var (avar_f x1)) L1) ->
      (chain G (x1 ~ L1 & h & x2 ~ L2) /\ (x1 ~ L1 & h & x2 ~ L2) = seen
        \/ (x1 = x2 /\ L1 = L2) /\ (x1 ~ L1) = seen) ->
      forall l,
       (exists D, typ_has G (typ_sel (pth_var (avar_f x2)) L2) D /\ label_of_dec D = l) \/
       (cyclic G (typ_sel (pth_var (avar_f x2)) L2))
  ). {
    lets __________separator__________: True.
    intro u. induction u.
    + intros seen Eq.
      rewrite from_list_nil in Eq. rewrite (union_empty_l _) in Eq.
      admit.
    + admit.
  }

  destruct (fset_finite cart) as [cartL Eq].
  specialize (Inner cartL empty).
  rewrite <- Eq in Inner.
  rewrite empty_def in Inner. rewrite from_list_nil in Inner.
  apply (Inner (union_empty_r _)).
Qed.

Lemma typ_has_total_or_cyclic: forall G T l,
  wf_typ G T ->
  (exists D, typ_has G T D /\ label_of_dec D = l) \/
  cyclic G T.
Proof.

Qed.

(* T1 structurally contains T2
Inductive typ_contains: typ -> typ -> Prop :=
| typ_self_contains: forall T,
    typ_contains T T
| typ_rcd_contains: forall D T,
    dec_contains D T ->
    typ_contains (typ_rcd D) T
| typ_and_contains_1: forall T1 T2 U,
    typ_contains T1 U ->
    typ_contains (typ_and T1 T2) U
| typ_and_contains_2: forall T1 T2 U,
    typ_contains T2 U ->
    typ_contains (typ_and T1 T2) U
| typ_or_contains_1: forall T1 T2 U,
    typ_contains T1 U ->
    typ_contains (typ_or T1 T2) U
| typ_or_contains_2: forall T1 T2 U,
    typ_contains T2 U ->
    typ_contains (typ_or T1 T2) U
with dec_contains: dec -> typ -> Prop :=
| dec_typ_contains_1: forall L T1 T2 U, (* not needed for lookup of type members *)
    typ_contains T1 U ->
    dec_contains (dec_typ L T1 T2) U
| dec_typ_contains_2: forall L T1 T2 U,
    typ_contains T2 U ->
    dec_contains (dec_typ L T1 T2) U
| dec_fld_contains: forall L T1 T2 U,
    typ_contains T1 U ->
    dec_contains (dec_typ L T1 T2) U
....*)

(* "needs_lookup G T h" means "in order to look up a member in type T, we must
   also lookup members in all x.L in h, but not more" *)
Inductive needs_lookups: ctx -> typ -> fset (var * typ_label) -> Prop :=
  | needs_lookups_top: forall G,
      needs_lookups G typ_top \{}
  | needs_lookups_bot: forall G,
      needs_lookups G typ_bot \{}
  | needs_lookups_rcd: forall G D,
      needs_lookups G (typ_rcd D) \{}
  | needs_lookups_sel: forall G x X L Lo Hi h1 h2,
      binds x X G ->
      needs_lookups G X h1 ->
      typ_has G X (dec_typ L Lo Hi) ->
      needs_lookups G Hi h2 ->
      needs_lookups G (typ_sel (pth_var (avar_f x)) L) (h1 \u h2)
  | needs_lookups_and: forall G T1 T2 h1 h2,
      needs_lookups G T1 h1 ->
      needs_lookups G T2 h2 ->
      needs_lookups G (typ_and T1 T2) (h1 \u h2)
  | needs_lookups_or: forall G T1 T2 h1 h2,
      needs_lookups G T1 h1 ->
      needs_lookups G T2 h2 ->
      needs_lookups G (typ_or T1 T2) (h1 \u h2).

Definition cyclic(G: ctx)(T: typ) := exists x L h,
  T = (typ_sel (pth_var (avar_f x)) L) /\
  (x, L) \in h /\
  needs_lookups G (typ_sel (pth_var (avar_f x)) L) h.

Lemma typ_has_total_or_cyclic: forall G T l,

  exists D, typ_has G T D /\ label_of_dec D = l.
Proof.

Qed. typ_has_impl


(* an object to measure the size of an fset *)
Inductive finite(A: Type): fset A -> Prop := 
  | finite_nil: finite \{}
  | finite_cons: forall s v,
      finite s -> finite (\{ v } \u s).

Lemma fset_is_finite: forall (A: Type) (s: fset A), finite s.
Proof.
  intros. destruct (fset_finite s) as [l Eq]. gen s.
  induction l; intros.
  + rewrite from_list_nil in Eq. subst. apply finite_nil.
  + rewrite from_list_cons in Eq. subst. apply finite_cons. apply (IHl _ eq_refl).
Qed.

Definition wf_typ(G: ctx)(T: typ) := True.

Lemma collect_path_types: forall G,
  exists h, forall x X L Lo Hi,
    binds x X G ->
    typ_has G X (dec_typ L Lo Hi) ->
    (x, L) \in h.
Proof.
  (* doesn't hold because if X has cyclic upper bounds, it has a decl for each type
    label, so h is not finite! 
    make number of type labels finite?? *)
Abort.

Lemma collect_path_types: forall G1 G2,
  exists h, forall x L, wf_typ (G1 & G2) (typ_sel (pth_var (avar_f x)) L) -> (x, L) \in h.
Proof.
  intros G1 G2. gen_eq G: (G1 & G2). gen G2 G1.
  apply (env_ind (fun G2 => forall G1, G = G1 & G2 ->
   exists h, forall (x : var) (L : typ_label),
     wf_typ G (typ_sel (pth_var (avar_f x)) L) -> (x, L) \in h)).
  + introv Eq.


 lets Eq: (concat_empty_r G1). gen Eq.
 rewrite <- (concat_empty_r G1). gen_eq G2: (@empty typ).
Qed.

(* "needs_lookup G T h" means "in order to look up a member in type T, we must
   also lookup members in all x.L in h, and maybe even more" 
Inductive needs_lookups: ctx -> typ -> fset (var * typ_label) -> Prop :=
  | needs_lookups_base: forall G T,
      needs_lookups G T \{}
  | needs_lookups_sel: forall G x X L Lo Hi h1 h2,
      binds x X G ->
      needs_lookups G X h1 ->
      typ_has G X (dec_typ L Lo Hi) ->
      needs_lookups G Hi h2 ->
      needs_lookups G (typ_sel (pth_var (avar_f x)) L) (h1 \u h2)
  | needs_lookups_and: forall G T1 T2 h1 h2,
      needs_lookups G T1 h1 ->
      needs_lookups G T2 h2 ->
      needs_lookups G (typ_and T1 T2) (h1 \u h2)
  | needs_lookups_or: forall G T1 T2 h1 h2,
      needs_lookups G T1 h1 ->
      needs_lookups G T2 h2 ->
      needs_lookups G (typ_or T1 T2) (h1 \u h2).

Definition cycle(G: ctx)(T: typ) := exists x L h, T = x.L
  (x, L) \in h /\ needs_lookups G (typ_sel (pth_var (avar_f x)) L) h.
*)

Lemma hm:
   (forall h G T D1, typ_has_impl h G T D1 ->
      typ_has G T D1 \/ cycle G T)
/\ (forall h G T l, typ_hasnt_impl h G T l ->
      typ_hasnt G T l \/ cycle G T).
Proof.
  apply typ_has_hasnt_mut.


(* for every typ_has/typ_hasnt judgment with some history h,
   either it also holds without the history h,
   or there's a cycle. *)
Lemma no_history_or_cycle:
   (forall h G T D1, typ_has_impl h G T D1 ->
      typ_has G T D1 \/ cycle G T)
/\ (forall h G T l, typ_hasnt_impl h G T l ->
      typ_hasnt G T l \/ cycle G T).
Proof.
  apply typ_has_hasnt_mut.
  + (* case typ_bot_has *) eauto.
  + (* case typ_rcd_has *) eauto.
  + (* case typ_sel_has_break *)
    introv In.
  + (* case typ_sel_has *) admit.
  + (* case typ_and_has_1 *) admit.
  + (* case typ_and_has_2 *) admit.
  + (* case typ_and_has_12 *) admit.
  + (* case typ_or_has *) admit.
  + (* case typ_top_hasnt *) admit.
  + (* case typ_rcd_hasnt *) admit.
  + (* case typ_sel_hasnt *) admit.
  + (* case typ_and_hasnt *) admit.
  + (* case typ_or_hasnt_1 *) admit.
  + (* case typ_or_hasnt_2 *) admit.
Qed.


(*
Inductive cycle: ctx -> typ -> Prop :=
  | cycle_indeed: forall x L h,
      (x, L) \in h ->
      needs_lookup G (typ_sel (pth_var (avar_f x)) L) h.*)

(*
Inductive trace: ctx -> typ -> typ -> Prop :=
  | trace_1: forall G A B,
      binds x (typ_sel (pth_var (avar_f y)) M) G ->
      trace G A B
  | trace_2: forall G X x L Lo y M,
      binds x X G ->
      typ_has G X (dec_typ L Lo (typ_sel (pth_var (avar_f y)) M)) ->
      trace G x L y M.

(* trace of what you've to do when looking up a member in a type 
  (= deciding typ_has/typ_hasnt)
  "trace G x L y M" means "when trying to lookup some member in x.L, 
   you'll also have to lookup some (not necessarily the same) member in y.M"
 *)

Inductive trace: ctx -> var -> typ_label -> var -> typ_label -> Prop :=
  | trace_10: forall G x L y M,
      binds x (typ_sel (pth_var (avar_f y)) M) G ->
      trace G x L y M
  | trace_20: forall G X x L Lo y M,
      binds x X G ->
      typ_has G X (dec_typ L Lo (typ_sel (pth_var (avar_f y)) M)) ->
      trace G x L y M
  | trace_1: forall G x L y M,
      binds x (typ_sel (pth_var (avar_f y)) M) G ->
      trace G x L y M
  | trace_2: forall G X x L Lo y M,
      binds x X G ->
      typ_has G X (dec_typ L Lo (typ_sel (pth_var (avar_f y)) M)) ->
      trace G x L y M.
*)

Lemma swap_sub_and_typ_has: forall G T1 T2 D2,
  subtyp G T1 T2 ->
  typ_has G T2 D2 ->
  exists D1, typ_has G T1 D1 /\ subdec G D1 D2.
Proof.
  introv St. gen D2. induction St; introv THas.
  + (* case subtyp_refl *) eauto.
  + (* case subtyp_top *)
    inversions THas.
  + (* case subtyp_bot *)
    exists (dec_bot (label_of_dec D2)). apply (conj (typ_bot_has _ _ _)). 
    destruct D2; simpl; eauto.
  + (* case subtyp_rcd *)
    inversions THas. eauto.
  + (* case subtyp_sel_l *)
    specialize (IHSt _ THas). destruct IHSt as [D1 [UHas Sd]].
    exists D1. refine (conj _ Sd).
    apply typ_sel_has with X S U.
    (* if (x: x.L) in G, we have a cycle, which contradicts T <: x.L,
       because types involved in subtyping judgments don't have cycles *)
  + (* case subtyp_sel_r *)
    rename H into Bi, H0 into XHas.
    inversions THas. rename T0 into X', H1 into Bi', H3 into XHas', H5 into UHas.
    lets Eq: (binds_func Bi' Bi). subst X'. clear Bi'.
    lets Eq: (typ_has_unique XHas' XHas eq_refl). inversions Eq. clear XHas'.
             (**************)
    specialize (IHSt1 _ UHas). destruct IHSt1 as [D1 [SHas Sd12]].
    specialize (IHSt2 _ SHas). destruct IHSt2 as [D0 [THas Sd01]].
    exists D0. apply (conj THas). apply (subdec_trans Sd01 Sd12).
  + (* case subtyp_and *)
    inversions THas.
    - eauto.
    - eauto.
    - rename D2 into D, D0 into D2.
      specialize (IHSt1 _ H1). destruct IHSt1 as [D0 [SHasD0 Sd1]].
      specialize (IHSt2 _ H3). destruct IHSt2 as [D0' [SHasD0' Sd2]].
      remember (label_of_dec D) as l eqn: Eq.
      assert (Eq1: l = label_of_dec D1) by (inversions H5; simpl in *; reflexivity).
      assert (Eq2: l = label_of_dec D2) by (inversions H5; simpl in *; assumption).
      lets Eq0: (subdec_to_label_of_dec_eq Sd1). rewrite <- Eq1 in Eq0.
      lets Eq0': (subdec_to_label_of_dec_eq Sd2). rewrite <- Eq2 in Eq0'.
      rewrite <- Eq0' in Eq0.
      lets EqD0: (typ_has_unique SHasD0 SHasD0' Eq0). subst D0'. clear Eq0 SHasD0'.
                 (**************)
      rename Eq0' into Eq0; symmetry in Eq0.
      exists D0. apply (conj SHasD0).
      apply (subdec_and Sd1 Sd2 H5).
  + (* case subtyp_and_l *)
    rename D2 into D.
    specialize (IHSt _ THas). destruct IHSt as [D1 [T1Has Sd]].
    (* TODO need to decide if T2 has or hasn't (label_of_dec D) *)
    admit.
  + (* case subtyp_and_r *)
    rename D2 into D.
    specialize (IHSt _ THas). destruct IHSt as [D2 [T2Has Sd]].
    (* TODO need to decide if T2 has or hasn't (label_of_dec D) *)
    admit.
  + (* case subtyp_or *)
    rename D2 into D.
    specialize (IHSt1 _ THas). destruct IHSt1 as [D1 [T1Has Sd1]].
    specialize (IHSt2 _ THas). destruct IHSt2 as [D2 [T2Has Sd2]].
    lets Eq12: (subdec_to_label_of_dec_eq Sd1).
    rewrite <- (subdec_to_label_of_dec_eq Sd2) in Eq12.
    lets P: (union_dec_total _ _ Eq12). destruct P as [D12 u].
    exists D12. split.
    - apply (typ_or_has T1Has T2Has u).
    - apply (subdec_or Sd1 Sd2 u).
  + (* case subtyp_or_l *)
    inversions THas. rename D2 into D, D0 into D2.
    specialize (IHSt _ H1). destruct IHSt as [D0 [SHas Sd]].
    exists D0. apply (conj SHas).
    apply (subdec_or_l Sd H5).
  + (* case subtyp_or_r *)
    inversions THas. rename D2 into D, D0 into D2.
    specialize (IHSt _ H3). destruct IHSt as [D0 [SHas Sd]].
    exists D0. apply (conj SHas).
    apply (subdec_or_r Sd H5).
  + (* case subtyp_trans *)
    rename D2 into D3, THas into T3Has.
    specialize (IHSt2 _ T3Has). destruct IHSt2 as [D2 [T2Has Sd23]].
    specialize (IHSt1 _ T2Has). destruct IHSt1 as [D1 [T1Has Sd12]].
    exists D1. apply (conj T1Has). apply (subdec_trans Sd12 Sd23).
Qed.

Print Assumptions swap_sub_and_typ_has. (* TODO *)

(* Because T is wf in G1, we can drop everything to the right of G1.
   Note: Wouldn't work with imprecise typing, because D there could be
   subsumption towards something which is in G2 or contains x. *)
Lemma strengthen_typ_has: forall G1 x T G2 D,
  typ_has (G1 & x ~ T & G2) T D ->
  typ_has G1 T D.
Admitted.

(*
(* Corresponds to "expansion is total".
   TODO: also needs wf-ness of T.
   Doesn't hold if there are circular upper bounds (only possible if self refs).
   We can exclude circular upper bounds in realizable envs, but not in any env,
   which might get bad through narrowing+intersection. *)
Definition has_decidable_for(n: nat) := forall s G T l x,
  ctx_size G = n ->
  wf_sto s G ->
  binds x T G -> (* <- just to get realizability *)
  typ_hasnt G T l \/ exists D, typ_has G T D /\ label_of_dec D = l.

Lemma has_decidable_for_base: has_decidable_for 0.
Proof.
  introv Eq Wf Bi. apply ctx_size_zero_inv in Eq. subst.
  exfalso. apply (binds_empty_inv Bi).
Qed.

Lemma has_decidable_step: forall n,
  (forall k, k <= n -> has_decidable_for k) ->
  has_decidable_for (S n).
Proof.
  intros n IH. introv Eq Wf Bi.
  lets P: (invert_wf_sto Wf (ty_var Bi)).
  destruct P as [ds [T' [s1 [s2 [G1 [G2 [Eqs [EqG [Wf1 Tyds]]]]]]]]]. subst.
  lets Ok: (wf_sto_to_ok_G Wf).
  lets Eq2: (binds_middle_eq_inv Bi Ok). subst T'.
  lets xNs: (wf_sto_to_x_notin_G
  lets Wf2: (wf_sto_push Wf1 
  induction Tyds.
  + left. apply typ_top_hasnt.
  + 
Qed.
Admitted.


Lemma subtyp_preserves_is_bot_step: forall n,
  (forall k, k <= n -> subtyp_preserves_is_bot_for k) ->
 subtyp_preserves_is_bot_for (S n).
Proof.
  intros n IH. unfold subtyp_preserves_is_bot_for in *.
*)

(* narrowing needed for function calls *)
Lemma narrowing:
   (forall G T D2, typ_has G T D2 -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     exists D1, typ_has (G1 & x ~ S1 & G2) T D1 /\
                 subdec (G1 & x ~ S1 & G2) D1 D2)
/\ (forall G T l, typ_hasnt G T l -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     typ_hasnt (G1 & x ~ S1 & G2) T l)
/\ (forall G T1 T2, subtyp G T1 T2 -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     subtyp (G1 & x ~ S1 & G2) T1 T2)
/\ (forall G D1 D2, subdec G D1 D2 -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     subdec (G1 & x ~ S1 & G2) D1 D2)
/\ (forall G t T2, ty_trm G t T2 -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     exists T1, ty_trm (G1 & x ~ S1 & G2) t T1
             /\ subtyp (G1 & x ~ S1 & G2) T1 T2)
/\ (forall G d D2, ty_def G d D2 -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     exists D1, ty_def (G1 & x ~ S1 & G2) d D1
             /\ subdec (G1 & x ~ S1 & G2) D1 D2)
/\ (forall G ds T2, ty_defs G ds T2 -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     exists T1, ty_defs (G1 & x ~ S1 & G2) ds T1
             /\ subtyp (G1 & x ~ S1 & G2) T1 T2)
/\ (forall G ds d, can_add G ds d -> forall G1 x S1 S2 G2,
     G = G1 & x ~ S2 & G2 ->
     subtyp G1 S1 S2 ->
     can_add (G1 & x ~ S2 & G2) ds d).
Proof.
  apply ty_mutind.
  + (* case typ_bot_has_typ *)
    admit.
  + (* case typ_bot_has_fld *)
    admit.
  + (* case typ_bot_has_mtd *)
    admit.
  + (* case typ_rcd_has *)
    admit.
  + (* case typ_sel_has *)
    introv Bix THas2 IHTHas Hi2Has2 IHHiHas Eq StS. subst.
    rename D into D2, Lo into Lo2, Hi into Hi2.
    specialize (IHTHas _ _ _ _ _ eq_refl StS).
    destruct IHTHas as [DT [THas1 Sd]].
    apply invert_subdec_typ_sync_left in Sd.
    destruct Sd as [Lo1 [Hi1 [Eq [StLo21 StHi12]]]]. subst.
    specialize (IHHiHas _ _ _ _ _ eq_refl StS).
    destruct IHHiHas as [Dm [Hi2Hasm Sdm2]].
    lets P: (swap_sub_and_typ_has StHi12 Hi2Hasm).
            (********************)
    destruct P as [D1 [Hi1Has1 Sd1m]].
    apply binds_middle_inv in Bix.
    destruct Bix as [Bix | [[xG2 [Eq1 Eq2]]|[xG2 [Ne Bix]]]].
    - (* case x in G2 *)
      exists D1. split. 
      * apply (typ_sel_has (binds_concat_right _ Bix) THas1 Hi1Has1).
      * apply (subdec_trans Sd1m Sdm2). (* <-- will need narrowing once we have self refs *)
    - (* case x = x0 *)
      subst x0 T.
      clear StLo21 StHi12 Lo1 Hi1 Hi1Has1 THas1 D1 Sd1m.
      lets S2Has: (strengthen_typ_has THas2).
      lets P: (swap_sub_and_typ_has StS S2Has).
              (********************)
      destruct P as [DT [S1Has Sd]].
      apply invert_subdec_typ_sync_left in Sd.
      destruct Sd as [Lo1 [Hi1 [Eq [StLo21 StHi12]]]]. subst.
      apply (weaken_subtyp_end (okadmit (G1 & x ~ S1))) in StHi12.
      apply (weaken_subtyp_end (okadmit (G1 & x ~ S1 & G2))) in StHi12.
      lets P: (swap_sub_and_typ_has StHi12 Hi2Hasm).
              (********************)
      destruct P as [D1 [Hi1Has1 Sd1m]].
      apply (weaken_typ_has_end (okadmit (G1 & x ~ S1))) in S1Has.
      apply (weaken_typ_has_end (okadmit (G1 & x ~ S1 & G2))) in S1Has.
      exists D1. split. 
      * apply (typ_sel_has (binds_middle_eq _ _ xG2) S1Has Hi1Has1).
      * apply (subdec_trans Sd1m Sdm2). (* <-- will need narrowing once we have self refs *)
    - (* case x in G1 *)
      exists D1. split. 
      * refine (typ_sel_has _ THas1 Hi1Has1). auto.
      * apply (subdec_trans Sd1m Sdm2). (* <-- will need narrowing once we have self refs *)
  + (* case typ_and_has_1 *)
    intros G U V D2 UHas IHUHas VHasnt IHVHasnt. introv Eq St. subst.
    specialize (IHUHas _ _ _ _ _ eq_refl St). destruct IHUHas as [D1 [UHas' Sd]].
    specialize (IHVHasnt _ _ _ _ _ eq_refl St).
    exists D1. refine (conj _ Sd).
    apply (typ_and_has_1 UHas').
    rewrite (subdec_to_label_of_dec_eq Sd).
    exact IHVHasnt.
  + (* case typ_and_has_2 *)
    admit.
  + (* case typ_and_has_12 *)
    admit.
  + (* case typ_or_has *)
    admit.
  + (* case typ_top_hasnt *)
    admit.
  + (* case typ_rcd_hasnt *)
    admit.
  + (* case typ_sel_hasnt *)
    admit.
  + (* case typ_and_hasnt *)
    admit.
  + (* case typ_or_hasnt_1 *)
    admit.
  + (* case typ_or_hasnt_2 *)
    admit.
  + (* case subtyp_refl *)
    admit.
  + (* case subtyp_top *)
    admit.
  + (* case subtyp_bot *)
    admit.
  + (* case subtyp_rcd *)
    admit.
  + (* case subtyp_sel_l *)
    admit.
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
    admit.
  + (* case subdec_typ *)
    admit.
  + (* case subdec_fld *)
    admit.
  + (* case subdec_mtd *)
    admit.
  + (* case ty_var *)
    admit.
  + (* case ty_sel *)
    admit.
  + (* case ty_call *)
    admit.
  + (* case ty_new *)
    admit.
  + (* case ty_typ *)
    admit.
  + (* case ty_fld *)
    admit.
  + (* case ty_mtd *)
    admit.
  + (* case ty_defs_nil *)
    admit.
  + (* case ty_defs_cons *)
    admit.
  + (* case can_add_typ *)
    introv dsHasnt StLoHi IHSt Eq StS. subst. apply (can_add_typ dsHasnt).
    apply* IHSt.
  + (* case can_refine_typ *)
    introv dsHasnt St1 IH1 St2 IH2 St3 IH3 Eq StS. subst.
    apply* can_refine_typ.
  + (* case can_add_fld *)
    introv dsHasnt Eq StS. apply* can_add_fld.
  + (* case can_add_mtd *)
    intros. apply* can_add_mtd.
Qed.

Stop Here.

(* ------GARBAGE------------------------------

Parameter max_typ_label: nat.

Inductive typ_label: Set :=
| mk_typ_label: forall n, n <= max_typ_label -> typ_label.

Fixpoint get_typ_labels_list_up_to(n: nat): n <= max_typ_label -> list typ_label :=
match n with
| 0 => fun Hle => cons (mk_typ_label Hle) nil
| S n' => fun Hle =>
          cons (mk_typ_label Hle) (get_typ_labels_list_up_to (Le.le_Sn_le _ _ Hle))
end.

Fixpoint get_0_le(n: nat): 0 <= n := match n with
| 0 => le_n 0
| S n' => le_S _ _ (get_0_le n')
end.

Definition typ_labels: list typ_label := get_typ_labels_list_up_to (get_0_le max_typ_label).



prop_ext

Fixpoint get_typ_labels_list_up_to(n: nat)(Hle: n <= max_typ_label): list typ_label :=
(match n return n <= max_typ_label -> list typ_label with
| 0 => fun Hle => cons (mk_typ_label Hle) nil
| S n' => fun Hle => 
   cons (mk_typ_label Hle) (get_typ_labels_list_up_to (Le.le_Sn_le _ _ Hle))
end) Hle.


le_Sn_le : forall n m, S n <= m -> n <= m.

Fixpoint get_typ_labels_list_up_to(n: nat)(Hle: n <= max_typ_label): list typ_label :=
match n with
| 0 => cons (mk_typ_label Hle) nil
| S n' => cons (mk_typ_label Hle) (get_typ_labels_list_up_to (Le.le_Sn_le _ _ Hle))
end.

S n' <= max_typ_label
n' <= max_typ_label

le_S

Fixpoint get_0_le(n: nat): 0 <= n := match n with
| 0 => le_n 0
| S n' => le_S _ _ (get_0_le n')
end.

Fixpoint get_typ_labels_list_up_to(n: nat)(Hle: n <= max_typ_label): list typ_label :=
match n with
| 0 => cons (mk_typ_label (get_0_le max_typ_label)) nil
| S n' => cons (mk_typ_label Hle) (get_typ_labels_list_up_to n' _)
end.


Fixpoint get_typ_labels_list(n: nat): list typ_label := match n with
| 0 => cons (mk_typ_label (le_n max_typ_label)) nil
| S n' => let (n'', Hle) := 
end.
*)

(*
Lemma get_typ_labels_list: forall n (Hle1: n <= max_typ_label),
  exists (ls: list typ_label), 
    forall n0 (Hle2: n0 <= n), 
      Mem (mk_typ_label (Le.le_trans _ _ _ Hle2 Hle1)) ls.
Proof.
  intro n. induction n.
  - intro. exists (@nil typ_label). intros. assert (n0 = 0) by ome inversions Hle2.
  - intro. assert (Hle1': n <= number_of_typ_labels) by omega.
    specialize (IHn Hle1'). destruct IHn as [ls IH].
    assert (Hlt1: n < number_of_typ_labels) by omega.
    exists (cons (mk_typ_label Hlt1) ls).
    intros.
    rewrite Mem_cons_eq. 
    destruct (classicT (n0 = n)) as [Eq | Ne].
    + left. subst. f_equal. unfold lt in *.
      destruct Hlt1.
Qed.
*)


Lemma get_typ_labels_list:
  exists (ls: list typ_label), forall l: typ_label, Mem l ls.
Proof.
  destruct (get_typ_labels_list_impl (le_n number_of_typ_labels)) as [ls F].
  assert (C: number_of_typ_labels = 0 \/ number_of_typ_labels > 0) by omega.
  destruct C as [Eq | Gt].
  - subst. exists (@nil typ_label). intro l. inversion l. rewrite Eq in H. omega.
  - remember (pred number_of_typ_labels) as N.
    assert (Eq: (S N) = number_of_typ_labels) by omega. 
    specialize (F N). assert (N < number_of_typ_labels) by omega.
    specialize (F H).
 inversion F.
rewrite <- Eq in F. 
    (* destruct number_of_typ_labels. as [|N] would be simpler but doesn't work *)
  specialize (F numb  
Qed.

Definition typ_labels: list typ_label.
  destruct (get_typ_labels_list (le_n number_of_typ_labels)) as [ls F].

(*------*)
Parameter raw_label_type: Set.

Parameter raw_typ_labels: list raw_label_type.
Parameter raw_fld_labels: list raw_label_type.
Parameter raw_mtd_labels: list raw_label_type.

Inductive typ_label: Set :=
| mk_typ_label: forall l, Mem l raw_typ_labels -> typ_label.
Inductive fld_label: Set :=
| mk_fld_label: forall l, Mem l raw_fld_labels -> fld_label.
Inductive mtd_label: Set :=
| mk_mtd_label: forall l, Mem l raw_mtd_labels -> mtd_label.

Lemma get_typ_labels_list: forall n,
  exists (ls: list typ_label), 
    forall r, Mem r raw_typ_labels -> 
Proof.


Lemma get_typ_labels_list: exists (ls: list typ_label), 
  forall (l: typ_label), Mem l ls.
Proof.
  gen_eq L: raw_typ_labels. induction L; introv Eq.
  - exists (@nil typ_label). intro l. inversion l. rewrite <- Eq in H.
    inversions H.
  - exists ( take
Defined.



(*
Definition typ_labels := map (fun r => (mk_typ_label raw_typ_labels
*)

(*
Parameter typ_label: Set.
Parameter fld_label: Set.
Parameter mtd_label: Set.
*)

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

(* Basic check that all variables occuring in the type are bound in G
   But do we also check that for all usages of x.L, L is a member of x? 
   If yes, this check can lead to cycles, and is not preserved by narrowing,
   unless we add history&break functionality... 
   Or we can say that "hasn't L" means "has L: Bot..Top". 
   Inductive wf_typ: ctx -> typ -> Prop :=
*)