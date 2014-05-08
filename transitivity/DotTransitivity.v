

Set Implicit Arguments.

(* CoqIDE users: Run open.sh (in ./ln) to start coqide, then open this file. *)
Require Import LibLN.

(** Syntax **)

Definition label := var.

(* any var (free or bound) *)
Inductive avar : Type :=
  | avar_b : nat -> avar
  | avar_f : var -> avar
.

(* path *)
Inductive pth : Type :=
  | pth_var : avar -> pth
(*| pth_sel : pth -> label -> pth*)
.

Inductive typ : Type :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_bind : label -> dec -> typ (* { z => one decl } *)
  | typ_asel : pth -> label -> typ (* select on abstract type *)
with dec : Type :=
  | dec_typ  : typ -> typ -> dec
  | dec_fld  : typ -> dec
.

Inductive notsel: typ -> Prop :=
  | notsel_top  : notsel typ_top
  | notsel_bot  : notsel typ_bot
  | notsel_bind : forall l d, notsel (typ_bind l d).


(* ... opening ...
   replaces in some syntax a bound variable with dangling index (k) by a free variable x
*)

Fixpoint open_rec_avar (k: nat) (u: var) (a: avar) { struct a } : avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_pth (k: nat) (u: var) (p: pth) { struct p } : pth :=
  match p with
  | pth_var a => pth_var (open_rec_avar k u a)
(*| pth_sel p l => pth_sel (open_rec_pth k u p) l *)
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (t: typ) { struct t } : typ :=
  match t with
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_bind l d => typ_bind l (open_rec_dec (S k) u d)
  | typ_asel p l => typ_asel (open_rec_pth k u p) l
  end
with open_rec_dec (k: nat) (u: var) (d: dec) { struct d } : dec :=
  match d with
  | dec_typ ts tu => dec_typ (open_rec_typ k u ts) (open_rec_typ k u tu)
  | dec_fld t => dec_fld (open_rec_typ k u t)
  end.

Definition open_avar u a := open_rec_avar 0 u a.
Definition open_pth  u p := open_rec_pth  0 u p.
Definition open_typ  u t := open_rec_typ  0 u t.
Definition open_dec  u d := open_rec_dec  0 u d.


(* ... subtyping ... *)

(* mapping from var to typ_bind (types other than typ_bind are never put into
 the ctx, because we only put self types into the ctx, which are always typ_bind *)
Definition ctx := env typ.

Inductive has : ctx -> pth -> label -> dec -> Prop :=
  | has_var : forall G x l d,
      binds x (typ_bind l d) G ->
      has G (pth_var (avar_f x)) l d.

(* mode = "is transitivity at top level accepted?" *)
Inductive mode : Type := notrans | oktrans.

Inductive subtyp : mode -> ctx -> typ -> typ -> Prop :=
  (* why is there no reflexivity in fsub-mini1h.elf ? *)
  (* There's a separate rsdc judgment (reflexive sub-declaration) *)
  | subtyp_refl : forall G T,
      subtyp notrans G T T
  | subtyp_top : forall G T,
      subtyp notrans G T typ_top
  | subtyp_bot : forall G T,
      subtyp notrans G typ_bot T
  | subtyp_bind : forall L G l d1 d2,
      (forall z, z \notin L ->
        subdec oktrans (G & (z ~ (typ_bind l (open_dec z d1)))) 
                       (open_dec z d1) (open_dec z d2)) ->
      subtyp notrans G (typ_bind l d1) (typ_bind l d2)
  | subtyp_asel_l : forall G p L S U T,
      has G p L (dec_typ S U) ->
      subtyp oktrans G U T ->
      subtyp notrans G (typ_asel p L) T
  | subtyp_asel_r : forall G p L S U T,
      has G p L (dec_typ S U) ->
      subtyp oktrans G S U -> (* <--- makes proofs a lot easier!! *)
      subtyp oktrans G T S ->
      subtyp notrans G T (typ_asel p L)
  | subtyp_mode : forall G T1 T2,
      subtyp notrans G T1 T2 ->
      subtyp oktrans G T1 T2
  | subtyp_trans : forall G T1 T2 T3,
      subtyp oktrans G T1 T2 ->
      subtyp oktrans G T2 T3 ->
      subtyp oktrans G T1 T3
with subdec : mode -> ctx -> dec -> dec -> Prop :=
  | subdec_typ : forall m G Lo1 Hi1 Lo2 Hi2,
      (* only allow implementable decl *)
      subtyp m G Lo1 Hi1 ->
      subtyp m G Lo2 Hi2 ->
      (* lhs narrower range than rhs *)
      subtyp m G Lo2 Lo1 ->
      subtyp m G Hi1 Hi2 ->
      (* conclusion *)
      subdec m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2)
  | subdec_fld : forall m G T1 T2,
      subtyp m G T1 T2 ->
      subdec m G (dec_fld T1) (dec_fld T2).

Scheme subtyp_mut := Induction for subtyp Sort Prop
with subdec_mut := Induction for subdec Sort Prop.

(*
Lemma invert_subdec: forall m G d1 d2,
   subdec m G d1 d2 -> (
   (exists Lo1 Hi1 Lo2 Hi2, d1 = (dec_typ Lo1 Hi1) /\ d2 = (dec_typ Lo2 Hi2) /\
     subtyp m G Lo2 Lo1 /\ subtyp m G Hi1 Hi2)
\/ (exists T1 T2, d1 = (dec_fld T1) /\ d2 = (dec_fld T2) /\
     subtyp m G T1 T2)).
Proof.
  intros.
  inversion H.
  left. exists Lo1 Hi1 Lo2 Hi2. subst. auto.
  right. exists T1 T2. subst. auto.
Qed.
*)

(* want a judgment which says "predicate P holds for all subtyp proofs wrapped
  in this given subdec proof" *)

Definition p_subtyp_to_p_subdec(m: mode)(G: ctx)(d1 d2: dec)
  (P : forall (m0: mode) (G0: ctx) (T1 T2 : typ), subtyp m0 G0 T1 T2 -> Prop)
  (sd: subdec m G d1 d2) (* <- not used on rhs, but useful to infer m G d1 d2 *) :=
(  (exists (Lo1 Hi1 Lo2 Hi2: typ) (stL: subtyp m G Lo2 Lo1) (stH: subtyp m G Hi1 Hi2),
     d1 = (dec_typ Lo1 Hi1) /\ 
     d2 = (dec_typ Lo2 Hi2) /\
     P m G Lo2 Lo1 stL /\
     P m G Hi1 Hi2 stH)
\/ (exists (T1 T2: typ) (st: subtyp m G T1 T2),
     d1 = (dec_fld T1) /\ 
     d2 = (dec_fld T2) /\
     P m G T1 T2 st)).

(*
Definition subtyp_mut' := fun 
  (P : forall (m : mode) (c : ctx) (t t0 : typ), subtyp m c t t0 -> Prop)
  (P0: forall (m : mode) (c : ctx) (d d0 : dec), subdec m c d d0 -> Prop)
  => fun f_refl f_top f_bot f_bind_typ f_bind_fld f_asel_l f_asel_r f_mode f_trans f_typ f_fld =>
fix F (m : mode) (c : ctx) (t t0 : typ) (s : subtyp m c t t0) {struct s} :
  P m c t t0 s :=
  match s as s0 in (subtyp m0 c0 t1 t2) return (P m0 c0 t1 t2 s0) with
  | subtyp_refl G T => f_refl G T
  | subtyp_top G T => f_top G T
  | subtyp_bot G T => f_bot G T
  | subtyp_bind L G l d1 d2 s0 => match d1 with
      | dec_typ Lo Hi => f_bind_typ L G l d1 d2 s0
        (fun (z : var) (n : z \notin L) =>
         F0 oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
           (open_dec z d2) (s0 z n))
      | dec_fld U => f_bind_fld L G l d1 d2 s0
        (fun (z : var) (n : z \notin L) =>
         F0 oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
           (open_dec z d2) (s0 z n))
      end
  | subtyp_asel_l G p L S0 U T h s0 =>
      f_asel_l G p L S0 U T h s0 (F oktrans G U T s0)
  | subtyp_asel_r G p L S0 U T h s0 s1 =>
      f_asel_r G p L S0 U T h s0 (F oktrans G S0 U s0) s1 (F oktrans G T S0 s1)
  | subtyp_mode G T1 T2 s0 => f_mode G T1 T2 s0 (F notrans G T1 T2 s0)
  | subtyp_trans G T1 T2 T3 s0 s1 =>
      f_trans G T1 T2 T3 s0 (F oktrans G T1 T2 s0) s1 (F oktrans G T2 T3 s1)
  end
with F0 (m : mode) (c : ctx) (d d0 : dec) (s : subdec m c d d0) {struct s} :
  P0 m c d d0 s :=
  match s as s0 in (subdec m0 c0 d1 d2) return (P0 m0 c0 d1 d2 s0) with
  | subdec_typ m0 G Lo1 Hi1 Lo2 Hi2 s0 s1 s2 s3 =>
      f_typ m0 G Lo1 Hi1 Lo2 Hi2 s0 (F m0 G Lo1 Hi1 s0) s1 (F m0 G Lo2 Hi2 s1)
        s2 (F m0 G Lo2 Lo1 s2) s3 (F m0 G Hi1 Hi2 s3)
  | subdec_fld m0 G T1 T2 s0 => f_fld m0 G T1 T2 s0 (F m0 G T1 T2 s0)
  end
for F.


Definition subtyp_mut' := fun 
  (P : forall (m : mode) (c : ctx) (t t0 : typ), subtyp m c t t0 -> Prop)
  (P0: forall (m : mode) (c : ctx) (d d0 : dec), subdec m c d d0 -> Prop)
  => fun f_refl f_top f_bot f_bind_typ f_bind_fld f_asel_l f_asel_r f_mode f_trans f_typ f_fld =>
fix F (m : mode) (c : ctx) (t t0 : typ) (s : subtyp m c t t0) {struct s} :
  P m c t t0 s :=
  match s as s0 in (subtyp m0 c0 t1 t2) return (P m0 c0 t1 t2 s0) with
  | subtyp_refl G T => f_refl G T
  | subtyp_top G T => f_top G T
  | subtyp_bot G T => f_bot G T
  | subtyp_bind L G l d1 d2 s0 =>
      f_bind_typ L G l d1 d2 s0
        (fun (z : var) (n : z \notin L) =>
         F0 oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
           (open_dec z d2) (s0 z n))
  | subtyp_asel_l G p L S0 U T h s0 =>
      f_asel_l G p L S0 U T h s0 (F oktrans G U T s0)
  | subtyp_asel_r G p L S0 U T h s0 s1 =>
      f_asel_r G p L S0 U T h s0 (F oktrans G S0 U s0) s1 (F oktrans G T S0 s1)
  | subtyp_mode G T1 T2 s0 => f_mode G T1 T2 s0 (F notrans G T1 T2 s0)
  | subtyp_trans G T1 T2 T3 s0 s1 =>
      f_trans G T1 T2 T3 s0 (F oktrans G T1 T2 s0) s1 (F oktrans G T2 T3 s1)
  end
with F0 (m : mode) (c : ctx) (d d0 : dec) (s : subdec m c d d0) {struct s} :
  P0 m c d d0 s :=
  match s as s0 in (subdec m0 c0 d1 d2) return (P0 m0 c0 d1 d2 s0) with
  | subdec_typ m0 G Lo1 Hi1 Lo2 Hi2 s0 s1 s2 s3 =>
      f_typ m0 G Lo1 Hi1 Lo2 Hi2 s0 (F m0 G Lo1 Hi1 s0) s1 (F m0 G Lo2 Hi2 s1)
        s2 (F m0 G Lo2 Lo1 s2) s3 (F m0 G Hi1 Hi2 s3)
  | subdec_fld m0 G T1 T2 s0 => f_fld m0 G T1 T2 s0 (F m0 G T1 T2 s0)
  end
for F.





(*
Definition lift_subtypP_to_subdecP(m: mode)(G: ctx)(d1 d2: dec)
  (P : forall (m0: mode) (G0: ctx) (T1 T2 : typ), subtyp m0 G0 T1 T2 -> Prop)
  (sd: subdec m G d1 d2) : Prop := 
match sd with
| @subdec_typ m G Lo1 Hi1 Lo2 Hi2 _ _ HL HH => P m G Lo2 Lo1 HL /\ P m G Hi1 Hi2 HH
| @subdec_fld m G T1 T2 H => P m G T1 T2 H
end.
*)

(* mutual induction on ty/list ty (Set)
   but we want mutual induction on subtyp, which is a Prop 
Fixpoint liftp (P:ty->Prop)(l:list ty) {struct l} : Prop := match l
with
| cons t l => P t /\ liftp P l
| _ => True
end.
*)


(*exercise: prove subtyp_mut *)
Lemma subtyp_mut'  : forall
         (P : forall (m : mode) (c : ctx) (t t0 : typ),
              subtyp m c t t0 -> Prop)
         (P0 : forall (m : mode) (c : ctx) (d d0 : dec),
               subdec m c d d0 -> Prop),
       (forall (G : ctx) (T : typ), P notrans G T T (subtyp_refl G T)) ->
       (forall (G : ctx) (T : typ), P notrans G T typ_top (subtyp_top G T)) ->
       (forall (G : ctx) (T : typ), P notrans G typ_bot T (subtyp_bot G T)) ->
       (forall (L : fset var) (G : env typ) (l : label) (d1 d2 : dec)
          (s : forall z : var,
               z \notin L ->
               subdec oktrans (G & z ~ typ_bind l (open_dec z d1))
                 (open_dec z d1) (open_dec z d2)),
        (forall (z : var) (n : z \notin L),
         P0 oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
           (open_dec z d2) (s z n)) ->
        P notrans G (typ_bind l d1) (typ_bind l d2) (subtyp_bind d1 d2 s)) ->
       (forall (G : ctx) (p : pth) (L : label) (S U T : typ)
          (h : has G p L (dec_typ S U)) (s : subtyp oktrans G U T),
        P oktrans G U T s -> P notrans G (typ_asel p L) T (subtyp_asel_l h s)) ->
       (forall (G : ctx) (p : pth) (L : label) (S U T : typ)
          (h : has G p L (dec_typ S U)) (s : subtyp oktrans G S U),
        P oktrans G S U s ->
        forall s0 : subtyp oktrans G T S,
        P oktrans G T S s0 ->
        P notrans G T (typ_asel p L) (subtyp_asel_r h s s0)) ->
       (forall (G : ctx) (T1 T2 : typ) (s : subtyp notrans G T1 T2),
        P notrans G T1 T2 s -> P oktrans G T1 T2 (subtyp_mode s)) ->
       (forall (G : ctx) (T1 T2 T3 : typ) (s : subtyp oktrans G T1 T2),
        P oktrans G T1 T2 s ->
        forall s0 : subtyp oktrans G T2 T3,
        P oktrans G T2 T3 s0 -> P oktrans G T1 T3 (subtyp_trans s s0)) ->
       (forall (m : mode) (G : ctx) (Lo1 Hi1 Lo2 Hi2 : typ)
          (s : subtyp m G Lo1 Hi1),
        P m G Lo1 Hi1 s ->
        forall s0 : subtyp m G Lo2 Hi2,
        P m G Lo2 Hi2 s0 ->
        forall s1 : subtyp m G Lo2 Lo1,
        P m G Lo2 Lo1 s1 ->
        forall s2 : subtyp m G Hi1 Hi2,
        P m G Hi1 Hi2 s2 ->
        P0 m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2) (subdec_typ s s0 s1 s2)) ->
       (forall (m : mode) (G : ctx) (T1 T2 : typ) (s : subtyp m G T1 T2),
        P m G T1 T2 s -> P0 m G (dec_fld T1) (dec_fld T2) (subdec_fld s)) ->
       forall (m : mode) (c : ctx) (t t0 : typ) (s : subtyp m c t t0),
       P m c t t0 s.
Proof.
  fix 17.
  intros.
  inversion s; subst.
  apply (@H c t0).
  Guarded.
  assumption.
Qed.
(*
  intros.
  apply (subtyp_mut P P0); assumption.
*)
Qed.

Lemma subtyp_mut2:
  forall (P : forall (m : mode) (c : ctx) (t t0 : typ), subtyp m c t t0 -> Prop),
       (forall (G : ctx) (T : typ), P notrans G T T (subtyp_refl G T)) ->
       (forall (G : ctx) (T : typ), P notrans G T typ_top (subtyp_top G T)) ->
       (forall (G : ctx) (T : typ), P notrans G typ_bot T (subtyp_bot G T)) ->


       (*(forall (L : fset var) (G : env typ) (l : label) (d1 d2 : dec)
          (s : forall z : var,
               z \notin L ->
               subdec oktrans (G & z ~ typ_bind l (open_dec z d1))
                 (open_dec z d1) (open_dec z d2)),
        (forall (z : var) (n : z \notin L),
         P0 oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
           (open_dec z d2) (s z n)) ->
        P notrans G (typ_bind l d1) (typ_bind l d2) (subtyp_bind d1 d2 s)) -> *)

      (forall (L : fset var) (G : env typ) (l : label) (T1 T2 : typ)
          (s: forall (z : var) (n: z \notin L),
              subtyp oktrans (G & z ~ typ_bind l (open_dec z (dec_fld T1)))
                             (open_typ z T1) (open_typ z T2))
          (z2: var)
          (sd: subdec oktrans (G & z2 ~ typ_bind l (open_dec z2 (dec_fld T1)))
                 (open_dec z2 (dec_fld T1)) (open_dec z2 (dec_fld T2))),
          p_subtyp_to_p_subdec P sd
          (*s : forall (z : var) (n: z \notin L),
               subdec oktrans (G & z ~ typ_bind l (open_dec z (dec_fld T1)))
                 (open_dec z (dec_fld T1)) (open_dec z (dec_fld T2))*)

        (*(forall (z : var) (n : z \notin L),
          p_subtyp_to_p_subdec P s 
         P0 oktrans (G & z ~ typ_bind l (open_dec z (dec_fld T1))) 
           (open_dec z (dec_fld T1))
           (open_dec z (dec_fld T2)) (s z n))*)  ->
        P notrans G (typ_bind l (dec_fld T1)) (typ_bind l (dec_fld T2)) 
          (subtyp_bind (dec_fld T1) (dec_fld T2) 
                       (fun (z: var) (n: z \notin L) => subdec_fld (s z n)))) ->


(*
       (forall (L : fset var) (G : env typ) (l : label) (d1 d2 : dec)
          (s : forall z : var,
               z \notin L ->
               (forall (sd: subdec oktrans (G & z ~ typ_bind l (open_dec z d1))
                 (open_dec z d1) (open_dec z d2)), p_subtyp_to_p_subdec P sd)),
        (*(forall (z : var) (n : z \notin L),
         P0 oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
           (open_dec z d2) (s z n)) ->*)
        P notrans G (typ_bind l d1) (typ_bind l d2) (subtyp_bind d1 d2 s)) ->



       (forall (L : fset var) (G : env typ) (l : label) (l1 l2 : label) (T1 T2: typ)
          (s : forall z : var,
               z \notin L ->
               subdec oktrans (G & z ~ typ_bind l (open_dec z d1))
                 (open_dec z d1) (open_dec z d2)),
        (forall (z : var) (n : z \notin L),
         P0 oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
           (open_dec z d2) (s z n)) ->
        P notrans G (typ_bind l (dec_fld T1)) (typ_bind l (dec_fld T2)) 
                    (subtyp_bind (dec_fld T1) (dec_fld T2) s)) ->
*)





       (forall (G : ctx) (p : pth) (L : label) (S U T : typ)
          (h : has G p L (dec_typ S U)) (s : subtyp oktrans G U T),
        P oktrans G U T s -> P notrans G (typ_asel p L) T (subtyp_asel_l h s)) ->
       (forall (G : ctx) (p : pth) (L : label) (S U T : typ)
          (h : has G p L (dec_typ S U)) (s : subtyp oktrans G S U),
        P oktrans G S U s ->
        forall s0 : subtyp oktrans G T S,
        P oktrans G T S s0 ->
        P notrans G T (typ_asel p L) (subtyp_asel_r h s s0)) ->
       (forall (G : ctx) (T1 T2 : typ) (s : subtyp notrans G T1 T2),
        P notrans G T1 T2 s -> P oktrans G T1 T2 (subtyp_mode s)) ->
       (forall (G : ctx) (T1 T2 T3 : typ) (s : subtyp oktrans G T1 T2),
        P oktrans G T1 T2 s ->
        forall s0 : subtyp oktrans G T2 T3,
        P oktrans G T2 T3 s0 -> P oktrans G T1 T3 (subtyp_trans s s0)) ->
       (*(forall (m : mode) (G : ctx) (Lo1 Hi1 Lo2 Hi2 : typ)
          (s : subtyp m G Lo1 Hi1),
        P m G Lo1 Hi1 s ->
        forall s0 : subtyp m G Lo2 Hi2,
        P m G Lo2 Hi2 s0 ->
        forall s1 : subtyp m G Lo2 Lo1,
        P m G Lo2 Lo1 s1 ->
        forall s2 : subtyp m G Hi1 Hi2,
        P m G Hi1 Hi2 s2 ->
        P0 m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2) (subdec_typ s s0 s1 s2)) ->
       (forall (m : mode) (G : ctx) (T1 T2 : typ) (s : subtyp m G T1 T2),
        P m G T1 T2 s -> 
        P0 m G (dec_fld T1) (dec_fld T2) (subdec_fld s)) ->*)
       forall (m : mode) (c : ctx) (t t0 : typ) (s : subtyp m c t t0),
       P m c t t0 s.

Proof.
  intros.
Admitted.






Definition test 
    (P : forall (m : mode) (c : ctx) (t t0 : typ), subtyp m c t t0 -> Prop)
    (P0: forall (m : mode) (c : ctx) (d d0 : dec), subdec m c d d0 -> Prop) :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => conj
    (subtyp_mut P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (subdec_mut P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).

Definition test2 
    (P : forall (m : mode) (c : ctx) (t t0 : typ), subtyp m c t t0 -> Prop)
    (P0: forall (m : mode) (c : ctx) (d d0 : dec), subdec m c d d0 -> Prop) :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    (subtyp_mut P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).


Definition even_odd_mutual_ind' (P P0: Z -> Prop) :=
  fun h1 h2 h3 => conj (even_ind_2 P P0 h1 h2 h3) (odd_ind_2 P P0 h1 h2 h3).


Check subtyp_ind.
*)

(* ... free vars ... *)

Inductive fvar : avar -> Prop :=
  | fvar_f : forall x,
      fvar (avar_f x).

Inductive path : pth -> Prop :=
  | path_var : forall a,
      fvar a ->
      path (pth_var a)
(*| path_sel : forall p l,
      path p ->
      path (pth_sel p l)*).

Inductive type : typ -> Prop :=
  | type_top : type (typ_top)
  | type_bot : type (typ_bot)
  | type_rfn : forall L t l d,
      type t ->
      (forall x, x \notin L -> decl (open_dec x d)) ->
      type (typ_bind l d)
  | type_asel : forall p l,
      path p ->
      type (typ_asel p l)
with decl : dec -> Prop :=
  | decl_typ  : forall ts tu,
      type ts ->
      type tu ->
      decl (dec_typ ts tu)
  | decl_fld : forall t,
      type t ->
      decl (dec_fld t).

Fixpoint fv_avar (a: avar) { struct a } : vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Fixpoint fv_pth (p: pth) { struct p } : vars :=
  match p with
  | pth_var a => fv_avar a
(*| pth_sel p l => fv_pth p*)
  end.

Fixpoint fv_typ (t: typ) { struct t } : vars :=
  match t with
  | typ_top => \{}
  | typ_bot => \{}
  | typ_bind l d => fv_dec d
  | typ_asel p l => fv_pth p
  end
with fv_dec (d: dec) { struct d } : vars :=
  match d with
  | dec_typ ts tu => (fv_typ ts) \u (fv_typ tu)
  | dec_fld t => fv_typ t
  end.


(* ... infrastructure ... *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x        ) in
  let B := gather_vars_with (fun x : var  => \{ x }   ) in
  let C := gather_vars_with (fun x : ctx  => dom x    ) in
  let D := gather_vars_with (fun x : avar => fv_avar x) in
  let E := gather_vars_with (fun x : pth  => fv_pth  x) in
  let F := gather_vars_with (fun x : dec  => fv_dec  x) in
  let G := gather_vars_with (fun x : typ  => fv_typ  x) in
  constr:(A \u B \u C \u D \u E \u F \u G).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(* not needed
Lemma notin_empty: forall z A, z # (@empty A).
Proof.
  intros.
  unfold notin.
  rewrite -> dom_empty.
  rewrite -> in_empty.
  rewrite -> not_False.
  apply I.
Qed. *)


(* ... examples ... *)

(*    { l1: { l2: Top }} <: { l1: Top }     *)
Definition subtyp_example_1(l1 l2: label): Prop :=
  subtyp notrans empty
    (typ_bind l1 (dec_fld (typ_bind l2 (dec_fld typ_top))))
    (typ_bind l1 (dec_fld typ_top)).

Fact subtyp_example_1_proof: exists l1 l2, subtyp_example_1 l1 l2.
Proof.
  unfold subtyp_example_1.
  pick_fresh l1.
  pick_fresh l2.
  exists l1 l2.
  apply (@subtyp_bind \{} empty).
  intros.
  apply subdec_fld.
  apply subtyp_mode.
  apply subtyp_top.
Qed.


(* ... transitivity in oktrans mode (trivial) ... *)

Lemma subtyp_trans_oktrans: forall G T1 T2 T3,
  subtyp oktrans G T1 T2 -> subtyp oktrans G T2 T3 -> subtyp oktrans G T1 T3.
Proof.
  introv H12 H23.
  apply (subtyp_trans H12 H23).
Qed.

Lemma subdec_trans_oktrans: forall G d1 d2 d3,
  subdec oktrans G d1 d2 -> subdec oktrans G d2 d3 -> subdec oktrans G d1 d3.
Proof.
  introv H12 H23.
  destruct d2 as [Lo2 Hi2 | T2].
  (* case typ *)
  inversion H12 as [? ? Lo1 Hi1 ?   ?   HLo1Hi1 HLo2Hi2 HLo2Lo1 HHi1Hi2 | ]; subst.
  inversion H23 as [? ? ?   ?   Lo3 Hi3 ?       HLo3Hi3 HLo3Lo2 HHi2Hi3 | ]; subst.
  apply (subdec_typ HLo1Hi1 HLo3Hi3
    (subtyp_trans_oktrans HLo3Lo2 HLo2Lo1)
    (subtyp_trans_oktrans HHi1Hi2 HHi2Hi3)
  ).
  (* case fld *)
  inversion H12 as [ | ? ? T1 ? HT12 ]; subst.
  inversion H23 as [ | ? ? ? T3 HT23 ]; subst.
  apply subdec_fld.
  apply (subtyp_trans HT12 HT23).
Qed.


(* ... helper lemmas ... *)

Lemma has_unique: forall G p X d1 d2, 
  has G p X d1 -> has G p X d2 -> d1 = d2.
Proof.
  introv H1 H2.
  inversion H1. inversion H2. subst.
  injection H8.
  intro; subst.
  assert (typ_bind X d1 = typ_bind X d2) by apply (binds_func H H6).
  injection H0.
  trivial.
Qed.

(* Lemma invert_subtyp_bot: forall m G T, subtyp m G T typ_bot -> T = typ_bot.
   Does not hold because T could be a p.L with lower and upper bound bottom. *)

(*
Lemma invert_subtyp_bot: forall m G T, subtyp m G T typ_bot -> T = typ_bot.

Proof.
  intros.
  inversion H; subst.
  trivial.
  trivial.
  inversion H; subst.

*)


(* ... weakening lemmas ... *)

Lemma subdec_weaken_last: forall G z l d1 d2 dA dB,
  subdec oktrans (G & z ~ typ_bind l d2) dA dB ->
  subdec oktrans (G & z ~ typ_bind l d1) d1 d2 ->
  subdec oktrans (G & z ~ typ_bind l d1) dA dB.
Proof.
  (* TODO ;-) *)
Admitted.


(* ... transitivity in notrans mode, but no p.L in middle ... *)

Lemma subtyp_trans_notrans: forall G T1 T2 T3,
  notsel T2 -> subtyp notrans G T1 T2 -> subtyp notrans G T2 T3 -> subtyp notrans G T1 T3.
Proof.
  introv Hnotsel H12 H23.

  inversion Hnotsel (*as [ | | l d2]*); subst.
  (* case top *)
  skip.
  (* case bot *)
  skip. 
  (* case bind *)
  inversion H12; inversion H23; subst; (
    assumption ||
    apply subtyp_refl ||
    apply subtyp_top ||
    apply subtyp_bot ||
    idtac
  ).

  (* bind <: bind <: bind *)
  apply (@subtyp_bind (L \u L0)).
  intros.
  assert (HzL: z \notin L) by notin_solve.
  assert (HzL0: z \notin L0) by notin_solve.
  specialize (H3 z HzL).
  specialize (H7 z HzL0).
  assert (H7': subdec oktrans (G & z ~ typ_bind l (open_dec z (*->*)d1(*<-*))) 
                              (open_dec z d) (open_dec z d3)).
  apply (subdec_weaken_last H7 H3).
  apply (subdec_trans_oktrans H3 H7').

  (* bind <: bind <: sel  *)
  assert (H1S: subtyp oktrans G (typ_bind l d1) S).
  apply (subtyp_trans_oktrans (subtyp_mode H12) H6).
  apply (subtyp_asel_r H4 H5 H1S).

  (* sel  <: bind <: bind *)
  assert (HU2: subtyp oktrans G U (typ_bind l d2)).
  apply (subtyp_trans_oktrans H0 (subtyp_mode H23)).
  apply (subtyp_asel_l H HU2). 

  (* sel  <: bind <: sel  *)
  assert (H1S0: subtyp oktrans G (typ_asel p L) S0).
  apply (subtyp_trans_oktrans (subtyp_mode H12) H6).
  apply (subtyp_asel_r H1 H5 H1S0).
Qed.

(*
(notransl G A B) means that there exists a notrans-subtyping chain/list
    A <: T1 <: T2 <: ... <: TN <: B
where no Ti is a p.L
*)
Inductive notransl: ctx -> typ -> typ -> Prop :=
  | notransl_nil : forall G A B,
      (* could also just have reflexivity here, but having a subtyp makes 
      top/bot cases easier *)
      subtyp notrans G A B ->
      notransl G A B
  | notransl_cons : forall G A T1 B,
      subtyp notrans G A T1 ->
      notsel T1 ->
      notransl G T1 B ->
      notransl G A B.

(* 
(follow_ub G p1.X1 T) means that there exists a chain
  (p1.X1: _ .. p2.X2), (p2.X2: _ .. p3.X3), ... (pN.XN: _ .. T)
which takes us from p1.X1 to T
*)
Inductive follow_ub : ctx -> typ -> typ -> Prop :=
  | follow_ub_nil : forall G T,
      follow_ub G T T
  | follow_ub_cons : forall G p X Lo Hi T,
      has G p X (dec_typ Lo Hi) ->
      follow_ub G Hi T ->
      follow_ub G (typ_asel p X) T.

(*
(follow_lb G T pN.XN) means that there exists a chain
  (p1.X1: T .. _), (p2.X2: p1.X1 .. _), (p3.X3: p2.X2 .. _),  (pN.XN: pN-1.XN-1 .. _)
which takes us from T to pN.XN
*)
Inductive follow_lb: ctx -> typ -> typ -> Prop :=
  | follow_lb_nil : forall G T,
      follow_lb G T T
  | follow_lb_cons : forall G p X Lo Hi U,
      has G p X (dec_typ Lo Hi) ->
      follow_lb G (typ_asel p X) U ->
      follow_lb G Lo U.

Lemma follow_ub_top: forall G T, follow_ub G typ_top T -> T = typ_top.
Proof.
  intros.
  inversion H.
  trivial.
Qed.

Lemma follow_ub_bind: forall G l d T, 
  follow_ub G (typ_bind l d) T -> T = (typ_bind l d).
Proof.
  intros.
  inversion H.
  trivial.
Qed.

(*
Require Import Coq.Program.Equality.

Lemma follow_ub_bot: forall G T,
  follow_ub G T typ_bot -> T = typ_bot.
does not hold (can have a p.X:bot..bot, and follow_ub_nil bot) *)

(*
Lemma follow_ub_sel_sel: forall G p1 X1 T,
  follow_ub G (typ_asel p1 X1) T -> exists p2 X2, T = (typ_asel p2 X2).
Proof.
  intros.
  dependent induction H.
  exists p1 X1.
  trivial.
  specialize (IHfollow_ub p1 X1).
  induction H.
  skip.
  assumption.
*)
(* not needed
Lemma follow_ub_bot: forall G T, follow_ub G typ_bot T -> T = typ_bot.
Proof.
  intros.
  inversion H.
  trivial.
Qed.*)

(* linearize a derivation that uses transitivity *)

Definition chain (G: ctx) (A D: typ): Prop :=
   (exists B C, follow_ub G A B /\ notransl G B C /\ follow_lb G C D)
(*\/ (A = typ_top /\ subtyp notrans G A D)
\/ (D = typ_bot /\ subtyp notrans G A D)*).


Lemma subtyp_mut_test_1: forall m G A1 A2,
  subtyp m G A1 A2 ->
  True.
Proof.
  apply subtyp_mut with 
    (P := fun (m': mode) (G': ctx) (A1' A2': typ) (st: subtyp m' G' A1' A2') 
          => True)
    (P0:= fun (m': mode) (G': ctx) (d1' d2': dec) (sd: subdec m' G' d1' d2') 
          => True); auto.
Qed.

Inductive isEnv: ctx -> Prop :=
  | isEnvYes: forall G, isEnv G.

Lemma subtyp_mut_test_2: forall m G A1 A2,
  subtyp m G A1 A2 ->
  isEnv G.
Proof.
  apply subtyp_mut with 
    (P := fun (m': mode) (G': ctx) (A1' A2': typ) (st: subtyp m' G' A1' A2') 
          => isEnv G')
    (P0:= fun (m': mode) (G': ctx) (d1' d2': dec) (sd: subdec m' G' d1' d2') 
          => isEnv G')
  ; intros; apply isEnvYes.
Qed.

Lemma subtyp_mut_test_3: forall G A1 A2,
  subtyp oktrans G A1 A2 ->
  isEnv G.
Proof.
  apply subtyp_mut with 
    (P := fun (m': mode) (G': ctx) (A1' A2': typ) (st: subtyp m' G' A1' A2') 
          => isEnv G')
    (P0:= fun (m': mode) (G': ctx) (d1' d2': dec) (sd: subdec m' G' d1' d2') 
          => isEnv G')
  ; intros; apply isEnvYes.
Qed.

(* exercise: prove something easy about subtyp/subdec proof sizes *)

Inductive stsize: forall (m: mode) (G: ctx) (T1 T2: typ) (st: subtyp m G T1 T2), 
                         nat -> Prop :=
  | stsize_refl : forall (m: mode) (G: ctx) (T: typ) (st: subtyp m G T T),
      stsize st 0
  | stsize_top : forall (m: mode) (G: ctx) (T: typ) (st: subtyp m G T typ_top),
      stsize st 0
  | stsize_bot : forall (m: mode) (G: ctx) (T: typ) (st: subtyp m G typ_bot T),
      stsize st 0
  | stsize_bind : forall (G: ctx) (l: label) (d1 d2: dec)
     (L: fset var) (z : var) (noti: z \notin L)
     (s: forall (z : var) (noti: z \notin L),
        subdec oktrans (G & z ~ typ_bind l (open_dec z d1)) (open_dec z d1)
          (open_dec z d2))
         (n: nat),
      sdsize (s z noti) n ->
      stsize (subtyp_bind d1 d2 s) (S n)
  | stsize_asel_l : forall (G: ctx) (p: pth) (L: label) (S0 U T: typ)
                           (H: has G p L (dec_typ S0 U))
                           (st: subtyp oktrans G U T) (n: nat),
      stsize st n ->
      stsize (subtyp_asel_l H st) (S n)
  | stsize_asel_r : forall (m: mode) (G: ctx) (T: typ) (p: pth) (L: label)
                           (st: subtyp m G T (typ_asel p L)),
      stsize st 0
  | stsize_mode : forall (G: ctx) (T1 T2: typ) (st: subtyp notrans G T1 T2),
      stsize (subtyp_mode st) 0
  | stsize_trans : forall (G: ctx) (T1 T2 T3: typ)
                          (st12: subtyp oktrans G T1 T2)
                          (st23: subtyp oktrans G T2 T3),
      stsize (subtyp_trans st12 st23) 0
with sdsize: forall (m: mode) (G: ctx) (d1 d2: dec) (sd: subdec m G d1 d2), 
                         nat -> Prop :=
  | sdsize_typ : forall (m: mode) (G: ctx) (Lo1 Hi1 Lo2 Hi2: typ)
                        (sd: subdec m G (dec_typ Lo1 Hi1) (dec_typ Lo2 Hi2)),
      sdsize sd 0
  | sdsize_fld : forall (m: mode) (G: ctx) (T1 T2: typ)
                        (sd: subdec m G (dec_fld T1) (dec_fld T2)),
      sdsize sd 0.

Hint Constructors stsize sdsize.

Lemma subtyp_mut_test_4: forall (G: ctx) (A1 A2: typ) (st: subtyp oktrans G A1 A2),
  exists N, stsize st N.
Proof.
  apply subtyp_mut with 
    (P := fun (m': mode) (G': ctx) (A1' A2': typ) (st: subtyp m' G' A1' A2') 
          => exists N, stsize st N)
    (P0:= fun (m': mode) (G': ctx) (d1' d2': dec) (sd: subdec m' G' d1' d2') 
          => exists N, sdsize sd N)
  ; intros; try (exists 0; progress auto).
  (* case bind *)
  pick_fresh z.
  assert (Hnoti: z \notin L) by notin_solve.
  set (H' := H z Hnoti).
  set (s' := s z Hnoti).
  destruct H' as [N H'].
  exists (S N).
  apply (stsize_bind d1 d2 Hnoti).
  apply H'.
  (* case asel_l *)
  destruct H as [N H].
  rename S into S0.
  exists (S N).
  apply (stsize_asel_l h H).
Qed.

Lemma notransl_head: forall G A C,
  notransl G A C ->
  (exists B, notsel B /\ subtyp notrans G A B /\ notransl G B C) \/
  (subtyp notrans G A C).
Proof.
  introv Hn.
  inversion Hn; subst.
  (* case notransl_nil *)
  right. assumption.
  (* case notransl_cons *)
  left.
  exists T1. auto.
Qed.

(*
Lemma notransl_asel_head: forall G p L C S U, 
  notransl G (typ_asel p L) C ->
  has G p L (dec_typ S U) ->
  (notransl G U C \/ C = (typ_asel p L)).
Proof.
  introv Hn Hh.
  inversion Hn; subst.
  (* case notransl_nil *)
  inversion H; subst.
  right. trivial.
  left. apply (notransl_nil (subtyp_top _ _)).
  skip.
  skip.
  (* case notransl_cons *)
  inversion H; subst.
*)  

(* prepend an oktrans to chain ("utrans0*") *)
Lemma prepend_chain: forall G A1 A2 D,
  subtyp oktrans G A1 A2 ->
  chain G A2 D ->
  chain G A1 D.
Proof.
  fix 5.
  introv Hokt Hch.
  unfold chain in *.
  inversion Hokt; inversion H; subst.
  (* case refl *)
  assumption.
  (* case top *)
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  exists A1 C.
  split. apply follow_ub_nil.
  apply follow_ub_top in Hch1. subst.
  split. apply (notransl_cons (subtyp_top G A1) notsel_top Hch2).
  apply Hch3.
  (* case bot *)
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  exists typ_bot C.
  split. apply follow_ub_nil.
  split. apply (notransl_nil (subtyp_bot G C)).
  apply Hch3.
  (* case bind *)
  destruct Hch as [B [C [Hch1 [Hch2 Hch3]]]].
  assert (B = typ_bind l d2) by apply (follow_ub_bind Hch1); subst.
  exists (typ_bind l d1) C.
  split. apply follow_ub_nil.
  split. apply (notransl_cons H (notsel_bind _ _) Hch2).
  assumption.
  (* case asel_l *)
  set (IH := (prepend_chain G U A2 D H4 Hch)).
  destruct IH as [B [C [IH1 [IH2 IH3]]]].
  exists B C.
  split. 
  apply (follow_ub_cons H0 IH1).
  split; assumption.
  (* case asel_r *)
  set (Hch' := Hch).
  destruct Hch' as [B [C [Hch1 [Hch2 Hch3]]]].
  inversion Hch1; subst.
    (* case follow_ub_nil *)
    inversion Hch2; subst.

  
    inversion Hch3; subst.
      (* case follow_lb_nil *)
      inversion Hch2; subst.

      skip.
      (* case follow_lb_cons *)
      skip.
    (* case follow_ub_cons *)
    apply (prepend_chain G A1 S D H5).
    apply (prepend_chain G S U D H4).
    assert (HdecEq: dec_typ Lo Hi = dec_typ S U) by apply (has_unique H6 H0).
    injection HdecEq; intros; subst.
    exists B C.
    split. assumption. split. assumption. assumption.
  (* case mode *)
  apply (prepend_chain G _ _ _ H (prepend_chain G _ _ _ H0 Hch)).
  (* case trans *)
  apply (prepend_chain G _ _ _ H (prepend_chain G _ _ _ H0 Hch)).
Qed.


(* garbage 


  (* cannot express dependency between A2 (in subtyp on which we do induction)
     and A2 in head of chain *)
  apply subtyp_mut with 
    (P := fun (m': mode) (G': ctx) (A1' A2': typ) (st: subtyp m' G' A1' A2') 
          => chain G' A1' D)
    (P0:= fun (m': mode) (G': ctx) (d1' d2': dec) (sd: subdec m' G' d1' d2') 
          => True)
    (m := oktrans)
    (c := G)
    (t0:= D);
  unfold chain in *;
  intros.

  (*
  apply subtyp_mut with 
    (P := (fun m G0 T1 T2 => fun (st: subtyp m G0 T1 T2) => chain G0 T1 T2))
    (P0:= (fun m G0 d1 d2 => fun (sd: subdec m G0 d1 d2) => True))
    (m := oktrans);
  unfold chain in *;
  intros.
  *)
  (* old proof start:
  introv Hokt Hch.
  unfold chain in *.
  induction Hokt.
  *)


(*  
(stlist G T1 B) means that there exists a notrans-subtyping chain
    T1 <: T2 <: ... <: TN <: B
where no Ti is a p.L
*)
Inductive stlist: ctx -> typ -> typ -> Prop :=
  | stlist_nil : forall G T1 B,
      notsel T1 ->
      subtyp notrans G T1 B ->
      stlist G T1 B
  | stlist_cons : forall G T1 T2 B,
      notsel T1 ->
      subtyp notrans G T1 T2 ->
      stlist G T2 B ->
      stlist G T1 B.

(*
(notsel_ub G p.X T) means that by repeatedly taking upper bound of p.X, we finally
reach a T which is not a sel.
*)
Inductive notsel_ub: ctx -> p -> label -> typ -> Prop :=
  | notsel_ub_nil : forall G p X Lo T,
      has G p X (dec_typ Lo T) ->
      notsel T ->
      notsel_ub G p X T
  | 


(*  
(st_list N G A B) means that there exists a notrans-subtyping chain
    A <: T1 <: T2 <: ... <: TN <: B
where no Ti is a p.L
*)
Inductive stlist: nat -> ctx -> typ -> typ -> Prop :=
  | stlist_nil : forall G A B,
      subtyp notrans G A B ->
      stlist O G A B
  | stlist_cons : forall N G A T1 B,
      subtyp notrans G A T1 ->
      notsel T1 ->
      stlist N G T1 B ->
      stlist (S N) G A B.


  
match goal with 
  | [ H : z \notin ?theL |- _ ] => match H with 
      | Fr => set (L2 := theL)
      end
  end.



(*
H3 :  subdec oktrans (G & z ~ typ_bind l d1) (open_dec z d1) (open_dec z d)

H7' : subdec oktrans (G & z ~ typ_bind l d1) (open_dec z d) (open_dec z d3)

 ^
 |

H7  : subdec oktrans (G & z ~ typ_bind l d ) (open_dec z d) (open_dec z d3)
*)


(*  
(st_list N G T0 TN+1) means that there exists a notrans-subtyping chain
    T0 <: T1 <: T2 <: ... <: TN <: TN+1
where no Ti is a p.L
*)    
Inductive stlist: nat -> ctx -> typ -> typ -> Prop :=
  | stlist_nil : forall G T0 T1,
      notsel T0 ->
      notsel T1 ->
      subtyp notrans G T0 T1 ->
      stlist O G T0 T1
  | stlist_cons : forall N G T0 T1 TNp2,
      notsel T0 ->
      subtyp notrans G T0 T1 ->
      stlist N G T1 TNp2 ->
      stlist (S N) G T0 TNp2.
*)

(*

.... follow_ub/lb versions which cannot be of size 0 ....

(* 
(follow_ub G p1 X1 T) means that there exists a chain
  (p1.X1: _ .. p2.X2), (p2.X2: _ .. p3.X3), ... (pN.XN: _ .. T)
which takes us from p1.X1 to T
*)
Inductive follow_ub : ctx -> pth -> label -> typ -> Prop :=
  | follow_ub_nil : forall G p X Lo T,
      has G p X (dec_typ Lo T) ->
      follow_ub G p X T
  | follow_ub_cons : forall G p1 X1 Lo1 p2 X2 T,
      has G p1 X1 (dec_typ Lo1 (typ_asel p2 X2)) ->
      follow_ub G p2 X2 T ->
      follow_ub G p1 X1 T.

(*
(follow_lb G T pN XN) means that there exists a chain
  (p1.X1: T .. _), (p2.X2: p1.X1 .. _), (p3.X3: p2.X2 .. _),  (pN.XN: pN-1.XN-1 .. _)
which takes us from T to pN.XN
*)
Inductive follow_lb: ctx -> typ -> pth -> label -> Prop :=
  | follow_lb_nil : forall G p X T Hi,
      has G p X (dec_typ T Hi) ->
      follow_lb G T p X
  | follow_lb_cons : forall G T p1 X1 Hi pN XN,
      has G p1 X1 (dec_typ T Hi) ->
      follow_lb G (typ_asel p1 X1) pN XN ->
      follow_lb G T pN XN.


*)

