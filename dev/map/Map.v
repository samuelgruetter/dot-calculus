Require Import Fsub.
Require Import Dsub.

Fixpoint emb_t (T: Fsub.typ): Dsub.typ :=
  match T with
    | Fsub.typ_top => typ_top
    | Fsub.typ_bvar i => typ_sel (trm_bvar i)
    | Fsub.typ_fvar x => typ_sel (trm_fvar x)
    | Fsub.typ_arrow T U => typ_all (emb_t T) (emb_t U)
    | Fsub.typ_all T U => typ_all (typ_mem false (emb_t T)) (emb_t U)
  end.

Fixpoint emb_e (e: Fsub.trm): Dsub.trm :=
  match e with
    | Fsub.trm_bvar i => trm_bvar i
    | Fsub.trm_fvar x => trm_fvar x
    | Fsub.trm_abs T e => trm_abs (emb_t T) (emb_e e)
    | Fsub.trm_tabs T e => trm_abs (typ_mem false (emb_t T)) (emb_e e)
    | Fsub.trm_app e1 e2 => trm_app (emb_e e1) (emb_e e2)
    | Fsub.trm_tapp e1 U => trm_app (emb_e e1) (trm_mem (emb_t U))
  end.
