import leon.lang._
import leon.collection._
import leon._

object muDOT {

  abstract class label
  case class label_typ(n: BigInt) extends label
  case class label_fld(n: BigInt) extends label
  case class label_mtd(n: BigInt) extends label

  abstract class avar
  case class avar_f(n: BigInt) extends avar
  // no bound vars, we use named vars everywhere

  abstract class typ {
    // substitute x by y
    def subst(x: avar, y: avar): typ = this match {
      case typ_top => typ_top
      case typ_bot => typ_bot
      case typ_bind(z, ds) if (x == z) => this
      case typ_bind(z, ds) if (x != z) => typ_bind(z, ds.subst(x, y))
      case typ_sel(z, l) if (x == z) => typ_sel(y, l)
      case typ_sel(z, l) if (x != z) => this
    }
  }
  case object typ_top extends typ
  case object typ_bot extends typ
  case class typ_bind(z: avar, ds: decs) extends typ
  case class typ_sel(p: avar, L: label_typ) extends typ
  
  abstract class dec {
    def label: label = this match {
      case dec_typ(l, _, _) => l
      case dec_fld(l, _) => l
      case dec_mtd(l, _, _) => l
    }
    def subst(x: avar, y: avar): dec = this match {
      case dec_typ(l, t1, t2) => dec_typ(l, t1.subst(x, y), t2.subst(x, y))
      case dec_fld(l, t1) => dec_fld(l, t1.subst(x, y))
      case dec_mtd(l, t1, t2) => dec_mtd(l, t1.subst(x, y), t2.subst(x, y))
    }
  }
  case class dec_typ(L: label_typ, Lo: typ, Hi: typ) extends dec
  case class dec_fld(l: label_fld, T: typ) extends dec
  case class dec_mtd(m: label_mtd, Arg: typ, Ret: typ) extends dec
  
  abstract class decs {
    def subst(x: avar, y: avar): decs = this match {
      case decs_nil => decs_nil
      case decs_cons(d, ds) => decs_cons(d.subst(x, y), ds.subst(x, y))
    }
  }
  case object decs_nil extends decs
  case class decs_cons(head: dec, tail: decs) extends decs
  
  abstract class bdecs
  case object bdecs_bot extends bdecs
  case class bdecs_decs(ds: decs) extends bdecs
  
  abstract class ctx
  case object ctx_nil extends ctx
  case class ctx_cons(tail: ctx, x: avar, t: typ) extends ctx
  
  // binds x T G == (x: T) in G
  abstract class binds {
    def avar: avar = this match {
      case binds_hit(x, t, g) => x
      case binds_skip(x, t, g, _) => x
    }
    def typ: typ = this match {
      case binds_hit(x, t, g) => t
      case binds_skip(x, t, g, _) => t
    }
    def ctx: ctx = this match {
      case binds_hit(x, t, g) => g
      case binds_skip(x, t, g, _) => g
    }
    def ok: Boolean = this match {
      case binds_hit(x, t, g) => g match {
        case ctx_nil => false
        case ctx_cons(g0, x0, t0) => x0 == x && t0 == t
      }
      case binds_skip(x, t, g, bi) => bi.ok && bi.avar == x && bi.typ == t && bi.ctx == g
    }      
  }
  case class binds_hit(x: avar, t: typ, g: ctx) extends binds
  case class binds_skip(x: avar, t: typ, g: ctx, bi: binds) extends binds
  
  // decs_hasnt ds l
  abstract class decs_hasnt {
    def decs: decs = this match {
      case decs_hasnt_nil(ds, l) => ds
      case decs_hasnt_cons(ds, l, hasnt) => ds
    }
    def label: label = this match {
      case decs_hasnt_nil(ds, l) => l
      case decs_hasnt_cons(ds, l, hasnt) => l
    }
    def ok: Boolean = this match {
      case decs_hasnt_nil(ds, l) => ds == decs_nil
      case decs_hasnt_cons(ds, l, hasnt) => ds match {
        case decs_nil => false
        case decs_cons(dshead, dstail) =>
          hasnt.ok && hasnt.decs == dstail && hasnt.label == l && dshead.label != l
      }
    }
  }
  case class decs_hasnt_nil(ds: decs, l: label) extends decs_hasnt
  case class decs_hasnt_cons(ds: decs, l: label, hasnt: decs_hasnt) extends decs_hasnt
  
  // decs_has ds d
  abstract class decs_has {
    def decs: decs = this match {
      case decs_has_hit(ds, _, _) => ds
      case decs_has_skip(ds, _, _) => ds
    }
    def dec: dec = this match {
      case decs_has_hit(_, d, _) => d
      case decs_has_skip(_, d, _) => d
    }
    def ok: Boolean = this match {
      case decs_has_hit(ds, d, hasnt) => ds match {
        case decs_nil => false
        case decs_cons(dshead, dstail) =>
          hasnt.ok && hasnt.decs == dstail && hasnt.label == dshead.label && dshead == d
      }
      case decs_has_skip(ds, d, has) => ds match {
        case decs_nil => false
        case decs_cons(dshead, dstail) =>
          has.ok && has.decs == dstail && has.dec == d && dshead.label != d.label
      }
    }
  }
  case class decs_has_hit(ds: decs, d: dec, hasnt: decs_hasnt) extends decs_has
  case class decs_has_skip(ds: decs, d: dec, has: decs_has) extends decs_has
  
  abstract class bdecs_has {
    def bdecs: bdecs = this match {
      case bdecs_has_decs(ds, _, _) => ds
      case bdecs_has_typ(ds, _) => ds
      case bdecs_has_fld(ds, _) => ds
      case bdecs_has_mtd(ds, _) => ds
    }
    def dec: dec = this match {
      case bdecs_has_decs(_, d, _) => d
      case bdecs_has_typ(_, d) => d
      case bdecs_has_fld(_, d) => d
      case bdecs_has_mtd(_, d) => d
    }
    def ok: Boolean = this match {
      case bdecs_has_decs(ds, d, has) => ds match {
        case bdecs_decs(ds2) => has.ok && has.decs == ds2 && has.dec == d
        case bdecs_bot => false
      }
      case bdecs_has_typ(ds, d) => d match {
        case dec_typ(l, lo, hi) => lo == typ_top && hi == typ_bot && ds == bdecs_bot
        case _ => false
      }
      case bdecs_has_fld(ds, d) => d match {
        case dec_fld(l, t) => t == typ_top && ds == bdecs_bot
        case _ => false
      }
      case bdecs_has_mtd(ds, d) => d match {
        case dec_mtd(l, a, r) => a == typ_top && r == typ_bot && ds == bdecs_bot
        case _ => false
      }
    }
  }
  case class bdecs_has_decs(ds: bdecs, d: dec, has: decs_has) extends bdecs_has
  case class bdecs_has_typ(ds: bdecs, d: dec) extends bdecs_has
  case class bdecs_has_fld(ds: bdecs, d: dec) extends bdecs_has
  case class bdecs_has_mtd(ds: bdecs, d: dec) extends bdecs_has
  
  // we'll only do precise judgments (no pmode), and always allow transitivity (no tmode)

  // exp g t z ds
  abstract class exp {
    def ctx: ctx = this match {
      case exp_top(g, _, _, _) => g
      case exp_bot(g, _, _, _) => g
      case exp_bind(g, _, _, _) => g
      case exp_sel(g, _, _, _, _, _) => g
    }
    def typ: typ = this match {
      case exp_top(_, g, _, _) => g
      case exp_bot(_, g, _, _) => g
      case exp_bind(_, g, _, _) => g
      case exp_sel(_, g, _, _, _, _) => g
    }
    def avar: avar = this match {
      case exp_top(_, _, g, _) => g
      case exp_bot(_, _, g, _) => g
      case exp_bind(_, _, g, _) => g
      case exp_sel(_, _, g, _, _, _) => g
    }
    def bdecs: bdecs = this match {
      case exp_top(_, _, _, g) => g
      case exp_bot(_, _, _, g) => g
      case exp_bind(_, _, _, g) => g
      case exp_sel(_, _, _, g, _, _) => g
    }
    def ok: Boolean = this match {
      case exp_top(g, t, z, ds) => t == typ_top && ds == bdecs_decs(decs_nil)
      case exp_bot(g, t, z, ds) => t == typ_bot && ds == bdecs_bot
      case exp_bind(g, t, z1, ds0) => t match {
        case typ_bind(z2, ds2) => ds0 match {
          case bdecs_decs(ds1) => ds2.subst(z2, z1) == ds1
          case _ => false
        }
        case _ => false
      }
      case exp_sel(g, t, z, ds, ha, ex) => t match {
        case typ_sel(p, l) => 
          ha.ok && ha.ctx == g && ha.avar == p && ha.dec.label == l &&
          ex.ctx == g && (ha.dec match {
            case dec_typ(_, _, hi) => hi == ex.typ
            case _ => false
          }) && ex.avar == z && ex.bdecs == ds
        case _ => false
      }
    }
  }
  case class exp_top(g: ctx, t: typ, z: avar, ds: bdecs) extends exp
  case class exp_bot(g: ctx, t: typ, z: avar, ds: bdecs) extends exp
  case class exp_bind(g: ctx, t: typ, z: avar, ds: bdecs) extends exp
  case class exp_sel(g: ctx, t: typ, z: avar, ds: bdecs, ha: has, ex: exp) extends exp
  
  // has G p D
  abstract class has {
    def ctx: ctx = this match {
      case has_var(g, _, _, _, _, _) => g
    }
    def avar: avar = this match {
      case has_var(_, p, _, _, _, _) => p
    }
    def dec: dec = this match {
      case has_var(_, _, d, _, _, _) => d
    }
    def ok: Boolean = this match {
      case has_var(g, p, d, bi, ex, bhas) =>
        bi.ok && bi.avar == p && bi.typ == ex.typ && bi.ctx == g &&
        ex.ok && ex.ctx == g && ex.avar == p /* "open" with p */ && ex.bdecs == bhas.bdecs &&
        bhas.ok && bhas.dec == d
    }
  }
  case class has_var(g: ctx, p: avar, d: dec, bi: binds, ex: exp, bhas: bdecs_has) extends has

  // subtyp G T1 T2
  abstract class subtyp {
    def ctx: ctx = this match {
      case subtyp_refl(g, _, _) => g
      case subtyp_top(g, _, _) => g
      case subtyp_bot(g, _, _) => g
      case subtyp_bind(g, _, _, _, _) => g
      case subtyp_sel_l(g, _, _, _, _, _) => g
      case subtyp_sel_r(g, _, _, _, _, _) => g
      case subtyp_trans(g, _, _, _, _) => g
    }
    def typ1: typ = this match {
      case subtyp_refl(_, g, _) => g
      case subtyp_top(_, g, _) => g
      case subtyp_bot(_, g, _) => g
      case subtyp_bind(_, g, _, _, _) => g
      case subtyp_sel_l(_, g, _, _, _, _) => g
      case subtyp_sel_r(_, g, _, _, _, _) => g
      case subtyp_trans(_, g, _, _, _) => g
    }
    def typ2: typ = this match {
      case subtyp_refl(_, _, g) => g
      case subtyp_top(_, _, g) => g
      case subtyp_bot(_, _, g) => g
      case subtyp_bind(_, _, g, _, _) => g
      case subtyp_sel_l(_, _, g, _, _, _) => g
      case subtyp_sel_r(_, _, g, _, _, _) => g
      case subtyp_trans(_, _, g, _, _) => g
    }
    def ok: Boolean = this match {
      case subtyp_refl(g, t1, t2) => t1 == t2
      case subtyp_top(g, t1, t2) => t2 == typ_top
      case subtyp_bot(g, t1, t2) => t1 == typ_bot
      case subtyp_bind(g, t1, t2, z, sds) => t1 match {
        case typ_bind(z1, ds1) => t2 match {
          case typ_bind(z2, ds2) =>
            sds.ok && sds.ctx == ctx_cons(g, z, typ_bind(z, ds1)) &&
            sds.decs1 == ds1.subst(z1, z) && sds.decs2 == ds2.subst(z2, z)
          case _ => false
        }
        case _ => false
      }
      case subtyp_sel_l(g, t1, t2, ha, st1, st2) => t1 match {
        case typ_sel(p1, l1) => ha.dec match {
          case dec_typ(l10, lo1, hi1) =>
            l10 == l1 &&
            ha.ok && ha.ctx == g && ha.avar == p1 &&
            st1.ok && st1.ctx == g && st1.typ1 == lo1 && st1.typ2 == hi1 &&
            st2.ok && st2.ctx == g && st2.typ1 == hi1 && st2.typ2 == t2
          case _ => false
        }
        case _ => false
      }
      case subtyp_sel_r(g, t1, t2, ha, st1, st2) => t2 match {
        case typ_sel(p2, l2) => ha.dec match {
          case dec_typ(l20, lo2, hi2) =>
            l20 == l2 &&
            ha.ok && ha.ctx == g && ha.avar == p2 &&
            st1.ok && st1.ctx == g && st1.typ1 == t1 && st2.typ2 == lo2 &&
            st2.ok && st2.ctx == g && st2.typ1 == lo2 && st2.typ2 == hi2
          case _ => false
        }
        case _ => false
      }
      case subtyp_trans(g, t1, t2, st1, st2) =>
        st1.ok && st1.ctx == g && st1.typ1 == t1 && st1.typ2 == st2.typ1 &&
        st2.ok && st2.ctx == g && st2.typ2 == t2
    }
  }
  case class subtyp_refl(g: ctx, t1: typ, t2: typ) extends subtyp
  case class subtyp_top(g: ctx, t1: typ, t2: typ) extends subtyp
  case class subtyp_bot(g: ctx, t1: typ, t2: typ) extends subtyp
  case class subtyp_bind(g: ctx, t1: typ, t2: typ, z: avar, sds: subdecs) extends subtyp
  case class subtyp_sel_l(g: ctx, t1: typ, t2: typ,
    ha: has, st1: subtyp, st2: subtyp) extends subtyp
  case class subtyp_sel_r(g: ctx, t1: typ, t2: typ,
    ha: has, st1: subtyp, st2: subtyp) extends subtyp
  case class subtyp_trans(g: ctx, t1: typ, t2: typ, st1: subtyp, st2: subtyp) extends subtyp
  
  // subdec G D1 D2
  abstract class subdec {
    def ctx: ctx = this match {
      case subdec_typ(g, d1, d2, stlo, sthi) => g
      case subdec_fld(g, d1, d2, st) => g
      case subdec_mtd(g, d1, d2, starg, stret) => g
    }
    def dec1: dec = this match {
      case subdec_typ(g, d1, d2, stlo, sthi) => d1
      case subdec_fld(g, d1, d2, st) => d1
      case subdec_mtd(g, d1, d2, starg, stret) => d1
    }
    def dec2: dec = this match {
      case subdec_typ(g, d1, d2, stlo, sthi) => d2
      case subdec_fld(g, d1, d2, st) => d2
      case subdec_mtd(g, d1, d2, starg, stret) => d2
    }
    def ok: Boolean = this match {
      case subdec_typ(g, d1, d2, stlo, sthi) => d1 match {
        case dec_typ(l1, lo1, hi1) => d2 match {
          case dec_typ(l2, lo2, hi2) =>
            l1 == l2 &&
            stlo.ok && stlo.ctx == g && stlo.typ1 == lo2 && stlo.typ2 == lo1 &&
            sthi.ok && sthi.ctx == g && sthi.typ1 == hi1 && sthi.typ2 == hi2
          case _ => false
        }
        case _ => false
      }
      case subdec_fld(g, d1, d2, st) => d1 match {
        case dec_fld(l1, t1) => d2 match {
          case dec_fld(l2, t2) =>
            l1 == l2 &&
            st.ok && st.ctx == g && st.typ1 == t1 && st.typ2 == t2
          case _ => false
        }
        case _ => false
      }
      case subdec_mtd(g, d1, d2, stlo, sthi) => d1 match {
        case dec_mtd(l1, lo1, hi1) => d2 match {
          case dec_mtd(l2, lo2, hi2) =>
            l1 == l2 &&
            stlo.ok && stlo.ctx == g && stlo.typ1 == lo2 && stlo.typ2 == lo1 &&
            sthi.ok && sthi.ctx == g && sthi.typ1 == hi1 && sthi.typ2 == hi2
          case _ => false
        }
        case _ => false
      }
    }
  }
  case class subdec_typ(g: ctx, d1: dec, d2: dec, stlo: subtyp, sthi: subtyp) extends subdec
  case class subdec_fld(g: ctx, d1: dec, d2: dec, st: subtyp) extends subdec
  case class subdec_mtd(g: ctx, d1: dec, d2: dec, starg: subtyp, stret: subtyp) extends subdec
  
  // subdecs G Ds1 Ds2
  abstract class subdecs {
    def ctx: ctx = this match {
      case subdecs_nil(g, ds1, ds2) => g
      case subdecs_cons(g, ds1, ds2, ds1has, sd, sds, ds2hasnt) => g
      case subdecs_refl(g, ds1, ds2) => g
    }
    def decs1: decs = this match {
      case subdecs_nil(g, ds1, ds2) => ds1
      case subdecs_cons(g, ds1, ds2, ds1has, sd, sds, ds2hasnt) => ds1
      case subdecs_refl(g, ds1, ds2) => ds1
    }
    def decs2: decs = this match {
      case subdecs_nil(g, ds1, ds2) => ds2
      case subdecs_cons(g, ds1, ds2, ds1has, sd, sds, ds2hasnt) => ds2
      case subdecs_refl(g, ds1, ds2) => ds2
    }
    def ok: Boolean = this match {
      case subdecs_nil(g, ds1, ds2) => ds2 == decs_nil
      case subdecs_cons(g, ds1, ds2, ds1has, sd, sds, ds2hasnt) => ds2 match {
        case decs_nil => false
        case decs_cons(ds2head, ds2tail) =>
          ds1has.ok && ds1has.decs == ds1 && ds1has.dec == sd.dec1 &&
          sd.ok && sd.ctx == g && sd.dec2 == ds2head &&
          sds.ok && sds.ctx == g && sds.decs1 == ds1 && sds.decs2 == ds2tail &&
          ds2hasnt.ok && ds2hasnt.decs == ds2tail && ds2hasnt.label == ds2head.label
      }
      case subdecs_refl(g, ds1, ds2) => ds1 == ds2
    }
  }
  case class subdecs_nil(g: ctx, ds1: decs, ds2: decs) extends subdecs
  case class subdecs_cons(g: ctx, ds1: decs, ds2: decs,
    ds1has: decs_has, sd: subdec, sds: subdecs, ds2hasnt: decs_hasnt) extends subdecs
  case class subdecs_refl(g: ctx, ds1: decs, ds2: decs) extends subdecs

  // subbdecs G Ds1 Ds2
  abstract class subbdecs {
    def ctx: ctx = this match {
      case subbdecs_bot(g, ds1, ds2) => g
      //case subbdecs_refl(g, ds1, ds2) => g 
      case subbdecs_decs(g, ds1, ds2, sds) => g
    }
    def bdecs1: bdecs = this match {
      case subbdecs_bot(g, ds1, ds2) => ds1
      //case subbdecs_refl(g, ds1, ds2) => ds1
      case subbdecs_decs(g, ds1, ds2, sds) => ds1
    }
    def bdecs2: bdecs = this match {
      case subbdecs_bot(g, ds1, ds2) => ds2
      //case subbdecs_refl(g, ds1, ds2) => ds2
      case subbdecs_decs(g, ds1, ds2, sds) => ds2
    }
    def ok: Boolean = this match {
      case subbdecs_bot(g, ds1, ds2) => ds1 == bdecs_bot
      //case subbdecs_refl(g, ds1, ds2) => ds1 == ds2
      case subbdecs_decs(g, ds1, ds2, sds) => ds1 match {
        case bdecs_decs(ds10) => ds2 match {
          case bdecs_decs(ds20) =>
            sds.ok && sds.ctx == g && sds.decs1 == ds10 && sds.decs2 == ds20
          case _ => false
        }
        case _ => false
      }
    }
  }
  case class subbdecs_bot(g: ctx, ds1: bdecs, ds2: bdecs) extends subbdecs
  //case class subbdecs_refl(g: ctx, ds1: bdecs, ds2: bdecs) extends subbdecs
  case class subbdecs_decs(g: ctx, ds1: bdecs, ds2: bdecs, sds: subdecs) extends subbdecs

  def exp_preserves_sub(g: ctx, t1: typ, t2: typ, z: avar, ds1: decs, ds2: decs, 
    st: subtyp, ex1: exp, ex2: exp): subdecs = {
    require(st.ok && st.ctx == g && st.typ1 == t1 && st.typ2 == t2 &&
      ex1.ok && ex1.ctx == g && ex1.typ == t1 && ex1.avar == z && ex1.bdecs == bdecs_decs(ds1) &&
      ex2.ok && ex2.ctx == g && ex2.typ == t2 && ex2.avar == z && ex2.bdecs == bdecs_decs(ds2))
    
    val g2 = ctx_cons(g, z, typ_bind(z, ds1))
    st match {
      case subtyp_refl(_, _, _) => subdecs_refl(g2, ds1, ds2)
      
      case subtyp_top(_, _, _) => subdecs_nil(g2, ds1, decs_nil)

      // case subtyp_bot(g, t1, t2) => not possible because t1==typ_bot -> exp1.bdecs==bdecs_bot
      
      case subtyp_bind(_, _, _, z0, sds) => sds // TODO subst z0 by z

      case subtyp_sel_l(g, t1, t2, ha, st1, st2) => subdecs_nil(g2, ds1, decs_nil)//TODO
      case subtyp_sel_r(g, t1, t2, ha, st1, st2) => subdecs_nil(g2, ds1, decs_nil)//TODO
      case subtyp_trans(g, t1, t2, st1, st2) => subdecs_nil(g2, ds1, decs_nil)//TODO
    }
  } ensuring { sds =>
    sds.ok && sds.ctx == ctx_cons(g, z, typ_bind(z, ds1)) && sds.decs1 == ds1 && sds.decs2 == ds2
  }
  
  /*
  This is the narrowing lemma for "subdecs" judgments. It says
  
  G, z: {z=>DsA} |- DsA <: DsB    (hypothesis named sdsAB)
  G, z: {z=>DsB} |- Ds1 <: Ds2    (hypothesis named sds12)
  ----------------------------
  G, z: {z=>DsA} |- Ds1 <: Ds2    (conclusion named sds)

  Instead of implementing a proof, we just return the hypothesis sds12.
  This is clearly wrong, and it would be easy to give a counterexample, because
  sds12.ctx ends on dsB, but the result sds must have sds.ctx ending on dsA, so it
  would be sufficient to build pick any dsA != dsB to get a counterexample.
  
  But when considering this VC, leon doesn't return any answer for more than a minute
  --> abort the leon experiment, disappointed :-(
  */
  def narrow_subdecs_end(g: ctx, z: avar, dsA: decs, dsB: decs, ds1: decs, ds2: decs,
    sdsAB: subdecs, sds12: subdecs): subdecs = {
    require(sdsAB.ok && sdsAB.ctx == ctx_cons(g, z, typ_bind(z, dsA)) &&
            sdsAB.decs1 == dsA && sdsAB.decs2 == dsB &&
            sds12.ok && sds12.ctx == ctx_cons(g, z, typ_bind(z, dsB)) &&
            sds12.decs1 == ds1 && sds12.decs2 == ds2)
    
    sds12
  } ensuring {sds => sds.ok && sds.ctx == ctx_cons(g, z, typ_bind(z, dsA)) &&
                     sds.decs1 == ds1 && sds.decs2 == ds2}

}



