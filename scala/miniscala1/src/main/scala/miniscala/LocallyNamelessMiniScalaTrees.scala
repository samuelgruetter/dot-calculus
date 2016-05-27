package miniscala

import scala.collection.immutable.Seq

/*
  p ::= x | x.l
  t ::= x | t.l | t t | new p | { ss; t }
  s ::= d
  d ::= val l: T = t | def m(x: S): T = t | class l { z => ds }
  T ::= p | (x:S)T | class { z => Ts }
  */
object LocallyNamelessMiniScalaTrees {

  // the original names of all vars and labels are kept just for comments in pretty printing

  sealed trait Vr
  case class VrFree(i: Int, origName: String) extends Vr // absolute position in context, invariant under context extension
  case class VrBound(i: Int, origName: String) extends Vr // de Bruijn index

  sealed trait Pth
  case class PthVar(name: Vr) extends Pth
  case class PthSel(prefix: Vr/*not (yet) Pth!*/, sel: Int, origSel: String) extends Pth

  sealed trait Trm
  case class Var(name: Vr) extends Trm
  case class App(receiver: Trm, label: Int, arg: Trm, origSel: String) extends Trm
  case class New(cls: Pth) extends Trm
  case class Block(stat: Stat, ret: Trm) extends Trm

  type Stat = Def

  sealed trait Def // names are given by position (if inside class) or by locally nameless (if inside expr)
  case class DefVal(typ: Typ, rhs: Trm, origLabel: String) extends Def
  case class DefDef(argTyp: Typ, retTyp: Typ, body: Trm, origLabel: String, origArgName: String) extends Def
  case class DefClass(defs: Seq[Def], origLabel: String, origSelfName: String) extends Def
  case object DefNone extends Def // to skip indices

  sealed trait Typ
  case class TypCls(ref: Pth) extends Typ
  case class TypMtd(argTyp: Typ, retTyp: Typ, origArgName: String) extends Typ
  case class TypOfCls(members: Seq[Def], origSelfName: String) extends Typ
}
