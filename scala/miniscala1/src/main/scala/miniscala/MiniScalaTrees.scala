package miniscala

import scala.collection.immutable.Seq

/*
  p ::= x | x.l
  t ::= x | t.l | t t | new p | { ss; t }
  s ::= d
  d ::= val l: T = t | def m(x: S): T = t | class l { z => ds }
  T ::= p | (x:S)T | class { z => Ts }
  */
object MiniScalaTrees {

  sealed trait Pth extends Trm
  case class PthVar(name: String) extends Pth
  case class PthSel(prefix: String /*not (yet) Pth!*/, sel: String) extends Pth

  sealed trait Trm
  case class Var(name: String) extends Trm
  case class Sel(qual: Trm, sel: String) extends Trm
  case class App(func: Trm, arg: Trm) extends Trm
  case class New(cls: Pth) extends Trm
  case class Block(stats: Seq[Stat], ret: Trm) extends Trm

  type Stat = Def

  sealed trait Def
  case class DefVal(name: String, typ: Typ, rhs: Trm) extends Def
  case class DefDef(name: String, argName: String, argTyp: Typ, retTyp: Typ, body: Trm) extends Def
  case class DefClass(name: String, selfName: String, defs: Seq[Def]) extends Def

  sealed trait Typ
  case class TypCls(ref: Pth) extends Typ
  case class TypMtd(argName: String, argTyp: Typ, retTyp: Typ) extends Typ
  case class TypOfCls(selfName: String, members: Seq[(String, Typ)]) extends Typ

  case class Prog(mainObjName: String, mainObjMembers: Seq[Def], mainExpr: Trm)
}
