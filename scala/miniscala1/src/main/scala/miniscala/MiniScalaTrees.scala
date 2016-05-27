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

  sealed trait Pth
  case class PthVar(name: String) extends Pth
  case class PthSel(prefix: String /*not (yet) Pth!*/, sel: String) extends Pth

  sealed trait Trm
  case class Var(name: String) extends Trm
  case class App(receiver: Trm, label: String, arg: Trm) extends Trm
  case class New(cls: Pth) extends Trm
  case class Block(stat: Stat, ret: Trm) extends Trm
  object Block {
    def apply(stats: Seq[Stat], ret: Trm): Trm = stats.foldRight(ret)((stat, oldRet) => Block(stat, oldRet))
  }

  type Stat = Def

  sealed trait Def {
    def name: String
  }
  case class DefVal(name: String, typ: Typ, rhs: Trm) extends Def
  case class DefDef(name: String, argName: String, argTyp: Typ, retTyp: Typ, body: Trm) extends Def
  case class DefClass(name: String, selfName: String, defs: Seq[Def]) extends Def

  sealed trait Typ
  case class TypCls(ref: Pth) extends Typ
  case class TypMtd(argName: String, argTyp: Typ, retTyp: Typ) extends Typ
  case class TypOfCls(selfName: String, members: Seq[Def]) extends Typ
}
