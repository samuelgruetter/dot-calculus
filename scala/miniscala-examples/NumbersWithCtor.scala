object NumbersWithCtor { def main(args: Array[String]): Unit = println({

  // abstract members, constructor args
  
  val unit = new AnyRef

  class Nats(dummy: AnyRef) extends AnyRef { nats =>

    abstract class Nat(dummy: AnyRef) extends AnyRef { n =>
      def plus(other: nats.Nat): nats.Nat
      def succ(dummy: AnyRef): nats.Succ = new nats.Succ(n)
      // def toInt: Int
    }

    class Zero(dummy: AnyRef) extends Nat(unit) { z =>
      def plus(other: nats.Nat): nats.Nat = other
      // def toInt = 0
    }

    // non-trivial constructor argument
    class Succ(pr: nats.Nat) extends nats.Nat(unit) { n =>
      def pred(dummy: AnyRef): nats.Nat = pr
      def plus(other: nats.Nat): nats.Nat = pr.plus(other).succ(unit)

      // Note: It is known that n (the self) has a member named "succ", even
      // though "succ" is never mentioned/repeated in the body of Succ, it's
      // only in the body of Nat
      def id(dummy: AnyRef): nats.Nat = n.succ(unit).pred(unit)

      // def toInt = 1 + pr.toInt
    }

  }

  val nats: Nats = new Nats(unit)

  val zero: nats.Nat = new nats.Zero(unit)
  val one: nats.Nat = new nats.Succ(zero)
  val two: nats.Nat = new nats.Succ(one)
  val three: nats.Nat = new nats.Succ(two)

  two.plus(three)

})}
