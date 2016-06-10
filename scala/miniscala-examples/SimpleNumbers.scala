object SimpleNumbers { def main(args: Array[String]): Unit = println({

  // abstract members, constructor args

  class Nats(dummy: AnyRef) extends AnyRef { nats =>

    abstract class Nat(dummy: AnyRef) extends AnyRef {
      def plus(other: nats.Nat): nats.Nat
      def times(other: nats.Nat): nats.Nat
      // def toInt: Int
    }

    class Zero(dummy: AnyRef) extends Nat(dummy) { z =>
      def plus(other: nats.Nat): nats.Nat = other
      def times(other: nats.Nat): nats.Nat = z
      // def toInt = 0
    }

    class Succ(pr: nats.Nat) extends nats.Nat(new AnyRef) { // non-trivial constructor argument
      def plus(other: nats.Nat): nats.Nat = new Succ(pr.plus(other))
      def times(other: nats.Nat): nats.Nat = pr.times(other).plus(other)
      // def toInt = 1 + pr.toInt
    }

    abstract class NatPair(dummy: AnyRef) extends AnyRef { p0 =>
      def getFirst(dummy: AnyRef): nats.Nat
      def getSecond(dummy: AnyRef): nats.Nat
      def setFirst(fst: nats.Nat): nats.NatPair = {
        class P(dummy: AnyRef) extends nats.NatPair(dummy) {
          def getFirst(dummy: AnyRef): nats.Nat = fst
          def getSecond(dummy: AnyRef): nats.Nat = p0.getSecond(dummy)
        }
        new P(dummy)
      }
      def setSecond(snd: nats.Nat): nats.NatPair = {
        class P(dummy: AnyRef) extends nats.NatPair(dummy) {
          def getFirst(dummy: AnyRef): nats.Nat = p0.getFirst(dummy)
          def getSecond(dummy: AnyRef): nats.Nat = snd
        }
        new P(dummy)
      }
    }
    class NatTwins(value: nats.Nat) extends NatPair(new AnyRef) {
      def getFirst(dummy: AnyRef): nats.Nat = value
      def getSecond(dummy: AnyRef): nats.Nat = value
    }

    def addition(a: nats.NatPair): nats.Nat = a.getFirst(new AnyRef).plus(a.getSecond(new AnyRef))
  }

  val nats: Nats = new Nats(new AnyRef)

  val zero = new nats.Zero(new AnyRef)
  val one = new nats.Succ(zero)
  val two = new nats.Succ(one)
  val three = new nats.Succ(two)

  nats.addition(new nats.NatTwins(two.times(three)).setSecond(two.times(two))) //.toInt

})}
