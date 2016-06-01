object NumbersNoCtor { def main(args: Array[String]): Unit = println({

  // inheritance, abstract def members

  val unit = new AnyRef
  
  class Nats { nats =>

    abstract class Nat extends AnyRef { n =>
      def succ(d: AnyRef): nats.Nat = {
        class S extends nats.Succ {
          def pred(d: AnyRef): nats.Nat = n
        }
        new S
      }
      def plus(other: nats.Nat): nats.Nat
      def times(other: nats.Nat): nats.Nat

      //def toInt: Int
    }

    class Zero extends Nat { z =>
      def plus(other: nats.Nat): nats.Nat = other
      def times(other: nats.Nat): nats.Nat = z

      //def toInt = 0
    }

    abstract class Succ extends nats.Nat { n =>
      def pred(d: AnyRef): nats.Nat
      def plus(other: nats.Nat): nats.Nat = n.pred(unit).plus(other).succ(unit)
      def times(other: nats.Nat): nats.Nat = pred(unit).times(other).plus(other)
      
      //def toInt = 1 + pred(unit).toInt
    }

  }

  val nats = new Nats

  val zero = new nats.Zero
  val one = zero.succ(unit)
  val two = one.succ(unit)
  val three = two.succ(unit)

  two.times(three.times(two)) //.toInt

})}
