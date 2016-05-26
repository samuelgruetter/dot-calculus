object Numbers { def main(args: Array[String]): Unit = println({

  class U // Unit
  val unit = new U

  class Nats { nats =>

    abstract class UFun {
      def call(d: U): nats.Nat
    }
    abstract class NatFun {
      def call(n: nats.Nat): nats.Nat
    }

    abstract class Nat {
      def destruct(zeroFun: nats.UFun, succFun: nats.NatFun): nats.Nat // two args list!
    }
    class Zero extends Nat {
      def destruct(zeroFun: nats.UFun, succFun: nats.NatFun): nats.Nat = {
        zeroFun.call(unit)
      }
    }
    class Succ(pr: nats.Nat) extends nats.Nat { // constructor args!
      def pred(d: U): nats.Nat = pr
      def destruct(zeroFun: nats.UFun, succFun: nats.NatFun): nats.Nat = {
        succFun.call(pred(unit))
      }
    }
  }

})}