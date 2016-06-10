object Numbers { def main(args: Array[String]): Unit = println({

  // inheritance, abstract members, constructor args

  class Nats(dummy: AnyRef) extends AnyRef { nats =>

    // Nat => Nat
    abstract class NatToNatFun(dummy: AnyRef) extends AnyRef {
      def call(n: nats.Nat): nats.Nat
    }

    // (Nat => Nat) => Nat
    abstract class NatToNatFunToNatFun(dummy: AnyRef) extends AnyRef {
      def call(f: NatToNatFun): nats.Nat
    }

    abstract class Nat(dummy: AnyRef) extends AnyRef {
      def add(other: nats.Nat): nats.Nat
      def destruct(ifZero: nats.Nat): nats.NatToNatFunToNatFun // OO-currying

      def toInt: Int
    }

    class Zero(dummy: AnyRef) extends Nat(dummy) {
      def add(other: nats.Nat): nats.Nat = other
      def destruct(ifZero: nats.Nat): nats.NatToNatFunToNatFun = {
        class f extends nats.NatToNatFunToNatFun(dummy) {
          def call(funIfSucc: nats.NatToNatFun): nats.Nat = ifZero
        }
        new f
      }

      def toInt = 0
    }

    class Succ(pr: nats.Nat) extends nats.Nat(new AnyRef) { // non-trivial constructor argument
      def add(other: nats.Nat): nats.Nat = new Succ(pr.add(other))
      def pred(dummy: AnyRef): nats.Nat = pr
      def destruct(ifZero: nats.Nat): nats.NatToNatFunToNatFun = {
        class f extends nats.NatToNatFunToNatFun(dummy) {
          def call(funIfSucc: nats.NatToNatFun): nats.Nat = funIfSucc.call(pr)
        }
        new f
      }

      def toInt = 1 + pr.toInt
    }
  }


})}
