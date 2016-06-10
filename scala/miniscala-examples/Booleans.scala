// requires inheritance, but nothing more, no primitives like Ints or Strings
object Booleans { def main(args: Array[String]): Unit = println({

  class U // Unit
  val unit = new U

  class Booleans { bs =>
    abstract class BoolFun {
      def call(n: bs.Bool): bs.Bool
    }

    abstract class Bool { self =>
      def destruct(ifTrue: bs.Bool): bs.BoolFun

      def not(dummy: U): bs.Bool = self.destruct(new bs.False).call(new bs.True)
      def and(other: bs.Bool): bs.Bool = self.destruct(other).call(new bs.False)
      def or(other: Bool): bs.Bool = self.destruct(new bs.True).call(other)
    }

    class True extends Bool {
      def destruct(ifTrue: bs.Bool): bs.BoolFun = {
        class f extends BoolFun {
          def call(ifFalse: bs.Bool): bs.Bool = ifTrue
        }
        new f
      }
    }

    class False extends Bool {
      def destruct(ifTrue: bs.Bool): bs.BoolFun = {
        class f extends BoolFun {
          def call(ifFalse: bs.Bool): bs.Bool = ifFalse
        }
        new f
      }
    }
  }

  val booleans: Booleans = new Booleans
  val tru: booleans.True = new booleans.True
  val fls: booleans.False = new booleans.False

  val a: booleans.Bool = tru
  val b: booleans.Bool = fls

  a.and(b.not(unit)).or(a.not(unit).and(b)) // a xor b

})}