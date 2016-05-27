object MutRec {

  def main(args: Array[String]): Unit = println({

    // begin of actual program

    class Lib1 { z =>
      class U // Unit

      class Author {
        def book(u: z.U): z.Book = new z.Book
      }

      class Book {
        def author(u: z.U): z.Author = new z.Author
      }

      def run(u: z.U): z.Book = {
        val a: z.Author = (new z.Book).author(new z.U)
        a.book(new z.U)
      }
    }
    val lib1: Lib1 = new Lib1
    lib1.run(new lib1.U)

    // end of actual program
  })
}

/*
Translation into DOT:

let Lib1 = new { Lib1 =>
  type T_Lib1 = { z =>
    { type T_U = { y => Top } } /\
    { type T_Author = { y => def book(u: z.U): z.T_Book } } /\
    { type T_Book = { y => def author(u: z.U): z.T_Author } } /\
    { def run(u: z.U): z.Book }
  }
  def new_Lib1(dummy: Top): Lib1.T_Lib1 = new { z =>
    type T_U = { y => Top }
    def new_U(dummy: Top): z.T_U = new {}
    type T_Author = { y => def book(u: z.T_U): z.T_Book }
    def new_Author(dummy: Top): z.T_Author = new {
      def book(u: z.T_U): z.T_Book = z.new_Book(new {})
    }
    type T_Book = { y => def author(u: z.T_U): z.T_Author }
    def new_Book(dummy: Top): z.T_Book = new {
      def author(u: z.T_U): z.T_Author = z.new_Author(new {})
    }
    def run(u: z.T_U): z.T_Book = {
      let a = (z.new_Book(new {})).author(z.new_U(new {})) in a.book(z.new_U(new {}))
    }
  }
} in
let lib1 = Lib1.new_Lib1(new {}) in
lib1.run(lib1.new_U(new {}))




Old translation into DOT which loops infinitely:

// definition of class inside expr is replaced by only a wrapper object containing the signature, but no implementation
// Note that Lib1.L0 is never used in this example, but it's generated anyways
let Lib1 = new {
  L0: { z =>
    { type U = { y => Top } } /\
    { type Author = { y => def book(u: z.U): z.Book } } /\
    { type Book = { y => def author(u: z.U): z.Author } } /\
    { def run(u: z.U): z.Book }
  }
} in
// the implementation is repeated every time a new instance is created
let lib1 = new { z =>
  type U = { y => Top }
  type Author = { y => def book(u: z.U): z.Book }
  type Book = { y => def author(u: z.U): z.Author }
  def run(u: z.U): z.Book = {
    let a = (new {
      def author(u: z.U): z.Author = new {
        def book(u: z.U): z.Book = OH NO, expanding the constructors at each usage results in infinite loops!!!!
      }
    }).author(new {}) in a.book(new {})
  }
} in
lib1.run(new {})

 */