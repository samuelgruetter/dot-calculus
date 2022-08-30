Dependent Object Types (DOT)
----------------------------

The DOT calculus proposes a new foundation for Scala's type system.

DOT has been presented at the FOOL 2012 workshop
([PDF](http://lampwww.epfl.ch/~amin/dot/fool.pdf)).

We now have several mechanized type safety proofs.
This repo implements [the wadlerfest model](https://github.com/samuelgruetter/dot-calculus.git)
in Coq, based on previous work in the
[namin/dot](https://github.com/namin/dot) and
[TiarkRompf/minidot](https://github.com/TiarkRompf/minidot) repos.

## Installation

Works in Coq 8.4.6 and OCaml 4.02.3.

- `opam switch create with-wadlerfest-dot 4.02.3`
- `eval $(opam env)`
- `opam pin add coq 8.4.6`

Then, run `make` from the `ln` directory.

