# The DOT Calculus with Recursive Types

A minimally complete version of dependent object types. The calculus comprises functions,
labeled types and terms combined through intersections, recursive bindings, and nothing else.

## Abstract Syntax

    Term member     a, b, c
    Type member     A, B, C
    Variable        x, y, z

    Type     S, T, U = {a: T}                       field declaration
                       {A: S..T}                    type declaration
                       S & T                        intersection
                       x.A                          projection
                       rec(x: T)                    recursive dependent type
                       all(x: S)T                   dependent function
                       Top                          top type
                       Bot                          bottom type

    Value          v = new(x: T)d                   object
                       lambda(x: T)t                lambda

    Term     s, t, u = x                            variable
                       v                            value
                       x.a                          selection
                       x y                          application
                       let x = t in u               let

    Definition     d = {a = t}                      field definition
                       {A = T}                      type definition
                       d & d'                       aggregate definition

    Store          s = ... x = v ...
    Environment    G = ... x: T ...

***

### Evaluation: `s | t -> s' | t'`

    (Project)
                             s | x.a  -->  s | t          if s(x) = new(x: T)(d, a = t)
    (Apply)
                             s | x y  -->  s | [z:=y]t    if s(x) = lambda(z: T)t
    (Let-Var)
                  s | let x = y in t  -->  s | [x:=y]t
    (Let-Value)
                  s | let x = v in t  -->  s, x = v | t
    (Ctx)
                               s | t  -->  s' | t'
                      ------------------------------------
                      let x = t in u  -->  let x = t' in u

***

## Typing Rules

### Type Assignment `G |- t: T`

    (Var)
                            G, x: T, G' |- x: T
    (All-I)
                       G, x: T |- t: U    (x not in fv(T))
                       -----------------------------------
                          G |- lambda(x: T)t: all(x: T)U
    (All-E)
                       G |- x: all(z: S)T    G |- y: S
                       -------------------------------
                              G |- x y: [z:=y]T
    ({}-I)
                               G, x: T |- d: T
                          --------------------------
                          G |- new(x: T)d: rec(x: T)
    ({}-E)
                                G |- x: {a: T}
                                --------------
                                 G |- x.a: T
    (Let)
                G |- t: T   G, x: T |- u: U   (x not in fv(U))
                ----------------------------------------------
                            G |- let x = t in u: U
    (Rec-I)
                                  G |- x: T
                              -----------------
                              G |- x: rec(x: T)
    (Rec-E)
                              G |- x: rec(x: T)
                              -----------------
                                  G |- x: T
    (&-I)
                            G |- x: T   G |- x: U
                            ---------------------
                                G |- x: T & U
    (Sub)
                           G |- t: T   G |- T <: U
                           -----------------------
                                  G |- t: U

***

### Definition Type Assignment `G |- d: T`

    (Fld-I)
                                  G |- t: T
                             --------------------
                             G |- {a = t}: {a: T}
    (Typ-I)
                           G |- {A = T}: {A: T..T}
    (AndDef-I)
           G |- d1: T1   G |- d2: T2   (dom(d1), dom(d2) disjoint)
           -------------------------------------------------------
                            G |- d1 & d2: T1 & T2


***

### Subtyping: `G |- T <: U`

    (<:-Top)
                                G |- T <: Top
    (Bot-<:)
                                G |- Bot <: T
    (Refl-<:)
                                G |- T <: T
    (Trans-<:)
                          G |- S <: T   G |- T <: U
                          -------------------------
                                 G |- S <: U
    (And-<:)
                               G |- T & U <: T

                               G |- T & U <: U
    (<:-And)
                          G |- S <: T   G |- S <: U
                          -------------------------
                                  S <: T & U
    (Fld-<:-Fld)
                                 G |- T <: U
                            ---------------------
                            G |- {a: T} <: {a: U}
    (Typ-<:-Typ)
                        G |- S2 <: S1   G |- T1 <: T2
                       -------------------------------
                       G |- {A: S1..T1} <: {A: S2..T2}
    (<:-Sel)
                              G |- x: {A: S..T}
                              -----------------
                                G |- S <: x.A
    (Sel-<:)
                              G |- x: {A: S..T}
                              -----------------
                               G |- x.A <: T
    (All-<:-All)
                     G |- S2 <: S1   G, x: S2 |- T1 <: T2
                     ------------------------------------
                      G |- all(x: S1)T1 <: all(x: S2)T2


*Note:* `G, x: T` is well-defined only if `x` is neither in the domain of `G` nor in
its free variables.

***

## Abbreviations

Group multiple intersected definitions or declarations in one pair of braces, replacing `&` with `;`. E.g.

             { A = T; a = t }  ===  { A = T } & { a = t }
            { A: S..T; a: T }  ===  { A: S..T } & { a: T }

Allow terms in applications and selections, using the expansions

                          t u  ===  let x = t in x u
                          x u  ===  let y = u in x y
                          t.a  ===  let x = t in x.a

Expand type ascriptions to applications:

                         t: T  ===  (lambda(x: T)x)t

Shorthand syntax for object types and values:

         { z => D1; ...; Dn }  ===  rec(z: D1 & ... & Dn)
     new { z => d1; ...; dn }  ===  new(x: D1 & ... & Dn)d1 & ... & dn
                                    where Di derived from di. (di needs to have full type info)

One can leave out the `z =>` if `z` does not appear in the rest of the term.

Shorthand syntax for self bounds: In type of `x`, expand

                      A <: T   ===  A: Bot .. T
                      A >: S   ===  A: S .. Top
                       A = T   ===  A: T .. T
                           A   ===  A: Bot .. Top

## Examples

    let scala_units =
      let scala_units_impl =
        new (su:
              { Unit: all(x: su.Unit)su.Unit..all(x: su.Unit)su.Unit } &
              { unit: su.Unit }
            ) { Unit = all(x: su.Unit)su.Unit } &
              { unit = lambda(x: su.Unit)x }
      in let scala_units_api_wrapper =
        lambda(x:
          { a: rec(su:
                    { Unit: su.Unit..su.Unit } &
                    { unit: su.Unit }
                  )
          }
        )x
      in scala_units_api_wrapper scala_units_impl

Or, using some of the shorthands:

    let scala_units =
      new (su: {
        Unit: all(x: su.Unit)su.Unit .. all(x: su.Unit)su.Unit
        unit: su.Unit
      }) {
        Unit = all(x: su.Unit)su.Unit
        unit = lambda(x: su.Unit)x
      }: { su =>
        Unit: su.Unit .. su.Unit
        unit: su.Unit
      }

Or, even shorter:

    let scala_units =
      new { su =>
        Unit = all(x: su.Unit)su.Unit
        unit: su.Unit = lambda(x: su.Unit)x
      }: { su =>
        Unit
        unit: su.Unit
      }

Encoding a generic list type:

    let scala_collections_immutable =
      new { sci =>
        List = { thisList => A; head: thisList.A; tail: sci.List & { A = thisList.A } }
        nil: all(x: {A})sci.List & {A = x.A} =
          lambda(x: {A})
            let thisList = new { thisList => A = x.A; head = thisList.head; tail = thisList.tail }
            in thisList
        cons: all(x: {A})all(hd: x.A)all(tl: sci.List & {A = x.A})sci.List & {A = x.A} =
          lambda(x: {A})lambda(hd: x.A)lambda(tl: sci.List & {A = x.A})
             let thisList = new { thisList => A = x.A; head = hd; tail = tl }
             in thisList
      }: { sci =>
        List <: { thisList => A; head: thisList.A; tail: sci.List & { A = thisList.A } }
        nil: all(x: {A})sci.List & {A = x.A}
        cons: all(x: {A})all(hd: x.A)all(tl: sci.List & {A = x.A})sci.List & {A = x.A}
      }

Here's a detailed argument why the body of the `cons` method has the required type
`sci.List & { A = x.A }`:

(1) We have:

       thisList: rec(thisList: { A = x.A, hd: x.A, tl: sci.List & {A = x.A}})

            by (Rec-E)

       thisList: { A = x.A, hd: x.A, tl: sci.List & {A = x.A}}

             by (Sub), since thisList.A <: x.A

       thisList: { A = x.A, hd: thisList.A, tl: sci.List & {A = thisList.A}}

             by (Sub), since {A: x.A..x.A} <: {A: Bot..Top}

       thisList: { A, hd: thisList.A, tl: sci.List & { A = thisList.A}}

             by (Rec-I)

       thisList: rec(thisList: { A, hd: thisList.A, tl: sci.List & { A = thisList.A}})

             by (Sub), since
             rec(thisList: { A, hd: thisList.A, tl: sci.List & { A = thisList.A}})
               <: sci.List

       thisList: sci.List

(2) We also have:

     thisList: { A = x.A, hd: x.A, tl: sci.List & {A = x.A}}

        by (Sub)

     thisList: {A = x.A}

(1) and (2) together give with (&-I)

     thisList: sci.List & { A = x.A }


Generally, we can encode:

  - abstract types
  - dependent function types
  - type parameters
  - covariant parameterized types
  - algebraic data types
  - modules
  - functors
  - objects
  - classes

## Meta Theory

### Definition (Precise typing)

`G |-! t: T` if `G |- t: T` and the following two conditions hold:

 1. If `t` is a value, the typing derivation of `t` ends in (All-I) or ({}-I).
 2. If `t` is a variable, the typing derivation of `t` consists only of (Var), (Rec-E)
    and (Sub) steps and every (Sub) step makes use of only the subtyping rules (And-<:)
    and (Trans).

### Definition (Environment/store correspondence)

An environment `G` corresponds to a store `s`, written `G ~ s`, if `G ~ s` can be derived
using the rules below.

                              (empty) ~ (empty)

                              G ~ s   G |-! v: T
                              ------------------
                              G, x: T ~ s, x = v

### Definition (Underlying value)
Given a store `s` and a variable `x` bound in `s`,
the underlying value `s(x)` is the value `v` such that `x = v in s`.

### Lemma (Weakening)
Let `G = G', x: S`. Then

 - If `G' |- t: T` then `G |- t: T`
 - If `G' |-! v: T` then `G |-! v: T`.
 - If `G' |- T <: U` then `G |- T <: U`.
 - If `G' ~ s` then `G ~ s`.

*Proof*: All derivations remain valid in an environment with extra information.

### Definition (Environment subsumption)

Environment `G` subsumes `G'`, written `G <: G'`, if
for all `x: T` in `G'` we have `G |- x: T`.


### Lemma (Narrowing)

If `G <: G'` then:

 - If `G' |- t: T` then also `G |- t: T`
 - If `G' |- d: T` then also `G |- d: T`
 - If `G' |- S <: T` then also `G' |- S <: T`

*Proof*: A straightforward induction on typing, subtyping and well-formedness derivations.


### Definition (Environment Renaming)

    [x:=y]G = [[x:=y]z: [x:=y]T | z: T in G]

### Lemma (Renaming)
Let [s] be a renaming `[x0:=y0]` for arbitrary variables `x0`, `y0`. Then

 - `     [s]rec(x: T)  =  rec([s]x: [s]T)`
 - `    [s]all(x: T)U  =  all([s]x: [s]T): [s]U`
 - `    [s]new(x: T)d  =  new([s]x: [s]T): [s]d`
 - ` [s]lambda(x: T)t  =  lambda([s]x: [s]T): [s]t`
 - `[s]let x = t in u  =  let [s]x = [s]t in [s]u`

*Proof*. We prove the first equation; the others are analogous. We distinguish whether or not `x0 = x`.

If `x0 = x` then

      [s]rec(x0: T)
    = (by definition of substitution)
      rec(x0: T)
    = (by alpha renaming x0 to y0)
      rec(y0: [y0:=x0]T)
    = (by rewriting)
      rec([s]x0: [s]T)

If `x0 != x` then

      [s]rec(x: T)
    = (by definition of substitution)
      rec(x: [s]T)
    = (since x0 != x)
      rec([s]x0: [s]T)

### Lemma (Subst)
 1. If `G, x: S |- t: T` and `G |- y: [x:=y]S`
then `G |- [x:=y]t: [x:=y]T`.
 2. If `G, x: S |- d: T` and `G |- y: [x:=y]S`
then `G |- [x:=y]d: [x:=y]T`.

We prove the more general proposition:

If `G, x: S, G' |- t: T` and `G, [x:=y]G' |- y: [x:=y]S`, then
`G, [x:=y]G' |- [x:=y]t: [x:=y]T`. (and the same for `d` instead of `t`).

Proof by mutual induction on derivations.
Let `[s] = [x0:=y0]`.
Assume `G, x0: S0, G' |- t0: T0` and `G, [s]G' |- y0: [s]S0`.
To show: `G, [s]G' |- [s]t0: [s]T0`.

We distinguish according to the last rule in the derivation of `G, x0: S0, G' |- t0: T0`

**Case (Var)**: We have in this case: `t = x0`, `T0 = S0`,
`G, x0: S0, G' |- x: S0`, and `G, [s]G' |- y0: [s]S0`.
Together, `G, x0: S0, G' |- [s]x0: [s]S0`.

**Case (All-I)** Then `t0 = lambda(x: T)t` and the last rule is

                     G, x0: S0, G', x: T |- t: U
              ------------------------------------------
              G, x0: S0, G' |- lambda(x: T)t: all(x: T)U

By the I.H., `G, [s]G', [s]x: [s]T |- [s]t: [s]U`.
By (All-I), `G, [s]G' |- lambda([s]x: [s]T)[s]t): all([s]x: [s]T)[s]U`.
By applying Lemma (Renaming) twice to the RHS, `G, [s]G' |- [s]lambda(x: T)t): [s]all(x: T)U`.

**Case (All-E)** Then `t0 = x y` and the last rule is

       G, x0: S0, G' |- x: all(y: S)T    G, x0: S0, G' |- y: S
       -------------------------------------------------------
                    G, x0: S0, G' |- x y: [z:=y]T

By the. I.H., `G, [s]G' |- [s]x: all(z: [s]S)[s]T` and `G, [s]G' |- [s]y: [s]S`.
By (All-E), `G, [s]G' |- [s]x [s]y: [z:=[s]y][s]T`.
W.l.o.g choose `z` so that `z != x0`, `z != y`.
Hence, `[z:=[s]z][s]` = [s][z:=y]. Together,
`G,[s]G' |- [s](x y): [s][z:=y]T`.

**Case ({}-I)**: Then `t0 = new(x: T)d` and the last rule is

                     G, x0: S0, G', x: T |- d: T
                --------------------------------------
                G, x0: S0, G' |- new(x: T)d: rec(x: T)

By the I.H., `G, [s]G', [s]x: [s]T |- [s]d: [s]T`.
By ({}-I), `G, [s]G' |- new([s]x: [s]T)[s]d: rec([s]x: [s]T)`
By applying Lemma (Renaming) twice to the RHS,
`G, [s]G' |- [s]new(x: T)d: [s]rec(x: T)`.

**Case ({}-E)** Then `t0 = x.a` and the last rule is:

                     G, x0: S0, G' |- x: {a: T}
                     ---------------------------
                       G, x0: S0, G' |- x.a: T

By the I.H., `G, [s]G' |- [s]x: {a: [s]T}`.
By ({}-E), `G, [s]G' |- [s]x.a: [s]T`.

**Case (Let)**: Then `t0 = let x = t in u` and the last rule is:

    G, x0: S0, G' |- t: T   G, x0: S0, G', x: T |- u: U   (x not in fv(U))
    ----------------------------------------------------------------------
                      G, x0: S0, G' |- let x = t in u: U

By the I.H., `G, [s]G' |- [s]t: [s]T` and `G, [s]G', [s]x: [s]T |- [s]u: [s]U`.
With (Let) it follows that `G, [s]G' |- let [s]x = [s]t in [s]u: [s]U`.
By (Renaming), `G, [s]G' |- [s]let x = t in u: [s]U`.

**Case (Rec-I)**: Then `t0 = x` and the last rule is:

                              G |- x: T
                          -----------------
                          G |- x: rec(x: T)

By the I.H., `G, [s]G' |- [s]x: [s]T`.
By (Rec-I), `G, [s]G' |- [s]x: rec([s]x: [s]T)`.
By applying Lemma (Renaming) to the `rec` term, `G, [s]G' |- [s]x: [s]rec(x: T)`.

**Case (Rec-E)**: Then `t0 = x` and the last rule is:

                    G, x0: S0, G' |- x: rec(x: T)
                    -----------------------------
                        G, x0: S0, G' |- x: T

By the I.H., `G, [s]G' |- [s]x: [s]rec(x: T)`.
By applying Lemma (Renaming) to the `rec` term, `G, [s]G' |- [s]x: rec([s]x: [s]T)`.
By (Rec-E), `G, [s]G' |- [s]x: [s]T`.

**Case (&=I)**. Then `t0 = x` amd the last rule is:

                        G |- x: T   G |- x: U
                        ---------------------
                            G |- x: T & U

By the I.H., `G, [s]G' |- [s]x: [s]T` and `G, [s]G' |- [s]x: [s]U`.
By (&=I), `G, [s]G' |- [s]x: [s]T & [s]U`.

**Case (Sub)** Then `t0 = t` and the last rule is:

           G, x0: S0, G' |- t: T   G, x0: S0, G' |- T <: U
           -----------------------------------------------
                        G, x0: S0, G' |- t: U

By the I.H., `G, [s]G' |- [s]t: [s]T`.
By (Subst-<:), `G, [s]G' |- [s]T <: [s]U`.
By (Sub), `G, [s]G' |- [s]T: [s]U`.

**Case (Fld)**. Then `t0 = {a = t}` and the last rule is:

                        G, x0: S0, G' |- t: S
                   --------------------------------
                   G, x0: S0, G' |- {a = t}: {a: T}

By the I.H, `G, [s]G' |- [s]t: [s]S`.
By (Fld), `G, [s]G' |- {a = [s]t}: {a: [s]T}`.
Rewriting this gives `G, [s]G' |- [s]{a = t}: [s]{a: T}`.

**Cases (Typ), (And)** are analogous to (Fld).

***


### Lemma (Subst-<:)

If `G, x: S, G' |- T <: U` and
`G, [x:=y]G' |- y: [x:=y]S`, then
`G, [x:=y]G' |- [x:=y]T <: [x:=y]U`.

Proof by mutual induction on derivations.
Let [s] = [x0:=y0].
Assume `G, x0: S0, G' |- T0 <: U0` and `G, [s]G' |- y0: [s]S0`.
To show: `G [s]G' |- [s]T0 <: [s]U0`.

We only show two cases; the others are similar.

**Case(<:-Sel)**: Then `T0 = S` and the last rule of `D` is:

                    G, x0: S0, G' |- x: {A: S..T}
                    -----------------------------
                      G, x0: S0, G' |- S <: x.A

By the I.H., `G, [s]G' |- [s]x: {A: [s]S..[s]T}`.
By (<:-Sel), `G, [s]G' |- [s]S <: [s]x.A`.

**Case (All-<:-All)** Then `T0 = all(x: S1)T1` and the last rule is:

     G, x0: S0, G' |- S2 <: S1   G, x0: S0, G', x: S2 |- T1 <: T2
     ------------------------------------------------------------
            G, x0: S0, G' |- all(x: S1)T1 <: all(x: S2)T2

By the I.H., `G, [s]G' |- [s]S2 <: [s]S1` and
`G, [s]G', [s]x: [s]S2 |- [s]T1 <: [s]T2`.
By (All-<:-All), `G, [s]G' |- all([s]x: [s]S1)[s]T1 <: all([s]x: [s]S1)[s]T1`.
By (Renaming), `G, [s]G' |- [s]all(x: S1)T1 <: [s]all(x: S2)T2`.


### Lemma (Corresponding Definition Types)

If `G ~ s` and `s(x) = new(x: S)d` for some definitions `d = d1 & ... & dn` then
 1. `x: rec(x: S) in G`.
 2. `S = S1 & ... & Sn` where for each `i` either

    - `di` is of the form `{a = t}` and `Si = {a: T}` for some `T` such that `G |- t: T`, or
    - `di` is of the form `{A = T}` and `Si = {A: T..T}`.

*Proof* By the definition of `~`, `G` contains a binding for `x`, say
`G = G1,x:T,G2` such that `G1 |- s(x): T`. Also by the definition of `~` and with ({}-I),
`G1 |-! new(x: S)d: rec(x: S)`, which establishes (1).
Furthermore, by the formulation of the ({}-I) Rule and definition typing
it follows that `S` has the form given in (2).

### Lemma (Corresponding types)

If `G ~ s` and `x: T in G` then exactly one of the following alternatives applies:
 1. `s(x) = lambda(y:S)t` for a term `t` such that `G, x: S |- t: U` and `T = all(x: S)U`.
 2. `s(x) = new(s:S)d` and `T = rec(x:S)`.

*Proof*: Assume `x: T in G`, say `G = G1,x:T,G2`.
By the definition of `~`, `G1 |-! v: T` for some value `v`.
We distinguish acccording to whether `v` is a `lambda` or `new`.

In the first case, let `v = lambda(y: S)t`.
By by definition of `|-!`, `T` is derived using rule (all-I).
Hence, `T = all(x: S)U` for some type `U` such that `G1, x: S |- t: U`.
By (Weakening), `G, x: S |- t: U`.

In the second case, let `v = new(x: S)d`
(arranging w.l.o.g by alpha renaming that the bound variable in the new is `x`).
By by definition of `|-!`, `T` is derived using rule ({}-I).
Hence, `T = rec(x: S)`.

### Lemma (Unique tight bounds)

If `G ~ s` and `G |-! x: {A: T1..T1}` and `G |-! x: {A: T2..T2}` then `T1 = T2`.

*Proof*
Since `G |-! x: {A: Ti..Ti}` (i = 1,2), `G` contains a binding for `x`, say `x: T in G`.
By (Corresponding Types) one of the following alternatives applies.

 1. `s(x) = lambda(y:S)t` for a term `t` such that `G, x: S |- t: U` and `T = all(x: S)U`.
    But `x: {A: Ti..Ti)` cannot be derived from `x: all(x: S)U` using only (Rec-E) and
    (And-<:), (Trans) subsumption steps, so this alternative is impossible.

 2. `s(x) = new(x:S)d` and `T = rec(x:S)`. By (Corresponding Definition Types),
    `T` is of the form
    `rec(x: S1 & ... & Sn)` where exactly one `Si` defines a label `A`. Let `Si = {A: U..U}`.
    It follows that `T1 = U = T2`.


### Definition (Tight bound typing)

A typing or subtyping derivation is *tight* in environment `G` if
it only contains the following
tight variants of (Sel-<:), (<:-Sel) when `G' = G`:

    (<:-Sel-tight)
                              G' |-! x: {A: T..T}
                              -------------------
                                 G' |- T <: x.A
    (Sel-<:-tight)
                              G' |-! x: {A: T..T}
                              -------------------
                                 G' |- x.A <: T

For environments that extend G, full (Sel-<:) and (<:-Sel) are permitted.

We write `G |-# t: T` if `G |- t: T` with a derivation that is tight in `G`.

We write `G |-# S <: U` if `G |- S <: U` with a derivation that is tight in `G`.


### Definition (Has member)

A variable `x` with type `T` has a member `A: S..U`
in environment `G`, written `G |-# x: T has A: S..U`, if `G |-# x: T` and
the judgement is derivable by the following rules.

    (Refl-has)
                        G |-# x: {A: S..U} has A: S..U
    (&-has)
                           G |-# x: T1 has A: S..U
                         ----------------------------
                         G |-# x: T1 & T2 has A: S..U

                           G |-# x: T2 has A: S..U
                         ----------------------------
                         G |-# x: T1 & T2 has A: S..U
    (rec-has)
                            G |-# x: T has A: S..U
                        ------------------------------
                        G |-# x: rec(x: T) has A: S..U
    (sel-has)
                G |-! y: {B: T'..T'}   G |-# x: T' has A: S..U
                ----------------------------------------------
                           G |-# x: y.B has A: S..U
    (Bot-has)
                        G |-# x: Bot has A: S..U

### Lemma (Has member inversion)
If `G |- x: T has A: S..U` then one of the following cases applies:

 1. `T = {A: S..U}`.
 2. `T = T1 & T2` and `G |-# x: T1 has A: S..U` or `G |-# x: T2 has A: S..U`.
 3. `T = rec(x: T')` and `G |-# x: T' has A: S..U`.
 4. `T = y.B` and there exists a type `T'` such that
    `G |-! y: {B: T'..T'}` and `G |-# x: T' has A: S..U`.
 5. `T = Bot`.

*Proof:* Direct from the (Has member) rules.

### Lemma (Has member tightness)

If `G ~ s` and `s(x) = new(x: T)d` and `G |-# x: rec(x: T) has A: S..U` then
there is a type `T'` such that `S = T'` and `U = T'`.

*Proof:* By inspection of definition typing.

### Lemma (Has member covariance)
If `G ~ s`, `G |-# T1 <: T2` and `G |-# x: T1` and `G |-# x: T2 has A: S2..U2` then
there exist types `S1`, `U1` such that `G |-# x: T1 has A: S1..U1`
and `G |-# S2 <: S1` and `G |-# U1 <: U2`.

*Proof:* by induction on subtyping derivations.

**Case (<:-Top)**. Does not apply since `Top` cannot appear in a `has` judgement.

**Case (Bot-<:)**. By definition of (Has-member), case (Bot-has).

**Case (Refl-<:)**. Immediate

**Case (Trans-<:)**. Then the last rule is:

                    G |-# T1 <: T3   G |-# T3 <: T2
                    -------------------------------
                            G |-# T1 <: T2

By subsumption, since `G |-# x: T1` we have also `G |-# x: T3`.
By the I.H. there exist types `S3`, `U3` such that
`G |-# x: T3 has A: S3..U3` and `G |- S2 <: S3` and `G |- U3 <: U2`.
By the I.H. again, `G |- x: T1 has A: S1..U1` with `G |- S3 <: S1` and `G |- U1 <: U3`.
By (Trans-<:), `G |- S2 <: S1` and `G |- U1 <: U2`.

**Case (And-<:)**. Then the last rule is one of the axioms `G |-# T2 & U <: T2` or
`G |-# U & T2 <: T2`. Assume the first, the second is analogous. By rule (has-&),
`G |-# x: T2 & U has A: S2..U2`.

**Case (<:-And)**. Then `T2 = T21 & T22` and the last rule is:

                  G |-# T1 <: T21   G |-# T1 <: T22
                  ---------------------------------
                        G |-# T1 <: T21 & T22

By (Has member inversion), there exists `i in {1,2}` such that `G |-# x: T2i has A: S2..U2`.
By the I.H., `G |-# x: T1 has S2..U2`.

**Case (Fld-<:-Fld)**. Does not apply since `{a: U}` cannot appear in a `has` judgement.

**Case (Typ-<:-Typ)**. Then `T1 = {A1: S1..U1}` and `T2 = {A2: S2'..U2'}`
and the last rule is:

                  G |-# S2' <: S1   G |-# U1 <: U2'
                  ----------------------------------
                  G |-# {A: S1..U1} <: {A: S2'..U2'}

By (Has member inversion) on `T2`, `S2' = S2` and `U2' = U2`.
By definition of (Has member) on `T1`, `G |-# x: T1 has A: S1..U1`.
By inversion of the subtyping rule, the result follows.

**Case (<:-Sel-tight)**. Then `T2 = y.B` and the last rule is:

                         G |-! y: {B: T1..T1}
                         -------------------
                           G |-# T1 <: y.B

By (has member inversion), there exists a type `T` such that
`G |-! y: {B: T..T}` and `G |-# x: T has A: S2..U2`.
By (Unique tight bounds), `T = T1`, which proves the case.


**Case (Sel-<:-tight)**. Then `T1 = y.B` and the last rule is:

                         G |-! y: {B: T2..T2}
                         -------------------
                           G |-# y.B <: T2

By definition of (Has member), case (sel-has), the result follows.

**Case (All-<:-All)**. Does not apply since `all(x:S)T` cannot appear in a `has` judgement.

### Lemma (Has member monotonicity)

If `G ~ s` and `s(x) = new(x: T0)d` and
`G |-# x: T has A: S..U` then there exists a type `T1` such that
`G |-# x: rec(x: T0) has {A: T1..T1}`
and `G |-# S <: T1` and `G |-# T1 <: U`.

*Proof:* By induction of `G |-# x: T`.

**Case (Var)**. Then the last rule is

                         G, x: T, G' |- x: T

Since `G ~ s`, `T = rec(x: T0)`. By (Has member tightness), there is a type `T1` such that
`S = T1` and `U = T1`.

**Case (Sub)**. Then the last rule is:

                     G |-# x: T2   G |-# T2 <: T
                     ---------------------------
                              G |-# x: T

By (Has member covariance) there are types `S1`, `U1` such that
`G |- x: T2 has A: S1..T1` and `G |- S <: S1` and `G |- U1 <: U`.
By the I.H. there exists a type  `T1` such that `G |- x: rec(x: T0) has {A: T1..T1}`
and `G |- S <: T1` and `G |- T1 <: U1`. By (Trans) `G |- S <: T1` and `G |- T1 <: U`.

**Case (Rec-I)**. Then `T = rec(x: T')` and the last rule is:

                             G |-# x: T'
                          ------------------
                         G |-# x: rec(x: T')

By (Has member inversion), `G |-# x: T' has A: S..U`.
By the I.H., there exists a type `T1` such that
`G |-# x: rec(x: T0) has {A: T1..T1}` and `G |-# S <: T1` and `G |-# T1 <: U`.

**Case (Rec-E)**. Then the last rule is:

                          G |-# x: rec(x: T)
                          -----------------
                              G |-# x: T

By (has-rec), `G |-# x: rec(x: T) has A: S..U`.
By the I.H. there exists a type `T1` such that
`G |-# x: rec(x: T0) has {A: T1..T1}` and `G |-# S <: T1` and `G |-# T1 <: U`.

**Case (&-I)**. Then `T = T1 & T2` and the last rule is:

                      G |-# x: T1   G |-# x: T2
                      -------------------------
                           G |- x: T1 & T2

By (Has member inversion), there exists `i in {1,2}` such that `G |-# x: Ti has A: S..U`.
By the I.H. there exists a type  `T1` such that `G |- x: rec(x: T') has {A: T1..T1}`
and `G |- S <: T1` and `G |- T1 <: U`.

### Lemma (Tight bound completeness)

If `G ~ s` and `s(x) = new(x: T)d` and `G |-# x: {A: S..U}` then `G |-# x.A <: U` and `G |-# S <: x.A`.

*Proof:* Since `G |-# x: {A: S..U}`, we have also `G |-# x: {A: S..U} has A: S..U`.
By (Has member monotonicity), there exists a type  `T1` such that
`G |-# x: rec(x: T) has {A: T1..T1}` and `G |-# S <: T1` and `G |-# T1 <: U`.
By (Has member inversion, case 3), `G |-# x: T has A: T1..T1`.
By (Corresponding Definition Types) `T` is of the form `S1 & ... & Sn` where each
`Si` is of the form `{A: Ti..Ti}` or `{a: Ti}`.
By (Has member inversion, case 2), there must exist a `Si` such that
`G |- x: Si has A: T1..T1`.
By (Has member inversion), `Si = {A: T1..T1}`.
By Definition of (|-!), `G |-! x: {A: T1..T1}`.
By definition of (Sel-<:-tight) and (<:-Sel-tight),
`G |-# x.A <: T1` and `G |-# T1 <: x.A`.
By (Trans)
`G |-# x.A <: U` and `G |-# S <: x.A`.

### Lemma (All-I Inversion)

If `G |-! lambda(x: S)t: U` then `U = all(x: S)T` for some type `T` such that
`G, x: S |- t: T`.

### Lemma ({}-I Inversion)

If `G |-! new(x: T)(d1 & ... & dn): U` then `U = rec(x: T)` and `T` is of the form `S1 & ... & Sn`, where each `Si` corresponds to exactly one definition `di` in the following way:

 - if `di = {a = t}` then `Si = {a: T'}` for some `T'` such that `G |- t: T'`.
 - if `di = {A = T}` then `Si = {A: T..T}`.

### Definition (Possible types)

For a variable `x`, value `v`, environment `G`, the set
`Ts(G, x, v)` of possible types of `x` defined as `v` in `G` is the smallest set `SS` such that:

 1. If `v = new(x: T)d` then `T` in `SS`.
 2. If `v = new(x: T)d` and `{a = t}` in `d` and `G |- t: T'` then `{a: T'} in SS`.
 3. If `v = new(x: T)d` and `{A = T'}` in `d` and `G |- S <: T'`, `G |- T' <: U`
   then `{A: S..U} in SS`.
 4. If `v = lambda(x: S)t` and `G, x: S |- t: T` and
    `G |- S' <: S` and `G, x: S' |- T <: T'` then `all(x: S')T' in SS`.
 5. If `S1 in SS` and `S2 in SS` then `S1 & S2 in SS`.
 6. If `S in SS` and `G |-! y: {A: S..S}` then `y.A in SS`.
 7. If `T in SS` and then `rec(x: T) in SS`.
 8. `Top` in `SS`.

### Lemma (Tight possible types closure)
If `G ~ s` and `s(x) = v` then
`Ts(G, x, v)` is closed wrt `G |-# _ <: _`.

*Proof*: Let `SS = Ts(G, x, v)`. We show `SS` is closed wrt `G |-# _ <: _`.

Assume `T0 in SS` and `G |- T0 <: U0`.
We show `U0 in SS` by an induction on subtyping derivations of `G |-# T0 <: U0`.

**Case (<:-Top)**. Then `U0 = Top`. By (rule 8), `Top` in `SS`.

**Case (Bot-<:)**. Does not apply, since assumption `T0 in SS` cannot hold when `T0 = Bot`.

**Case (Refl-<:)**. Then `U0 = T0` hence `U0 in SS`.

**Case (Trans-<:)**. Then last last rule is:

                          G |- T0 <: S   G |- S <: U0
                          ---------------------------
                                 G |- T0 <: U0

Then by the I.H. (twice), `S in SS` and `U0 in SS`.

**Case (And-<:)**. Then `T0 = U0 & S` or `T0 = S & U0` for some type
`T`. Assume the first alternative, the second is analogous. The only ways a type `T & U` can
be part of set `SS` is through rule (1) or (5). If `T0` is part of `SS` through rule (1), then `v = new(x: T0)d`, for some definitions `d`. By (Corresponding Definition Types) `T0` is of the form `S1 & ... & Sn` where each `Si` corresponds to an atomic definition in `d`, and `U0` is the intersection of some subset of the `Si` types.
By rule (2) and (3) each of the `Si` types is in `SS`. Hence by applying
rule (5) as often as necessary, `U0 in SS`.
If `T0` is part of `SS` because of rule (5),
`U0` and `S` must both be in `SS`.

**Case (<:-And)**. Then `U0 = T & U` and `G |- T0 <: T`, `G |- T0 <: U`.
By the I.H. `T` and `U` are in `SS`. Hence, with rule (5), `U0 in SS`.

**Case (Fld-<:-Fld)**. Then `T0 = {a: T1}` and `U0 = {a: U1}` for types `T1`, `U1` such that
`G |- T1 <: U1`. The only way `T0` can be in `SS` is through rule (2),
or rule (1) convertible to rule (2) by `G ~ s`. That is,
`v = new(x: T)d` and `{a = t}` in `d` and `G |- t: T1`. Since `G |- T1 <: U1`
we get with (Sub) that `G |- t: U1`. With rule (2), `U0 in SS`.

**Case (Typ-<:-Typ)** Then `T0 = {A: T1..T2}` and `U0 = {A: U1..U2}` for types
`T1`, `T2`, `U1`, `U2` such that `G |- U1 <: T1` and `G |- T2 <: U2`.
The only way `T0` can be in `SS` is through rule (3) or rule (1) convertible to
rule (3) by `G ~ s`. That is,
`v = new(x: T)d` and `{A = T'}` in `d` and `G |- T1 <: T'`, `G |- T' <: T2`.
With (Trans), `G |- U1 <: T'` and `G |- T' <: U2`. With rule (3), `U0 in SS`.

**Case (<:-Sel-tight)**. Then `U0 = y.A` for some `y` such that `G |-! y: {A: T0..T0}`.
With rule (6), `U0 in SS`.

**Case (Sel-<:-tight)** Then `T0 = y.A` for some `y` such that `G |-! y: {A: U0..U0}`.
The only way `y.A` can be in `SS` is through rule (6).
That is, there is a type `S in SS` such that
`G |-! y: {A: S..S}`. By (Unique tight bounds), `U0 = S`, hence `U0 in SS`.

**Case (All-<:-All)**. Then `T0 = all(y: T1)T2` and `U0 = all(y: U1)U2`
for some `T1`, `U1` such that `G |- U1 <: T1` and for some `T2`, `U2`
such that `G, y: U1 |- T2 <: U2`. The only way `T0` can be in `SS` is
through rule (4). That is, `v = lambda(x: T)d` and `G |- T1 <: T` and
`G, x: T1 |- t: T2`. By (Narrowing), `G, x: U1 |- t: T2`. With (Sub),
`G, x: U1 |- t: U2`. With (Trans), `G |- U1 <: T`. With rule (4),
`all(x: U1)U2 in SS`.

This concludes the induction. Therefore, `SS` is closed wrt `G |-# _ <: _`.

### Lemma (Possible types completeness for values)

If `G ~ s` and `x = v in s` and  `G |-! v: T` then `T in Ts(G, x, v)`.

*Proof*. Assume first that `v = new(x: S)d`.
By the definition `|-!`, the proof of `G |-! v: T` must end in a `{}-I` rule.
By ({}-I Inversion), `T = rec(x: S)`. By rule (1) of (Possible Types), `S in Ts(G, x, v)`.
By rule (7) of (Possible Types), `rec(x: S) in Ts(G, x, v)`.

Assume now that `v = lambda(x: S)t`. By the definition `|-!`, the proof of `G |-! v: T` must end in a `All-I` rule. By (All-I Inversion),
`U = all(x: S)T` for some type `T` such that `G, x: S |- t: T`.
By rule (4) of (Possible Types), `all(x: S)T in Ts(G, x, v)`.


### Lemma (Tight possible types completeness)

If `G ~ s` and `x = v in s` and  `G |-# x: T` then `T in Ts(G, x, v)`.

*Proof*: By induction on the derivation of `G |-# x: T`. The derivation
of `G |-# x: T` must end in one of the following cases:

**Case (Var)**. Since  `G ~ s`, `G` contains a binding `x: T` such that `G |-! v: T`.
By (Possible types completeness for values), `T in Ts(G, x, v)`.

**Case (Rec-I)**. Then the last rule is:

                                  G |-# x: T
                              -----------------
                              G |-# x: rec(x: T)

By the I.H., `T in Ts(G, x, v)`. By rule (7) of (Possible Types), `rec(x: T) in Ts(G, x, v)`.

**Case (Rec-E)**. Then the last rule is:

                              G |-# x: rec(x: T)
                              -----------------
                                  G |-# x: T

By the I.H., `rec(x: T) in Ts(G, x, v)`. The only way a `rec` type can be in `Ts(G, x, v)` is through rule (7). Hence, `T in Ts(G, x, v)`.

**Case (&-I). Then the last rule is:

                            G |-# x: T   G |-# x: U
                            ---------------------
                                G |-# x: T & U

By the I.H., `T in Ts(G, x, v)` and `U in Ts(G, x, v)`. By rule (5) of (Possible Types),
`T & U in Ts(G, x, v)`.

**Case (Sub)**. Then the last rule is:

                           G |-# x: T   G |-# T <: U
                           -----------------------
                                  G |-# x: U

By the I.H., `T in Ts(G, x, v)`. By (Tight possible types closure), `U in Ts(G, x, v)`.

### Lemma (Equivalence of `G |- ...` and `G |-# ...`)

`G |-# ...` to `G |- ...` is straightforward by mutual induction on
typing and subtyping derivations.

For `G |-# ...` to `G |- ...`, all cases are straightforward by mutual
induction except tightening subtyping of type selections. We can use
(Tight bound completeness), provided we can show that `G |-# x :
{A:S..U}` implies that `s(x) = new(x: T)d` for some `T` and `d`, given
also `G ~ s`. Since `G ~ s`, we know that `s(x) = v` for some
`v`. By (Tight possible types completeness), `{A:S..U} in Ts(G, x,
v)`. By inversion, `v` must have of the form `new(x: T)d` for some `T`
and `d`.

### Lemma (Possible types closure)
If `G ~ s` and `s(x) = v` then `Ts(G, x, v)` is closed wrt `G |- _ <: _`.

*Proof*: By (Tight possible types) and (Equivalence of `G |- _ <: _` and `G |-# _ <: _`).

### Lemma (Possible types completeness)

If `G ~ s` and `x = v in s` and  `G |- x: T` then `T in Ts(G, x, v)`.

*Proof*: By (Tight possible types completeness) and (Equivalence of `G |- _ : _` and `G |-# _ : _`).

### Lemma (Possible types)
If `G ~ s` and `G |- x: T` then, for some value `v`,
`s(x) = v` and `T in Ts(G, x, v)`.

*Proof*: If `G |- x: T`, `x` must be bound in `G`. Since `G ~ s` there must be a value `v`
such that `s |= x = v`. By (Possible types completeness), `T in Ts(G, x, v)`.

### Lemma (Canonical forms 1)
If `G ~ s` and `G |- x: all(x: T)U` then `s(x) = lambda(x: T')t` where
`G |- T <: T'` and `G, x: T |- t: U`.

Proof: Since `x` has a type in `G`, `x` must be bound in `G`, say `G = G1,x:S,G2`.
Since `G ~ s` there exists a value `v` such that `x = v` in `s` and `G1 |- v:S`.
By (Possible Types), `v` cannot be a new because `all(x: T)U` is not in `T(G, x, v)`
if `v` is a `new`.
So `v` must be of the form `lambda(x: T')t`.
Again by (Possible Types) the only way an `x` defined as a `lambda(x: T')t`
can have a type `all(x: T)U` is
if, for some `U0`, `G |- T <: T'`, `G, x: T' |- t: U0` and `G, x: T |- U0 <: U`.
By (Sub) and (Narrowing), `G, x: T |- t: U`.

### Lemma (Canonical forms 2)
If `G ~ s` and `G |- x: {a: T}` then `s(x) = new(x: S)d` for some type `S`,
definition `d` such that
`G |- d: S` and `d` contains a definition `{a = t}` where `G |- t: T`.

Proof: Since `x` has a type in `G`, `x` must be bound in `G`, say `G = G1,x:S,G2`.
Since `G ~ s` there exists a value `v` such that `x = v` in `s` and `G1 |- v:S`.
By (Possible Types) `v` cannot be a lambda because `{a: T}` is not in `T(G, x, v)`
if `v` is a `lambda`.
So `v` must be of the form `new(x: S)d`.
Again by (Possible Types) the only way an `x` defined as `new(x: S)d` can have a type
`{a: T}` is if there is a definition `{a = t}` in `d` and `G |- t: T`.


<!---
### Lemma (Alternative formulation of existential subtyping)

Instead of (Ex-<:) and (<:-Ex) one may equivalently use the three rules below:

    (Ex-<:)
                               (x not in fv(T))
                             -------------------
                             G |- ex(x: S)T <: T
    (<:-Ex)
                                  G |- x: S
                            ---------------------
                             G |- T <: ex(x: S)T
    (Ex-<:-Ex)
                     G :- S1 <: S2   G, x: S1 |- T1 <: T2
                     ------------------------------------
                       G |- ex(x: S1)T1 <: ex(x: S2)T2

Proof: we can derive each rule in one rule system using the rules of the other.
-->


### Theorem (Preservation)

If `G |- t: T` and `G ~ s` and `s | t -> s' | t'`, then there exists
an environment `G''` such that, letting `G' = G, G''` one has `G' |- t': T` and `G' ~ s'`.

### Theorem (Progress)

If `G |- t: T` and `G ~ s` then either

 - `t` is a normal form, or
 - `s | t -> s' | t'`, for some store `s'`, term `t'`.

*Proof*: We prove both theorems together. To be shown:

Let `G |- t: T` and `G ~ s`. Then either

 - `t` is a normal form, or
 - there exists a store `s'`, term `t'` such that `s | t -> s' | t'`, and
   for any such `s'`, `t'` there exists an environment `G''` such that, letting `G' = G, G''` one has
   `G' |- t': T` and `G' ~ s'`.

The proof is by a induction on typing derivations of `G |- t: T`.

If the last rule is one of (Var), (All-I), ({}-I), (Rec-I), (Rec-E), (&-I),
`t` is a normal form and the result follows immediately.

**Case (All-E)**: Then the last rule is:

                       G |- x: all(z: S)T    G |- z: S
                       -------------------------------
                                 G |- x y: [z:=y]T

Since `G ~ s`, `G |- s(x): all(z: S)T`. By (Canonical forms 1),
`s(x) = lambda(z: S')t` where `G |- S <: S'` and `G, z: S |- t: T`.
By (Apply), `s | x y ->  s | [z:=y]t`.
By (Subst), G |- [z:=y]t: [z:=y]T.

**Case ({}-E)**: Then the last rule is:

                                G |- x: {a: T}
                                --------------
                                 G |- x.a: T

Since `G ~ s`, `G |- s(x): {a: T}`. By (Canonical forms 2),
`s(x) = new(y: S)d` for some binding `y = new(y: S)d`, such that `G |- d: S` and `d` contains
a definition `{a = t}` where `G |- t: T`.
By (Project) `s | x.a -> s | t`, which proves the case.

**Case (Let)**: Then the last rule is:

                G |- t: T   G, x: T |- u: U   (x not in fv(U))
                ----------------------------------------------
                            G |- let x = t in u: U

we distinguish according to whether `t` is a value, variable, or general term.

If `t = v` for some value `v`, then by (Let-Value),
`s | let x = v in t --> s, x = v | t`.
Inspection of the type assignment rules shows that
any typing of a `lambda` must contain an (All-I) rule, which can only
be followed by (Sub) steps. Similarly, the typing of a `new` must
contain a ({}-I) rule, which can be only followed by subsumption
steps. Let `T'` be the type obtained for `v` by the (All-I) or ({}-I)
rule and let `D` be the (possibly empty) sequence of subsumption steps
that follows it. Applying a (Var) step on `x` and following with `D`
gives a derivation of `G, x: T' |- x: T`.
This means `G, x: T' <: G, x: T`.
By (Narrowing), `G, x: T' |- u: U`.
Furthermore, by the construction of `T'`, `G |-! v: T'`, hence
`G, x: T' ~ s, x = v`.

If `t = y` for some variable `y`, then by (Let-Var)
`s | let x = y in t --> s | [x:=y]t`.
The preconditions of the last rule are then: `G |- y: T` and `G, x: T |- u: U` and
`x not in fv(U)`.
Furthermore, since `fv(T) <= dom(G)` and `x not in dom(G)`, `x not in fv(T)`.
It follows with (Subst) that `[x:=y]t: [x:=y]U`. Since `x not in fv(U)`, `[x:=y]U = U`,
which proves the case.

If `t` is not a value nor a variable, then by the induction hypothesis
 there exist `s'`, `t'` such that `s | t -> s' | t'` and for any such
 `s'`, `t'` there exists an environment `G' = G, G''` such that `G' |-
 t': T` and `G' ~ s'`. By (Weakening) `G, G'', x: T |- u: U`. Hence,
 by (Let), `G' |- let x = t' in u: U`.

**Case (Sub)**: Then the last rule is:

                           G |- t: T   G |- T <: U
                           -----------------------
                                  G |- t: U

If `t` is a value, the result follows immediately. Assume now that `t` is not a value.
By the induction hypothesis there exist
 `s'`, `t'` such that `s | t -> s' | t'` and for any such `s'`, `t'`
 there exists an environment `G' = G, G''` such that `G' |- t': T` and
 `G' ~ s'`. By (Weakening, 2nd clause), `G' |- T <: U`.
Then by (Sub) it follows that `G' |- t: U`.


