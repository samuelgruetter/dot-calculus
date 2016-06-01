
Miniscala Syntax
================

    Var/label    x, y, l, m
    Path         p ::= x
                       x.l                    no real paths at the moment, only length 1
                       AnyRef
    Term         t ::= x
                       t.m(t)
                       new p                  p has to refer to a class definition
                       s; t                   allows to construct blocks of statements ended by return expr
    Statement    s ::= d                      will later also include terms, but pointless if no side-effects
    Definition   d ::= val l: T = t
                       def m(x: S): T = t
                       class l extends p { z => d...}
    Type         T ::= p                      path referring to class (the only type which user programs can contain)
                       extends p { z => d... }    type of a path referring to a class def (like dotty's ClassInfo)

Note: Vars, class labels, type labels, and def labels are all taken from the same set.
Miniscala has no values and no reduction rules, but it reuses those of DOT.
Note: This calculus is very lame: No inheritance, no subtyping, no type members...

Note: In the current version, the context G is not needed for the translation, but only for the typechecking (in particalar, to enforce nominality).

TODO: If `new AnyRef` is allowed, we can enforce that all constructors take exactly 1 argument, instead of a useless DOT new {}.


Translating user types `T ~> U`
===============================

Read as "miniscala type T translates to DOT type U".
Only used for types that user programs can contain, i.e. for paths referring to classes.    


    ------------- trTypAnyRef
    AnyRef ~> Top


    ---------- trTypCls1       (for references to classes which are defined in a term)
    x ~> x.T_x
    

    ------------ trTypCls2     (for references to classes which are members of an object)
    x.l ~> x.T_l
    


Translating the type of a definition `d ~y~> (l: T')...`
========================================================

Translates the type of definition `d` occurring in a class whose self reference is `y`.

Does two steps at once (because it's simpler to define like this):
1) turn the definition (including implementation) into a declaration (without implementation)
2) translate the type of the declaration
Note that one definition in miniscala can result in 1 or 2 declarations in DOT, so we return a list.
The y in ~y~> is the name of the outer self ref.


    (d ~z~> (m: T')...)...             p ~> U
    ----------------------------------------------------------------------------------------------------- trTypOfDefCls
    class l extends p {z => d...} ~y~> (type T_l: {z => U /\ (/\(m: T')...})); (def new_l(x: Top): y.T_l)

    
    S ~> S'     T ~> T'
    ---------------------------------------- trTypOfDefMtd
    def m(x: S): T = t ~y~> def m(x: S'): T'


Note: No rule for val defs yet, because they cannot yet be members of classes.



Translating defs of classes `G |- d ~y~> d'...`
===============================================

Also does typechecking: Checks that the actual types correspond to the declared types, but since all types are ascribed, no need to assign types in the judgment.


    S ~> S'     T ~> T'      G, x: S |- t: T ~> t'
    --------------------------------------------------------------------- trDefDef
    G |- (def m(x: S): T = t) ~y~> (def m(x: S'): T' = t')

    
    G |- z0.l <z da...
    (G, z: z0.l |- da ~z~> d'...)...       (d ~z~> (m: T')...)...       p ~> U
    -------------------------------------------------------------------------------------------- trDefCls
    G |- class l extends p { z => d...} ~z0~> (type T_l = { z => U /\ (/\(m: T')...}));
                                              (def new_l(x: Top): z0.T_l = new {z => d'...})

Note: There is no trDefVal rule yet, because excluding top-level uses of the self ref on the RHS of the val def requires some additional tricks (eg "regular & restricted vars").



Class lookup `G |- class p extends q { z => d...}`
==================================================

Read as "In context `G`, the path `p` refers to a class whose definition is `extends q { z => d...}`".


    (x: extends q { z => d...}) in G
    ----------------------------------- clLookup1
    G |- class x extends q { z => d...}
    
    
    G |- x <x d0a...; class l extends q { z => d...}; d0b...
    -------------------------------------------------------- clLookup2
    G |- class x.l extends q { z => d...}



Class expansion `G |- p <z d...`
================================

Read as "In context `G`, the path `p` refers to a class whose members (including inherited) are `d`, with self ref `z`".


    -------------------- expandAnyRef
    G |- AnyRef <z empty


    G |- class p extends q { z => d2...}
    G |- q <z d1...
    ------------------------------------ expandCls
    G |- p <z d1...; d2...                           note: d2 overrides d1



Substitution by a term which is forced to a var if needed `substIfOccurs z t1 X`
================================================================================

X can be a term, type, path, def

`substIfOccurs z t1 X` is a partial function which does the following:

    if z in FV(X) then
      if t1 is a variable then
        return [t1/z]X
      else
        fail
    else
      return X



Translating terms `G |- t: T ~> u`
==================================

Read as "In context G, miniscala term t has type T and translates to DOT term u".


    (x: T) in G
    -------------- trVar
    G |- x: T ~> x


    G |- class x {z => d...}
    --------------------------------- trNew1
    G |- new x: x ~> x.new_x(new {})


    G |- class x.l {z => d...}
    ------------------------------------ trNew2
    G |- new x.l: x.l ~> x.new_l(new {})
    
    
    G |- t1: p ~> t1'
    G |- p <z d0...; def m(x:S2): T0 = t; d1...
    G |- t2: S1 ~> t2'
    G |- S1 <: S2
    substIfOccurs z t1 T0 = T1
    substIfOccurs x t2 T1 = T2
    ----------------------------------------------- trApp
    G |- t1.m(t2) : T2 ~> t1'.m(t2')
    
    
    G |- t1 : T1 ~> t1'
    G, l: T1 |- t2 : T2 ~> t2'
    --------------------------------------------------- trSeqVal
    G |- (val l: T1 = t1; t2) : T2 ~> let l = t1' in t2'

    
    G, l: extends p { z => d...} |- l <z da...
    (G, l: extends p { z => d...}, z: l |- da ~z~> d'...)...
    (d ~z~> (m: T'))...
    G, l: extends p { z => d...} |- t2 : T2 ~> t2'
    p ~> U
    ------------------------------------------------------------- trSeqCls
    G |- (class l extends p { z => d...}; t2) : T2 
         ~> let l = new { y =>
              type T_l = {z => U /\ (/\(m: T')...)}
              def new_l(x: Top): y.T_l = new { z => da...}
            } in t2'

Note: No trSeqDef for the moment because DOT only supports methods as members, not lambdas (could encode them, though).



Subtyping `G |- T1 <: T2`
=========================


    ------------- subRefl
    G |- p1 <: p1


    G |- class p1 extends p2 { z => d...}
    G |- p2 <: p3
    ------------------------------------- subStep
    G |- p1 <: p3



Translating contexts (only needed for proofs) `G ~> G'`
=======================================================

    empty ~> empty

    
    G ~> G'
    G |- T ~> T'
    ------------------------
    (G, x: T) ~> (G', x: T')



Theorem (or conjecture)
=======================

If `empty |- t: T ~> t'`, then there exists `T'` such that `empty |- T ~> T'` and `empty |- t': T'` according to the DOT rules.

To have a strong enough IH, we will have to state it as follows:

If `G |- t: T ~> t'`, then there exist `G'` and `T'` such that `G ~> G'` and `G |- T ~> T'` and `G' |- t': T'` according to the DOT rules.


