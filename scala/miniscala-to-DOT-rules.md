
Miniscala Syntax
================

    Var/label    x, y, l, m
    Path         p ::= x
                       x.l                    no real paths at the moment, only length 1
    Term         t ::= x
                       t.l
                       t t
                       new p                  p has to refer to a class definition
                       s; t                   allows to construct blocks of statements followed by return expr
    Statement    s ::= d                      statements will later also include terms, but pointless if no side-effects
    Definition   d ::= val l: T = t
                       def m(x: S): T = t
                       class l { z => d... }
    Type         T ::= p                      path referring to class (the only type which user programs can contain)
                       (x:S)T                 dependent method type
                       class p { z => d... }  type of a path p referring to a class def (like dotty's ClassInfo)

Note: Vars, class labels, type labels, and def labels are all taken from the same set.
Miniscala has no values and no reduction rules, but it reuses those of DOT.
Note: This calculus is very lame: No inheritance, no subtyping, no type members...

In miniscala, paths referring to a class are terms and types at the same time: They are terms because the definition typing rules assign types to them (their type is just their definition), and they are types because `new p` has type `p`.
In the translation, they lose their term aspect and become just types. A class def inside an expression `class l { z => d....} in t` is translated to a wrapper object holding just the type: `let l = new { L0: {z => ...} } in t'`. If the class def appears as a member, it is just replaced by the type directly, without wrapping.


Translating types `G |- T ~> U`
===============================

Read as "In context G, miniscala type T translates to DOT type U".
Not needed if we only want to typecheck without translating.


    (G, z: p |- d: (l: T) ~> d')...
    (G, z: p |- T ~> T')...
    ----------------------------------------------- trTypClsOfCls
    G |- class p {z => d...} ~> {z => /\(l: T')...}

    
    G |- S ~> S'     G, x: S |- T ~> T'
    ----------------------------------- trTypMtd
    G |- (x:S)T ~> all(x:S')T'

    
    G |- class x.l { z => d...}
    --------------------------- trTypCls1
    G |- x.l ~> x.l

    
    G |- class x { z => d...}
    ------------------------- trTypCls2
    G |- x ~> x.L0
    
Note: `L0` is a designated label that we use to wrap types.


Class lookup `G |- class p { z => d...}`
========================================

Read as "In context `G`, the path `p` refers to a class whose definition is `{ z => d...}`".
Note: `class p { z => d...}` is also a type, and we can also interpret this `G |- class p { z => d...}` judgment as a judgment saying that this type is well-formed (`p` indeed defined in `G`, with rhs `{ z => d...}`).

    (x: class x { z => d...}) in G
    ------------------------------ clLookup1
    G |- class x { z => d...}
    
    
    G |- class p { z0 => (class l { z => d...}); d'... } 
    G |- x: p ~> x
    ---------------------------------------------------- clLookup2
    G |- class x.l { z => d...}


Translating terms `G |- t: T ~> u`
==================================

Read as "In context G, miniscala term t has type T and translates to DOT term u".


    (x: T) in G
    -------------- trVar
    G |- x: T ~> x


    G |- class p {z => d...}
    (G, z: p |- d : (m: T) ~> d')...
    --------------------------------- trNew
    G |- new p: p ~> new {z => d'...}


    G |- class p {z => (l: T); d...}
    G |- x: p ~> x
    -------------------------------- trSel1
    G |- x.l: [x/z]T ~> x.l


    G |- class p {z => (l: T); d...}
    z notin fv(T)
    G |- t: p ~> t'
    -------------------------------- trSel2
    G |- t.l: T ~> t'.l
    
    
    G |- t1: (x:S)T ~> t1'
    G |- x2: S ~> x2
    ------------------------------ trApp1
    G |- t1 x2 : [x2/x]T ~> t1' x2
    
    
    G |- t1: (x:S)T ~> t1'
    x notin fv(T)
    G |- t2: S ~> t2'
    ------------------------- trApp2
    G |- t1 t2 : T ~> t1' t2'
    

    G |- t1 : T1 ~> t1'
    G, l: T1 |- t2 : T2 ~> t2'
    --------------------------------------------------- trSeqVal
    G |- (val l: T1 = t1; t2) : T2 ~> let l = t1' in t2'

    
    G |- S ~> S'
    G, x: S |- t1: T1 ~> t1'
    G, m: (x:S)T1 |- t2 : T2 ~> t2'
    --------------------------------------------------------------------- trSeqDef
    G |- (def m(x: S): T1 = t1; t2) : T2 ~> let m = lambda(x:S')t1' in t2'
Leave out the above rule for the moment because DOT only supports methods as members, not lambdas (could encode them, though).

    
    (G, l: class l { z => d...}, z: l |- d : (m: T) ~> d')...
    (G, l: class l { z => d...}, z: l |- T ~> T')...
     G, l: class l { z => d...} |- t2 : T2 ~> t2'
    ------------------------------------------------------------------------------------------- trSeqCls
    G |- (class l { z => d...}; t2) : T2 ~> let l = new { type L0 = {z => /\(m: T')...} } in t2
    
    
    
Translating defs of classes `G |- d : (l: T) ~> d'`
===================================================


    G |- S ~> S'     G, x: S |- T ~> T'      G, x: S |- t: T ~> t'
    ------------------------------------------------------------------- trDefDef
    G |- (def m(x: S): T = t) : (m: (x: S)T) ~> (def m(x: S'): T' = t')

    
    (G, z: z0.l |- d : (m: T) ~> d')...     (G, z: z0.l |- T ~> T')...
    -------------------------------------------------------------------------------------------- trDefCls
    G |- (class l { z => d...}) : (l: class z0.l {z => d...}) ~> (type l = { z => /\(m: T')...})

Note: There is no trDefVal rule yet, because excluding top-level uses of the self ref on the RHS of the val def requires some additional tricks (eg "regular & restricted vars").



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


