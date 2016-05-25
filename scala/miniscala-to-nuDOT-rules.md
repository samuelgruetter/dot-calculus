
Miniscala Syntax
================

    Variable     x
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
                       class { z => T... }    type of a path referring to a class def (like dotty's ClassInfo)

Miniscala has no values and no reduction rules, but it reuses those of nuDOT.
Note: This calculus is very lame: No inheritance, no subtyping, no type members...


Translating types `G |- T ~> U`
===============================

Read as "In context G, miniscala type T translates to nuDOT type U".


    (maybe some wf-ness/closed-ness conditions)
    ----------------------------------------------------------- trTypClsOfCls
    G |- class {z => (l: T)...} ~> [z: /\(l: T)... | (l: T)...]


    G |- S ~> S'     G, x: S |- T ~> T'
    ----------------------------------- trTypMtd
    G |- (x:S)T ~> all(x:S')T'


    (G |- T ~> T')...
    G |- p : class { z => (l: T)...}
    -------------------------------- trTypCls
    G |- p ~> { z => /\(l: T')...}

Note: In the above rule, we see why it's useful to have a G where we can loookup p.
But in this simple variant, we could probably also just create a type alias whenever we define a class, so that we don't have to look it up, but just replace p by, say, p.DesignatedAliasName.
But later when we add inheritance, we might want to collect all members of a class, and then G will definitely be useful.

 
Translating terms `G |- t: T ~> u`
==================================

Read as "In context G, miniscala term t has type T and translates to nuDOT term u".


    (x: T) in G
    -------------- trVar
    G |- x: T ~> x


    G |- p: class {z => (l: T)...} ~> u
    ------------------------------------ trNew
    G |- new p: p ~> new u


    G |- p: class {z => (l: T)...} ~> _
    G |- x: p ~> x
    ----------------------------------- trSel1
    G |- x.li: [x/z]Ti ~> x.li


    G |- p: class {z => (l: T)...} ~> _
    z notin fv(Ti)
    G |- t: p ~> t'
    ----------------------------------- trSel2
    G |- t.li: Ti ~> t'.li
    
    
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

    
    (G, l: class { z => (m: T)...}, z: l |- d as z.m : T ~> d')...
    (G, l: class { z => (m: T)...}, z: l |- T ~> T')...
    G, l: class { z => (m: T)...} |- t2 : T2 ~> t2'
    ------------------------------------------------------------------------------- trSeqCls
    G |- (class l { z => d...}; t2) : T2 ~> let l = [z: /\(m: T')... | d'...] in t2'
    
    
    
Translating defs of classes `G |- d as z.l : T ~> d'`
=====================================================

Read as "definition d, whose label is l, when it's a member of z (which is already in G), has type T and translates to d'".


    G |- S ~> S'     G, x: S |- T ~> T'      G, x: S |- t: T ~> t'
    ---------------------------------------------------------------------- trDefDef
    G |- (def m(x: S): T = t) as z0.m : (x: S)T ~> (def m(x: S'): T' = t')

    
    (G, z: z0.l |- d as z.m : T ~> d')...     (G, z: z0.l |- T ~> T')...
    ------------------------------------------------------------------------------------------------ trDefCls
    G |- (class l { z => d...}) as z0.l : class {z => (m: T)...} ~> (val l = [z: /\(m: T') | d'...])


Note: There is no trDefVal rule yet, because excluding top-level uses of the self ref on the RHS of the val def requires some additional tricks (eg "regular & restricted vars").



Theorem (or conjecture)
=======================

If `empty |- t: T ~> t'`, then there exists `T'` such that `empty |- T ~> T'` and `empty |- t': T'` according to the nuDOT rules.


