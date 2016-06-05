
Miniscala Syntax
================

    Var/label    x, y, l, m
    Path         p ::= x
                       x.l                    no real paths at the moment, only length 1
                       AnyRef
    Term         t ::= x
                       t.l
                       t t
                       new p                  p has to refer to a class definition
                       s; t                   allows to construct blocks of statements ended by return expr
                       _abstract_             "body" of abstract defs
    Statement    s ::= d                      will later also include terms, but pointless if no side-effects
    Definition   d ::= val l: T = t
                       def m(x: S): T = t
                       class l extends p { z => d...}
    Type         T ::= p                      path referring to class (the only type user programs can contain)
                       (x:S)T                 type of def
                       extends p { z => d... }    type of a path referring to a class def (like dotty's ClassInfo)

    Context      G ::= (x: T)...              used for class lookup during translation

Note: Vars, class labels, type labels, and def labels are all taken from the same set.
Miniscala has no values and no reduction rules, but it reuses those of POT.


POT Syntax
==========

    Var          x, y, z
    Label        a, b, c, f, l, m
    Value        v ::= lambda(x:T)t           function
                       [T]                    type tag ("wrapped type")
                       {z => d...}            object
    Term         t ::= x
                       v
                       t.l
                       t t
    Definition   d ::= (a: T = t)             t must be a value or a var (enforced by typing rules)
    Type         T ::= Top
                       Bot
                       {a: T}                 record with one val/def/type member
                       all(x:T)U
                       [T..U]                 type of type tags, with bounds
                       t!                     unwrap type tag, t must be a path (enforced by typing rules)
                       {z => T}
                       T /\ T
                       T \/ T
   

Substitution: Only var-by-value.

    isPath x
    
    isPath v
    
    isPath p
    ----------
    isPath p.l


Problem: Define selection 2x? once p.l, once t.l, define step for it 2x?
That's why we don't have path p ::= x | v | p.l


POT reduction rules
===================

    Reduction:

    (lambda(x:T)t1) v -> [v/x]t1
    
    {z => (l: T = v); d...}.l -> [v/z]v
    
    
    Congruence:
    
    t -> t'
    -----------
    t.l -> t'.l
        
    t1 -> t1'
    -----------------
    t1 t2 -> t1' t2

    t -> t'
    -----------
    v t -> v t'



The translation
===============

Needs a context `G` to look up class defs and to collect all inherited members, so that they can be put together in the constructors.



Translating user types
======================

All user types in miniscala are paths p referring to a class, and their translation is always p.branding.C.



Translating constructors `new p ~> t`
=====================================

Constructor invocations `new p` translate to `p.create(new {})`



Dropping the implementation (= extracting the declared type) of a POT definition `dropImpl d = {a: T}`
======================================================================================================

    (dropImpl (a: T = x)) = {a: T}
    (dropImpl (a: T = v)) = {a: T}
    


Dropping the implementation of a POT definition list `dropImpls d... = T` (where T is a chained And-type)
=========================================================================================================

    (dropImpls nil) = Top
    (dropImpl (d; ds)) = (dropImpl d) /\ (dropImpls ds)


Shorthand (for not repeating the types)
=======================================

`(a = {z => ds})` is a shorthand for `(a: {z => (dropImpls ds)} = {z => ds})`

Note that we depend on annotating val defs with less precise types to get the branding!


Translating defs `G |- d ~> (a: T = t)`
=======================================

    
    t ~> t'
    --------------------------------------------- trDefVal
    G |- (val a: T = t) ~> (a: T.branding.C = t')


    G, x: S |- t ~> t'
    ------------------------------------------------------------------------------------------------ trDefDef
    G |- (def m(x: S): T = t) ~> (m: all(x:S.branding.C)T.branding.C = lambda(x: S.branding.C) = t')


    (G |- d ~> (m: T = t))...
    G |- p <z d0...
    G |- d0...; d1... ~> d2...        <-- if this fails because it contains some non-overriden
                                          abstract methods, no "create" constructor is added
                                          below, and the rest of the rule remains the same
    -------------------------------------------------------------------------------------------- trDefCls
    G |- class l extends p { z => d1...}
      ~> (l = { l =>
           (branding: { b => 
             type R = p.branding.A /\ (/\ (m: T)...)
             type A = p.branding.C /\ (/\ (m: T)...)
             type C <: b.C
             brand: all(x: [Bot..b.R]) all(y: x!) b.C /\ x!
           } = { b =>
             type R = p.branding.A /\ (/\ (m: T)...)
             type A = p.branding.C /\ (/\ (m: T)...)
             type C = b.C
             brand = lambda(x: [Bot..b.R]) lambda(y: x!) p.branding.brand[x!](y)
           })
           (create: all(dummy: Top)l.branding.C = lambda(dummy: Top) l.branding.brand[l.branding.R]({z =>
              d2...
           }))
         })


Note: Undefined for abstract defs, they must be overridden by concrete ones before we can make a constructor.


Toplevel "Library"
==================

Every translated program starts with this:

let AnyRef = new { AnyRef =>
  val branding: { b =>
    type R = Top
    type A = Top
    type C <: b.A
    def brand[X <: b.R](x: b.A): b.C & X
  } = new { b =>
    type R = { z => Top }
    type A = { z => Top }
    type C = b.A
    def brand[X <: b.R](x: b.A): b.C & X = x
  }
  def create(dummy: Top): AnyRef.branding.C = AnyRef.branding.brand(new {})
} in ...



Translating the type of defs `G |- d ~> {a: T}`
===============================================


    G |- d ~> (a: T = t)
    -------------------- trTypOfConcreteDef
    G |- d ~> {a: T}


    S ~> S'    T ~> T'
    ------------------------------------------------------ trTypOfAbstractDef
    G |- (def m(x: S): T = _abstract_) ~> {m: all(x:S')T'}



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




Translating terms `G |- t ~> t'`
================================

    
    ----------- trVar           (no need to check if x in G, because we're not typechecking)
    G |- x ~> x


    ------------------------------ trNew
    G |- new p ~> p.create(new {})


    G |- t ~> t'
    ---------------- trSel
    G |- t.l ~> t'.l

    
    G |- t1 ~> t1'
    G |- t2 ~> t2'
    --------------------- trApp
    G |- t1 t2 ~> t1' t2'
    
    
    G |- (val l: T1 = t1) ~> (l: T1' = t1')
    G, l: T1 |- t2 ~> t2'
    ----------------------------------------------- trSeqVal
    G |- (val l: T1 = t1; t2) ~> let l = t1' in t2'

    
    G |- (def f(x: T0): T1 = t1) ~> (f: all(x: T0')T1' = lambda(x: T0')t1)
    G, l: T1 |- t2 ~> t2'
    ---------------------------------------------------------------------- trSeqDef
    G |- (val l: T1 = t1; t2) ~> let l = t1' in t2'
    
    
    G |- (class l extends p { z => d...}) ~> (l = v)
    G, l: extends p { z => d...} |- t2 ~> t2'
    ------------------------------------------------------------- trSeqCls
    G |- (class l extends p { z => d...}; t2) ~> let l = v in t2'


