
Miniscala Syntax
================

    Var/label    x, y, l, m
    Path         p ::= x
                       x.l                    no real paths at the moment, only length 1
    Term         t ::= x
                       t.m(t)
                       new c
                       s; t                   allows to construct blocks of statements ended by return expr
                       _abstract_             placeholder for bodies of abstract defs
    Statement    s ::= d                      will later also include terms, but pointless if no side-effects
    Definition   d ::= val l: T = t
                       def m(x: S): T = t
                       class l(x: T) extends c { z => d...}
    Type         T ::= p                      path referring to class
                       AnyRef
    Constructor  c ::= p(t)                   constructor invocations always have exactly 1 argument
                       AnyRef                 except for AnyRef

Note: Vars, class labels, type labels, and def labels are all taken from the same set.
Miniscala has no values and no reduction rules, but it reuses those of nuDOT.

Note: Class constructors take one argument, which they use in the expression passed to the parent constructor.
This is very simple to encode because the glueing is done by the core calculus, contrary to encodings into DOT/POT.

Note: Nominality is not enforced.



Translating types: `trTyp T = U`
================================

Read as "miniscala type T translates to nuDOT type U".


    ------------------ trTypAnyRef
    trTyp AnyRef = Top
    
    
    ------------- trTypClsVar
    trTyp x = x.C                     (for references to classes which are defined in a term)
    
    
    ----------------- trTypClsSel
    trTyp x.l = x.C_l                 (for references to classes which are members of an object)
    


Translating constructor invocations `trCtor c = t`
==================================================

miniscala constructor c translates to nuDOT term t (which is always of type "class template")


    --------------------------- trCtorAnyRef
    trCtor AnyRef = [z: Top | ]

    
    trTrm t = t'
    ----------------------- trCtorVar
    trCtor x(t) = x.tpl(t')


    trTrm t = t'
    --------------------------- trCtorSel
    trCtor x.l(t) = x.tpl_l(t')



Translating the template type of a constructor `trTplTypOfCtor c = T`
=====================================================================


    ----------------------------------- trTplTypOfCtorAnyRef
    trTplTypOfCtor AnyRef = [z: Top | ]


    ------------------------ trTplTypOfCtorVar
    trTplTypOfCtor x = x.Tpl


    ------------------------------- trTplTypOfCtorSel
    trTplTypOfCtor x.l(t) = x.Tpl_l



Translating the instance type of a constructor `trInstTypOfCtor c = T`
======================================================================

 
    ---------------------------- trInstTypOfCtorAnyRef
    trInstTypOfCtor AnyRef = Top


    -------------------------- trInstTypOfCtorVar
    trInstTypOfCtor x = x.Inst


    --------------------------------- trInstTypOfCtorSel
    trInstTypOfCtor x.l(t) = x.Inst_l



Translating the type of a definition `trTypOfDef y d = (l: T')...`
==================================================================

Translates the type of definition `d` occurring in a class whose self reference is `y`.

Does two steps at once (because it's simpler to define like this):
1) turn the definition (including implementation) into a declaration (without implementation)
2) translate the type of the declaration
Note that one definition in miniscala can result in 1 or 2 or 3 declarations in nuDOT, so we return a list.


    trTyp S = S'     trTyp T = T'
    ------------------------------------------------------ trTypOfDefDef
    trTypOfDef y (def m(x: S): T = t) = (def m(x: S'): T')
    

    trInstTypOfCtor c = U                       trTyp R = R'     
    (trTypOfDef z d = (m: T')...)...
    -------------------------------------------------------------------------------------------- trTypOfDefCls
    trTypOfDef y (class l(x: R) extends c { z => d...}) = (type Inst_l = { z => U /\ (/\(m: T')...)});
                                                          (type Tpl_l = [ z: y.Inst_l | (/\(m: T')...)]);
                                                          (def tpl_l(x: R'): y.Tpl_l)


Note: No rule for val defs yet, because they cannot yet be members of classes.



Translating defs of classes `trDef y d = d'...`
===============================================


    trDef S = S'     trDef T = T'      trTrm t = t'
    ------------------------------------------------------ trDefDef
    trDef y (def m(x: S): T = t) = (def m(x: S'): T' = t')


    trCtor c = c'
    trInstTypOfCtor c = U                       trTyp R = R'     
    (trTypOfDef z d = (m: T')...)...            (trDef z d = d'...)...
    ----------------------------------------------------------------------------------------------- trDefCls
    trDef y (class l(x: R) extends c { z => d...}) = (type Inst_l = { z => U /\ (/\(m: T')...)});
                                                     (type Tpl_l = [ z: y.Inst_l | (/\(m: T')...)]);
                                                     (def tpl_l(x: R'): y.Tpl_l = c' & [ z: y.Inst_l | d'...])


Note: There is no trDefVal rule yet, because excluding top-level uses of the self ref on the RHS of the val def requires some additional tricks (eg "regular & restricted vars").



Term translation `trTrm t = t'`
===============================


    ----------- trVar
    trTrm x = x


    trCtor c = t'
    --------------------- trNew
    trTrm (new c) = new t'

    
    trTrm t1 = t1'
    trTrm t2 = t2'
    --------------------------- trApp
    trTrm t1.m(t2) = t1'.m(t2')
    
    
    trTrm t1 = t1'
    trTrm t2 = t2'
    trTyp T1 = T1'
    ------------------------------------------------------ trSeqVal
    trTrm (val l: T1 = t1; t2) = (let l: T1' = t1' in t2')


    trCtor c = c'
    trTrm t2 = t2'       trTyp R = R'
    (trTypOfDef z d = (m: T')...)...            (trDef z d = d'...)...
    ------------------------------------------------------------------ trSeqCls
    trTrm (class l(x: R) extends c { z => d...}; t2) 
        = (let l = new [l: { l =>
            (type Inst = { z => U /\ (/\(m: T')...)});
            (type Tpl = [ z: l.Inst | (/\(m: T')...)]);
            (def tpl(x: R'): l.Tpl)
          } | 
            (type Inst = { z => U /\ (/\(m: T')...)});
            (type Tpl = [ z: l.Inst | (/\(m: T')...)]);
            (def tpl(x: R'): l.Tpl = c' & [ z: l.Inst | d'...])
          ] in t2'


Note: No trSeqDef for the moment because nuDOT only supports methods as members, not lambdas (could encode them, though).

