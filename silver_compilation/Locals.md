
We will handle local attributes very similarly to how we handle any
other attribute.





# A Running Example

As a running example, we will consider the following Silver attribute
grammar:
```
inherited attribute evalctx::[Pair<String Integer>];
synthesized attribute evalctx_out::[Pair<String Integer>];
synthesized attribute bval::Boolean;

nonterminal Stmt;
attribute evalctx occurs on Stmt;
attribute evalctx_out occurs on Stmt;

nonterminal BExpr;
attribute evalctx occurs on BExpr;
attribute bval occurs on BExpr;

abstract production while
top::Stmt ::= cond::BExpr body::Stmt
{
  cond.evalctx = top.evalctx;
  body.evalctx = top.evalctx;
  local subWhile::Stmt = while(cond, body);
  subWhile.evalctx = body.evalctx_out;

  top.evalctx_out = if cond.bval
                    then subWhile.evalctx_out
                    else top.evalctx;
}
```





# Encoding Accessing Local Attributes

A local attribute with a nonterminal type is stored as a pair of a
term structure and a `node_tree`.  Our naming scheme is a bit
different for local attributes than for standard attributes.  Recall
that, for standard attributes, our naming scheme is
```
access__<attr name>__<nonterminal name>
```
For local attributes, we need to make sure the access name doesn't
overlap with any standard attributes, and we need to make sure the
access name doesn't overlap if we have local attributes with the same
name in different productions.  To do this, we use the following
naming scheme:
```
access__<production name>__local_<attr name>__<nonterminal name>
```
For the local attribute `subWhile`, our access relation would be
```
Type access__while__local_subWhile__Stmt
     node_Stmt -> attrVal (pair nt_Stmt node_tree) -> prop.
```

If the local is not of a decorable type, we would not have a pair, but
the access relation would otherwise be the same.

Assuming the Silver grammar being encoded has been typechecked, no
other productions can be accessing this particular local.  That means
it is safe to make it available in any production, since no other
production's equations will access it.





# Attribute Equations for Local Attributes

The equation relations for local attributes are fairly similar to the
equations for synthesized attributes.  However, the equation relation
not only needs to define the attribute, but also any inherited
attributes which are defined on the local attribute.

Why do we define the inherited attributes in the equation for the
local rather than in the equation for the inherited attribute?  There
are two reasons why this is the correct choice:
1. We would need separate clauses in the equation relation for the
   inherited attribute depending on whether the local is defined or
   undefined, while all the rest of the pieces of the clause would
   remain the same.
2. We can be consistent with where the inherited attributes for locals
   are defined this way.  If we introduce a local in an extension and
   define a host inherited attribute on it, the equation for that goes
   with the local attribute's definition relation.  Otherwise, we
   would have some local attributes having their inherited attributes
   defined with their forms and others having their local attributes
   defined with the inherited attribute equation relations.

Because each local only occurs on one production, we can give the full
relation as a defined relation in the component.  We do not need to
use component relations to build it because only the component
introducing it can do anything with the particular local.

The equation for the `subWhile` local from above would be as follows,
with two clauses:
```
Define while_local_subWhile : nt_Stmt -> node_tree -> prop by
  while_local_subWhile (prod_while Cond Body)
                       (ntr_Stmt Node [ntr_BExpr CondNode _,
                                       ntr_Stmt BodyNode _]) :=
     exists LocNode LocCL ECtx,
        access__while__local_subWhile__Stmt Node
           (attr_ex (pair_c (prod_while Cond Body)
                            (ntr_Stmt LocNode LocCL))) /\
        wpd_Stmt (prod_while Cond Body) (ntr_Stmt LocNode LocCL) /\
        access__evalctx__Stmt LocNode (attr_ex ECtx) /\
        access__evalctx_out__Stmt BodyNode (attr_ex ECtx);
```
There are four conjuncts in the body of this first clause:
1. We access the local on the root's node, getting its structure
   (equal to the root's structure for this local) and its `node_tree`,
   which has the appropriate form for a tree of type `Stmt`.
2. We require the structure of the local attribute associated with its
   `node_tree` to be well-partially-decorated.
3. We access the `evalctx` inherited attribute on the local and ensure
   it has a value.
4. We access the `evalctx_out` synthesized attribute on the body of
   the root and ensure it has the same value as the value being
   assigned into the `evalctx` attribute on the local.
```
  while_local_subWhile (prod_while Cond Body)
                       (ntr_Stmt Node [ntr_BExpr CondNode _,
                                       ntr_Stmt BodyNode _]) :=
     exists LocNode LocCL,
        access__while__local_subWhile__Stmt Node
           (attr_ex (pair_c (prod_while Cond Body)
                            (ntr_Stmt LocNode LocCL))) /\
        wpd_Stmt (prod_while Cond Body) (ntr_Stmt LocNode LocCL) /\
        access__evalctx__Stmt LocNode attr_no /\
        access__evalctx_out__Stmt BodyNode attr_no.
```
The second clause has the same first two conjuncts (it describes the
same term structure, with a well-partially-decorated tree), but the
`evalctx` attribute on the local has no value and neither does the
`evalctx_out` attribute.  We need this second clause because the local
`subWhile` can still be defined even if its `evalctx` inherited
attribute is not defined.  We do this with all combinations of the
inherited attributes which are defined on the local (e.g. if we have
inherited attributes `a` and `b`, we will have clauses for both `a`
and `b` being assigned, `a` being assigned and `b` being undefined,
`a` being undefined and `b` being assigned, and both being undefined).
In use for proofs, since locals tend to be used for one thing, the
inherited attributes being assigned onto a local are generally going
to exist or not exist together, so most of the rules won't be used.

If the local attribute does not have any inherited attributes defined
on it, we, of course, do not need to include anything for defining
inherited attributes.  However, if the local has a nonterminal type,
we still must include the WPD requirement, since we treat all terms as
inherently-decorated trees (e.g. its pretty print attribute will still
be accessible, even if it has no inherited attributes).

We might consider defining any inherited attributes we know about but
which we do not define on the local to have value `attr_no` (not
exist).  For example, if we have an inherited attribute `tyCtx` for
typing, we would add the following to both clauses of the equation
relation from above:
```
   access__tyCtx__Stmt LocNode attr_no
```
This lets us show the attribute *does not* have a value on the local.
Leaving this out allows it to have any value.  This may not matter,
particularly if the grammar has passed MWDA, since it can't influence
any attributes which are accessed on the local.  Passing MWDA appears
to be necessary regardless for our encoding, since we are not doing
anything about the values of attributes from unknown extensions and
their values on the local.  If MWDA passes for all components, they
are irrelevant to any attributes the current component can be
accessing on its local.





# WPD Node Relations

The equation relation for a local attribute goes into the WPD node
relation just as any other equation relation does.  For the `Stmt`
nonterminal above, our WPD node relation for the host would be:
```
Define wpd_node_Stmt__host : nt_Stmt -> node_tree -> prop by
  wpd_node_Stmt__host Tree Ntr :=
    evalctx__Stmt Tree Ntr        /\
    evalctx_out__Stmt Tree Ntr    /\
    while_local_subWhile Tree Ntr.
```
Building the full relation is not affected by the inclusion of local
attributes.





# Composition

In the composition, equations for local attributes will reference WPD
nonterminal relations.  These, in turn, will reference WPD node
relations.  These will then reference the equations for local
attributes.  Therefore all three of these types of relations will need
to be defined mutually-inductively in the composition.  This is what
will give us that local attributes are inductively-smaller than our
original tree as well, so this is necessary, not something we want to
get rid of.

