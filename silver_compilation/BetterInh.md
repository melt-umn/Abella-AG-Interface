
A basic encoding of inherited attributes into a relational setting is
described in [BasicEncoding.md](BasicEncoding.md).  As noted there,
this encoding is not ideal in the interactive-proving setting, and we
can do better.

Note that our discussion here will ignore the encoding refinements
from [CompleteEquations.md](CompleteEquations.md).  While those
refinements contribute to the issue with the basic encoding, we can
examine the infelicities without them.  They merely make it easier to
create a compelling example.





# Problems with Encoding

In the basic encoding of inherited attributes, we encode all equations
in a production setting the same inherited attribute on any child
together.  Let us look at a fragment of a basic, contrived grammar:
```
inherited attribute key::Integer;
synthesized attribute val::Integer;

nonterminal Expr;
attribute key occurs on Expr;
attribute val occurs on Expr;

abstract production plus
top::Expr ::= e1::Expr e2::Expr
{
  e1.key = top.key;
  e2.key = top.key;
  top.val = e1.val + e2.val;
}

abstract production ifKey
top::Expr ::= e1::Expr e2::Expr
{
  e1.key = top.key;
  e2.key = if e2.val > 0 then e2.val else 0;
  top.val = e1.val;
}
```
We have a `key` inherited attribute which passes a number down the
tree, and a `val` synthesized attribute passing a number up the tree.
The `plus` production merely passes the `key` down the tree, where the
`ifKey` value is a bit more creative.  For both productions we encode
the equations for `e1.key` and `e2.key` together into single clauses.

For the `plus` production, we get one clause defining the `key`
attribute in the component relation:
```
key__Expr__host (plus E1 E2)
                (ntr_Expr Node [ntr_Expr E1Node _,
                                ntr_Expr E2Node _]) :=
   exists Key,
      access__key__Expr Node (attr_ex Key) /\
      access__key__Expr E1Node (attr_ex Key) /\
      access__key__Expr E2Node (attr_ex Key);
```

However, the `ifKey` production will give us two clauses:
```
key__Expr__host (ifKey E1 E2)
                (ntr_Expr Node [ntr_Expr E1Node _,
                                ntr_Expr E2Node _]) :=
   exists Key Val,
      access__key__Expr Node (attr_ex Key) /\
      access__key__Expr E1Node (attr_ex Key) /\
      access__val__Expr E1Node (attr_ex Val) /\
      greater Val 0 btrue /\
      access__key__Expr E2Node (attr_ex Val);
key__Expr__host (ifKey E1 E2)
                (ntr_Expr Node [ntr_Expr E1Node _,
                                ntr_Expr E2Node _]) :=
   exists Key Val,
      access__key__Expr Node (attr_ex Key) /\
      access__key__Expr E1Node (attr_ex Key) /\
      access__val__Expr E1Node (attr_ex Val) /\
      greater Val 0 bfalse /\
      access__key__Expr E2Node (attr_ex 0);
```
Both clauses encode the same value for `e1.key` because there is only
one possibility.  We only need two clauses because of the branching in
the `e2.key` equation.

If we wish to examine the ways in which `e1.key` can be set in a tree
built by the `plus` production, we end up also looking at the ways in
which `e2.key` can be set.  Since there is only one way in which each
can be done, this doesn't have much effect.

However, if we wish to examine the ways in which `e1.key` can be set
in a tree built by the `ifKey` production, we end up also looking at
the ways in which `e2.key` can be set.  Note that we set the `val`
attribute in the `ifKey` production:  it only depends on `e1.val`.  If
we are trying to prove something about the `val` attribute, we
probably only care about the single way we can set `e1.key`.  However,
the bundling of the `e1.key` and `e2.key` equations makes us do the
same proof twice due to differences which we know cannot affect the
proof.

Even in the case of the `plus` production where we do not get extra
cases from the bundling, doing case analysis on the equation setting
`e1.key` can be confusing for the user because it reveals information
about the equation for `e2.key` which he did not request.

Clearly the best situation would be for case analysis on one equation
to examine only that one equation.  This can result in more efficient
proof effort, since we don't get extraneous cases based on irrelevant
information, and clearer situations for the prover by not revealing
information he need not consider.





# Non-Bundled Encoding of Inherited Attribute Equations

In forming a non-bundled encoding, we need to take care that we still
end up requiring all equations for all children to hold.  One approach
which springs to mind, but which is incorrect, would be to encode each
equation into its own clause in the component equation relations.  The
problem with this is that it would require *one of* the equations for
`e1.key` or `e2.key` to hold for the above productions, but not both.

Rather, to avoid bundling but still have all equations required to
hold, we need to have a separate equation relation for each equation.
We then require all these relations, which we shall refer to with the
pithy moniker *inherited attribute child equation relations*,
sometimes shortened to *child equation relations* since they only make
sense to have for inherited attributes.



## Encoding Child Equation Relations

We define a separate inherited attribute child equation relation for
each attribute and each child in a production.  The relations have not
only the attribute name and nonterminal, but also the production and
index of the child to correctly identify them.

For the `ifKey` production, we would get the following two relations,
the first defining `e1.key` and the second defining `e2.key`:
```
Define key__Expr__ifKey__child1 : Expr -> node_tree -> prop by
   key__Expr__ifKey__child1 (ifKey E1 E2)
                            (ntr_Expr Node [ntr_Expr E1Node _,
                                            ntr_Expr E2Node _]) :=
      exists Key,
         access__key__Expr Node (attr_ex Key) /\
         access__key__Expr E1Node (attr_ex Key);
   key__Expr__ifKey__child1 Tree NodeTree :=
      (exists E1 E2, Tree = ifKey E1 E2) -> false.

Define key__Expr__ifKey__child2 : Expr -> node_tree -> prop by
   key__Expr__ifKey__child2 (ifKey E1 E2)
                            (ntr_Expr Node [ntr_Expr E1Node _,
                                            ntr_Expr E2Node _]) :=
      exists Val,
         access__val__Expr E1Node (attr_ex Val) /\
         greater Val 0 btrue /\
         access__key__Expr E2Node (attr_ex Val);
   key__Expr__ifKey__child2 (ifKey E1 E2)
                            (ntr_Expr Node [ntr_Expr E1Node _,
                                            ntr_Expr E2Node _]) :=
      exists Val,
         access__val__Expr E1Node (attr_ex Val) /\
         greater Val 0 bfalse /\
         access__key__Expr E2Node (attr_ex 0);
   key__Expr__ifKey__child2 Tree NodeTree :=
      (exists E1 E2, Tree = ifKey E1 E2) -> false.
```
We include not only the definitions of the equations, but also one
other clause.  This extra clause, which requires nothing of the
attribute, holds if the tree is *not* the production for which we are
defining an equation.  Because we need these relations to hold on all
trees, we need to have a way for them to hold on trees built by other
productions.

Note that we simply have these child equation relations, not full and
component versions of them.  This is because each one is based on a
single equation in a single production, and the equation cannot be
extended in further language extensions.

Each language component defines these child equation relations for
each inherited attribute equation on a child.  It also produces a
component equation relation for the inherited attributes.  However,
the component relation is no longer a series of clauses defining
different equations on different productions.  Rather it is defined as
a conjunction of the child equation relations, similar to the
construction of the WPD node component relations.  For the above
grammar, the `key` component equation relation would be as follows:
```
Define key__Expr__host : Expr -> node_tree -> prop by
   key__Expr__host Tree NodeTree :=
      key__Expr__plus__child1 Tree NodeTree /\
      key__Expr__plus__child2 Tree NodeTree /\
      key__Expr__ifKey__child1 Tree NodeTree /\
      key__Expr__ifKey__child2 Tree NodeTree /\
      ...
```
All the other productions would also include their child equation
relations at the end.

The component equation relation is not strictly necessary here, as the
WPD node component relations are not strictly necessary.  However,
they both make the composition easier by bundling up all the relevant
relations from the language component, so we include them.



## Composition

In the language composition, we need to produce a full equation
relation for each inherited attribute.  This is built as the
conjunction of the component relations, in the same manner as the
full WPD node relation is built in the composition.  If we are
composing grammars `host`, `a`, and `b`, the full relation for the
`key` attribute would be as follows:
```
Define key__Expr : Expr -> node_tree -> prop by
   key__Expr Tree NodeTree :=
      key__Expr__host Tree NodeTree /\
      key__Expr__a Tree NodeTree /\
      key__Expr__b TreeNodeTree.
```

The conjunction in the composition and the conjunctions in the
component relations ensure that all the child equation relations are
required to hold, so we have all equations hold.

This modification of the encoding does not change anything in the
encoding of other pieces, such as the WPD relations.



## Forwards and Local Attributes

We can use this scheme in the encoding of inherited attributes on
forwards and local attributes.  Rather than encode the inherited
attributes as part of the equation relation defining the forward or
local, we can define child equation relations for them as well.  The
"indices" on such relation are `forward` or `local__foo` so we can
identify on which tree they are intended to be setting the attribute.
This is a cleaner encoding for forwards and locals for the same
reasons it is a cleaner encoding for inherited attributes on children.

We must also define full and component relations for inherited
attributes on these.  These relations are not for a single attribute,
but for a single tree on which attributes are set.  We would need a
full relation `forward__Expr__inhs` for the inherited attributes on
the forward of expressions, for example, and we would have a component
relation in each language component bundling up the equations for all
inherited attributes set on all forwards in that component.  These
full relations need to be included in the WPD node component relation
as well so they are required to hold on all well-partially-decorated
trees.

Another benefit of this encoding is that we are no longer bound to
have local attributes fully defined with all their inherited
attributes in a single component.  We can have production attributes,
since their inherited attributes can be set individually.

