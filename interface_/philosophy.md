
# Philosophy of the Interface
This interface allows users to reason about attribute grammar
specifications written in Silver.  Its philosophy is twofold:
- The user should be able to reason about the attribute grammars,
  which are extensible, without seeing or needing to know any of the
  details used to encode the extensibility.
- The user should be able to reason about the attribute grammars
  without knowing how the attribute grammars are encoded from Silver
  into Abella.

We discuss each of these goals in turn.




## Goal:  Hiding the Implementation of Extensibility
The view of extensibility in Silver is quite simple, with each
production defining its own equations, resulting in a naturally
modular specification.  In the encoding used for the interface, we
declare (undefined) full relations and define partial component
relations in language components, with the declared full relation
being replaced by a full relation defined by joining the component
relations in the composition.

We want the user to see Silver-type extensibility when reasoning about
grammars.  This means that anything requiring partial relations or
shifting between full and partial relations should not be seen by the
user.  Instead, the interface itself should handle these concerns
behind the scenes.  The only issues related to extensibility the user
should ever see are those which also make sense in the Silver setting.
For example, the user can be told they can't do case analysis on the
structure of a tree, or that they can't examine the equation defining
a certain attribute on a tree when the structure of said tree is not
known.




## Goal:  Hiding the Encoding of Attribute Grammars
We must encode Silver nonterminals, productions, and equations into
Abella types, constants, and relations.  For example, equations from
Silver are encoded as relations in Abella, and we have a relation
requiring all equation relations to hold; the former is quite
different from what we have in Silver, and the latter has no
corresponding Silver structure.  In our Abella encoding, we also
separate the notions of the syntax of a tree, built by productions,
from the nodes holding attributes, a distinction not generally
considered in Silver.

The user ought to see the grammar presented in the same way as it
would be viewed in Silver, as much as possible.  One part of this is
to hide the fact that we split decorated trees into terms and
attribute nodes, instead showing it to the user as one unified tree.
We also want to use syntax familiar to Silver users, such as the
standard attribute access syntax of `t.a`, rather than relational
syntax.  We also want to hide any relations which have no direct
corollary in Silver, such as equation relations or WPD node relations,
which require that all equation relations hold.

Another, rather minor, way in which we would like to present the
grammar as seen in Silver is to provide encodings of Silver's
primitive types without showing how they are encoded.  This lets users
ignore the encoding details and use the syntax with which they are
familiar in Silver.


### Maintaining Abella's Style
One consideration to make in hiding details of encodings and trying to
look like Silver is that we are still essentially working in Abella,
and we want users of Abella to still recognize some of the style of
reasoning in Abella in reasoning with the interface.

Maintaining Abella's style also limits some of what we can do in the
way of presenting the user a Silver-style specification.  For example,
we might like to use attribute accesses as values, such as in `3 +
t.a`, as we do in Silver.  However, attribute access is encoded into
Abella as a relation, which makes using it in this manner difficult.
Therefore we are limited to the formula form of `t.a = X`, where we
may then use `X` in the place of the attribute access, giving us the
expression `3 + X` instead.  Similarly, because we encode operations
on primitive types as relations on the encoded primitive types, we
must write `3 + X = Y /\ Y + 1 = Z` rather than `3 + X + 1 = Z`.  This
is probably beneficial in reasoning, to have to split out each
subexpression into its own premise rather than having one large
expression for an equation as we write in Silver, since we may want to
use values of subexpressions in reasoning.  However, it does somewhat
show that we are using relations to encode them.

We also have `is` relations for primitive types, which we have no
concept of in Silver, but which are part of the style of Abella.
These are necessary for proving theorems about the operations on
primitive types, and thus for using these theorems as well.

These are not serious issues which have a large effect on making the
interface look like, or not look like, Silver, but they should be
noted as limiting somewhat the Silver look of the interface.

