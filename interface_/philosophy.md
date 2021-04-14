
# Philosophy of the Interface
This interface allows users to reason about attribute grammar
specifications written in Silver.  It combines two separate
philosophies we might have for such interfaces:
- The specification about which the user is reasoning is encoded
  extensibly, but the encoding of the extensibility is hidden from the
  user.  The proofs are done as if the specification is monolithic.
- The user is reasoning about specifications of attribute grammars,
  but doesn't know how the attribute grammars are encoded into the
  logic.  The proofs are done in a way which looks very similar to
  what one might write if reasoning about an attribute grammar
  directly.
  
We discuss each of these philosophies in turn, along with their
applications to our particular interface for reasoning about Silver
attribute grammars.




## Philosophy:  Hiding the Implementation of Extensibility
To discuss the hiding of the implementation of extensibility, we first
need to discuss what the implementation actually is.  We build
extensible specifications by using declared (undefined) full relations
and defined partial component relations which can only reference full
relations.  In the composition, the declared full relations are
replaced by defined relations which delegate to all the component
relations, which now refer to the defined full relations.

Hiding this implementation requires that component relations not be
seen, only full relations.  If we need to shift between full relations
and component relations, the interface must do it without the user
specifying it.  The only issues the user should ever see related to
extensibility are those which make sense at the object level of the
specification.

Another piece of encoding extensibility is to facilitate doing proofs
in components which will apply to the composition.  The interface
should provide a manner of proving theorems which will allow the
proofs to be appropriately composed in the composition to apply to the
entire composition as well.


### Interface For Silver
The view of extensibility in Silver is quite simple, with each
production defining its own equations, resulting in a naturally
modular specification.  In the encoding into Abella, relations
representing equations and defining well-partially-decorated trees are
encoded extensibly as described above.

We want the user to see Silver-style extensibility when reasoning
about grammars.  Thus, when a user wants to do case analysis on an
attribute equation, the interface applies the appropriate theorem to
move from the full equation relation to the appropriate component
relation for the production building the tree, then does case analysis
on the component relation.  If the tree does not have a known form,
the user is shown an error message.  This is appropriate because it is
part of the limitations of extensibility in Silver, not just the
extensibility encoding, that one cannot examine the equation for an
attribute on a tree which may be built with syntax introduced in an
unknown extension.

We provide a proof method for users to state and prove theorems based
on induction on decorated trees.  In this, the interface determines
the correct inductive statement to make for each known production and
the correct inductive hypotheses to generate, which the user then
proves.  Because of how these proofs are set up by the interface, they
are still valid in the composition.




## Philosophy:  Hiding the Encoding of Attribute Grammars
We must encode nonterminals, productions, and equations from an
attribute grammar into Abella types, constants, and relations.  For
example, equations are encoded as relations in Abella, and we have a
relation requiring all equation relations to hold; the former is quite
different from what we have in a standard attribute grammar, and the
latter has no corresponding structure in attribute grammars.  In our
Abella encoding, we also separate the notions of the syntax of a tree,
built by productions, from the nodes holding attribute values, a
distinction not generally considered in attribute grammars.

The user of the interface ought to see the grammar presented in the
same way as it would be viewed in the context of the attribute grammar
itself as much as possible.  One part of this is to hide the fact that
we split decorated trees into terms and attribute nodes, instead
showing it to the user as one unified tree.  We also want to use
syntax familiar to users of attribute grammars, such as the standard
attribute access syntax of `t.a` rather than the relational syntax.
We also want to hide any relations which have no direct corollary in
the setting of attribute grammars, such as equation relations or
relations for trees being well-partially-decorated.

Another, rather minor, way in which we would like to present the
grammar as a grammar is to provide encodings of the primitive types
without showing how they are encoded.  This lets users ignore the
encoding details which have nothing to do with the grammar and use the
syntax with which they are familiar in attribute grammar setting.


### Maintaining Abella's Style
One consideration to make in hiding details of encodings and trying to
look like an attribute grammar is that we are still essentially
working in Abella, and we want users of Abella to still recognize some
of the style of reasoning in Abella in reasoning with the interface.

Maintaining Abella's style also limits some of what we can do in the
way of presenting the user an attribute-grammar-style specification.
For example, we might like to use attribute accesses as values, such
as in `3 + t.a`, as we do in attribute grammars.  However, attribute
access is encoded into Abella as a relation, which makes using it in
this manner difficult.  Therefore we are limited to the formula form
of `t.a = X`, where we may then use `X` in the place of the attribute
access, giving us the expression `3 + X` instead.  Similarly, because
we encode operations on primitive types as relations on the encoded
primitive types, we must write `3 + X = Y /\ Y + 1 = Z` rather than
`3 + X + 1 = Z`.  This is probably broadly beneficial in reasoning, to
have to split out each subexpression into its own premise rather than
having one large expression for an equation as we normally write,
since we may want to use values of subexpressions in reasoning.
However, it does somewhat show that we are using relations to encode
them.

We also have `is` relations for primitive types, which we have no
concept of in attribute grammars, but which are part of the style of
Abella.  These are necessary for proving theorems about the operations
on primitive types, and thus for using these theorems as well.

These are not serious issues which have a large effect on making the
interface look like, or not look like, an attribute grammar, but they
should be noted as limiting somewhat the attribute-grammar look of the
interface.




## Independence of these Philosophies
These two philosophies are not inherently tied together.  They could
be implemented in different interfaces, or with only one or the other
philosophies used in a system with an extensible attribute grammar.

**Extensibility Without Attribute Grammars:**  
We might write an interface to reason about an extensible system based
on structural operational semantics which hides the extensibility
portion.  This system would implicitly transition between the full and
component relations which define the SOS relations.

**Attribute Grammars Without Extensibility:**  
We might also think of an interface to reason about a monolithic
attribute grammar encoded in Abella.  This would be similar to our
current encoding, but without full and component versions of
relations.  We would, for example, simply have a relation for the
equations for an attribute `a` which would hold clauses defining `a`
on trees built from any production.  The interface would hide the
details of this encoding, but there would be no full and component
relations for it to convert between.

**Extensibility and Explicitly Encoding Attribute Grammars:**  
We could build an interface for reasoning about attribute grammars
which does not hide the encoding of attribute grammars, but which does
hide the extensibility.  This system would transition between full and
partial relations as necessary without the user's knowledge, but still
show the relations for attribute access, attribute equations, and
partial decoration of trees.

**Explicit Extensibility and Attribute Grammars:**  
While more difficult, we might also make an interface which treats
attribute grammars implicitly and extensibility explicitly.  This
would require the user to note the correct component for operations
which rely on knowing the component, such as doing case analysis on an
attribute equation.

