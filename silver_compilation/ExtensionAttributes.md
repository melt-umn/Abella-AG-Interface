
Extension-introduced attributes are similar to host-introduced
attributes, but they introduce some more difficulties with defining
the attributes for other extensions in the composition.




  
# Running Example

Suppose we have an extension `security`.  This extension adds the
following attributes and occurrences (among others):
```
inherited attribute secCtx::[Pair<String Integer>];
synthesized attribute secLevel::Integer;

attribute secCtx occurs on Expr;
attribute secLevel occurs on Expr;
```
This extension does not introduce any new productions.  It defines
these attributes on the host language's productions.

We have a second extension `newEx` which adds the following
productions:
```
abstract production add3
top::Expr ::= e1::Expr e2::Expr e3::Expr
{
  forwards to add(e1, add(e2, e3));
}

abstract production ascribe
top::Expr ::= e::Expr ty::Type
{
  forwards to e;
}
```
It doesn't matter whether these productions define any other
attributes.  We only care that they are from another extension.

Our host language has the following productions for the `Expr`
nonterminal type:
```
abstract production add
top::Expr ::= e1::Expr e2::Expr
{ ... }

abstract production num
top::Expr ::= n::Integer
{ ... }

abstract production name
top::Expr ::= n::String
{ ... }
```
We don't care about any of the semantics introduced by the host
language here.




  
# Access Relations

The access relations are the same for extension-introduced attributes
as for host-introduced attributes.  For our example, we get two access
relations:
```
Type access__secCtx__Expr
        node_Expr -> attrVal (list (pair string integer)) -> prop.
Type access__secLevel__Expr   node_Expr -> attrVal integer -> prop.
```

We are assuming, for our naming scheme, that we will not get
overlapping attribute names from different extensions.  If we decide
not to assume this, we only need to change our naming scheme.  The
ideas remain the same.




  
# Attribute Equations for Extension-Introduced Synthesized Attributes

Our encoding of equations for extension-introduced attributes includes
many of the same ideas as the encoding for host-introduced attributes.

We declare a full equation relation with the appropriate type.  We
follow the same naming scheme as we had for the host language.

We define a component relation for equations on known productions,
both introduced by this extension and introduced by the host language.
Such an equation is encoded the same as for a host-introduced
attribute.  We encode the expression in the equation, then combine
that with accessing the attribute and getting the appropriate value.

We add another component relation as well.  For the `secLevel`
attribute in our example, this would be named
```
secLevel__Expr__copy
```
This relation will only have one clause, a rule for copying the value
from the forward.  This clause goes as follows:
```
secLevel__Expr__copy Term (ntr_Expr Node _) :=
   exists Val ForwardNode,
      access__secLevel__Expr Node (attr_ex Val) /\
      access__forward__Expr
         Node
         (attr_ex (pair_c _ (ntr_Expr ForwardNode _))) /\
      access__secLevel__Expr ForwardNode (attr_ex Val)
```
Here we access the attribute on the current tree, getting a value
`Val`, then we find that the forward exists and `ForwardNode` holds
the values, and that node also contains `Val` for the attribute.  This
is the definition of the assignment
```
top.secLevel = top.forward.secLevel;
```
which is inherently what Silver's forwarding mechanism is doing.

In the composition, we will replace the copy relation with a relation
where `Term` is replaced by a term built by each production introduced
by another extension.  For example, if we compose the host language,
the `security` extension, and the `newEx` extension, we get the
following composed copy relation for `secLevel`:
```
Define secLevel__Expr__copy : nt_Expr -> node_tree -> prop by
   secLevel__Expr__copy (prod_add3 _ _ _) (ntr_Expr Node _) :=
      exists Val ForwardNode,
         access__secLevel__Expr Node (attr_ex Val) /\
         access__forward__Expr
            Node
            (attr_ex (pair_c _ (ntr_Expr ForwardNode _))) /\
         access__secLevel__Expr ForwardNode (attr_ex Val);
   secLevel__Expr__copy (prod_ascribe _ _) (ntr_Expr Node _) :=
      exists Val ForwardNode,
         access__secLevel__Expr Node (attr_ex Val) /\
         access__forward__Expr
            Node
            (attr_ex (pair_c _ (ntr_Expr ForwardNode _))) /\
         access__secLevel__Expr ForwardNode (attr_ex Val).
```
By specializing it in the composition, we ensure it is only used for
productions without an actual equation.

The composed full equation relation will delegate to the component
relation and the composition copy relation.  If another extension
builds on top of this one, it will also delegate to the component
relation from that extension.

The purpose of the having a copy relation separate from the original
relation is that we will have axioms for the proof which let us go
from the full equation relation to the component equation relation,
and having them separate keeps us from using the copy rule on an
invalid equation.

I'm pretty sure this solution of having no restrictions in the
component relation and specializing in the composition is sound
because of the separation of the two relations.  I need to think about
it some more to make sure it doesn't let us prove something in the
component which won't be provable in the composition.



## An Alternative Formulation

An alternative formulation is to define the full relation.  The clause
from the `copy` relation then adds assumptions that the term is not
built from any known production constructors.  For our running
example, the relation would be something like this:
```
Define secLevel__Expr : nt_Expr -> node_tree -> prop by
  secLevel__Expr (prod_add E1 E2)
             (ntr_Expr Node [ntr_Expr E1Node _, ntr_Expr E2Node _]) :=
     ... ;
  secLevel__Expr (prod_num N) (ntr_Expr Node []) := ... ;
  secLevel__Expr (prod_name N) (ntr_Expr Node []) := ... ;
  secLevel__Expr Term (ntr_Expr Node _) :=
     exists Val ForwardNode,
        ((exists E1 E2, Term = prod_add E1 E2) -> false) /\
        ((exists N, Term = prod_num N) -> false) /\
        ((exists N, Term = prod_name N) -> false) /\
        access__secLevel__Expr Node (attr_ex Val) /\
        access__forward__Expr Node
           (attr_ex (pair_c _ (ntr_Expr ForwardNode))) /\
        access__secLevel__Expr ForwardNode (attr_ex Val).
```
Our relation here defines `secLevel` on the three known productions
(we elide the actual definitions), then defines a copy rule.  The copy
rule precludes itself from being used for any of the known productions
and otherwise copies as we had above.

With this scheme, we do not need to specialize the copy rule in the
composition, since we are already limited in how we use it.  We
directly use the defined full relation given above.  However, this
also means that this rule applies in the composition to any production
from any other extension.  This keeps us from defining the attribute
in productions from other extensions which build on top of this one.
For example, if we wanted to build an extension `betterSecurity` on
top of `security`, we would not be allowed to define `secLevel` on any
productions introduced by `betterSecurity`.  This limitation is
because the copy rule would always apply to new productions; we would
still have this limitation even if we built the composed relation by
delegating to component relations.




  
# Attribute Equations for Extension-Introduced Inherited Attributes

We can treat inherited attributes in the same way as synthesized
attributes, but I would like to expand a bit more on why.

We declare a full equation relation with the appropriate type and
define a component relation for equations on known productions.  As in
the host language, these will encode all the equations setting the
attribute on subtrees.

As with synthesized attributes, we have a copy relation with a single
clause which states that both the current tree and its forward have
the same value for the attribute.  For `secCtx`, this is as follows:
```
secCtx__Expr__copy Term (ntr_Expr Node _) :=
   exists Val ForwardNode,
      access__secCtx__Expr Node (attr_ex Val) /\
      access__forward__Expr
         Node
         (attr_ex (pair_c _ (ntr_Expr ForwardNode _))) /\
      access__secCtx__Expr ForwardNode (attr_ex Val)
```
This definition, while the same as if `secCtx` were a synthesized
attribute, now represents assignment in the other direction, from the
current tree to the forward:
```
top.forward.secCtx = top.secCtx;
```
We assign to the forward because this is always implicitly done in
Silver.  Because this rule is to be used for productions from
extensions which are not aware of the attribute, the inherited
attribute will not be assigned on any other trees, and this is the
only rule which will apply.

As with synthesized attributes, we will specialize the copy relation
to the productions on which it applies in the composition.

We have the same alternative formulation for the copy relation for
inherited attributes as for synthesized attributes.





# Note on Copy Relations

Our copy relations are the only relations where the clauses change
between the component definition and the composition.  Every other
relation which we define in a component keeps exactly the same clauses
in the composition.  It is fine for this to change because we are
making it more specific by restricting it to specific productions but
we are not changing its preconditions.

