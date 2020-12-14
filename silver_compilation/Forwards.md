
We will handle forwarding very similarly to how we handle local
attributes.  We can essentially think of the forward as a special kind
of local attribute, and therefore we will draw heavily on the
information in [Locals.md](Locals.md).





# A Running Example

As a running example, we will consider the following Silver attribute
grammar production:
```
abstract production plusEquals
top::Stmt ::= name::String e::Expr
{
  forwards to assign(name, plus(var(name), e));
}
```
We will assume this production is in an extension named `convenience`
and that `Stmt` and `Expr` are host-introduced nonterminals.





# Encoding Accessing the Forward

For attribute access, the forward may be treated as a local
attribute.  The host introduces an access relation for it as it would
for any other attribute it introduces:
```
Type access__forward__Stmt
     node_Stmt -> attrVal (pair nt_Stmt node_tree) -> prop.
```





# Equations for Forwards

The equation is inherently a host-introduced attribute.  Therefore the
host language introduces a declared full relation for it:
```
Type forward__Stmt   nt_Stmt -> node_tree -> prop.
```

Each component which introduces a forwarding production needs to
provide a component relation for the forward equation.  As with local
attributes, we set any known inherited attributes for the forward in
the equation defining the equation.  For our running example, we would
get the following:
```
Define forward__Stmt__convenience : nt_Stmt -> node_tree -> prop by
  forward__Stmt__convenience (prod_plusEquals N E)
                             (ntr_Stmt Node [ntr_Expr ENode ECL]) :=
     exists FwdNode FCL,
        access__forward__Stmt Node
           (attr_ex
              (pair_c (prod_assign N (prod_plus (prod_var N) E))
                      (ntr_Stmt FwdNode FCL))) /\
        wpd_Stmt (prod_assign N (prod_plus (prod_var N) E))
                      (ntr_Stmt FwdNode FCL))) /\
        <setting inherited attributes on the forward>.
```
We determine that the forward has the correct form (an assignment, the
body of which is an addition), that it is well-partially-decorated,
and that its inherited attributes have the appropriate values.

We still need to include an equation in this relation for each
inherited attribute of which we are aware in the current component but
which we do not write an explicit equation for in Silver.  This is
because Silver's behavior is to implicitly insert such copying
equations.

For example, an inherited attribute `ia` which occurs on `Stmt` but
for which we do not provide an inherited attribute for the forward on
the production `plusEquals`, we add an equation to copy its value over
to the forward.  This will add the following to the above clause for
the equation:
```
   access__ia__Stmt FwdNode (attr_ex Val) /\
   access__ia__Stmt Node    (attr_ex Val)
```
We duplicate the entire definitional clause for the case `ia` is not
defined on the current tree, as we did for inherited attributes on
locals:
```
   access__ia__Stmt FwdNode attr_no /\
   access__ia__Stmt Node    attr_no
```

If we add an extension which adds an inherited attribute on an
existant nonterminal, we also need to copy its value over to the
forward on any existing forwarding productions.  For example, if we
add an extension which adds an attribute `new_ia` on the `Stmt`
nonterminal, we need to define the copying of `new_ia` on the
`plusEquals` production to its forward.  We can't add this to the
equation relation defining the forward because that is already set.
Instead, we add this to the component relation which defines `new_ia`
on the `plusEquals` production, along with any equations defining it
on other children.

This aspect production
```
aspect production plusEquals
top::Stmt ::= name::String e::Expr
{
  e.new_ia = top.new_ia;
}
```
from an extension called `newExtension` will give us two clauses in
the component equation relation like the following:
```
  new_ia__Stmt__newExtension (prod_plusEquals N E)
                             (ntr_Stmt Node (ntr_Expr ENode ECL)) :=
    exists Val FwdNode,
      access__new_ia__Stmt Node (attr_ex Val) /\
      access__new_ia__Expr ENode (attr_ex Val) /\
      access__forward__Stmt Node (attr_ex (pair_c _ FwdNode)) /\
      access__new_ia__Stmt FwdNode (attr_ex Val);
  new_ia__Stmt__newExtension (prod_plusEquals N E)
                             (ntr_Stmt Node (ntr_Expr ENode ECL)) :=
    exists Val FwdNode,
      access__new_ia__Stmt Node (attr_ex Val) /\
      access__new_ia__Expr ENode (attr_ex Val) /\
      access__forward__Stmt Node (attr_no);
```
We assign the value of `top.new_ia` to both the `e` child and the
forward, but we need to check the forward exists first.



## An Alternative Formulation for Known Inherited Attributes

An alternative to putting the equations for known inherited attributes
in the relation defining the forward is to include them in the
relation defining the inherited attributes for the forwarding
production, as we do for attributes from further extensions.

I prefer, at least for now, to try to push everything related to the
forward into the relation defining the forward.  That way, if we don't
touch the forward in a proof case, we don't need to even consider that
it exists.  If, instead, we put the forward's inherited attributes
into the relation for defining the inherited attribute, we would end
up duplicating the cases for other equations for that inherited
attribute.  We can see this with `newExtension` above, where we had
two separate clauses for defining `new_ia`, where the only difference
is whether the forward is defined or not.  Regardless of whether we
need the forward for our proof, we must have two cases, with the only
difference being whether the forward is defined.  If we could include
`new_ia` for the forward in the relation defining the forward, we
would not have this problem.



## A Raw Alternative Formulation

This is "raw" as in I just came up with it and haven't thought through
the implications and implementation yet.

Since the forward holds a special place in Silver, we might create a
relation which holds the equations for attributes on the forward, both
ones which are set and ones which are copied.  This relation could be
built by components joined by conjunction, with the full relation
included in WPD.

This would allow us to define all the inherited attributes we need on
the forward without them interfering in (1) defining the structure of
the forward (as we see with defining the forward for `plusEquals`
above) or (2) defining the inherited attributes on other subtrees (as
we see with `new_ia` above).

I want to get some other things done, but I intend to come back to
this to flesh out the details and study its feasibility.  I think it
sounds nicer than my current idea.





# WPD Node Relations

As with other attributes, we include the equation relation for the
forward in the WPD node relation.  Because this is inherently a
host-introduced attribute, it is included in the host WPD node
component relation for each nonterminal, regardless of whether the
host introduces any forwarding productions.





# Composition

In the composition, equation relations for forwards will need to be
mutually-inductive with WPD nonterminal relations, just as equation
relations for local attributes must be.

