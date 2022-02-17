
We want to encode Silver grammars into Abella so we can reason about
their properties.  There are several pieces in this encoding,
essentially all of which interact with each other:
* We need to translate nonterminals into Abella types
* We need to translate productions into Abella constructors of the
  appropriate types.
* We need to encode equations into definitional clauses for relations,
  which requires encoding Silver expressions into logical expressions
  in Abella.
* We need to define WPD (well-partially-decorated) relations for each
  nonterminal on which we have any attributes, which depends on the
  attributes included on it.
  
A lot of the ideas in this encoding are not specific to Abella and
could be used to encode attribute grammars in any relational system.
While the code shown will be for Abella, all the ideas should be
applicable in other relational systems as well.

This document will cover a basic encoding.  Other documents will
contain details for encoding more complex portions of the attribute
grammar.

Please note that all naming schemes in this document are subject to
change.  In particular, I might do something like adding a dollar sign
to the front of each generated name so the user, using the interface,
can't override the names.





# A Running Example

As a running example, we will consider the following Silver attribute
grammar as a host language:
```
inherited attribute ctx::[Pair<String Integer>];
synthesized attribute val::Integer;

nonterminal Expr;
attribute ctx occurs on Expr;
attribute val occurs on Expr;

abstract production num
top::Expr ::= n::Integer
{
  top.val = n;
}

abstract production plus
top::Expr ::= e1::Expr e2::Expr
{
  e1.ctx = top.ctx;
  e2.ctx = top.ctx;
  top.val = e1.val + e2.val;
}

abstract production name
top::Expr ::= n::String
{
  top.val = lookup(top.ctx, n);
}

abstract production let
top::Expr ::= n::String e1::Expr e2::Expr
{
  e1.ctx = top.ctx;
  e2.ctx = [pair(n, e1.val)] ++ top.ctx;
  top.val = e2.val;
}

function lookup
Integer ::= ctx::[Pair<String Integer>] n::String
{
  return if fst(head(ctx)) == n
         then snd(head(ctx))
         else lookup(tail(ctx), n);
}
```





# Encoding Nonterminals and Productions

In a typed relational setting, such as Abella, we want to create a
type for each nonterminal in the attribute grammar.  For each
(abstract) production, we want to define a constructor of the
appropriate type.

For our grammar above, we would have the following types and
constructors in an Abella encoding:
```
Kind nt_Expr   type.

Type prod_num   integer -> nt_Expr.
Type prod_plus   nt_Expr -> nt_Expr -> nt_Expr.
Type prod_name   string -> nt_Expr.
Type prod_let   string -> nt_Expr -> nt_Expr -> nt_Expr.
```
Assume here that Silver `Integer`s are encoded into an Abella type
`integer` and Silver `String`s are encoded into an Abella type
`string`.



  

# Encoding Decorated Trees

There are two aspects to building a decorated tree:  one is the
encoding of the attributes for a single production in a tree, and the
other is how to connect these for all the productions in a tree to
build the decorated tree itself.  We look at each in turn.



## Holding Attributes for a Single Production

Our decorated trees will store their attribute values in a separate
node.  Each nonterminal type gets its own node type.  In Abella, for
our grammar above, we would have the node type
```
Kind node_Expr   type.
```
If we had another nonterminal type, it would have its own node type as
well.

Some encodings of attribute grammars from previous work have stored
attribute values in the constructor for each production instead
(e.g. `prod_num` would have arguments for `ctx` and `val` as well as
for its child integer).  I don't think that is a good idea for
extensible languages, since then the production constructors would
need to change with each extension added in.

With a separate node type, which, as we will discuss below, we only
intend to access values out of using relations for that purpose, we do
not have this extensibility problem.  In reasoning about the grammar,
we can ignore any details about the node.  While not necessary, since
the access relations will hide the details, we can leave the node type
abstract (no constructor) in each component, then build a constructor
for it in the composed language which actually holds the attribute
values.

It would also be possible to have a constructor in each component
which is simply replaced in a larger composition by a new one to hold
all attributes introduced by all extensions, since we will have
abstracted the details of the node out of the definitions and
reasoning process.

Because we intend to make the node concrete in the composition, we
could use this encoding to translate a Silver attribute grammar into a
relational system such as Prolog to evaluate a tree in the composed
grammar.  We will discuss the structure of nodes in the composition in
the next section.



## Structure of a Decorated Tree

We will create a type for trees of nodes holding attribute values,
with a constructor for each nonterminal type which will let us build a
tree of nodes.

Our Abella type for trees of nodes is
```
Kind node_tree   type.
```
For each nonterminal in the grammar, we create a constructor for this
type.  This constructor will hold the node for the root of the tree
and a list of the trees of nodes for the children.  For the `Expr`
nonterminal from our running example, this would be
```
Type ntr_Expr   node_Expr -> list node_tree -> node_tree.
```

If we have a term `prod_plus A B`, we would have a decorated tree
```
ntr_Expr PlusNode [ntr_Expr ANode AChildren, ntr_Expr BNode BChildren]
```
Here `PlusNode` holds the attributes for the tree rooted in the `plus`
production, `ANode` and `BNode` hold the attributes for the roots of
`A` and `B` respectively, and `AChildren` and `BChildren` hold the
decorated trees for the children of `A` and `B`.

The decorated tree for a term `prod_num N` would be
```
ntr_Expr NumNode []
```
where `NumNode` holds the attribute values for the tree rooted in the
`num` production.  Because it does not have any children of a
nonterminal type, it has an empty child list.

Why don't we have separate `node_tree` constructors for each
production?  That would enforce the number of children in the child
list.  However, we would not be able to get at the node holding
attributes so easily for the children.  With `prod_plus` above, our
current encoding allows us to grab the nodes for the children to
access attribute values without caring about the structure of the
children, a necessity for our extensible setting.

We will have relations later which check that a pair of a term and a
decorated tree are well-formed, ensuring that we have the right number
of children in the decorated tree for the production in the node tree,
so this is enforced in our scheme even though it is not enforced by
the type system.



  

# Encoding Attribute Access

To get attributes off our trees, we only need to know the type on
which we are accessing the attribute and the attribute's name, not the
production with which it is associated.  This is because we have a
node type for each nonterminal, not differentiated for each
production.

For each occurs declaration, we create an accessor relation on a node
with the appropriate result type.  A wrinkle in this is that we may or
may not have a value on a particular decorated tree.  To handle this,
we introduce a new type with two constructors:
```
Kind attrVal   type -> type.
Type attr_ex   A -> attrVal A.
Type attr_no   attrVal A.
```
This is a standard `option`/`Maybe` type.  We need to introduce it
since Abella has nearly no types built in, so I am naming it for its
purpose of determining whether an attribute value *ex*ists or does
*no*t exist.  It has an associated `is` relation which takes a
subrelation as an argument:
```
Define is_attrVal : (A -> prop) -> attrVal A -> prop by
  is_attrVal SubRel attr_no;
  is_attrVal SubRel (attr_ex V) := SubRel V.
```

With this type in mind, we can encode the declarations of attributes
and their occurrences from our running example into Abella:
```
Type access__ctx__Expr
        node_Expr -> attrVal (list (pair string integer)) -> prop.
Type access__val__Expr   node_Expr -> attrVal integer -> prop.
```
If, say, `val` occurred on another nonterminal `Foo`, we would also
have an accessor for `val` on `node_Foo`s.  Note that we don't care
about whether attributes are inherited or synthesized here, only their
occurrences and their types.  Each node type will hold all attributes
of a tree, inherited or synthesized.

We give these access relations without any definition (using `Type`
instead of `Define` in Abella).  This is because we are leaving the
node types abstract.  If we change that, these should change to pull
the appropriate values out of the constructor.



## Node Constructors and Attribute Access in Composition

Now that we have the `attrVal` type, we can define what constructors
for the node types in the composition will look like.  Each node type
will have a single constructor, this constructor having an argument
for each attribute which occurs on it.  For our running example, if no
extension included in the composition adds more attributes, our
constructor for `node_Expr` would be
```
Type node_Expr_c
   attrVal (list (pair string integer)) -> attrVal integer ->
   attrVal (pair Expr node_tree) -> node_Expr.
```
The arguments are
* the `ctx` attribute
* the `val` attribute
* the forward, which we will discuss in detail in a separate document
  dedicated to handling the forward and forwarding.

With concrete nodes, our accessors for `ctx` and `val` become defined
relations which access the appropriate argument:
```
Define access__ctx__Expr :
     node_Expr -> attrVal (list (pair string integer)) -> prop by
  access__ctx__Expr (node_Expr_c Ctx _ _) Ctx.

Define access__val__Expr : node_Expr -> attrVal integer -> prop by
  access__ctx__Expr (node_Expr_c _ Val _) Val.
```

An alternative formulation would be to have separate constructors for
all possible combinations of attributes which have values and don't
have values, leaving out the attributes which don't have values.  For
example, with `ctx` and `val` (ignoring the forward), we would have
four constructors:
```
Type node_Expr_ctx_val
   list (pair string integer) -> integer -> node_Expr.
Type node_Expr_ctx   list (pair string integer) -> node_Expr.
Type node_Expr_val   integer -> node_Expr.
Type node_Expr__   node_Expr.
```
The access relations would have a clause for each of these, giving
`attr_ex` and `attr_no` depending on whether the node constructor
included a value for the attribute being accessed or not.

I don't like this approach.  Not only is there the exponential
blow-up, but it seems less faithful in spirit to Silver, where we have
a node which either has an attribute value or doesn't, but all
nonterminals really have the same "node constructor" underneath.  In
the end, however, it doesn't really matter which node scheme we use,
since all the details should be hidden by only using the access
relations to get attributes out.





# Encoding Primitive Types

The representation of primitive types is the part of our scheme which
is most dependent on the language into which we are encoding.  Abella
doesn't have many built-in types; therefore, to use Abella, we need to
encode our own.  However, if we were encoding into Prolog, we would be
able to use its integers for our integers.

**Boolean**:  We can create a type for Booleans and two constants for
true and false:
```
Kind Bool   type.
Type btrue   Bool.
Type bfalse  Bool.
```

**Integer**:  Integers can be handled as unary natural numbers wrapped
in a positive/negative constructor:
```
Kind nat   type.
Type zero   nat.
Type succ   nat -> nat.

Kind integer   type.
Type posInt   nat -> integer.
Type negSuccInt   nat -> integer.
```
We can then define addition and other operations on them as relations
in the standard way.

We can think of encoding other primitive types (and quasi-primitive
types) from Silver into Abella as well.  These are discussed in a
separate document.





# Encoding Expressions

We have a relation **encode** which has four arguments:
* an environment assigning Abella terms to variable names
* a Silver expression
* a set/list of Abella clauses into which it translates
* the variable which holds the result of the translation in the Abella
  encoding

The environment tells us how to translate variables.  In a well-typed
grammar, we should always have a binding in the environment for a
variable when we encounter it to encode.  We need the variable holding
the result to use the result in the next computation, and we would not
have access to the result without this.

I am going to be imprecise in how I write these rules in a few ways
which I believe are clearer to read than absolute precision would be:
* I will use a set of clauses directly to represent mapping over it.
  For example, if we have `encode e el x` and write `el /\ x = btrue`,
  that means mapping over all the clauses in `el` and using
  conjunction to add the condition `x = btrue`.
* I will write that variables are equal to other variables or to
  values.  This could be replaced by substituting into already-encoded
  clauses to replace a variable with the thing to which it is equal.
* I will not concern myself with avoiding reusing the same variable
  name.  This is something an implementation needs, but I'll just
  assume names are new in a rule when I want to use them.


**If-Then-Else:**
```
encode Env c cl xc
encode Env th thl xth
encode Env el ell xel
----------------------------------------
encode Env
       (if c then th else el)
       [cl /\ xc = btrue /\ thl /\ x = xth,
        cl /\ xc = false /\ ell /\ x = xel] x
```


**Addition (and other defined operations):**
```
encode Env t1 l1 x1
encode Env t2 l2 x2
----------------------------------------
encode Env (t1 + t1) [l1 /\ l2 /\ plus x1 x2 x] x
```
We can replace `plus` here with the appropriate relation for the
operation and for the type of the operands.  This rule should
translate the arithmetic operations as well as numeric comparison
operators, and generally any defined relation.


**Conjunction:**
```
encode Env t1 l1 x1
encode Env t2 l2 x2
----------------------------------------
encode Env (t1 && t2)
       [l1 /\ x1 = btrue /\ l2 /\ x = x2,
        l1 /\ x1 = bfalse /\ x = bfalse] x
```
Conjunction and disjunction could be defined as relations over
Booleans, as we are defining numeric operations.  However, since they
are short-circuiting operations, we cannot define them as relations on
two values, since that would require both values to exist.  As an
example, consider the Silver expression `t.a && t.b`.  If `t.a` is
`false`, Silver will never demand `t.b`.  Encoding conjunction as a
relation in Abella would require the value of `t.b` regardless of the
value of `t.a`, so the short-circuiting operations need to be encoded
directly.


**Disjunction:**
```
encode Env t1 l1 x1
encode Env t2 l2 x2
----------------------------------------
encode Env (t1 || t2)
       [l1 /\ x1 = btrue /\ x = x1,
        l1 /\ x1 = bfalse /\ l2 /\ x = x2] x
```


**Attribute Access:**
```
encode Env t tl tx
tree_type t tau
----------------------------------------
encode Env (t.a)
       [tl /\ tx = pair_c structure node /\
        attr_access__a__tau node (attr_ex x)] x
```


**Let:**
```
encode Env t1 l1 x1
encode ((y,x1)::Env) t2 l2 x2
----------------------------------------
encode Env (let y::tau = t1 in t2)
       [l1 /\ y = x1 /\ l2] x2
```


**Variable:**
```
(x, e) in Env
----------------------------------------
encode Env x [x = e] x
```


**Equality Check:**
```
encode Env t1 l1 x1
encode Env t2 l2 x2
----------------------------------------
encode Env (t1 == t2)
       [l1 /\ l2 /\ x1 = x2 /\ x = btrue,
        l1 /\ l2 /\ x1 <> x2 /\ x = bfalse] x
```


**Decorate:**
```
encode Env t tl tx
encode Env eqs eql
tree_type t tau
----------------------------------------
encode Env (decorate t with {eqs})
       [tl /\ eql /\ tx = pair_c T _ /\ wpd_tau T Node /\
        x = pair_c T Node] x
```
We will explain the use of `wpd_tau` later.  We are abusing notation
here to encode the equations contained in the `decorate` expression.
What this does is, for each equation `i=e`, we do `encode Env e el
ex`, then add `el /\ access__i__tau Node ex` to the clauses for all
the equations.  For example, for the decorating equations
`{i1 = 3; i2 = 3 + 4;}`, we get something like
```
access__i1__tau Node 3 /\ plus 3 4 x /\ access__i2__tau Node x
```




  
# Attribute Equations for Host-Introduced Attributes

We discuss here our scheme for encoding equations for host-introduced
attributes.  We will need a modification of this scheme for
extension-introduced attributes, which we will discuss in another
document.

For each occurs declaration, we need a relation to show that the
equation for the attribute holds on the root node.  This relation
needs to be extensible, so in Abella we will have defined relations
for each component and a declared relation for the full relation.
These relations relate a syntactic structure and a `node_tree` which
holds the attribute values for the syntactic structure.

The component relation has one or more clauses for each production.
These clauses encode the appropriate equation(s) in each production.
We might get multiple clauses for a single equation due to branching
in the equation's expression.  Each clause relates a syntactic
structure and a node tree, with a precondition.

The component relations for **synthesized** attributes encode a single
equation branch in each clause for a particular production.  If an
equation does not branch (e.g. `t.a = c1.a + c2.a`), only a single
clause will be generated for that production in the component
relation.  If a production does not have an equation for a particular
synthesized attribute, we do not need to insert a clause for it.

The component relations for **inherited** attributes encode all
equations setting the inherited attribute for children together.  If a
production has two children on which it sets an inherited attribute
`ia`, it will encode both equations together into a single clause.
The purpose of the equation relations is to ensure that the attributes
in a decorated tree obey the equations given for them, so we need to
encode all the equations.  If the equations for inherited attributes
branch, we need to encode the Cartesian production of the clause sets
for all the equations.  If a production does not have an equation for
a particular inherited attribute, we still create a definitional cause
for the production in the component relation, but without a body.
This means that the set of equations is vacuously satisfied, since
there are no equations.

We can end up defining equation relations for inherited attributes
which don't occur on a nonterminal, but which occur on its children,
if it sets the inherited attributes on them.  For example, we commonly
have a `Root` nonterminal in Silver which wraps a top-level construct
in the language.  This `Root` does not have inherited attributes occur
on it, but sets the appropriate inherited attributes for its child,
such as an attribute `env` for the environment.  Thus we need an
equation relation for `env` for `Root` to capture this equation.

In systems where relations are assumed to be extensible, such as
Prolog, we don't need to have declared full equation relations and
defined component equation relations.  We can simply define the
clauses which go into the component relation in Abella directly as
clauses of the full relation.

If we have an equation or equations to encode, the precondition is the
encoding of the equation's expression (`el` in `encode Env e el ex`
where `Env` contains bindings for the root and children and any local
attributes) joined with accessing the attribute and getting its value
as `ex` (`access__attrname__nonterminal Node (attr_ex ex)`).  This
shows that `ex`, the result of the equation`s expression, is the value
of the attribute being defined.

For our running example, we will generate two full equation relations:
```
Type ctx__Expr   nt_Expr -> node_tree -> prop.
Type val__Expr   nt_Expr -> node_tree -> prop.
```
We will also generate a defined component relation for each attribute,
which would look something like this (which might be cleaner than what
`encode` would give us):
```
Define val__Expr__host : nt_Expr -> node_tree -> prop by
  val__Expr__host (num N) (ntr_Expr Node nil) :=
     access__val__Expr Node (attr_ex N);
  val__Expr__host (plus E1 E2)
                  (ntr_Expr Node [ntr_Expr E1Node _,
                                  ntr_Expr E2Node _]) :=
     exists PlusResult E1Val E2Val,
        access__val__Expr Node (attr_ex PlusResult) /\
        access__val__Expr E1Node (attr_ex E1Val) /\
        access__val__Expr E2Node (attr_ex E2Val) /\
        plus E1Val E2Val PlusResult;
  val__Expr__host (name N) (ntr_Expr Node nil) :=
     exists V Ctx,
        access__val__Expr Node (attr_ex V) /\
        access__ctx__Expr Node (attr_ex Ctx) /\
        function_lookup Ctx N V;
  val__Expr__host (let N E1 E2)
                  (ntr_Expr Node [ntr_Expr E1Node _,
                                  ntr_Expr E2Node _]) :=
     exists V,
        access__val__Expr Node (attr_ex V) /\
        access__val__Expr E2Node (attr_ex V).

Define ctx__Expr__host : nt_Expr -> node_tree -> prop by
  ctx__Expr__host (num N) (ntr_Expr Node nil);
  ctx__Expr__host (plus E1 E2)
                  (ntr_Expr Node [ntr_Expr E1Node _,
                                  ntr_Expr E2Node _]) :=
     exists C,
        access__ctx__Expr Node (attr_ex C) /\
        access__ctx__Expr E1Node (attr_ex C) /\
        access__ctx__Expr E2Node (attr_ex C);
  ctx__Expr__host (name N) (ntr_Expr Node nil);
  ctx__Expr__host (let N E1 E2)
                  (ntr_Expr Node [ntr_Expr E1Node _,
                                  ntr_Expr E2Node _]) :=
     exists C V L,
        access__ctx__Expr Node (attr_ex C) /\
        access__ctx__Expr E1Node (attr_ex C) /\
        access__val__Expr E1Node (attr_ex V) /\
        append [pair_c N V] C L /\
        access__ctx__Expr E2Node (attr_ex L).
```
We can see here how we add the access for the attribute being defined
as the result of the expression in the equation.  We can also see how
we combine the two equations for `ctx` on the `plus` production to
form one clause in the component relation, as well as how we have a
clause with no preconditions for `ctx` with `num` and `name` because
they do not define `ctx` on any trees.

This implementation of inherited attributes works fine for animating.
However, for interactive proofs it is less than ideal due to the
bundling of separate equations together.  The reasons this is
undesirable in the interactive-proof setting and a better encoding is
described in [BetterInh.md](BetterInh.md).



## Composing Equation Relations

In the composition, we will build the full equation relations in our
normal extensible fashion; that is, the full relation will delegate to
the component relations.

For `ctx__Expr`, if we have the host and extensions `E1` and `E2`
(with component relations `ctx__Expr__E1` and `ctx__Expr__E2`), we
will define the full equation relation in the composition in Abella to
replace the declared full relation as follows:
```
Define ctx__Expr : nt_Expr -> node_tree -> prop by
   ctx__Expr E Nt := ctx__Expr__host E Nt;
   ctx__Expr E Nt := ctx__Expr__E1 E Nt;
   ctx__Expr E Nt := ctx__Expr__E2 E Nt.
```
This isn't an inductive relation, so we don't need to combine the
definitions, as we will have to do in the section.  We merely delegate
to one of the already-defined relations, so the equation is satisfied
if it is defined in one of the components.  Because each clause in
each of these relations checks the form of the term underlying the
decorated tree, adding another component relation can't change the
equation for an attribute on an already-known production.

Note here that the host language is not special in our scheme for
equation relations.  We treat the host component relation and the
extension component relations equally.  This is because the host
doesn't have a special place in syntax and semantic definitions for
its attributes, which all extensions may define equally.  It will have
a special place for metatheory, however.





# Well-Partially-Decorated (WPD) Relations

We use equation relations to define relations which state that a
particular combination of a syntactic structure and `node_tree` is
well-partially-decorated, meaning that, for each attribute at each
node in the tree, the equation relation for the attribute is either
satisfied or the attribute is empty (`attr_no`).

Because we're concerned with extensible languages here, the WPD
relations need to be built in an extensible manner, which also turns
out to be a convoluted manner.  We are going to have two types of WPD
relations:
* **WPD node relations** check that all the equations for all the
  attributes are obeyed on the current root of a tree.
* **WPD nonterminal relations** walk over the term structure and check
  that all equations, on all nodes at all levels of the tree, are
  satisfied.



## WPD Node Relations

We have declared full WPD node relations for each nonterminal type.
These relate a syntactic structure and a `node_tree`.  The full
relation for the `Expr` nonterminal type is:
```
Type wpd_node_Expr   nt_Expr -> node_tree -> prop.
```

The component relations combine the equation relations for each
attribute declared by the component.  For each attribute, the equation
holds.  We also want to add requirements that `is` relations hold for
attributes of primitive types, which we do by using `is_attrVal` so we
don't need separate cases for the cases where the attribute has and
does not have a value.  For our running example, this would be:
```
Define wpd_node_Expr__host : nt_Expr -> node_tree -> prop by
  wpd_node_Expr__host Tree (ntr_Expr Node TreeCL) :=
    forall ACtx AVal,
       ctx__Expr Tree (ntr_Expr Node TreeCL /\
       access__ctx__Expr Node ACtx /\
       is_attrVal (is_list (is_pair is_string is_integer)) ACtx /\
       %
       val__Expr Tree (ntr_Expr Node TreeCL) /\
       access__val__Expr Node AVal /\
       is_attrVal is_integer AVal.
```
Note that we use the full equation relations, not the component
relations.  This relation is going to be what ensures all productions
from all components have these host-introduced attributes obeying
their equations, so we need to use the full relation which governs all
the component relations.

Most relations built extensibly will replace their declared full
relation in the composition with a definition with clauses which each
delegate to a single component relation.  WPD node relations do not do
this.  Instead, the composition's full relations are defined as a
conjunction of the component relations.  For `Expr`, if we have the host
and two extensions `E1` and `E2`, the full relation in the composition
will be
```
Define wpd_node_Expr : nt_Expr -> node_tree -> prop by
  wpd_node_Expr Tree NodeTree :=
     wpd_node_Expr__host Tree NodeTree /\
     wpd_node_Expr__E1   Tree NodeTree /\
     wpd_node_Expr__E2   Tree NodeTree.
```
This composition ensures all the attributes from all three components
are defined according to their equations.



## WPD Nonterminal Relations

We have declared full WPD nonterminal relations for each nonterminal
type.  As with the node relations, these relate a syntactic structure
and a `node_tree`.  The full relation for the `Exr` nonterminal type
is
```
Type wpd_Expr   nt_Expr -> node_tree -> prop.
```

The component relations check that the node for the root is
well-partially-decorated and that the child trees are
well-partially-decorated.  We do this by matching on the production
building the tree.  For our example grammar, the component relation
would be as follows:
```
Define wpd_Expr__host : nt_Expr -> node_tree -> prop by
  wpd_Expr__host (prod_num N) (ntr_Expr Node []) :=
     wpd_node_Expr (prod_num N) (ntr_Expr Node []) /\
     is_integer N;
  wpd_Expr__host (prod_plus E1 E2) (ntr_Expr Node [E1Ntr, E2Ntr]) :=
     wpd_node_Expr (prod_plus E1 E2) (ntr_Expr Node [E1Ntr, E2Ntr]) /\
     wpd_Expr E1 E1Ntr /\
     wpd_Expr E2 E2Ntr;
  wpd_Expr__host (prod_name N) (ntr_Expr Node nil) :=
     wpd_node_Expr (prod_name N) (ntr_Expr Node nil) /\
     is_string N;
  wpd_Expr__host (prod_let N E1 E2) (ntr_Expr Node [E1Ntr, E2Ntr]) :=
     wpd_node_Expr (prod_let N E1 E2) (ntr_Expr Node [E1Ntr, E2Ntr]) /\
     is_string N /\
     wpd_Expr E1 E1Ntr /\
     wpd_Expr E2 E2Ntr.
```
Note that we also have `is` relations for primitive children.


### Composition

In the composition, we would replace the `wpd_Expr` declared relation
with a defined relation delegating to each of the component
relations.  In Abella, we must take all the relations and define them
mutually:
```
Define wpd_Expr : nt_Expr -> node_tree -> prop,
       wpd_Expr__host : nt_Expr -> node_tree -> prop,
       wpd_Expr__E1 : nt_Expr -> node_tree -> prop,
       wpd_Expr__E2 : nt_Expr -> node_tree -> prop by
  %full relation
  wpd_Expr Term NodeTree := wpd_Expr__host Term NodeTree;
  wpd_Expr Term NodeTree := wpd_Expr__E1 Term NodeTree;
  wpd_Expr Term NodeTree := wpd_Expr__E2 Term NodeTree;
  %host relation
  <all the clauses from wpd_Expr__host>
  %E1 relation
  <all the clauses from wpd_Expr__E1>
  %E2 relation
  <all the clauses from wpd_Expr__E2>.
```
We need to define these mutually inductively so Abella will recognize
that references to `wpd_Expr` which occur within any of the component
relations are smaller (in an inductive sense) than the original
`wpd_Expr` that delegated to the component relation.


### Alternative Definition

An alternative, which does not obviate the need for combining
definitions in Abella and thus we do not do there, is to take an
argument for a full relation when defining the component relations.
Then the type of `wpd_Expr__host` would become
```
nt_Expr -> node_tree -> (nt_Expr -> node_tree -> prop) -> prop
```
The clause for the `plus` production in this relation would then
become something like
```
  wpd_Expr__host (prod_plus E1 E2)
                 (ntr_Expr Node [E1Ntr, E2Ntr])
                 SubRel :=
     wpd_node_Expr (prod_plus E1 E2) (ntr_Expr Node [E1Ntr, E2Ntr]) /\
     SubRel E1 E1Ntr /\
     SubRel E2 E2Ntr;
```
We might think of doing something similar for passing the WPD node
relations to the WPD nonterminal relations.  This would make composing
component definitions as simple as importing them and then adding a
few definitions on top of the existing ones rather than needing to
redo the definitions.

