
We want to encode Silver grammars into Abella so we can reason about
their properties.  There are several pieces in this encoding,
essentially all of which interact with each other:
* We need to translate nonterminals into Abella types
* We need to translate productions into Abella constructors of the
  appropriate types.
* We need to encode equations into definitional clauses for relations,
  which requires encoding Silver expressions into logical expressions
  in Abella.
* We need to define WPD relations for each nonterminal on which we
  have any attributes, which depends on the attributes included on it.

Please note that all naming schemes in this document are subject to
change.  In particular, I might do something like adding an underscore
to the front of each generated name so the user, using the interface,
can't override the names.





# Encoding Nonterminals and Productions

For each nonterminal the program declares, we create a type in Abella:
```
Kind nt_<Nonterminal Name>   type.
```

For each (abstract) production, we define a type in Abella:
```
Type prod_<Production Name>   <Child Types> -> nt_<Building Type>.
```

Consider the following declarations in a Silver grammar:
```
nonterminal A;
nonterminal B;

abstract production a1
top::A ::= c1::A c2::B
{
  ...
}

abstract production a2
top::A ::=
{
  ...
}

abstract production b
top::B ::= c::A
{
  ...
}
```
These will be encoded to the following Abella code:
```
Kind nt_A   type.
Kind nt_B   type.

Type prod_a1   nt_A -> nt_B -> nt_A.
Type prod_a2   nt_A.

Type prod_b   nt_A -> nt_B.
```



  

# Encoding Decorated Trees

Each nonterminal gets its own type of node.  For example, if we have
nonterminals
```
nonterminal Foo;
nonterminal Bar;
```
we will have node types
```
Kind node_Foo.
Kind node_Bar.
```
I think we can leave these without constructors in the encoded
language components.

We create a type for trees of nodes holding attribute values:
```
Kind node_tree   type.
```
We have a constructor for each nonterminal type to build a tree of
nodes.  For the two nonterminals above, we would get the following
constructors:
```
Type ntr_Foo   node_Foo -> list node_tree -> node_tree.
Type ntr_Bar   node_Bar -> list node_tree -> node_tree.
```
When we have `ntr_Foo n l`, `n` is the node at the root of the tree
and `l` is the list of node trees for the children.  Using this form
rather than having a `node_tree` constructor for each production
allows us to access the node for a child without needing to know the
form of the child and without needing another auxiliary relation, an
access which we shall need to do later.  The correct number of child
nodes occurring in the list will be verified by other checking later.

A decorated tree in our encoding is a syntactic structure associated
with a node tree which holds the attribute values for all levels of
the tree.  For example, the decorated tree
```
(prod_f A B, ntr_Foo Nf [NA, NB])
```
is built from a production `f` with two children building the type
`Foo`.  The node `Nf` contains the attribute values for the root of
the tree, `NA` is a tree of nodes associated with the syntactic
structure for `A`, and `NB` is a tree of nodes associated with the
syntactic structure for `B`.



  

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
Type attr_ex   A -> attr_val A.
Type attr_no   attr_val A.
```
This is a standard `option`/`Maybe` type.  We need to introduce it
since Abella has nearly no types built in, so I am naming it for its
purpose of determining whether an attribute value *ex*ists or does
*no*t exist.

With this in mind, we can encode the following declarations into
Abella:
```
inherited attribute a::Bar;
synthesized attribute b::Foo;

attribute a occurs on Foo;
attribute b occurs on Foo;
attribute b occurs on Bar;
```
These give us the following relations:
```
Type access__a__Foo   node_Foo -> attrVal nt_Bar -> prop.
Type access__b__Foo   node_Foo -> attrVal nt_Foo -> prop.
Type access__b__Bar   node_Bar -> attrVal nt_Foo -> prop.
```
Note that we don't care about whether attributes are inherited or
synthesized here, only their occurrences and their types.

We give these access relations without any definition (using `Type`
instead of `Define`).  This is because we are leaving the node types
abstract.  If we change that, these should change to pull the
appropriate values out of the constructor.



## Local Attributes

We also need to store local attributes.  While it doesn't make sense
that we can access local attributes from any production, I believe it
greatly simplifies the encoding of them.  If we have
```
abstract production f
top::Foo ::= ...
{
  local loc::Bar = ...;
}
```
we will produce an access relation
```
Type access__f__local_loc__Foo
       node_Foo -> attrVal (pair nt_Bar node_tree) -> prop.
```
We assume any local of a decoratable type is decorated, and thus we
include the `node_tree` with attribute values.  If the local is not of
a decoratable type, we would not have the pair.

Assuming the Silver grammar being encoded has been typechecked, no
other productions can be accessing this local.  That means it is safe
to make it available in any production, since no other production's
equations will access it.



## Forward

The forward is also stored in the node and has an access relation
generated for it.  For the `Foo` nonterminal given above, this
relation is
```
Type access__forward__Foo
       node_Foo -> attrVal (pair nt_Foo node_tree) -> prop.
```
As with local attributes, the forward may be decorated and thus we
need a pair of a term and the nodes containing the attribute values
decorating it.





# Encoding Primitive Types

Abella doesn't have many built-in types.  Therefore we need to encode
our own.

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
Kind Nat   type.
Type Zero   Nat.
Type Succ   Nat -> Nat.

Kind Integer   type.
Type PosInt   Nat -> Integer.
Type NegInt   Nat -> Integer.
```
We can then define addition and other operations on them as relations.

**Float**:  I'm not quite sure how to handle these.  We can't encode
them for real.  We might treat them as unknowable quantities, that is,
define them and their operations as follows:
```
Kind Float   type.
Type plusFloat   Float -> Float -> Float -> prop.
```
This says there is a type `Float`, and we have a way of relating three
`Float`s, but we do not say anything about elements of `Float`.
Abella lets us do this safely, since we can't do case analysis on
anything that isn't defined as a relation.  We could probably do all
the reasoning on floating-point numbers that we need to do by defining
relations like this and declaring axioms over them.

**String**:  I'm not quite sure how to handle strings either.
Something that would probably work is to encode the most-common
characters, then use lists of characters as strings:
```
Kind char   type.
Type c_a, c_b, c_c, c_d, c_e, c_f, c_g, c_h, c_i, c_j, c_k   char.
Type c_l, c_m, c_n, c_o, c_p, c_q, c_r, c_s, c_t, c_u, c_v   char.
Type c_w, c_x, c_y, c_z, c_1, c_2, c_3, c_4, c_5, c_6, c_7   char.
Type c_8, c_9, c_0, c__   char.
```
We can then define operations over these strings with relations.  We
could encode all possible characters, since the set is finite, even
though I didn't do that in the above.

**IO**:  I don't know enough about the Silver `IO` primitive type to
suggest an encoding for it.  However, I also don't think there is a
lot one would want to prove about this, so I think putting it off is
okay for now.

**[A]**:  This isn't actually a primitive type in Silver, but I
haven't seen it used as if it isn't a primitive type.  Lists are one
of two data structures of which I am aware which are actually built
into Abella.  Therefore it makes sense to use the built-in lists to
encode any Silver lists.

**Pair<A B>**:  This also isn't actually a primitive type in Silver,
but I also don't see it being used as if it isn't a primitive type.
We need to build our own pairs, which we are using elsewhere as well.
We can encode pairs as
```
Kind pair   type -> type -> type.
Type pair_c   A -> B -> pair A B.
```

We could encode other core types, like `Maybe`, `Either`, etc. as
primitive types as well, since they don't really get used as
nonterminal types.  We can figure these out as we need them.





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
which I belive are clearer to read than absolute precision would be:
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
operators and append (`++`) for lists and strings.


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
Booleans, as we are defining numeric operations.  However, it is
simpler for the proof writer to do them outright, I think, since it
eliminates another level of case analysis that would otherwise be
required.  We can't do that with non-Boolean relations because they
tend to be recursive.


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
        attr_access__a__tau node x] x
```


**Negation:**
```
encode Env t l xt
----------------------------------------
encode Env (- t) [l /\ negate xt x] x
```
As with addition above, we can use the appropriate relation for the
type of `t`.


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
the equations.  For example, for the decorating equations `{i1 = 3; i2
= 3 + 4;}`, we get something like
```
access__i1__tau Node 3 /\ plus 3 4 x /\ access__i2__tau Node x
```



## Pattern Matching

I thought I had a pattern matching scheme that captured Silver's
pattern matching semantics with the patterns as written.  However,
Silver's pattern matching is even more complicated than I thought, and
my scheme coludn't handle that.

OCaml pattern matching would be easy to represent.  We could walk
through the list of patterns, walking down each pattern to test if the
term being matched against it does match it.  If not, we could simply
discard the pattern and move down the line to test the next pattern.

The problem is that Silver forwards if it doesn't find a match in the
list of patterns.  My initial encoding scheme handled forwarding to
match at the top, but not in lower productions.  For example,
`p1(p2())` can match the pattern `p1(p3())` if `p2()` forwards to
`p3()`.  My scheme was only forwarding at the top level (e.g. it would
forward `p1` to match but not `p2`).

Below I will discuss pattern matching on primitive types, then two
different ideas for encoding Silver's matching semantics, including
forwarding as appropriate.


### Matching for Primitive Types

Regardless of how we handle matching on nonterminal types, we can
match on primitive types.  We have a relation for matching
against a single pattern.

We create a pattern type for the patterns of each primitive type, with
a pattern for each constructor and a separate variable pattern
constructor.  For Booleans, this would look like this:
```
Kind bool_Pattern   type.
Type btrue_bool_Pattern   bool_Pattern.
Type bfalse_bool_Pattern   bool_Pattern.
Type mvar_bool_Pattern   bool_Pattern.
```

Our type-specific matching relation for a primitive type determines
whether a particular Boolean value matches a particular Boolean
pattern, with a list for variables being bound.  This has a clause for
each constructor of the corresponding pattern type.  For Booleans, we
would have the following:
```
Define match_bool : bool -> bool_Pattern ->
                    list pattern_match_var_result -> prop by
  match_bool btrue btrue_bool_Pattern nil;
  match_bool bfalse bfalse_bool_Pattern nil;
  match_bool B mvar_bool_Pattern [pmvr_bool B].
```

We can do some general things for matching.  We first create a general
type for the bound variables resulting from matching a particular
pattern for any type of pattern.  This type is
```
Kind pattern_match_var_result   type.
```
We will have a constructor for this type for each type which we can
get from matching.  For example, the constructor for Booleans is
```
Type pmvr_bool   bool -> pattern_match_var_result.
```

We can also make a general matching relation which matches through a
list of patterns to find the first pattern which matches.  This is
```
Define match_pattern_list : TermTy -> list PattTy ->
                            (TermTy -> PattTy ->
                             list pattern_match_var_result -> prop) ->
                            nat -> list pattern_match_var_result ->
                            prop by
   match_pattern_list Tm (Patt::Rest) MatchRel zero L :=
      MatchRel Tm Patt L;
   match_pattern_list Tm (Patt::Rest) MatchRel (succ N) L :=
      ((exists L, MatchRel Tm Patt L) -> false) /\
      match_pattern_list Tm Rest MatchRel N L.
```
This takes
* the term to match
* the list of patterns to match the term against
* the matching relation for the term type
* the index into the list for the pattern which matched
* the list of terms which matched variables

The actual matching logic is handled by the match-relation argument.
This relation simply asks this relation if the term and the first
pattern match at each step.  If they do, we matched the zeroth pattern
in the list and bound the variables found in `L`.  If they don't
match, we find the first match in the rest of the list and add one to
the index.

When encoding a `case` expression, we encode the expression on which
we are pattern matching and we encode the Silver patterns into Abella
patterns in the obvious way.  For the `case` expression, we match on
the encdoded list of patterns, then match on the index of the matched
pattern and the contents of the list of the matched variables.

This is best explained by example.  Consider the following Silver
`case` expression:
```
case x, y of
| 3, b -> e1
| a, 3 -> e2
| a, b -> e3
end
```
We can encode matching the second match rule under the environment
`Env` by the following logical expression:
```
match_pattern_list (pair_c X Y) Patts match_int_pairs
                   (succ zero) [A] /\
e2l /\ e2x = x
```
Here we have
* `x` encodes to `X`
* `y` encodes to `Y`
* the patterns from the rules encode to `Patts`
* `match_int_pairs` matches a pair of integers against a pattern for a
  pair of integers
* `encode ((a,A)::Env) e2 e2l e2x`
* the variable holding the result is `x`

By matching on the list of matched variables being `[A]`, we get the
number which will be bound to `a` in Silver without needing to keep
track of the particular names being bound in patterns.  In encoding
matching, we will also have the variables in the result list in the
same order as they appear in the text of the Silver pattern.  This
means that, for the last match rule, we would match on the list as
`[A, B]` where `A` corresponds to `a` and `B` corresponds to `b`.

We could also define particular relations for matching on pattern
lists for each primitive type (e.g. have a `match_bool_list`,
`match_int_list`, etc.).



### Compiling Nonterminal Matching to Single Matches

I was trying to avoid compiling the patterns into single-level
matches.  We can do this; I would prefer to be able to match on the
patterns as written instead because I think that is more clear.  I
don't think I can hide details of compilation of patterns from the
user, and that removes the encoding from what the user wrote and would
like to reason about.

Compiled pattern matching, which matches on a single level of
constructors at once, creates its own pattern type as for the
primitive types.  The constructors of this type correspond to the
productions, but without any subpatterns.  This is because we don't
need another level of matching, and we know exactly how many children
it has.  For example, the following Silver code
```
nonterminal Nt;

abstract production p
top::Nt ::= t::Nt i::Integer
{ }
```
would produce the following pattern type and constructor:
```
Kind nt_Nt_Pattern   type.
Type prod_p_nt_Nt_Pattern   nt_Nt_Pattern.
```
We would also need to create a constructor for
`pattern_match_var_result` for this type.  We will need a `node_tree`
with our result as well (which we will discuss below), so our
constructor needs to include this as well.  The constructor for `Nt`
would be
```
Type pmvr_nt_Nt   nt_Nt -> node_tree -> pattern_match_var_result.
```

The match relation would need to be built extensibly, since more
patterns can be introduced by other extensions.  Because of this, we
need to declare a full relation and give component relations.  In
Silver, decorated subtrees keep their decoration, so we need to carry
the `node_tree` around.  For the grammar above, this would be
```
Type match_nt_Nt   nt_Nt -> node_tree -> nt_Nt_Pattern ->
                   list pattern_match_var_result -> prop.
Define match_nt_Nt__host : nt_Nt -> node_tree -> nt_Nt_Pattern ->
                         list pattern_match_var_result -> prop by
  match_nt_Nt__host (prod_p T I) (ntr_Nt Node [ntr_Nt TNode TCL])
                    prod_p_nt_Nt_Pattern
                    [pmvr_nt_Nt T (ntr_Nt TNode TCL), pmvr_Int I].
```

We need to forward if no patterns in a list match.  Therefore we need
a relation which tries to match every pattern in a list, then forwards
if they all failed.  This gives us something similar to the general
`match_list` we had for primitive types, but with an extra case for
forwarding.  For `Nt` above, this gives us:
```
Define match_nt_Nt_list : nt_Nt -> node_tree -> list nt_Nt_Pattern ->
                          nat -> list pattern_match_var_result ->
                          list nt_Nt_Pattern -> prop by
  match_nt_Nt_list T NodeTree (Patt::Rest) zero L FullPatts :=
    match_nt_Nt T NodeTree Patt L;
  match_nt_Nt_list T NodeTree (Patt::Rest) (succ N) L FullPatts :=
    ((exists NL, match_nt_Nt T NodeTree Patt NL) -> false) /\
    match_nt_Nt_list T NodeTree Rest N L;
  match_nt_Nt_list T (ntr_Nt Node TCL) nil N L FullPatts :=
    access__forward__Nt Node (attr_ex (pair_c Fwd FNodeTr)) /\
    match_nt_Nt_list Fwd FNodeTr FullPatts N L FullPatts.
```
We carry around the full list of patterns because we need to start
again from the beginning of the list when we forward.  When we want to
match against a list of patterns `PattList`, we start with this as
both the first pattern list and the full pattern list:
```
match_nt_Nt_list Tm NodeTree PattList N L PattList
```

Consider how we encode a primitive match of the form
```
match e return ty with rules else -> fail end
```
We encode `e` with a result variable `ex`.  We go through `rules` and
encode a list of patterns.  We then use `match_nt_Nt_list` to match
`ex` against the encoded patterns.  For each possible index into the
list of patterns, we build a clause for matching and filling in
variables as we did in the section for matching primitive types
above.  Finally, we also add a clause for the `fail` branch with the
condition that `match_nt_Nt_list` does not succeed for any index or
list of bound variables.


### Testing All Nonterminal Matches

The idea in this section is to match all the patterns in a list of
patterns from a `case` expression as we walk through the list,
forwarding as necessary, but keeping track of how many forwards we
needed and where.

This scheme doesn't quite match the matching semantics of Silver as
they currently are.  This finds a match if a match exists; Silver may
not, depending on forwarding.  However, I'm not sure Silver's current
semantics are the intended ones, so I'll write this up anyway.

To keep track of the matching, we create a type with two constructors:
```
Kind match_forwards   type.
Type mf_prod   nat -> list match_forwards -> match_forwards.
Type mf_var   match_forwards.
```
The term `mf_prod N L` says we forwarded `N` times to match a
production pattern, with the matching done for each child as recorded
in `L`.  The term `mf_var` says we matched a variable.

Our basic matching relation would be as follows (except appropriately
broken into component relations):
```
Define match_nt_Nt :
      nt_Nt -> node_tree -> nt_Nt_Pattern -> nat -> match_forwards ->
      list pattern_match_var_result -> prop by
  % Example rule for pattern for p : Nt -> Nt -> Nt
  match_nt_Nt (prod_p A B)
              (ntr_Nt Node [ntr_Nt ANode ACL, ntr_Nt BNode BCL])
              (prod_p_nt_Nt_Pattern APatt BPatt)
              N
              (mf_prod N [AMF, BMF])
              CombinedBindList :=
     match_nt_Nt A (ntr_Nt ANode ACL) APatt zero AMF ABindList /\
     match_nt_Nt B (ntr_Nt BNode BCL) BPatt zero BMF BBindList /\
     append ABindList BBindList CombinedBindList;
  % Forwarding rule for p
  match_nt_Nt Tm (ntr_Nt Node CL) (prod_p_nt_Nt_Pattern APatt BPatt)
              N MF BindList :=
    exists Fwd FwdNode,
      ((exists A B, Tm = prod_p A B) -> false) /\
      access__forward__Nt Node (attr_ex (pair_c Fwd FwdNode)) /\
      match_nt_Nt Fwd FwdNode Patt (succ N) MF BindList;
  % Variable pattern---can't have required forwarding
  match_nt_Nt Tm NTr mvar_nt_Nt_Pattern zero mf_var [pmvr_nt_Nt Tm].
```
So what am I doing here?  Our arguments are:
1. The term structure on which we are matching
2. The `node_tree` holding attributes for this tree
3. The pattern we are matching
4. The record of how many times we had to forward at different levels
   of the pattern
5. The number of times we have forwarded in matching the current
   pattern and different subpatterns (left to right)
6. The variable bindings resulting from this match

If we are matching against a pattern `p1(p2(p3(), _), p4())` and we
get a `match_forwards` of
```
mf_prod 0 [mf_prod 1 [mf_prod 0 nil, mf_var], mf_prod 2 nil]
```
that means we forwarded zero times to match `p1`, one time to match
`p2`, zero times to match `p3`, zero times to match the default, and
two times to match `p4`.

We create a relation to match over a list of patterns which gathers a
list of pairs of `nat`, `match_forwards`, and
`list pattern_match_var_result`, which we will use to find a match and
give the correct index for each pattern matched.  This relation can be
made general over any nonterminal type by taking a matching relation:
```
Define match_nt_list_all :
       Tm -> node_tree -> list PattTy -> nat ->
       (Tm -> node_tree -> PattTy -> nat ->  match_forwards ->
        list pattern_match_var_result -> prop) ->
       list (pair nat (pair match_forwards pattern_match_var_result))
       by
  match_nt_list_all Tm NTr (Patt::Rest) Index MatchRel
                ((pair_c nat (pair_c MF Binds))::L) :=
      MatchRel Tm NTr Patt zero MF Binds /\
      match_nt_list_all Tm NTr Rest (succ Index) MatchRel L;
  match_nt_list_all Tm NTr (Patt::Rest) Index MatchRel L :=
      ((exists MF Binds,
           MatchRel Tm NTr Patt zero MF Binds) -> false) /\
      match_nt_list_all Tm NTr Rest Index MatchRel L;
  match_nt_list_all Tm NTr nil Index MatchRel nil.
```

We need a way to compare two `match_forwards` to determine which
matching pattern should be matched.  We do this as follows:
```
Kind comp   type.
Type less   comp.
Type greater   comp.
Type equal   comp.

Define compare_matches :
          match_forwards -> match_forwards -> comp -> prop,
       compare_matches_list :
          list match_forwards -> match_forwards -> comp -> prop by
  compare_matches (mf_prod N NL) (mf_prod M ML) less :=
     less_nat N M;
  compare_matches (mf_prod N L1) (mf_prod N L2) Comp :=
     compare_matches_list L1 L2 Comp;
  compare_matches mf_var (mf_prod N L) less;
  compare_matches (mf_prod N L) mf_var less;
  compare_matches M1 M2 greater := compare_matches M2 M1 less;
  compare_matches MF MF equal;
  % lists
  compare_matches_list (H1::Tl1) (H2::Tl2) less :=
     compare_matches H1 H2 less;
  compare_matches_list (H1::Tl1) (H2::Tl2) greater :=
     compare_matches H1 H2 greater;
  compare_matches_list (H1::Tl1) (H2::Tl2) Comp :=
     compare_matches H1 H2 equal;
     compare_matches_list Tl1 Tl2 Comp;
  compare_matches_list nil nil equal.
```
The lesser match, by this comparison, is the match that would be
chosen by Silver pattern matching.

Using this, we can then find a minimum out of the whole list as
follows:
```
Define actual_match :
       list (pair nat (pair match_forwards list
                            list pattern_match_var_result)) ->
       nat -> list pattern_match_var_result -> prop by
  actual_match [pair_c N (pair_c MF L)] N L;
  actual_match ((pair_c N1 (pair_c MF1 L1))::
                (pair_c N2 (pair_c MF2 L2))::Rest) OutN OutL :=
     compare_matches MF1 MF2 less /\
     compare_matches ((pair_c N1 (pair_c MF1 L1))::Rest) OutN OutL;
  actual_match ((pair_c N1 (pair_c MF1 L1))::
                (pair_c N2 (pair_c MF2 L2))::Rest) OutN OutL :=
     compare_matches MF1 MF2 greater /\
     compare_matches ((pair_c N2 (pair_c MF2 L2))::Rest) OutN OutL;
  actual_match ((pair_c N1 (pair_c MF1 L1))::
                (pair_c N2 (pair_c MF2 L2))::Rest) OutN OutL :=
     compare_matches MF1 MF2 equal /\
     compare_matches ((pair_c N1 (pair_c MF1 L1))::Rest) OutN OutL.
```
This takes the best earliest match.

Our full matching relation over a list, which gives the index of the
pattern matched and the list of bindings as in the other schemes, is
```
Define match_nt_list :
       Tm -> node_tree -> list PattTy ->
       (Tm -> node_tree -> PattTy -> nat -> match_forwards ->
        list pattern_match_var_result -> prop) ->
       nat -> list pattern_match_var_result -> prop by
   match_nt_list Tm NTr Patts MatchRel N Binds :=
     exists L,
       match_nt_list_all Tm NTr Patts zero MatchRel L /\
       actual_match L N Binds.
```

This looks really complicated.  Why would we want to do this?  I think
it lets us easily say, when we have a Silver pattern
`p1(p2(), p3(x))`, that we match *this* pattern as a whole, rather
than that something matches `p1`, which has children which match `p2`
and `p3`.  Having written all this, I'm not sure if this is worth it.
It certainly shouldn't be used if we decide the current Silver
semantics of matching left-to-right without backtracking is correct,
since we can get wrong results from this.



## Functions and Function Calls

We can encode a function as a relation with the same types of
arguments as the Silver function (appropriately encoded, of course),
with an additional argument for the result.

We can encode a function into a relation by encoding the `return`
expression, with different clauses for different branches of the
expression.  Consider the following Silver function:
```
function append
[a] ::= l1::[a] l2::[a]
{
  return case l1 of
         | [] -> l2
         | h::t -> h::append(t, l2)
         end;
}
```
This function is encoded as (leaving out the expression encodings in
the clause bodies):
```
Define append : list A -> list A -> list A -> prop by
  append L1 L2 Result := ... ; %L1 is empty
  append L1 L2 Result := ... . %L1 is non-empty
```
Because we have two branches in the Silver function, we get two
clauses in the definition.

If we have a nonterminal-type argument, we only take the term
structure as an argument (unless it is declared as a decorated
argument).  We need to decorate such an argument.  We can do this by
including a `node_tree` variable in the body of the clause, encoding
any equations for its attributes, and requiring it follows all
equations (in a manner which we will discuss later).  The difference
from encoding attribute equations is that we take the encoding of the
clause and join it to the result of encoding the expression in the
`return`.  If any of the equations branch, we need to create all
possible combinations of the branches (e.g. the `t.a` equation has
branches `A` and `B` and the `t.c` equation has branches `C` and `D`
means we need clauses for `(A,C)`, `(A,D)`, `(B,C)`, and `(B,D)`).

We'll show an example here of encoding a function with attribute
equations, but not discuss the details:
```
function f
String ::= t::Nt
{
  t.ia = "ia";
  return t.sa;
}
```
This encodes into the following (abusing string notation):
```
Define f : Nt -> String -> prop by
  f T Result :=
    exists Node,
      wpd_Nt T Node /\
      access__ia__Nt Node (attr_ex "ia") /\
      access__sa__Nt Node (attr_ex Result).
```

**Function Call:**
```
encode Env f lf funname
encode Env args la eargs
----------------------------------------
encode Env f(args) [lf /\ la /\ funname eargs x] x
```
Here we are abusing notation; `args` is a sequence of arguments, and
`eargs` is the encoded sequence.  Encoding the argument sequence is
encoding all the argument expressions and joining together all their
clauses using conjunction.




  
# Attribute Equations

For each occurs declaration, we need a relation to show that the
equation for the attribute holds on the root node.  This relation
needs to be extensible, so we will have defined relations for each
component and a declared relation for the full relation.  These
relations relate a syntactic structure and a `node_tree` which holds
the attribute values for the syntactic structure.

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
branch, we need to encode the cartesian production of the clause sets
for all the equations.  If a production does not have an equation for
a particular inherited attribute, we still create a definitional cause
for the production in the component relation, but without a body.
This means that the "equation" is vacuously satsified, since there is
no equation.

If we have an equation or equations to encode, the precondition is the
encoding of the equation's expression (`el` in `encode Env e el ex`
where `Env` contains bindings for the root and children and any local
attributes) joined with accessing the attribute and getting its value
as `ex` (`access__attrname__nonterminal Node (attr_ex ex)`).  This
shows that `ex`, the result of the equation`s expression, is the value
of the attribute being defined.

Consider the following attribute grammar:
```
synthesized attribute sa::Integer;
inherited attribute ia::Integer;

nonterminal Nt;
attribute sa occurs on NT;
attribute ia occurs on NT;

abstract production p1
top::Nt ::= x::Nt y::Nt
{
  x.ia = top.ia;
  y.ia = top.ia;
  top.sa = x.sa + y.sa;
}

abstract production p2
top::Nt ::=
{
  top.sa = top.ia;
}
```
We will generate two full equation relations:
```
Type sa__Nt   nt_Nt -> node_tree -> prop.
Type ia__Nt   nt_Nt -> node_tree -> prop.
```
We will also generate a defined component relation for each attribute,
which would look something like this (which might be cleaner than what
`encode` would give us):
```
Define sa__Nt__host : nt_Nt -> node_tree -> prop by
   sa__Nt__host (p1 X Y)
                (ntr_Nt Node [ntr_Nt XNode XCL, ntr_Nt YNode YCL]) :=
      exists PlusResult XSa YSa,
         access__sa__Nt Node (attr_ex PlusResult) /\
         access__sa__Nt XNode (attr_ex XSa) /\
         access__sa__Nt YNode (attr_ex YSa) /\
         plus XSa YSa PlusResult;
   sa__Nt__host p2 (ntr_Nt Node nil) :=
      exists Val,
         access__sa__Nt Node (attr_ex Val) /\
         access__ia__Nt Node (attr_ex Val).

Define ia__Nt__host : nt_Nt -> node_tree -> prop by
   ia__Nt__host (p1 X Y)
                (ntr_Nt Node [ntr_Nt XNode XCL, ntr_Nt YNode YCL]) :=
      exists Val,
         access__ia__Nt Node (attr_ex Val) /\
         access__ia__Nt XNode (attr_ex Val) /\
         access__ia__Nt YNode (attr_ex Val);
   ia__Nt__host p2 (ntr_Nt Node nil).
```
We can see here how we add the access for the attribute being defined
as the result of the expression in the equation.  We can also see how
we combine the two equations for `ia` on `x` and `y` to form one
clause in the component relation, as well as how we have a clause with
no preconditions for `ia` with `p2` because it does not define `ia` on
any trees.



## Local Attributes

We also need to provide equation relations for local attributes.
These relations are fairly similar to equation relations for
synthesized attributes.  Because each local is only on one production,
we can give the full relation as a defined relation with all clauses
defining it on the production which has it.

Our relation's clauses also define any inherited attributes given to
the local.  There are two reasons why including the equations for
inherited attributes here rather than in the equation relation for the
inherited attribute is the correct choice:
1. We would need separate clauses in the equation relation for the
   inherited attribute depending on whether the local is defined or
   undefined, while all the rest of the pieces of the clause would
   remain the same.
2. We can be consistent with where the inherited attributes for locals
   are defined this way.  For example, if we introduce a local in an
   extension and define a host inherited attribute on it, the equation
   for that goes with the local attribute's definition relation.
   Otherwise, we would have some local attributes having their
   inherited attributes defined with their forms and others having
   their local attributes defined with the inherited attribute
   equation relations.
   
Suppose we add the following production to the grammar from above:
```
abstract production p3
top::Nt ::= a::Integer b::Nt
{
  local loc::Nt = p1(b, b);
  loc.ia = a;
  top.sa = b.sa + loc.sa;
}
```
The equation relation for the local would be as follows:
```
Define p3_local_loc : nt_Nt -> node_tree -> prop by
  p3_local_loc (p3 A B) (ntr_Nt Node [ntr_Nt BNode BCL]) :=
     exists LocNode LocCl,
        access__p3_local_loc__Nt Node
           (attr_ex (pair_c (p1 B B) (ntr_Nt LocNode LocCL))) /\
        wpd_Nt (p1 B B) (ntr_Nt LocNode LocCL) /\
        access__ia__Nt LocNode A.
```
There are three conjuncts in the body of the only clause in this
definition:
1. We access the local on the root's node, getting its structure
   (equal to the child `B` of the production) and its `node_tree`,
   which has the appropriate form for a tree of type `Nt`.
2. We require the structure of the local attribute (`p1 B B`)
   associated with its `node_tree` (`ntr_Nt LocNode LocCL`) to be well
   partially-decorated.  We will discuss WPD relations in the next
   section.  For now, just trust that this is necessary.
3. We access the `ia` attribute on the local and ensure it is equal to
   the child `A`.



## Forward

The forward is treated somewhat like a local attribute.  However, we
must include a full relation for it, since different productions may
forward.

The full relation for the forward on the `Nt` nonterminal type given
above would be:
```
Type forward__Nt   nt_Store -> node_tree -> prop.
```
We would define, for each component which includes forwarding
constructs, a component relation for the forward.  Each clause would
include the inherited attributes given to the forward, as we saw with
local attributes, as well as an assumption of being
well-partially-decorated.




  
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

Let us continue to consider the attribute grammar from above:
```
synthesized attribute sa::Integer;
inherited attribute ia::Integer;

nonterminal Nt;
attribute sa occurs on NT;
attribute ia occurs on NT;

abstract production p1
top::Nt ::= x::Nt y::Nt
{
  x.ia = top.ia;
  y.ia = top.ia;
  top.sa = x.sa + y.sa;
}

abstract production p2
top::Nt ::=
{
  top.sa = top.ia;
}

abstract production p3
top::Nt ::= a::Integer b::Nt
{
  local loc::Nt = p1(b, b);
  loc.ia = a;
  top.sa = b.sa + loc.sa;
}
```



## WPD Node Relations

We have declared full WPD node relations for each nonterminal type.
These relate a syntactic structure and a `node_tree`.  The full
relation for the `Nt` nonterminal type is:
```
Type wpd_node_Nt   nt_Nt -> node_tree -> prop.
```

The component relations combine the equation relations for each
attribute declared by the component (including local attributes).  For
each attribute, either the equation relation holds or the attribute's
value is undefined.  For the grammar above, this would be:
```
Define wpd_node_Nt__host : nt_Nt -> node_tree -> prop by
  wpd_node_Nt__host Tree (ntr_Nt Node TreeCL) :=
    (  sa__Nt Tree (ntr_Nt Node TreeCL)  \/
       access__sa__Nt Node attr_no  )             /\
    (  ia__Nt Tree (ntr_Nt Node TreeCL)  \/
       access__ia__Nt Node attr_no  )             /\
    (  p3_local_loc Tree (ntr_Nt Node TreeCL) \/
       access__p3_local_loc__Nt Node attr_no  )   /\
    (  forward__Nt Tree (ntr_Nt Node TreeCL)  \/
       access__forward__Nt Node attr_no  ).
```
Note that we include the equation for the forward, even though we have
no forwarding productions, since the forward is inherently a host
attribute.  Note also that we use the full relations, not the
component relation.  This relation is going to be what ensures all
productions from all components have these host-introduced attributes
obeying their equations, so we need to include the forward.

I thought about whether these disjunctions should be split across
separate clauses.  I decided against it because we sometimes don't
care whether particular attributes are defined or not (e.g. if we're
proving something about typing, we don't care if evaluation attributes
are defined).  Splitting them into separate clauses would lead to a
lot of extra cases getting thrown in which are essentially equal.
This way you can do case analysis just on whether the attributes in
which you are interested are defined.

I also thought about whether the disjunct for being undefined should
explicitly include that the equation relation does not hold.  I don't
think we actually need that, since any clause in the equation relation
which actually does something includes a precondition that the
attribute must have a real value (`attr_ex`).

Most relations built extensibly will replace their declared full
relation in the composition with a definition with clauses which each
delegate to a single component relation.  WPD node relations do not do
this.  Instead, the composition's full relations are defined as a
conjunction of the component relations.  For `Nt`, if we have the host
and two extensions `E1` and `E2`, the full relation in the composition
will be
```
Define wpd_node_Nt : nt_Nt -> node_tree -> prop by
  wpd_node_Nt Tree NodeTree :=
     wpd_node_Nt__host Tree NodeTree /\
     wpd_node_Nt__E1   Tree NodeTree /\
     wpd_node_Nt__E2   Tree NodeTree.
```
This composition ensures all the attributes from all three components
are either defined according to their equations or have undefined
values.



## WPD Nonterminal Relations

We have declared full WPD nonterminal relations for each nonterminal
type.  As with the node relations, these relatio a syntactic structure
and a `node_tree`.  The full relation for the `Nt` nonterminal type
is:
```
Type wpd_Nt   nt_Nt -> node_tree -> prop.
```

The component relations check that the node for the root is
well-partially-decorated and that the child trees are
well-partially-decorated.  We do this by matching on the production
building the tree.  For the grammar above, the component relation
would be as follows:
```
Define wpd_Nt__host : nt_Nt -> node_tree -> prop by
  wpd_Nt__host (p1 X Y)
               (ntr_Nt Node [ntr_Nt XNode XCL, ntr_Nt YNode YCL]) :=
     wpd_node_Nt (p1 X Y)
                 (ntr_Nt Node [ntr_Nt XNode XCL, ntr_Nt YNode YCL]) /\
     wpd_Nt X /\
     wpd_Nt Y;
  wpd_Nt__host p2 (ntr_Nt Node nil) :=
     wpd_node_Nt p2 (ntr_Nt Node nil);
  wpd_Nt__host (p3 A B) (ntr_Nt Node [ntr_Nt BNode BCL]) :=
     wpd_node_Nt (p3 A B) (ntr_Nt Node [ntr_Nt BNode BCL]) /\
     wpd_Nt B.
```

