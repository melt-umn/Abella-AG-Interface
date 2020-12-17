
I thought I had a pattern matching scheme that captured Silver's
pattern matching semantics with the patterns as written.  However,
Silver's pattern matching is even more complicated than I thought, and
my scheme couldn't handle that.

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
forwarding as appropriate.  If we match on a nonterminal type and all
the patterns are for non-forwarding productions, both schemes are
equivalent.





# Matching for Primitive Types

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
the encoded list of patterns, then match on the index of the matched
pattern and the contents of the list of the matched variables.

This is best explained by example.  Consider the following Silver
`case` expression:
```
case x, y of
| 3, b -> 5
| a, 3 -> a + 1
| a, b -> a + b
end
```
We can encode matching the second match rule under the environment
`Env` by the following logical expression:
```
match_pattern_list (pair_c X Y) Patts match_int_pairs
                   (succ zero) [A] /\
plus A 1 e2x /\ e2x = x
```
Here we have
* `x` encodes to `X`
* `y` encodes to `Y`
* the patterns from the rules encode to `Patts`
* `match_int_pairs` matches a pair of integers against a pattern for a
  pair of integers
* `encode ((a,A)::Env) (a + 1) [plus A 1 e2x] e2x`
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



## Matching for Generic Types

In our example above, we had a relation `match_int_pairs` to match on
pairs of integers.  In reality, we don't need to have separate
relations for matching on different types of pairs, or on different
types of lists.

We can define a pattern type for pairs as follows:
```
Kind pair_Pattern   type -> type -> type.
Type pair_pair_Pattern   A -> B -> pair_Pattern A B.
Type mvar_pair_Pattern   pair_Pattern A B.
```
This allows us to put different pattern types inside our patterns for
pairs, so we can use the same pair pattern encoding for pairs of
integers, pairs of strings, pairs of integers and strings, and
anything else.

For matching, we will need a constructor to hold the results for
matching a variable for a pair pattern:
```
Type pmvr_pair   pair A B -> pmvr_pair.
```
We can write code that is **not** typesafe with this.  I think that is
something that they missed when adding schematic polymorphism.  We can
guarantee all the code we write is typesafe by encoding well-typed
Silver code.  If this typing bug is fixed, however, I'm not sure how
we can encode the pattern matches generically.

We can define the pattern matching relation for pairs as follows:
```
Define match_pair :
       (A -> APatt -> list pattern_match_var_result -> prop) ->
       (B -> BPatt -> list pattern_match_var_result -> prop) ->
       pair A B -> pair_Pattern APatt BPatt ->
       list pattern_match_var_result -> prop by
  match_pair ARel BRel (pair_c A B)
             (pair_pair_Pattern APatt BPatt) ResultList :=
     exists AList BList,
        ARel A APatt AList /\
        BRel B BPatt BList /\
        append AList BList ResultList;
  match_pair ARel BRel Pair mvar_pair_Pattern [pmvr_pair Pair].
```
Because our pairs are generic over the type they contain, we take
matching relations as arguments for the types contained in the pairs.
When we match a pair constructor, we use these relations to match the
first and second elements of the pair, then combine the lists of
variables which are matched in the two matchings.

With this encoding, the `match_int_pairs` relation referenced above
would be the partial application `match_pair match_int match_int`
which specializes matching on pairs to specifically matching on pairs
of integers.

We might need to have a different encoding for matching on pairs and
lists which contain nonterminals, depending on what we decide the
correct semantics of Silver pattern matching are.





# Compiling Nonterminal Matching to Single Matches

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





# Testing All Nonterminal Matches

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

