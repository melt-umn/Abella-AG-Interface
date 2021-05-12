
# Differences Between Encoding and Interface
Elsewhere we laid out an encoding of attribute grammars, especially
Silver, into relational systems, especially Abella.  However, it turns
out that this encoding, while clear, isn't perfectly suited to use in
the prover interface.  We make some changes which don't affect the
ideas of the encoding overall, but which make it suited for use in the
interface.

We will usually not show the effects of one change in a separate
section of this document.  For example, we changed our naming scheme,
but the sections not related to the naming scheme do not use the new
naming scheme.  This is to make it easier to understand each deviation
from the original encoding separately.



## Encoded Names
We deviate greatly from the names given in the encoding.  In
particular, we use the dollar sign character liberally in the names in
the encoding for the interface.  We ban the use of the dollar sign by
the interface user in names, which means the user cannot override the
names from the encoding.  We also use it to make it easier to
dismantle relation names, such as to find the attribute name from an
access.  For example, the access relation which was
```
access__env__nt_A
```
in the described encoding becomes
```
$access_$_env_$_nt_A
```
in the encoding used for the interface.  The dollar signs around the
attribute name `env` make it easier for the interface to dismantle the
name of the relation to get the name of the attribute.

This does not affect the semantics of the encoding, but it is good to
know when trying to read the encoding.  Unfortunately, this also makes
it much more difficult to read.



## Encoding Attribute Access and Equations
Recall that our encoding calls for attribute accesses to be encoded
to take the attribute out of the node.  For example, under this
encoding, an attribute access for `val::Integer` occurring on a
nonterminal `Expr` would be encoded as a relation with type
```
node_nt_Expr -> attrVal integer -> prop
```
The encoding we use for the interface adds an extra argument to this
scheme, a term for the tree:
```
nt_Expr -> node_nt_Expr -> attrVal integer -> prop
```
This term is not going to be used in defining the access, but it
stands for the tree structure on which the access is happening.

The initial plan for the interface was to relate the tree and its node
by having them have related names (`$Tm_<treename>` and
`$Node_<treename>`, respectively, with just `treename` being shown to
the user).  This is a bad idea for two reasons.  First, Abella may
generate different names for the tree and node; this may not happen,
but relying on Abella's naming scheme is probably not a good idea, as
it is not documented, nor is it guaranteed.  The second, and more
immediate problem, is that we could end up with a tree and another
variable with apparently the same name.  We might have a tree `T`
(with Abella variables `$Tm_T` and `$Node_T`) and an integer `T`;
Abella would permit these because it would not know they appear the
same after processing by the interface.

When we were using related names for the parts of trees, it was easy
to turn an access of attribute `a` on `$Node_Tree` into `Tree.a`.
Once we started using different names, however, we needed to find a
way to relate a node and a tree to turn an access into the form the
user should see.

We considered finding the related pairs by checking WPD nonterminal
relations, which have both the tree name and the node in them.
However, this did not allow us to show future subgoals if they should
include attribute accesses, because the WPD nonterminal assumptions
are not visible to the interface until the subgoal comes up for
proving.  This also does not work for our "fake" inductive hypotheses
for local attributes in extensible theorems, since they do not include
WPD nonterminal assumptions.

We fix these problems by adding the variable for the tree, which is
the tree's name, to the accesses.  This way we have the name of the
tree in the access to turn an access on a tree variable `T` and node
`Node` for an attribute `a` into `T.a` to show to the user without
needing to search for the correct tree elsewhere.  The way the
interface interacts with Abella ensures that this will always be a
variable, not a structure.

We also need to change the equation relations to reflect this fact.
The original encoding for equation relations had an equation for an
attribute on a tree of type `nt_Expr` as
```
nt_Expr -> nodeTree -> prop
```
We change this for the interface to
```
nt_Expr -> nt_Expr -> nodeTree -> prop
```
In the original encoding, the first argument was the structure of the
tree (e.g. `prod_num N`) and the second argument was the node tree
associated with the structure to form a decorated tree.  The interface
encoding adds a new first argument which is used in the interface for
the variable which is the name of the tree.  Then, in the bodies of
the clauses, we can use the variable version for the attribute
accesses so the interface can display them correctly.

For example, a clause defining `val` on a production `prod_num` is
would be written as
```
intVal__nt_Expr__host TreeName (prod_num N) (ntr_nt_Expr Node nil) :=
   access__val__nt_Expr TreeName Node (attr_ex N);
```
By keeping the structure as an argument, we ensure that only the
relevant clauses apply when case analysis is done on the equation,
which is only allowed when the structure of the tree is known.  By
adding the tree name, we can show the user the correct tree for the
attribute access.  The interface ensures the variable for the tree
name always takes the first spot, so the user doesn't end up with a
filled-in structure there instead.


### Representing Structures for Trees
In the original encoding, we did not need to concern ourselves with
maintaining tree names, as discussed above, so we simply put tree
structures in where they showed up.  For example, for the local
attribute `subWhile` on a while loop, we would have the following in
the body of the definition:
```
access__while__local_subWhile__nt_Stmt Node
   (pair_c (prod_while Cond Body)
           (ntr_nt_Stmt SubWhileNode SubWhileChildList))
```
The structure of the local is immediately placed in as the tree.  This
doesn't work for us to maintain trees by name, as discussed above.

The same issue arises if we try to simply use Abella's built-in
equality operator to show that a tree represented by a particular
variable name has a particular structure (e.g. we access the
`subWhile` local attribute as `pair_c SubWhile <node tree>` and have
`SubWhile = prod_while Cond Body`).  The equality will immediately
replace all occurrences of the variable name with the structure.

To handle this, we introduce structural equality relations.  These are
extensible relations, with the same compositional structure as
equation relations or WPD nonterminal relations, which define equality
of two tree structures.  For example, for a very basic arithmetic
nonterminal with addition and numbers, we would get the following
structural equality relation:
```
Define structure_eq__nt_A__host : nt_A -> nt_A -> prop by
  structure_eq__nt_A__host (prod_plus A1 A2) (prod_plus A3 A4) :=
     structure_eq__nt_A A1 A3 /\
     structure_eq__nt_A A2 A4;
  structure_eq__nt_A__host (prod_num N) (prod_num N)
```
We use the full structural equality relation for nonterminal-typed
children and Abella's unification for primitive children.  Using this
gives us the same information as Abella's built-in equality or
unification, but without the issues.

For attribute equations for nonterminal-typed attributes, we change
the original single assumption of an access with a particular
structure into two separate pieces:  the access and the structure.
Thus we get the following as part of the definition:
```
access__while__local_subWhile__nt_Stmt Node
   (pair_c SubWhile (ntr_nt_Stmt SubWhileNode SubWhileChildList)) /\
structure_eq_nt_Stmt SubWhile (prod_while Cond Body)
```
This gives us the same information as above, but also gives us a name
for the tree rather than just its structure.

We also use structural equality hypotheses for the fake inductive
hypotheses we generate in extensible induction.  We use a structural
equality relation to show the structure of the tree in a particular
case rather than Abella's equality.



## WPD Nonterminal Relations for Nonterminal-Typed Attributes
The original encoding calls for WPD nonterminal relations to be
assumed in the WPD node relation for nonterminal-typed attributes.
For example, a local attribute `subWhile` would give rise to the
following as part of the WPD node relation's definition:
```
access__while__local_subWhile__nt_Stmt Node ASubWhile /\
is_attrVal (split wpd_nt_Stmt) ASubWhile
```
This says that, if `ASubWhile = pair_c Tree NodeTree`, then
`wpd_nt_Stmt Tree NodeTree` holds.  This is done as a replacement for
having the WPD nonterminal assumption in the equation relation.

We keep the access and WPD assumption for trees in the WPD node
relation as described, but we also put it in the equation relation:
* We want it in the WPD node relation because that will make it easier
  to build fake inductive hypotheses for these trees in the
  composition---we don't have to dig into the equation, since the
  inductively-smaller instance of the WPD nonterminal relation will be
  in the WPD node relation.
* We want it in the equation relation so we will have the WPD
  nonterminal relation as an assumption whenever we have the structure
  of the tree.  We use the WPD nonterminal relation in the interface
  to get to the attribute equations, so having it available
  immediately is important.



## Simplified Copying Equations
In the encoding, we said that we could simplify equations which simply
copy their value.  For example, in encoding an equation
```
cond.env = top.env;
```
we could simply produce one clause for the equation
```
env__nt_Stmt__host (prod_while Cond Body)
   (ntr_nt_Stmt Node ((ntr_nt_Expr CondNode CondCL)::
                      (ntr_nt_Stmt BodyNode BodyCL)::nil) :=
   exists AEnv,
      access__env__nt_Stmt Node AEnv /\
      access__env__nt_Expr CondNode AEnv /\
      access__env__nt_Stmt BodyNode AEnv;
```
by not caring whether the environment has a value or not, rather than
two clauses by considering the existence or nonexistence of the value:
```
env__nt_Stmt__host (prod_while Cond Body)
   (ntr_nt_Stmt Node ((ntr_nt_Expr CondNode CondCL)::
                      (ntr_nt_Stmt BodyNode BodyCL)::nil) :=
   exists Env,
      access__env__nt_Stmt Node (attr_ex Env) /\
      access__env__nt_Expr CondNode (attr_ex Env) /\
      access__env__nt_Stmt BodyNode (attr_ex Env);
env__nt_Stmt__host (prod_while Cond Body)
   (ntr_nt_Stmt Node ((ntr_nt_Expr CondNode CondCL)::
                      (ntr_nt_Stmt BodyNode BodyCL)::nil) :=
   access__env__nt_Stmt Node attr_no /\
   access__env__nt_Expr CondNode attr_no /\
   access__env__nt_Stmt BodyNode attr_no;
```

It turns out that this simplification does not work well with the
interface.  It is better for displaying information to the user to
know whether an attribute has a value or no value.  Therefore we do
not plan to implement this simplification, even though it increases
the number of rules written.  Nearly always, if not always, we will
only be concerned with the cases where the the attribute has a value,
making the no-value case trivial, or the case where it does not have a
value, making the value case trivial.

