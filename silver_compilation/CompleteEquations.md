
The scheme we have described thus far for equation relations and WPD
relations requires that *all* attributes must have values.  This is
because we have encoded the success cases of equations in equation
relations, then required that all the equation relations must hold in
our WPD node relations.

This is not the case in Silver, however.  Not all attributes must have
values on a decorated tree.  For example, we can type a tree without
giving it an evaluation context, or we can evaluate the term
represented by a tree without giving it a typing context.  On a
finer-grained level, if the condition of an `if-then-else` evaluates
to `true`, the `else` branch needn't have an evaluation result.

The question, then, is how ought we to allow some attributes to be
undefined while ensuring equations are satisfied?  Some options we
considered:
* We could change the WPD node relation so each attribute either has
  its equation satisfied or the attribute is `attr_no` (undefined).
  This doesn't quite work, since we could have an equation
  ```
  top.val = 3;
  ```
  and still get `val` as undefined rather than as `3`.  This doesn't
  let us prove something like subject reduction, since our Silver
  equation would have a value but the encoding wouldn't.
* We could change the WPD node relation so each attribute either has
  its equation satisfied or the equation doesn't hold (implies false).
  This is worse than the previous one, since we can now have any value
  rather than just `attr_no`.  Combining the two approaches (equation
  doesn't hold *and* the attribute is `attr_no`) doesn't give us
  anything more.
* We could try to characterize the notion of "there isn't a value for
  this attribute that could possible make the equation hold".  This is
  really hard, and I'm not sure the idea I came up with is actually
  true (it might allow an equation not to hold if two equations didn't
  hold).  Even if I could come up with a way to do it, I think it
  would be complicated.

The approach we choose is entirely different from these.  We choose to
add equation failure resulting in undefined attribute values into the
equation relations themselves, rather than trying to encode it after
the fact in the WPD node relation.





# Encoding Equation Failure

The ways a Silver equation may directly fail to produce a value are
limited.  We assume operations on primitive types are total, ignoring
limitations of the machine.  Otherwise, the direct failures in Silver
equations come from
* Accessing an undefined attribute
* Not matching any pattern in pattern matching
* A function not returning a value

Once a failure is introduced, it may be passed up through other
constructs to the level of the equation.  For example, if the
condition of an `if-then-else` fails to produce a value, the
`if-then-else` fails to produce a value as well.



## Encoding Expression Failures

To produce the failure cases, we walk through the expression being
encoded as we did with the `encode` relation, but this time
considering the possible failures at each step rather than the
successes.  We do this with a relation **encode_failure** which has
three arguments:
* an environment assigning Abella terms to variable names
* a Silver expression
* a set/list of Abella clauses which encode failure

We only need to respect evaluation order in our failures when there is
actually a branch.  This means that for some constructs, such as
addition, we do not care what Silver would evaluate first.  We only
care that a subexpression is going to need to be evaluated for the
expression to have a value, and that the subexpression fails.


**If-Then-Else:**
```
encode_failure Env c cl
encode_failure Env th thl
encode_failure Env el ell
----------------------------------------
encode_failure
   Env
   (if c then th else el)
   (cl ++ thl ++ ell)
```


**Addition (and other defined operations, conjunction/disjunction,
  equality checking):**
```
encode_failure Env t1 l1
encode_failure Env t2 l2
----------------------------------------
encode_failure Env (t1 + t1) (l1 ++ l2)
```


**Attribute Access:**
```
encode_failure Env t failure_list
encode Env t tl tx
----------------------------------------
encode_failure  Env (t.a)
      ([tl /\ tx = pair_c structure node /\
        attr_access__a__tau node attr_no] ++
       failure_list)
```
This is a bit different than what we have seen thus far.  We have the
failure of the subterm `t`, with the failure clauses in
`failure_list`, but we also have the failure of the attribute access
itself which can fail by the attribute being undefined (`attr_no`).


**Let:**
```
encode_failure Env tl failure_list1
encode Env t1 l1 x1
encode_failure ((y,x1)::Env) t2 l2
----------------------------------------
encode_failure Env (let y::tau = t1 in t2)
       (failure_list1 ++ [l1 /\ y = x1 /\ l2])
```


**Variable:**
```
x not in Env
----------------------------------------
encode_failure Env x [true]

x in Env
----------------------------------------
encode_failure Env x []
```
If a variable is not in the current environment, there is no term or
set of terms to which it can translate.


**Decorate:**
```
encode_failure Env t tl tx
----------------------------------------
encode_failure Env (decorate t with {eqs}) tl
```
We don't need to take failure cases from the equations we use to
decorate the tree.  This is because any failures which occur there are
not failures of the expression overall.  They are encoded in the
successful part of the encoding of the `decorate`, with the attribute
being defined by the equation being undefined.


**Function Call:**
```
encode Env f lf funname
encode Env args la eargs
encode_failure Env f failure_l
encode_failure Env args failure_la
----------------------------------------
encode_failure Env (f(args))
       ([lf /\ la /\ (exists Res, funname eargs Res) -> false] ++
        failure_l ++ failure_la)
```
We have both the cases that the function fails and that one of the
arguments fails (written by abusing notation), as well as the case
that the function and arguments encode fine, but the function does not
have a result for the given arguments.


**Pattern Matching:**
It is a bit difficult to write a rule for pattern matching.  We have
three sources of failure:
1. The expression on which we are matching could fail.  The failure
   clauses for this are simply those produced by `encode_failure` on
   the expression.
2. There might be no pattern which matches.  This gives us the
   following failure clause, where we are matching `Term` against
   `Patts` with the single matching relation `match_rel`:
   ```
   (exists N L, match_pattern_list Term Patts match_rel N L) -> false
   ```
3. The expression for the selected pattern might fail.  In this case
   we take the conjunction of the encoding of the expression on which
   we are matching with the encoding of the pattern matching
   succeeding and the failure of the expression for the pattern clause
   which matched.

Consider encoding the following expression:
```
case t.a of
| production(a, b) -> t.b
end
```
We would get three clauses:
1. One clause would be for `t.a` being undefined.
2. One clause would be for if the value of `t.a` does not match the
   `production` constructor.
3. One clause would be for if `t.b` does not have a value once `t.a`
   has matched the `production` constructor.



## Encoding Equation Failures

Now that we have an encoding of expression failures, we can encode
equation failures.

For an equation `t.a = e;`, we get the result list `L` from
`encode_failure` for `e`.
* If `L` is empty, then we don't need to add any clauses to the
  equation relation.
* If `L` is nonempty, for each element `EncodedExpr` of `L` we add a
  clause to the equation relation with the body
  ```
  access__<attr>__<nonterminal> Node attr_no /\ EncodedExpr
  ```

As an example, suppose we want to encode the equation for `val` in the
following production:
```
abstract production ifThenElse
top::Expr ::= c::BoolExpr th::Expr el::Expr
{
  top.val = if c.bval
            then th.val
            else el.val;
}
```
This has three elements in the result list from `encode_failure`:
1. `access__bval__Expr CNode attr_no`
2. `access__bval__Expr CNode (attr_ex btrue) /\
    access__val__Expr ThNode attr_no`
3. `access__bval__Expr CNode (attr_ex bfalse) /\
    access__val__Expr ElNode attr_no`
    
Based on this, we add three failure clauses to the equation component
relation (we will say this is part of the host language):
```
val__Expr__host (prod_ifThenElse C Th El)
     (ntr_Expr Node [ntr_Expr CNode _, ntr_Expr ThNode _,
                     ntr_Expr ElNode _]) :=
   access__val__Expr Node attr_no /\
   access__bval__Expr CNode attr_no;
val__Expr__host (prod_ifThenElse C Th El)
     (ntr_Expr Node [ntr_Expr CNode _, ntr_Expr ThNode _,
                     ntr_Expr ElNode _]) :=
   access__val__Expr Node attr_no /\
   access__bval__Expr CNode (attr_ex btrue) /\
   access__val__Expr ThNode attr_no
val__Expr__host (prod_ifThenElse C Th El)
     (ntr_Expr Node [ntr_Expr CNode _, ntr_Expr ThNode _,
                     ntr_Expr ElNode _]) :=
   access__val__Expr Node attr_no /\
   access__bval__Expr CNode (attr_ex bfalse) /\
   access__val__Expr ElNode attr_no;
```
We have a clause where the value of `val` on `top` is undefined
(`attr_no`) for each of the three ways the equation could fail to
produce a value.  These are in addition to the success cases we get.





# Missing Equations

If an attribute does not have an equation, we need to encode that the
attribute must be undefined.

If we have a child tree which has a particular **inherited attribute**
occur on it but for which there is no equation, we add to all clauses
defining the inherited attribute a condition that this attribute has
value `attr_no`.

If we do not have an equation for a **synthesized attribute** on the
root of a tree, we add a clause to the equation relation requiring
that the attribute have value `attr_no`.  This only happens on
non-forwarding productions; forwarding productions which do not define
a synthesized attribute always implicitly have an equation which
copies the value of the attribute from the forward; this copy equation
should be encoded, along with its failure mode.





# Local Attributes

Recall that local attributes are defined by equations which are
defined on a single production.  We need to add a clause which says
the local is undefined on all other productions.  This clause has two
pieces:
1. The current term is not built by the production on which the local
   occurs.
2. The attribute's value is undefined (`attr_no`).

As an example of what this looks like, let us consider the running
example from [Locals.md](Locals.md), where we have a production
`while` with a local `subWhile`.  Its updated equation relation would
be as follows:
```
Define while_local_subWhile : nt_Stmt -> node_tree -> prop by
  while_local_subWhile (prod_while Cond Body)
                       (ntr_Stmt Node [ntr_BExpr CondNode _,
                                       ntr_Stmt BodyNode _]) :=
     <actual defining clause #1>
  while_local_subWhile (prod_while Cond Body)
                       (ntr_Stmt Node [ntr_BExpr CondNode _,
                                       ntr_Stmt BodyNode _]) :=
     <actual defining clause #2>;
  while_local_subWhile Term (ntr_Stmt Node _) :=
     ((exists Cond Body, Term = prod_while Cond Body) -> false) /\
     access__while__local_subWhile__Stmt Node attr_no.
```
We have the two defining clauses from before (we omit their bodies
because those details are not relevant here).  We also have a third
defining clause which only applies to productions which are not built
from the `while` production, which requires the local to be undefined.

Adding a default equation clause for other productions makes it so
this equation relation will hold on any tree, not just trees built
from `while`.





# WPD Relations

We note here that our WPD relations do not change as a result of the
changes to the equation relations.  WPD node relations are still
collections of equation relations holding, and WPD nonterminal
relations still simply walk over the tree ensuring the WPD node
relations hold at each node.





# Simplification on Equations which Copy

We can simplify equations which copy the value of one attribute into
another attribute.  Copy equations for extension-introduced
attributes, as seen in
[ExtensionAttributes.md](ExtensionAttributes.md), are an example of
this.  This idea will be easiest to implement with these explicit copy
relations, and so might only end up used there, but it is applicable
other places as well.

Now that we are including failures in our equation relations, an
equation such as
```
t1.a = t2.b
```
translates into two clauses:  one clause for when `t2.b` has a value
(`attr_ex`) and one for when `t2.b` is undefined (`attr_no`).
However, it doesn't really matter whether it is defined or not, since
either way `t1.a` will get the same value of type `attrVal` as `t2.b`
has.  We can then replace these two clauses with a single clause,
which has the following two conditions:
```
   access__a__Nt1 T1Node AttributeValue /\
   access__b__Nt2 T2Node AttributeValue
```
Here `AttributeValue` has an `attrVal` type, so it is either
constructed by `attr_ex` or `attr_no`, and it doesn't matter which.

We can actually do this kind of simplification whenever we end up
assigning the value of one attribute into the another attribute, even
if it comes after some conditions.  For example, if we have
```
t1.a = if <cond> then t2.b else 5;
```
we could encode the case where `<cond>` is `true` by encoding `<cond>`
then accessing `t2.b` without checking for `attr_ex`, simply taking
the value which is in it.

For example, suppose we have the following production:
```
abstract production option5
top::Expr ::= e1::Expr e2::Expr
{
  top.val = if e1.bval then e2.val else 5;
}
```
We can then encode this equation as into the three following clauses:
```
val__Expr__host (prod_option5 E1 E2)
             (ntr_Expr Node [ntr_Expr E1Node _, ntr_Expr E2Node _]) :=
   access__val__Expr Node attr_no /\
   access__bval__Expr E1Node attr_no;
val__Expr__host (prod_option5 E1 E2)
             (ntr_Expr Node [ntr_Expr E1Node _, ntr_Expr E2Node _]) :=
   access__val__Expr Node (attr_ex 5) /\
   access__bval__Expr E1Node (attr_ex bfalse);
val__Expr__host (prod_option5 E1 E2)
             (ntr_Expr Node [ntr_Expr E1Node _, ntr_Expr E2Node _]) :=
   exists ValValue,
      access__val__Expr Node ValValue /\
      access__bval__Expr E1Node (attr_ex btrue) /\
      access__val__Expr E2Node ValValue;
```
The first clause is for the case where `e1.bval` is undefined.  The
second clause is for when `e1.bval` is `false`.  The third clause is
for when `e1.bval` is true.  Here we are copying the value of `e2.val`
to `top.val` without checking whether it is defined or not.  With our
simplification, we only need this one clause.  Without it, this would
be split into two clauses which would be identical other than one
replacing `ValValue` with `attr_ex Val` and one replacing it with
`attr_no`.

