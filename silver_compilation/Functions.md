
In Silver, we occasionally define functions to help us write attribute
equations more easily.  We must encode these functions and calls to
them in our encoding scheme as well.





# Declared Functions

Let's consider the following Silver function as a running example:
```
function member
Boolean ::= x::Integer l::[Integer]
{
  return if null(l)
         then false
         else if x == head(l)
              then true
              else member(x, tail(l));
}
```
We could write this with pattern matching, but we'll write it with the
list functions instead to avoid all the overhead of explaining pattern
matching.



## Encoding Functions

We can encode a function as a relation with the same types of
arguments as the Silver function (appropriately encoded, of course),
with an additional argument for the result of the function.

We can encode a function into a relation by encoding the `return`
expression, with different clauses for different branches of the
expression.  The above `member` function would be encoded as follows:
```
Define member : integer -> list integer -> boolean -> prop by
  member X nil bfalse;
  member X (X::_) btrue;
  member X (H::T) SubResult :=
     (X = H -> false) /\ member X T SubResult.
```
A question that might arise from those thinking logically:  Why do we
include the condition `X = H -> false` in the last clause?  If we left
it out, we would get the same set of provable goals.  However, that is
not what Silver does, and we are trying to encode something of how
Silver *works*, not just its results.


### Nonterminal Arguments

If we have a nonterminal-type argument, we only take the term
structure as an argument (unless it is declared as a decorated
argument, in which case we also take the `node_tree` containing the
attribute values).  We need to decorate such an argument.  We can do
this by including a `node_tree` variable in the body of the clause,
encoding any equations for its attributes, and requiring it follows
all equations (in a manner which we will discuss later).  The
difference from encoding attribute equations is that we take the
encoding of the clause and join it to the result of encoding the
expression in the `return`.  If any of the equations branch, we need
to create all possible combinations of the branches (e.g. the `t.a`
equation has branches `A` and `B` and the `t.c` equation has branches
`C` and `D` means we need clauses for `(A,C)`, `(A,D)`, `(B,C)`, and
`(B,D)`).

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
    exists Node Children,
      wpd_Nt T (ntr_Nt Node Children) /\
      access__ia__Nt Node (attr_ex "ia") /\
      access__sa__Nt Node (attr_ex Result).
```



## Encoding Function Calls

We encode function calls by encoding the arguments, then giving their
results to the encoded function as arguments:
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





# Lambda Functions

I haven't actually considered the encoding of lambda functions in any
depth.  I don't think they're all that common unless someone wants to
use a `map` or something similar.

That being said, I don't think they are too difficult to handle.  They
can probably be encoded into a relation in the same way that declared
functions are.





# Partial Applications

I haven't considered partial applications either.  They can be viewed
as lambdas over the original functions to reorder the arguments, so
solutions to that problem should provide solutions to this.

