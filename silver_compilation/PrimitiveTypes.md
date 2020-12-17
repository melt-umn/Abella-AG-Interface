
In the [BasicEncoding.md](BasicEncoding.md) document, we described
encodings of the Silver `Boolean` and `Integer` types into Abella.  We
discuss here encoding other primitive and quasi-primitive types into
Abella.

As noted in the basic document, the encoding of primitive types is
probably the encoding which is most dependent on what relational
system we are using.  Therefore these encodings are specific to
Abella, and might be very different if we encode into a different
system.

We separate this document into classes of how necessary it is to
handle these types as primitives, or to handle them at all.





# Important Primitive Types

Some primitive types are used very often in Silver, so we need to
encode them.  This section contains not only the `String` type, but
also the `Boolean` and `Integer` types we discussed in
[BasicEncoding.md](BasiceEncoding.md).



## String

I'm not quite sure how to handle strings.  Something that would
probably work is to encode characters as constants, then use lists
of characters as strings:
```
Kind char   type.
Type c_a, c_b, c_c, c_d, c_e, c_f, c_g, c_h, c_i, c_j, c_k   char.
Type c_l, c_m, c_n, c_o, c_p, c_q, c_r, c_s, c_t, c_u, c_v   char.
Type c_w, c_x, c_y, c_z, c_1, c_2, c_3, c_4, c_5, c_6, c_7   char.
Type c_8, c_9, c_0, c__   char.
```
We can then define operations over these strings with relations.

We could encode all possible characters, since the set is finite, even
though I didn't do that in the above.  We could encode them as
`c_<ordinal>`, and rely on the interface to show them to the user as
actual characters.

We use `String`s in Silver to represent identifier names very often,
so we very much to have an encoding for them.





# Core Types to Encode as Primitives

This section contains types which aren't actually primitive in Silver,
but which are used as if they were primitive types.  We could encode
these as we encode nonterminals, but it is simpler to treat them as
primitives, and thus we want to encode them as such.



## [A]

Lists are one of two data structures of which I am aware which are
actually built into Abella.  Therefore it makes sense to use the
built-in lists to encode any Silver lists.

We can encode `++` with an `append` relation on lists.  We can encode
other common functions on lists directly:
```
encode Env L Ll Lx
----------------------------------------
encode Env (null L)
       [Ll /\ Lx = [] /\ x = btrue,
        Ll /\ Lx = _::_ /\ x = bfalse] x
        
encode Env L Ll Lx
----------------------------------------
encode Env (head L) [Ll /\ Lx = A::_ /\ x = A] x

encode Env L Ll Lx
----------------------------------------
encode Env (tail l) [Ll /\ Lx = _::A /\ x = A] x
```
Other functions we might have can be encoded either directly or as
relations.



## Pair<A B>

We need to build our own pairs, which we are using elsewhere as well.
We can encode pairs as
```
Kind pair   type -> type -> type.
Type pair_c   A -> B -> pair A B.
```
We can encode `fst` as follows:
```
encode Env p pl px
----------------------------------------
encode Env (fst p) [pl /\ px = pair_c A B /\ x = A] x
```
We can encode `snd` similarly.  We can also encode `p.fst` and `p.snd`
in this way.

We will need pairs for local attributes and forwards (discussed in
[Locals.md](Locals.md) and [Forwards.md](Forwards.md)), so we need to
include this definition regardless of whether we are going to encode
Silver pairs or not.



## Others

We could encode other core types, like `Maybe`, `Either`, etc. as
primitive types as well, since they don't really get used as
nonterminal types.  We can figure out what we need as we start
reasoning about some grammars.





# Other Types

This section contains the actual primitive types in Silver which we
have not yet discussed.  These are the types that are not used very
often, so it isn't too important that we have an encoding of them.



## Float

I'm not quite sure how to handle floating-point numbers.  We can't
encode them for real, as we could do with integers.  We might treat
them as unknowable quantities, that is, define them and their
operations as follows:
```
Kind float   type.
Type plusFloat   float -> float -> float -> prop.
```
This says there is a type `float`, and we have a way of relating three
`float`s, but we do not say anything about elements of `float`.
Abella lets us do this safely, since we can't do case analysis on
anything that isn't defined as a relation.  We could probably do all
the reasoning on floating-point numbers that we need to do by defining
relations like this and declaring axioms over them (e.g. if `a > b`
then adding `a` to `c` is greater than adding `b` to `c`).

Another possibility is to encode them as rational numbers, as
discussed
[here](https://dl.acm.org/doi/pdf/10.1145/79204.79210?casa_token=ASUKkRej0gUAAAAA:vDI6abC0uagF1CxwVPW3Y24eRazJlKGAjgjvlHn_OIDKZZvVijzfc6qtipusewm6O4Kgx5tuxq25).
While this doesn't perfectly capture the essence of a floating-point
numbers, it is probably close enough for anything we're interested
in.  We might treat them as rational numbers where the denominator is
a multiple of 10.

Finally, we might treat them as pairs of lists of digits
(e.g. `712.04` would be `([7, 1, 2], [0, 4])`), then define operations
over them syntactically.  This also misses the vagaries of true
floating-point numbers but is probably close enough for what we're
doing.

When we get serious about adding these (if we get serious about adding
these), I should look up CompCert and see how they handle the
semantics of floating-point numbers.

I don't think floating-point numbers ever come up other than in
interpreters over languages which have floating-point numbers, so this
may not be something we're really concerned about adding.



## IO

I don't know enough about the Silver `IO` primitive type to suggest an
encoding for it.  However, I also don't think there is a lot one would
want to prove about this, so I think putting it off is okay for now
(or forever).

