
# Philosophy

There are two implementation details we are looking to hide with this
interface.

The first thing is the interface should be to hide the details of the
implementation of extensibility.  We should never see anything that
shows how extinsibility is implemented.  It should look just like we
are doing proofs in the composition but without being able to look at
children.

The secondary thing to hide is the details of how we are encoding
attribute grammars from Silver into Abella.  This gets quite messy,
but I believe it is well-ordered enough that we can handle it with a
higher level of abstraction presented to the user.

While we are hiding details, this is still essentially Abella.  We
want to follow the Abella style when it doesn't interfere with hiding
the implementation details as described above.





# General notes

- We probably want to ban case analysis on operations like addition.
  There is nothing the user should gain by looking at how arithmetic
  operations are implemented, since that isn't really how they should
  be looking at them.  Boolean operations should still allow case
  analysis, since that gives useful information about the operands
  being `true` or `false`.
- To take care of things like addition, we probably want to try to
  automatically simplify things that can be simplified.  For example,
  if we have `1 + 3 = X`, we probably want to automatically turn that
  `X` into `4`.  Similarly, if we have `X + 0 = Y` or vice versa, we
  might want to unify `X` and `Y`.
  + We might think of a `compute <hyp>` tactic to figure out the
    missing value in a use of an operation.  This could handle
    hypotheses such as `X + 3 = 5`, `3 + X = 5`, or `3 + 2 = X`, or
    other operations which we can solve by simple arithmetic in
    Silver.





# Todo

- On line 205 in the `imp:host` theorems, it requires doing case
  analysis on the local's structure before doing case analysis on its
  inherited attribute.  There is no reason this should be required.
  It appears to be a problem with identifying it as a known tree,
  based on the error message.
- On line 262 in the calculator theorems, it is displaying
  `silver:core:append` rather than turning it into a use of `++`
- If an attr access or structure eq is used wrong, it currently
  displays an error message with the dollar signs and all.  This
  should be changed to better error messages.
- Backchain doesn't have much of anything set up---no apparent error
  checking, no special theorems.  It should.





# Things to think about doing:

- Perhaps keep track of abbreviated hypotheses.  This might be useful
  so we know we shouldn't change what we get back in them.  If someone
  happens to abbreviate them to valid code, that would be a bad thing.
  These should be tracked in a scope way, so we know when the
  abbreviation is gone.
- I really like Coq's semantic bullet points.  It annoys me that
  Abella doesn't have them.  I would like to add them here.
- I'm having problems with parsing in `fromAbella` if I include
  abbreviated hypotheses.  We could just disallow abbreviation;
  alternatively, we could change the command `abbrev H "text".` into
  `abbrev H "'text'".`  By quoting the text, we turn it into something
  which can't be mistaken for a normal metaterm, and thus we can allow
  abbreviation.  We would, of course, remove our added quotes for the
  display back.  Alternatively, we could track abbreviated hypotheses
  and abbreviate them ourselves rather than actually abbreviating them
  with Abella.  This might make some of the automation we are thinking
  about go easier.
- It would be nice to have some kind of a `Search` like Coq has to
  find relevant theorems, based on the relation being used or
  something like that.
- It is not always obvious what the necessary pieces are to prove a
  function holds.  Perhaps there is a way to display function
  definitions in an Abella way without the user needing to open the
  definitions file and read the actual Abella relation.





# Abella Questions

- What is the difference between `clear H1 H2.` and `clear -> H1 H2`?
  I don't see any difference in result.
  * Mary doesn't know either, and it isn't used in any examples in the
    Abella repository.  Perhaps the website?
- What is `async.`?
  * Mary doesn't know either, and it isn't used in any examples in the
    Abella repository.  Once again, perhaps the website has some
    examples?

