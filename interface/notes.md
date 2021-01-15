
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

- We want to use attribute accesses as values and as relations on
  which we can do case analysis.  We need to have some way to talk
  about attributes having values as well (versus being undefined).
- We need to be able to generate variables for the tree structure and
  node when we do a binding.  This relies on typing and knowing the
  defined relations.
  + This might rely on some type inference, since we want to be able
    to write `forall t, ... t.a ...` and be able to figure out what
    type `t` has.
- Equality between tree types needs to be equality between the
  structures, not the nodes.
- We need to be able to do induction on a tree (actually the WPD
  relation for it), which requires `induction on L` where `L` is
  either   numbers or tree names, with the tree names then translated
  to   numbers in the translated theorems.  We will also need to keep
  track   of this in bringing the results back from Abella,
  translating the   restriction on WPD into a restriction on the tree
  and such.
- We need some way to say `t.a` exists, preferrably without actually
  saying `t.a = X` for some value `X`.  This may fall out as I work out
  the translation, since uses of t.a are going to translate to replace
  the t.a with something like `t__DOT__a` and add a premise of
  `access__a__NT t_Node (attr_ex t__DOT__a)`.
- We need to keep track of the extra things we add to theorems, or
  some standard way of figuring out what we add.  When the user
  applies something with the `apply` tactic, we migth need to add some
  things to the premises they are applying with.  For example, if we
  added a WPD premise, we need to give it a WPD premise.  The things
  we add can probably just be underscores.
- I eventually want a command to generate the required proof theorems
  for modular semantic preservation rather than requiring the user to
  write them.  They are based on case analysis, so they can be written
  by the machine.
  * With this, we'll need to do the instantiation of the fake
    inductive hypotheses ourselves and present them to the user.
    Abella won't take care of it, since it isn't real Abella
    induction.
- We are likely to get multiple Abella commands out of one interface
  command at some points.  For undoing, we're going to need to keep
  track of how many commands, so we can undo the correct number of
  times in Abella.
- If two accesses of the same attribute come up as separate hypotheses
  in a proof, we should automatically apply a theorem to show that the
  values they access are equal.  This is part of treating attribute
  accesses as values.
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





# Things to think about doing:

- Perhaps keep track of abbreviated hypotheses.  This might be useful
  so we know we shouldn't change what we get back in them.  If someone
  happens to abbreviate them to valid code, that would be a bad thing.
  These should be tracked in a scope way, so we know when the
  abbreviation is gone.
- Keep track of the last proof state.  This will let us do the Proof
  General show-proof thing, along with other checking.
- Check that all hypotheses used in a proof are ones that the user
  actually sees, not hidden ones.  This should eliminate a lot of
  frustrating bugs in proof creation.
- Based on ideas for working with hypotheses here, it might be a good
  idea to have nonterminals for single hypotheses and lists of
  hypotheses, to allow analysis on them.
- Check that all variables being used in a proof are ones that the
  sure actually sees, not hidden ones.
- We want to hide the fact that we're using relations for the
  attribute accesses, and so we also want to hide the fact that we're
  using component relations to enforce the unknowability of children.
  Therefore we should try to insert applications of theorems allowing
  us to move logically between the different levels of definitions
  without the user needing to be aware of them.
- I might cut down on the allowed identifiers in Abella.  If, for
  example, we cut `_` from the allowed starting characters for
  identifiers in the interface, we can start all the encoded relations
  and identifier names with underscores and be certain the names
  aren't anything the user is going to overwrite.
- I really like Coq's semantic bullet points.  It annoys me that
  Abella doesn't have them.  I would like to add them here.
- If we end up with the expected encoding of strings (list of
  characters, where the characters are members of a defined type), we
  should catch that and replace it with a more normal string-looking
  string of characters.
- Abella doesn't have the standard bracketed list syntax as far as I
  know (e.g. you can't write `[3, 4]`; you have to write `3::4::nil`).
  This might be nice to include in the interface.
- Maybe add our own option for `Set`, which could turn on and off
  displaying the raw Abella proof state.  This might be helpful for
  debugging, especially if it showed both proof states.  It could be
  something like `Set interface_debug (true | false).`
- It would be nice to have functions show as `fun(args) = result`
  rather than as as relation `fun <args> result`.
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





# Abella Questions

- What is the difference between `clear H1 H2.` and `clear -> H1 H2`?
  I don't see any difference in result.
  * Mary doesn't know either, and it isn't used in any examples in the
    Abella repository.  Perhaps the website?
- What is `async.`?
  * Mary doesn't know either, and it isn't used in any examples in the
    Abella repository.  Once again, perhaps the website has some
    examples?

