
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





# Abella Questions

- What is the difference between `clear H1 H2.` and `clear -> H1 H2'?
  I don't see any difference in result.
- What is `async.`?





