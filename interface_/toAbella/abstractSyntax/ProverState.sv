grammar interface_:toAbella:abstractSyntax;


--We have some new known theorems, which are the prop-quantified
--   theorems we are handling by proving as assertions, then using.
aspect function defaultProverState
ProverState ::=
{
  knownThms <-
     --We don't actually need the statements of any of these, so we
     --   won't go to the work of actually writing them.
     [
      ("is_list_member", "silver:core", trueMetaterm()),
      ("is_list_append", "silver:core", trueMetaterm()),
      ("symmetry", "silver:core", trueMetaterm()),
      ("attr_unique", "silver:core", trueMetaterm()),
      ("attr_is", "silver:core", trueMetaterm())
     ];
}

