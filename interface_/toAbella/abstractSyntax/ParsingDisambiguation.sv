grammar interface_:toAbella:abstractSyntax;

{-
  The purpose of these productions is to disambiguate between the
  different application types (`f(a, b, c)` vs. `f a b c`) which we
  get from Silver and Abella.  The disambiguation is based on the
  lists of known functions and productions in the current state, as
  well as the forms of the applied term and the arguments.

  These break flow types for forwarding.  This is okay in our
  situation because, in our scheme, these cannot occur anywhere other
  than immediately after parsing in the context of the toAbella
  grammar.  It would be better if they didn't break it, but such is
  life.
-}


aspect production disambiguateEqMetaterm
top::Metaterm ::= leftSide::Term rightSide::Term
{
  top.errors <-
      case leftFun, rightFun of
      | just(_), just(_) ->
        [errorMsg("Can only have one function in an equality")]
      | _, _ -> []
      end;
}



aspect production disambiguateApplicationTerm
top::Term ::= f::Term args::TermList
{
}

