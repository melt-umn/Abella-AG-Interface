grammar interface_:fromAbella;


--imports fromAbella:concreteSyntax;
--imports fromAbella:abstractSyntax;


{-
  This is just to test parsing.  It is not permanent.
-}


parser topparse::FullDisplay_c
{
  interface_:fromAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}


function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local attribute args::String;
  args = implode(" ", largs);

  local attribute result::ParseResult<FullDisplay_c>;
  result = topparse(args, "<<args>>");
  local res_c::FullDisplay_c = result.parseTree;
  local res::FullDisplay = res_c.ast;
  res.silverContext = decorate emptySilverContext() with {};
  local trans::FullDisplay = res.translation;


  local attribute print_failure::IO;
  print_failure = print("Encountered a parse error:\n\n" ++
                        result.parseErrors ++ "\n\n",
                        ioin);

  return ioval(if result.parseSuccess
               then print("+++++++++ Parsed:\n" ++ res.pp ++ "\n\n+++++++++Translated:\n" ++ trans.pp ++ "\n", ioin)
               else print_failure, 0);
}

