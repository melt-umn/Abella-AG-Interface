grammar toAbella;


{-
  This is just to test parsing.  It is not permanent.
-}


parser topparse::TopCommand
{
  toAbella;
}


parser proofparse::Command
{
  toAbella;
}


parser termparse::Term
{
  toAbella;
}


parser metatermparse::Metaterm
{
  toAbella;
}


function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local attribute args::String;
  args = implode(" ", largs);

  local attribute result1::ParseResult<TopCommand>;
  result1 = topparse(args, "<<args>>");

  local attribute result2::ParseResult<Command>;
  result2 = proofparse(args, "<<args>>");

  local attribute result3::ParseResult<Term>;
  result3 = termparse(args, "<<args>>");

  local attribute result4::ParseResult<Metaterm>;
  result4 = metatermparse(args, "<<args>>");

  local attribute print_failure::IO;
  print_failure = print("Encountered a parse error:\n\n" ++
                        result1.parseErrors ++ "\n\n" ++
                        result2.parseErrors ++ "\n\n" ++
                        result3.parseErrors ++ "\n\n" ++
                        result4.parseErrors ++ "\n\n",
                        ioin);

  return ioval(if result1.parseSuccess
               then print("Parsed as Top Command\n\n", ioin)
               else if result2.parseSuccess
                    then print("Parsed as Proof Command\n\n", ioin)
                    else if result3.parseSuccess
                         then print("Parsed as Term\n\n", ioin)
                         else if result4.parseSuccess
                              then print("Parsed as Metaterm\n\n", ioin)
                              else print_failure, 0);
}

