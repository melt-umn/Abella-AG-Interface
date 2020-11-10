grammar toAbella;


{-
  This is just to test parsing.  It is not permanent.
-}


parser topparse::TopCommand_c
{
  toAbella;
}


parser proofparse::Command_c
{
  toAbella;
}

{-
parser termparse::Term_c
{
  toAbella;
}


parser metatermparse::Metaterm_c
{
  toAbella;
}
-}

function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local attribute args::String;
  args = implode(" ", largs);

  local attribute result1::ParseResult<TopCommand_c>;
  result1 = topparse(args, "<<args>>");

  local attribute result2::ParseResult<Command_c>;
  result2 = proofparse(args, "<<args>>");
{-
  local attribute result3::ParseResult<Term_c>;
  result3 = termparse(args, "<<args>>");

  local attribute result4::ParseResult<Metaterm_c>;
  result4 = metatermparse(args, "<<args>>");
-}
  local attribute print_failure::IO;
  print_failure = print("Encountered a parse error:\n\n" ++
                        result1.parseErrors ++ "\n\n" ++
                        result2.parseErrors ++ "\n\n"{- ++
                        result3.parseErrors ++ "\n\n" ++
                        result4.parseErrors ++ "\n\n"-},
                        ioin);

  return ioval(if result1.parseSuccess
               then print("Parsed as Top Command\n\n", ioin)
               else if result2.parseSuccess
                    then print("Parsed as Proof Command\n\n", ioin)
                    else {-if result3.parseSuccess
                         then print("Parsed as Term\n\n", ioin)
                         else if result4.parseSuccess
                              then print("Parsed as Metaterm\n\n", ioin)
                              else-} print_failure, 0);
}

