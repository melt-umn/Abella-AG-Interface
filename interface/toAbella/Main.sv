grammar toAbella;


--imports toAbella:concreteSyntax;
--imports toAbella:abstractSyntax;


{-
  This is just to test parsing.  It is not permanent.
-}


parser topparse::TopCommand_c
{
  toAbella:concreteSyntax;
}


parser proofparse::Command_c
{
  toAbella:concreteSyntax;
}

function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local attribute args::String;
  args = implode(" ", largs);

  local attribute result1::ParseResult<TopCommand_c>;
  result1 = topparse(args, "<<args>>");
  local res1_c::TopCommand_c = result1.parseTree;
  local res1::TopCommand = res1_c.ast;
  res1.attrOccurrences = [pair("a", [nameType("nt_Nt")])];


  local attribute result2::ParseResult<Command_c>;
  result2 = proofparse(args, "<<args>>");
  local res2_c::Command_c = result2.parseTree;
  local res2::ProofCommand = res2_c.ast;
  res2.attrOccurrences = [pair("a", [nameType("nt_Nt")])];


  local attribute print_failure::IO;
  print_failure = print("Encountered a parse error:\n\n" ++
                        result1.parseErrors ++ "\n\n" ++
                        result2.parseErrors ++ "\n\n",
                        ioin);

  return ioval(if result1.parseSuccess
               then print("Parsed as Top Command:\n" ++ res1.pp ++ "\n" ++ res1.translation.pp ++ "\n\n", ioin)
               else if result2.parseSuccess
                    then print("Parsed as Proof Command:\n" ++ res2.pp ++ "\n" ++ listProofCommandToString(res2.translation) ++ "\n\n", ioin)
                    else print_failure, 0);
}


function listProofCommandToString
String ::= l::[ProofCommand]
{
  return case l of
         | [] -> ""
         | h::t -> h.pp ++ listProofCommandToString(t)
         end;
}

