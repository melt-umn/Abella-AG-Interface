grammar interface_:toAbella:abstractSyntax;


nonterminal Error with pp;

abstract production errorMsg
top::Error ::= msg::String
{
  top.pp = "Error:  " ++ msg;
}


--Because we want to do this a lot of places
function errors_to_string
String ::= errs::[Error]
{
  return foldr(\ e::Error rest::String -> e.pp ++ "\n" ++ rest,
               "", errs);
}

