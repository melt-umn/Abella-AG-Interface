grammar interface_:toAbella:abstractSyntax;


nonterminal Error with pp;

abstract production errorMsg
top::Error ::= msg::String
{
  top.pp = "Error:  " ++ msg;
}

