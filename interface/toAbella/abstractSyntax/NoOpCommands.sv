grammar toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp;

--because we only intend to pass these through to Abella, we don't
--   need to actually know anything about the option or its value
--   other than its text
abstract production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.pp = "Set " ++ opt ++ " " ++ val ++ ".\n";
}


abstract production showCommand
top::NoOpCommand ::= theoremName::String
{
  top.pp = "Show " ++ theoremName ++ ".\n";
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = "Quit.\n";
}


abstract production backCommand
top::NoOpCommand ::=
{
  top.pp = "#back.\n";
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = "#reset.\n";
}

