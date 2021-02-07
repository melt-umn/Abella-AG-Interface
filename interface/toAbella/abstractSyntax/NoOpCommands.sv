grammar toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp,
   translation<NoOpCommand>,
   isQuit, isDebug;

--because we only intend to pass these through to Abella, we don't
--   need to actually know anything about the option or its value
--   other than its text, other than our own debug option
abstract production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.pp = "Set " ++ opt ++ " " ++ val ++ ".\n";

  top.translation = setCommand(opt, val);

  top.isQuit = false;
  --We'll be lazy and let anything with debug other than "on" be equivalent to "off"
  --Since users shouldn't be using this option, it's fine to be sloppy with it
  top.isDebug = pair(opt == "debug", val == "on");
}


abstract production showCommand
top::NoOpCommand ::= theoremName::String
{
  top.pp = "Show " ++ theoremName ++ ".\n";

  top.translation = showCommand(theoremName);

  top.isQuit = false;
  top.isDebug = pair(false, false);
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = "Quit.\n";

  top.translation = quitCommand();

  top.isQuit = true;
  top.isDebug = pair(false, false);
}


abstract production backCommand
top::NoOpCommand ::=
{
  top.pp = "#back.\n";

  --I don't understand what this does, so I can't be sure about translating it
  top.translation = error("Translation not done in backCommand yet");

  top.isQuit = false;
  top.isDebug = pair(false, false);
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = "#reset.\n";

  --I don't understand what this does, so I can't be sure about translating it
  top.translation = error("Translation not done in resetCommand yet");

  top.isQuit = false;
  top.isDebug = pair(false, false);
}

