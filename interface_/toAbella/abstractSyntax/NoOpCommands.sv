grammar interface_:toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp,
   translation<NoOpCommand>,
   errors, sendCommand, ownOutput,
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
  top.isDebug = pair(opt == "debug" && (val == "on" || val == "off"), val == "on");

  top.errors <-
      if opt == "debug"
      then if (val == "on" || val == "off")
           then []
           else [errorMsg("Unknown value '" ++ val ++
                          "' for key \"debug\"; expected 'on' or 'off'")]
      else [];

  top.sendCommand = opt != "debug";
  top.ownOutput =
      if opt == "debug"
      then if val == "on" || val == "off"
           then "Turning debug " ++ val ++ ".\n"
           else errors_to_string(top.errors)
      else errors_to_string(top.errors);
}


abstract production showCommand
top::NoOpCommand ::= theoremName::String
{
  top.pp = "Show " ++ theoremName ++ ".\n";

  top.translation = showCommand(theoremName);

  top.isQuit = false;
  top.isDebug = pair(false, false);

  top.sendCommand = true;
  top.ownOutput = "";
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = "Quit.\n";

  top.translation = quitCommand();

  top.isQuit = true;
  top.isDebug = pair(false, false);

  top.sendCommand = true;
  top.ownOutput = "";
}


abstract production backCommand
top::NoOpCommand ::= n::Integer
{
  top.pp = replicate(n - 1, "#back. ") ++ "#back.\n";

  --This is what Proof General uses for undoing things
  top.translation = --error("Translation not done in backCommand yet");
      backCommand(n);
  --When we handle the undo list in the composed Main function, we need to move everything back based on this.
  --We also need to translate this based on the undo list numbers.
  --We need to hold onto the entire undo list, from all theorems, for this.

  top.isQuit = false;
  top.isDebug = pair(false, false);

  top.sendCommand = true;
  top.ownOutput = "";
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = "#reset.\n";

  --I don't understand what this does, so I can't be sure about translating it
  top.translation = --error("Translation not done in resetCommand yet");
      resetCommand();

  top.isQuit = false;
  top.isDebug = pair(false, false);

  top.sendCommand = true;
  top.ownOutput = "";
}

