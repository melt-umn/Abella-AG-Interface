grammar interface_:toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp,
   translation<NoOpCommand>,
   errors, sendCommand, ownOutput, numCommandsSent,
   isQuit, isDebug,
   isUndo, undoListIn, undoListOut;

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
           else ""
      else "";
  top.numCommandsSent = if top.sendCommand then just(1) else just(0);

  top.isUndo = false;
  top.undoListOut = top.undoListIn;
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
  top.numCommandsSent = just(1);

  top.isUndo = false;
  top.undoListOut = top.undoListIn;
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
  top.numCommandsSent = just(1);

  top.isUndo = false;
  top.undoListOut = top.undoListIn;
}


--This is what Proof General uses for undoing things
abstract production backCommand
top::NoOpCommand ::= n::Integer
{
  top.pp = replicate(n - 1, "#back. ") ++ "#back.\n";

  local trans_n::Integer =
        foldr(\ p::(Integer, ProverState) i::Integer -> i + p.1,
              0, take(n, top.undoListIn));
  top.translation = backCommand(trans_n);

  top.errors <-
      if length(top.undoListIn) < n
      then [errorMsg("Too many #back commands")]
      else if any(map(\ p::(Integer, ProverState) -> p.1 == -1,
                      take(n, top.undoListIn)))
           then [errorMsg("Can't undo that far")]
           else [];

  top.isQuit = false;
  top.isDebug = pair(false, false);

  top.sendCommand = null(top.errors) && trans_n > 0;
  top.ownOutput = "";
  top.numCommandsSent = just(trans_n);

  top.isUndo = true;
  top.undoListOut = drop(n, top.undoListIn);
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
  top.numCommandsSent = just(1);

  top.isUndo = false;
  top.undoListOut = top.undoListIn;
}

