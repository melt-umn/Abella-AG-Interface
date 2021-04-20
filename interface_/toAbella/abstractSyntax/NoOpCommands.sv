grammar interface_:toAbella:abstractSyntax;


--things that aren't connected to the logic, like setting options

nonterminal NoOpCommand with
   --pp should always end with a newline
   pp,
   translation<NoOpCommand>,
   errors, sendCommand, ownOutput, numCommandsSent,
   isQuit, isUndo,
   stateListIn, stateListOut;

--because we only intend to pass these through to Abella, we don't
--   need to actually know anything about the option or its value
--   other than its text, other than our own debug option
abstract production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.pp = "Set " ++ opt ++ " " ++ val ++ ".\n";

  top.translation = setCommand(opt, val);

  top.isQuit = false;
  top.isUndo = false;

  top.errors <-
      if opt == "debug" || opt == "clean"
      then if (val == "on" || val == "off")
           then []
           else [errorMsg("Unknown value '" ++ val ++
                          "' for key \"" ++ opt ++ "\"; expected 'on' or 'off'")]
      else [];

  top.sendCommand = opt != "debug" && opt != "clean";
  top.ownOutput =
      if opt == "debug" || opt == "clean"
      then if val == "on" || val == "off"
           then "Turning " ++ opt ++ " " ++ val ++ ".\n"
           else ""
      else "";
  top.numCommandsSent = if top.sendCommand then 1 else 0;

  local currentState::ProverState = head(top.stateListIn).snd;
  top.stateListOut =
      (top.numCommandsSent,
       proverState(currentState.state,
                   if opt == "debug"
                   then val == "on"
                   else currentState.debug,
                   currentState.knownAttrs,
                   currentState.knownAttrOccurrences,
                   currentState.knownProductions,
                   currentState.knownWPDRelations,
                   currentState.knownInheritedAttrs,
                   if opt == "clean"
                   then val == "on"
                   else currentState.clean,
                   currentState.knownTheorems)
      )::top.stateListIn;
}


abstract production showCommand
top::NoOpCommand ::= theoremName::String
{
  top.pp = "Show " ++ theoremName ++ ".\n";

  top.translation = showCommand(theoremName);

  top.errors <-
      if startsWith("$", theoremName)
      then [errorMsg("Cannot start theorem names with \"$\"")]
      else [];

  top.isQuit = false;
  top.isUndo = false;

  top.sendCommand = true;
  top.ownOutput = "";
  top.numCommandsSent = 1;

  top.stateListOut = (1, head(top.stateListIn).snd)::top.stateListIn;
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = "Quit.\n";

  top.translation = quitCommand();

  top.isQuit = true;
  top.isUndo = false;

  top.sendCommand = true;
  top.ownOutput = "";
  top.numCommandsSent = 1;

  top.stateListOut = (1, head(top.stateListIn).snd)::top.stateListIn;
}


--This is what Proof General uses for undoing things
abstract production backCommand
top::NoOpCommand ::= n::Integer
{
  top.pp = replicate(n - 1, "#back. ") ++ "#back.\n";

  local trans_n::Integer =
        foldr(\ p::(Integer, ProverState) i::Integer -> i + p.1,
              0, take(n, top.stateListIn));
  top.translation = backCommand(trans_n);

  top.errors <-
      if length(top.stateListIn) < n
      then [errorMsg("Too many #back commands")]
      else if any(map(\ p::(Integer, ProverState) -> p.1 == -1,
                      take(n, top.stateListIn)))
           then [errorMsg("Can't undo that far")]
           else [];

  top.isQuit = false;
  top.isUndo = true;

  top.sendCommand = null(top.errors) && trans_n > 0;
  top.ownOutput = "";
  top.numCommandsSent = trans_n;

  top.stateListOut = drop(n, top.stateListIn);
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = "#reset.\n";

  --I don't understand what this does, so I can't be sure about translating it
  top.translation = error("Translation not done in resetCommand yet");

  top.isQuit = false;
  top.isUndo = false;

  top.sendCommand = true;
  top.ownOutput = "";
  top.numCommandsSent = 1;

  top.stateListOut = top.stateListIn;
}


abstract production showCurrentCommand
top::NoOpCommand ::=
{
  top.pp = "Show $$current.\n";

  top.translation = showCurrentCommand();

  top.isQuit = false;
  top.isUndo = false;

  top.sendCommand = false;
  --Don't need to show anything, because current state will be shown by main
  top.ownOutput = "";
  top.numCommandsSent = 0;

  top.stateListOut = top.stateListIn;
}

