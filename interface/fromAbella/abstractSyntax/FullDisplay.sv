grammar fromAbella:abstractSyntax;


nonterminal FullDisplay with
   pp,
   translation<FullDisplay>;

abstract production fullDisplay
top::FullDisplay ::= msg::ExtraInformation state::ProofState
{
  top.pp = msg.pp ++ (if msg.pp != "" then "\n\n" else "") ++ state.pp;

  top.translation = fullDisplay(msg.translation, state.translation);
}





nonterminal ExtraInformation with
  pp,
  translation<ExtraInformation>;


abstract production emptyInformation
top::ExtraInformation ::=
{
  top.pp = "";

  top.translation = emptyInformation();
}


abstract production proofCompleted
top::ExtraInformation ::=
{
  top.pp = "Proof completed.";

  top.translation = proofCompleted();
}


abstract production proofAborted
top::ExtraInformation ::=
{
  top.pp = "Proof ABORTED.";

  top.translation = proofAborted();
}


abstract production importInformation
top::ExtraInformation ::= moduleName::String
{
  top.pp = "Importing from \"" ++ moduleName ++ "\".";

  top.translation = importInformation(moduleName);
}


abstract production syntaxErrorInformation
top::ExtraInformation ::=
{
  top.pp = "Syntax error.";

  top.translation = syntaxErrorInformation();
}


abstract production processingError
top::ExtraInformation ::= msg::ProcessingErrorMessage
{
  top.pp = "Error: " ++ msg.pp;

  top.translation = processingError(msg.translation);
}


abstract production typingError
top::ExtraInformation ::= msg::TypingErrorMessage
{
  top.pp = "Typing Error.\n" ++ msg.pp;

  top.translation = typingError(msg.translation);
}


abstract production warningInformation
top::ExtraInformation ::= msg::WarningMessage
{
  top.pp = "Warning: " ++ msg.pp;

  top.translation = warningInformation(msg.translation);
}


abstract production alreadyImported
top::ExtraInformation ::= filepath::String
{
  top.pp = "Ignoring import: " ++ filepath ++ " has already been imported.";

  top.translation = alreadyImported(filepath);
}

