grammar fromAbella:abstractSyntax;


nonterminal FullDisplay with
   pp,
   translation<FullDisplay>,
   proof, isError, isWarning;

abstract production fullDisplay
top::FullDisplay ::= msg::ExtraInformation state::ProofState
{
  top.pp = msg.pp ++ (if msg.pp != "" then "\n\n" else "") ++ state.pp;

  top.translation = fullDisplay(msg.translation, state.translation);

  top.proof = state;
  top.isError = msg.isError;
  top.isWarning = msg.isWarning;
}





nonterminal ExtraInformation with
  pp,
  translation<ExtraInformation>,
  isError, isWarning;


abstract production emptyInformation
top::ExtraInformation ::=
{
  top.pp = "";

  top.translation = emptyInformation();

  top.isError = false;
  top.isWarning = false;
}


abstract production importInformation
top::ExtraInformation ::= moduleName::String
{
  top.pp = "Importing from \"" ++ moduleName ++ "\".";

  top.translation = importInformation(moduleName);

  top.isError = false;
  top.isWarning = false;
}


abstract production syntaxErrorInformation
top::ExtraInformation ::=
{
  top.pp = "Syntax error.";

  top.translation = syntaxErrorInformation();

  top.isError = true;
  top.isWarning = false;
}


abstract production processingError
top::ExtraInformation ::= msg::ProcessingErrorMessage
{
  top.pp = "Error: " ++ msg.pp;

  top.translation = processingError(msg.translation);

  top.isError = true;
  top.isWarning = false;
}


abstract production typingError
top::ExtraInformation ::= msg::TypingErrorMessage
{
  top.pp = "Typing Error.\n" ++ msg.pp;

  top.translation = typingError(msg.translation);

  top.isError = true;
  top.isWarning = false;
}


abstract production warningInformation
top::ExtraInformation ::= msg::WarningMessage
{
  top.pp = "Warning: " ++ msg.pp;

  top.translation = warningInformation(msg.translation);

  top.isError = false;
  top.isWarning = true;
}


abstract production alreadyImported
top::ExtraInformation ::= filepath::String
{
  top.pp = "Ignoring import: " ++ filepath ++ " has already been imported.";

  top.translation = alreadyImported(filepath);

  top.isError = false;
  top.isWarning = true;
}

