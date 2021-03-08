grammar interface_:toAbella:abstractSyntax;


{-
  We make the translation a string because it gives us a consistent
  type, even with ProofCommand translating to a list.  It is also one
  less thing the run_step function needs to handle.
-}

nonterminal AnyCommand with
   pp,
   translation<String>, attrOccurrences, hypList, inProof,
   isQuit, isDebug,
   sendCommand, ownOutput, numCommandsSent,
   isUndo, undoListIn, undoListOut;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;

  top.translation = c.translation.pp;

  top.isQuit = false;
  top.isDebug = (false, false);

  top.sendCommand =
      if top.inProof
      then false
      else null(c.errors) && c.sendCommand;
  top.ownOutput =
      if top.inProof
      then "Error:  Cannot use top commands in a proof\n"
      else if null(c.errors)
           then c.ownOutput
           else errors_to_string(c.errors);
  top.numCommandsSent =
      if top.sendCommand
      then case c.translation of
           | textCommand(_) -> nothing()
           | _ -> just(1)
           end
      else just(0);

  top.isUndo = false;
  top.undoListOut = top.undoListIn;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;

  top.isQuit = false;
  top.isDebug = (false, false);

  c.hypList = top.hypList;

  top.translation =
      foldr(\ p::ProofCommand rest::String -> p.pp ++ rest,
            "", c.translation);

  top.sendCommand =
      if top.inProof
      then null(c.errors) && c.sendCommand
      else false;
  top.ownOutput =
      if top.inProof
      then if null(c.errors)
           then c.ownOutput
           else errors_to_string(c.errors)
      else "Error:  Cannot use proof commands outside a proof\n";
  top.numCommandsSent =
      if top.sendCommand
      then just(length(c.translation))
      else just(0);

  top.isUndo = c.isUndo;
  c.undoListIn = top.undoListIn;
  top.undoListOut = c.undoListOut;
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;

  top.translation = c.translation.pp;

  top.isQuit = c.isQuit;
  top.isDebug = c.isDebug;

  top.sendCommand = null(c.errors) && c.sendCommand;
  top.ownOutput =
      if null(c.errors)
      then c.ownOutput
      else errors_to_string(c.errors);
  top.numCommandsSent =
      if top.sendCommand
      then c.numCommandsSent
      else just(0);

  top.isUndo = c.isUndo;
  c.undoListIn = top.undoListIn;
  top.undoListOut = c.undoListOut;
}

