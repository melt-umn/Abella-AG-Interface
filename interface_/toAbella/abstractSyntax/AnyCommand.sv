grammar interface_:toAbella:abstractSyntax;


{-
  We make the translation a string because it gives us a consistent
  type, even with ProofCommand translating to a list.  It is also one
  less thing the run_step function needs to handle.
-}

nonterminal AnyCommand with
   pp,
   translation<String>, currentState, translatedState, inProof, silverContext,
   isQuit, isUndo, shouldClean, mustClean,
   sendCommand, ownOutput, numCommandsSent, isError,
   stateListIn, stateListOut, newProofState, wasError;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;

  top.translation = c.translation.pp;

  top.isQuit = false;
  top.isUndo = false;
  --must clean if proving obligations without any actual proof needed
  --   (no new prods for imported extensible theorem)
  top.shouldClean = true;
  top.mustClean = true;

  top.sendCommand =
      if top.inProof
      then false
      else null(c.errors) && c.sendCommand;
  top.ownOutput =
      if top.inProof
      then "Error:  Cannot use top commands in a proof\n\n"
      else if null(c.errors)
           then c.ownOutput
           else errors_to_string(c.errors);
  top.isError = top.inProof || !null(c.errors);
  top.numCommandsSent =
      if top.sendCommand
      then c.numCommandsSent
      else 0;

  local currentState::ProverState = head(top.stateListIn).snd;
  --might be a good idea to put this logic into an attribute on TopCommand
  local newProofState::ProofState =
        case c of
        | extensibleTheoremDeclaration(depth, thms) ->
          extensible_proofInProgress(
             top.newProofState,
             c.translatedTheorems,
             c.numRelevantProds)
        | proveObligations(names) ->
          obligation_proofInProgress(
             top.newProofState,
             c.translatedTheorems,
             c.numRelevantProds)
        | _ -> top.newProofState
        end;
  top.stateListOut =
      if top.wasError || top.inProof || !null(c.errors)
      then top.stateListIn
      else (top.numCommandsSent,
            proverState(
               newProofState,
               c.provingTheorems,
               currentState.debug,
               currentState.clean,
               c.newKnownTheorems,
               currentState.remainingObligations)
           )::top.stateListIn;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;

  top.isQuit = false;
  top.isUndo = c.isUndo;
  top.shouldClean = c.shouldClean;
  top.mustClean =
      --extensible proof completed, so need to clean to assert it
      case top.newProofState of
      | proofCompleted() -> true
      | _ -> false
      end;

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
           else errors_to_string(c.errors) ++ "\n\n"
      else "Error:  Cannot use proof commands outside a proof\n\n";
  top.isError = !top.inProof || !null(c.errors);
  top.numCommandsSent =
      if top.sendCommand
      then length(c.translation)
      else 0;

  c.stateListIn = top.stateListIn;
  c.currentState = top.currentState;
  local currentState::ProverState = head(top.stateListIn).snd;
  currentState.replaceState = newProofState;
  local newProofState::ProofState =
        case top.currentState.state of
        | extensible_proofInProgress(_, oMt, numProds) ->
          extensible_proofInProgress(top.newProofState, oMt, numProds)
        | _ -> top.newProofState
        end;
  top.stateListOut =
      if top.wasError || !top.inProof || !null(c.errors)
      then top.stateListIn
      else if c.isUndo
           then c.stateListOut
           else (top.numCommandsSent,
                 currentState.replacedState)::top.stateListIn;
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;

  top.translation = c.translation.pp;

  top.isQuit = c.isQuit;
  top.isUndo = c.isUndo;
  top.shouldClean = false;
  top.mustClean = false;

  top.sendCommand = null(c.errors) && c.sendCommand;
  top.ownOutput =
      if null(c.errors)
      then c.ownOutput
      else errors_to_string(c.errors) ++ "\n\n";
  top.isError = !null(c.errors);
  top.numCommandsSent =
      if top.sendCommand
      then c.numCommandsSent
      else 0;

  c.stateListIn = top.stateListIn;
  top.stateListOut =
      if top.wasError || !null(c.errors)
      then top.stateListIn
      else c.stateListOut;
}


--Putting this in a production simplifies the run_step function
abstract production anyParseFailure
top::AnyCommand ::= parseErrors::String
{
  top.pp = "";

  top.translation = error("Should not translate anyParseFailure");

  top.isQuit = false;
  top.isUndo = false;
  top.shouldClean = false;
  top.mustClean = false;

  top.sendCommand = false;
  top.ownOutput = "Error:  Could not parse:\n" ++ parseErrors;
  top.isError = true;
  top.numCommandsSent = 0;

  top.stateListOut = top.stateListIn;
}

