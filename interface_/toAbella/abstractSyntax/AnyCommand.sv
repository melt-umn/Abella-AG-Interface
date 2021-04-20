grammar interface_:toAbella:abstractSyntax;


{-
  We make the translation a string because it gives us a consistent
  type, even with ProofCommand translating to a list.  It is also one
  less thing the run_step function needs to handle.
-}

nonterminal AnyCommand with
   pp,
   translation<String>, currentState, translatedState, inProof, abellaFileParser,
   isQuit, isUndo, shouldClean, mustClean,
   sendCommand, ownOutput, numCommandsSent,
   stateListIn, stateListOut, newProofState, wasError;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;

  top.translation = c.translation.pp;
      --This is a hack to correctly read input when we import a file
      --Any file we import with this had better be correct, or it will crash or hang
      {-case c.translation of
      | textCommand(_) ->
        c.translation.pp ++ " Theorem $$done : true. abort. "
      | _ -> c.translation.pp
      end;-}

  top.isQuit = false;
  top.isUndo = false;
  top.shouldClean = false;
  top.mustClean = false;

  c.abellaFileParser = top.abellaFileParser;

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
  top.numCommandsSent =
      if top.sendCommand
      then c.numCommandsSent
      else 0;

  local currentState::ProverState = head(top.stateListIn).snd;
  local newProofState::ProofState =
        case c of
        | extensibleTheoremDeclaration(name, depth, metaterm, tree) ->
          extensible_proofInProgress(
             top.newProofState, c.translatedTheorem,
             name, c.numRelevantProds)
        | _ -> top.newProofState
        end;
  top.stateListOut =
      if top.wasError || top.inProof || !null(c.errors)
      then top.stateListIn
      else (top.numCommandsSent,
            proverState(
               newProofState,
               currentState.debug,
               --Next lines need to change when we actually get it from imports
               c.newKnownAttrs,
               c.newKnownAttrOccurrences,
               c.newKnownProductions,
               c.newKnownWPDRelations,
               c.newKnownInheritedAttrs,
               currentState.clean,
               c.newKnownTheorems)
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
      case top.currentState.state, top.newProofState of
      | extensible_proofInProgress(_, _, _, _),
        proofCompleted() ->
        true
      | _, _ -> false
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
  top.numCommandsSent =
      if top.sendCommand
      then length(c.translation)
      else 0;

  c.stateListIn = top.stateListIn;
  c.currentState = top.currentState;
  local currentState::ProverState = head(top.stateListIn).snd;
  local newProofState::ProofState =
        case top.currentState.state of
        | extensible_proofInProgress(_, oMt, name, numProds) ->
          extensible_proofInProgress(top.newProofState, oMt, name, numProds)
        | _ -> top.newProofState
        end;
  top.stateListOut =
      if top.wasError || !top.inProof || !null(c.errors)
      then top.stateListIn
      else if c.isUndo
           then c.stateListOut
           else (top.numCommandsSent,
                 proverState(
                    newProofState,
                    currentState.debug,
                    currentState.knownAttrs,
                    currentState.knownAttrOccurrences,
                    currentState.knownProductions,
                    currentState.knownWPDRelations,
                    currentState.knownInheritedAttrs,
                    currentState.clean,
                    currentState.knownTheorems)
                )::top.stateListIn;
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
  top.numCommandsSent = 0;

  top.stateListOut = top.stateListIn;
}

