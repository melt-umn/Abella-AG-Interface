grammar interface_:toAbella:abstractSyntax;


{-
  We make the translation a string because it gives us a consistent
  type, even with ProofCommand translating to a list.  It is also one
  less thing the run_step function needs to handle.
-}

nonterminal AnyCommand with
   pp,
   translation<String>, currentState, translatedState, inProof,
   isQuit,
   sendCommand, ownOutput, numCommandsSent,
   stateListIn, stateListOut, newProofState, wasError;


abstract production anyTopCommand
top::AnyCommand ::= c::TopCommand
{
  top.pp = c.pp;

  top.translation = --c.translation.pp;
      --This is a hack to correctly read input when we import a file
      --Any file we import with this had better be correct, or it will crash or hang
      case c.translation of
      | textCommand(_) ->
        c.translation.pp ++ " Theorem $$done : true. abort. "
      | _ -> c.translation.pp
      end;

  top.isQuit = false;

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
      then case c.translation of
           | textCommand(_) -> nothing()
           | _ -> just(1)
           end
      else just(0);

  local currentState::ProverState = head(top.stateListIn).snd;
  local newProofState::ProofState =
        case c of
        | extensibleTheoremDeclaration(name, depth, metaterm, tree) ->
          extensible_proofInProgress(top.newProofState, c.translatedTheorem,
                                     name, c.numRelevantProds)
        | _ -> top.newProofState
        end;
  top.stateListOut =
      if top.wasError || top.inProof || !null(c.errors)
      then top.stateListIn
      else (case top.numCommandsSent of
            | just(x) -> x
            | nothing() -> -1
            end, proverState(
                    newProofState,
                    currentState.debug,
                    --Next lines need to change when we actually get it from imports
                    currentState.knownAttrs,
                    currentState.knownAttrOccurrences,
                    currentState.knownProductions,
                    currentState.knownWPDRelations,
                    currentState.knownInheritedAttrs)
           )::top.stateListIn;
}


abstract production anyProofCommand
top::AnyCommand ::= c::ProofCommand
{
  top.pp = c.pp;

  top.isQuit = false;

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
      then just(length(c.translation))
      else just(0);

  c.stateListIn = top.stateListIn;
  c.currentState = top.currentState;
  local currentState::ProverState = head(top.stateListIn).snd;
  local newProofState::ProofState =
        case currentState.state, top.newProofState of
        | extensible_proofInProgress(_, oMt, name, numProds), proofInProgress(_, _, _) ->
          extensible_proofInProgress(top.newProofState, oMt, name, numProds)
        | extensible_proofInProgress(_, oMt, name, numProds), noProof() ->
          noProof() --In this case, we need to send the cleanup commands (split and axiom), but I don't know how yet
        | _, _ -> top.newProofState
        end;
  top.stateListOut =
      if top.wasError || !top.inProof || !null(c.errors)
      then top.stateListIn
      else if c.isUndo
           then c.stateListOut
           else (case top.numCommandsSent of
                 | just(x) -> x
                 | nothing() -> -1
                 end, proverState(
                         newProofState,
                         currentState.debug,
                         currentState.knownAttrs,
                         currentState.knownAttrOccurrences,
                         currentState.knownProductions,
                         currentState.knownWPDRelations,
                         currentState.knownInheritedAttrs)
                )::top.stateListIn;
}


abstract production anyNoOpCommand
top::AnyCommand ::= c::NoOpCommand
{
  top.pp = c.pp;

  top.translation = c.translation.pp;

  top.isQuit = c.isQuit;

  top.sendCommand = null(c.errors) && c.sendCommand;
  top.ownOutput =
      if null(c.errors)
      then c.ownOutput
      else errors_to_string(c.errors) ++ "\n\n";
  top.numCommandsSent =
      if top.sendCommand
      then c.numCommandsSent
      else just(0);

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

  top.sendCommand = false;
  top.ownOutput = "Error:  Could not parse:\n" ++ parseErrors;
  top.numCommandsSent = just(0);

  top.stateListOut = top.stateListIn;
}

