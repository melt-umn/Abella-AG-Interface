grammar interface_:composed;


--Run through a list of files, checking them for validity
function run_files
IOVal<Integer> ::= ioin::IOToken filenames::[String]
{
  local ran::IOVal<Integer> = run_file(ioin, head(filenames));
  return
     case filenames of
     | [] -> ioval(ioin, 0)
     | hd::tl ->
       if ran.iovalue != 0
       then ran --error in that file, so quit
       else run_files(ran.io, tl)
     end;
}


--Run through a file to check that all the proofs are done correctly
function run_file
IOVal<Integer> ::= ioin::IOToken filename::String
{
  local fileExists::IOVal<Boolean> = isFileT(filename, ioin);
  local fileContents::IOVal<String> =
        readFileT(filename, fileExists.io);
  local fileParsed::ParseResult<FullFile_c> =
        file_parse(fileContents.iovalue, filename);
  local fileAST::(String, ListOfCommands) = fileParsed.parseTree.ast;
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
        processGrammarDecl(fileAST.1, fileContents.io);
  --
  local started::IOVal<Either<String ProcessHandle>> =
        startAbella(processed.io);
  --
  local ourSilverContext::IOVal<Decorated SilverContext> =
        set_up_abella_silver(
           fileAST.1, processed.iovalue.fromRight.1,
           processed.iovalue.fromRight.2, started.iovalue.fromRight,
           started.io);
  --
  local handleIncoming::IOVal<(Integer, ProverState, String)> =
        handleIncomingThms(
           (0, defaultProverState(processed.iovalue.fromRight.3)),
           ourSilverContext.iovalue, started.iovalue.fromRight,
           ourSilverContext.io);

  return
     if !fileExists.iovalue
     then ioval(printT("Given file " ++ filename ++ " does not exist\n",
                       fileExists.io), 1)
     else if !fileParsed.parseSuccess
     then ioval(printT("Syntax error:\n" ++ fileParsed.parseErrors ++
                       "\n", fileContents.io), 1)
     else if !processed.iovalue.isRight
     then ioval(printT("Error:  " ++ processed.iovalue.fromLeft ++
                       "\n", processed.io), 1)
     else if !started.iovalue.isRight
     then ioval(printT("Error:  " ++ started.iovalue.fromLeft ++
                       "\n", started.io), 1)
     else run_step_file(
             fileAST.2.commandList,
             filename,
             ourSilverContext.iovalue,
             [(-1, handleIncoming.iovalue.2)],
             started.iovalue.fromRight,
             handleIncoming.io);
}


{--
  - Walk through a list of commands, processing the proofs they represent
  -
  - @inputCommands  The list of commands through which to walk
  - @statelist  The state of the prover after each command issued to the prover.
  -             The current state of the prover is the first element of the list.
  - @abella  The process in which Abella is running
  - @ioin  The incoming IO token
  - @return  The resulting IO token and exit status
-}
function run_step_file
IOVal<Integer> ::=
   inputCommands::[AnyCommand]
   filename::String
   silverContext::Decorated SilverContext
   stateList::[(Integer, ProverState)]
   abella::ProcessHandle ioin::IOToken
{
  local currentProverState::ProverState = head(stateList).snd;
  local state::ProofState = currentProverState.state;
  state.silverContext = silverContext;

  {-
    PROCESS COMMAND
  -}
  --Translate command
  ----------------------------
  local any_a::AnyCommand = head(inputCommands);
  any_a.silverContext = silverContext;
  any_a.currentState = currentProverState;
  any_a.translatedState = state.translation;
  any_a.inProof = state.inProof;
  any_a.stateListIn = stateList;
  --whether we have an actual command to send to Abella
  local speak_to_abella::Boolean = any_a.sendCommand;
  --Send to abella
  ----------------------------
  local out_to_abella::IOToken =
        if speak_to_abella
        then sendToProcess(abella, any_a.translation, ioin)
        else ioin;


  {-
    PROCESS OUTPUT
  -}
  --Read output
  ----------------------------
  local back_from_abella::IOVal<String> =
        if speak_to_abella
        then read_abella_outputs(any_a.numCommandsSent, abella, out_to_abella)
        else ioval(out_to_abella, "");
  --Translate output
  ----------------------------
  local full_result::ParseResult<FullDisplay_c> =
        from_parse(back_from_abella.iovalue, "<<output>>");
  local full_a::FullDisplay = full_result.parseTree.ast;
  full_a.silverContext = silverContext;
  any_a.wasError =
        if speak_to_abella
        then !full_result.parseSuccess || full_a.isError
        else false;
  any_a.newProofState = full_a.proof;
  --Clean up state
  ----------------------------
  local shouldClean::Boolean =
        full_result.parseSuccess && !full_a.isError && any_a.shouldClean &&
        (currentProverState.clean || any_a.mustClean);
  local cleaned::(String, Integer, FullDisplay, [[Integer]], IOToken) =
        if shouldClean
        then cleanState(decorate full_a with
                        {replaceState = head(any_a.stateListOut).snd.state;}.replacedState,
                        silverContext, abella, back_from_abella.io)
        else ("", 0, decorate full_a with
                     {replaceState = head(any_a.stateListOut).snd.state;}.replacedState,
              [], back_from_abella.io);
  local newStateList::[(Integer, ProverState)] =
        (head(any_a.stateListOut).fst + cleaned.2,
         --just replace the proof state in the ProverState
         decorate head(any_a.stateListOut).snd with
           {replaceState = cleaned.3.proof;}.replacedState)::tail(any_a.stateListOut);
  --Show to user
  ----------------------------
  --Process any imported theorems we can now add
  ----------------------------
  local handleIncoming::IOVal<(Integer, ProverState, String)> =
        if head(newStateList).2.state.inProof
        then ioval(back_from_abella.io,
                   (head(newStateList).1, head(newStateList).2, ""))
        else handleIncomingThms(head(newStateList), silverContext,
                                abella, back_from_abella.io);
  local completeStateList::[(Integer, ProverState)] =
        (handleIncoming.iovalue.1, handleIncoming.iovalue.2)::tail(newStateList);


  {-
    EXIT
  -}
  local wait_on_exit::IOToken = waitForProcess(abella, out_to_abella);
  --We can't use our normal read function because that looks for a new prompt
  --Guaranteed to get all the output because we waited for the process to exit first
  local exit_message::IOVal<String> =
        readAllFromProcess(abella, wait_on_exit);


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
        run_step_file(tail(inputCommands), filename, silverContext,
                      completeStateList, abella, handleIncoming.io);


  return
     case inputCommands of
     | [] ->
       if state.inProof
       then ioval(printT("Proof in progress at end of file " ++
                         filename ++ "\n", ioin), 1)
       else if !null(head(stateList).2.remainingObligations)
       then ioval(printT("Not all proof obligations fulfilled in file " ++
                         filename ++ "\n", ioin), 1)
       else ioval(printT("Successfully processed file " ++
                         filename ++ "\n", ioin), 0)
     | _::tl ->
       if any_a.isQuit
       then ioval(exit_message.io, 0)
       else if any_a.isError
       then ioval(printT("Could not process full file " ++ filename ++
                         ":\n" ++ any_a.ownOutput ++ "\n",
                         back_from_abella.io),
                  1)
       else if full_a.isError
       then ioval(printT("Could not process full file " ++ filename ++
                         ":\n" ++ full_a.pp, back_from_abella.io), 1)
       else again
     end;
}

