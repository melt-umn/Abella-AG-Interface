grammar interface_:composed;


--Run through a list of files, checking them for validity
function run_files
IOVal<Integer> ::= ioin::IOToken filenames::[String] config::Decorated CmdArgs
{
  local ran::IOVal<Integer> = run_file(ioin, head(filenames), config);
  return
     case filenames of
     | [] -> ioval(ioin, 0)
     | hd::tl ->
       if ran.iovalue != 0
       then ran --error in that file, so quit
       else run_files(ran.io, tl, config)
     end;
}


--Run through a file to check that all the proofs are done correctly
function run_file
IOVal<Integer> ::= ioin::IOToken filename::String config::Decorated CmdArgs
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
     else run_step(
             fileAST.2.commandList,
             filename,
             ourSilverContext.iovalue,
             [(-1, handleIncoming.iovalue.2)],
             config,
             started.iovalue.fromRight,
             handleIncoming.io);
}


{--
  - Walk through a list of commands, processing the proofs they represent
  -
  - @inputCommands  The list of commands through which to walk
  - @filename  The name of the file we are processing, if any
  - @silverContext  The Silver elements we know (nonterminals, attributes, etc.)
  - @statelist  The state of the prover after each command issued to the prover.
  -             The current state of the prover is the first element of the list.
  - @config  The configuration of the process
  - @abella  The process in which Abella is running
  - @ioin  The incoming IO token
  - @return  The resulting IO token and exit status
-}
function run_step
IOVal<Integer> ::=
   inputCommands::[AnyCommand]
   filename::String
   silverContext::Decorated SilverContext
   stateList::[(Integer, ProverState)]
   config::Decorated CmdArgs
   abella::ProcessHandle ioin::IOToken
{
  local currentProverState::ProverState = head(stateList).snd;
  local state::ProofState = currentProverState.state;
  state.silverContext = silverContext;
  local debug::Boolean = currentProverState.debug;

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
  --an error or message based on our own checking
  local our_own_output::String = any_a.ownOutput;
  --Output if in debugging mode
  ----------------------------
  local debug_output::IOToken =
       if debug && config.showUser
       then printT(if speak_to_abella
                   then "Command sent:  " ++
                        implode("\n", (map((.pp), any_a.translation)))
                   else "Nothing to send to Abella",
                  ioin)
       else ioin;


  {-
    PROCESS OUTPUT
  -}
  --Send to Abella and read output
  ----------------------------
  local back_from_abella::IOVal<String> =
        if speak_to_abella
        then sendCmdsToAbella(map((.pp), any_a.translation), abella,
                              debug_output)
        else ioval(debug_output, "");
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
  local outputCleanCommands::IOToken =
        if debug && config.showUser
        then printT(cleaned.1 ++
                    "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n",
                    cleaned.5)
        else cleaned.5;
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
        then ioval(outputCleanCommands,
                   (head(newStateList).1, head(newStateList).2, ""))
        else handleIncomingThms(head(newStateList), silverContext,
                                abella, outputCleanCommands);
  local completeStateList::[(Integer, ProverState)] =
        (handleIncoming.iovalue.1, handleIncoming.iovalue.2)::tail(newStateList);
  local outputIncomingThms::IOToken =
        if debug && config.showUser
        then printT(handleIncoming.iovalue.3 ++
                    "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n", handleIncoming.io)
        else handleIncoming.io;
  --Show to user
  ----------------------------
  local debug_back_output::IOToken =
        if debug && speak_to_abella && config.showUser
        then printT("***** Read back from Abella: *****\n\n" ++
                    ( if shouldClean
                      then cleaned.3.pp
                      else back_from_abella.iovalue ) ++
                     "\n\n*****   End Abella output    *****\n\n\n",
                    outputIncomingThms)
        else outputIncomingThms;
  local subgoalCompletedNow::Boolean =
        subgoalCompleted(state.currentSubgoal,
                         head(any_a.stateListOut).snd.state.currentSubgoal) &&
        ! any_a.isUndo;
  local output_output::String =
      ( if subgoalCompletedNow
        then "Subgoal " ++ subgoalNumToString(state.currentSubgoal) ++ " completed\n"
        else "" ) ++
        if speak_to_abella
        then if shouldClean
             then foldr(\ x::[Integer] rest::String ->
                          "Subgoal " ++ subgoalNumToString(x) ++
                          " completed automatically\n" ++ rest,
                        "\n", cleaned.4) ++
                        decorate cleaned.3 with
                        {silverContext = silverContext;}.translation.pp ++ "\n"
             else full_a.translation.pp ++ "\n"
        else our_own_output ++ state.translation.pp ++ "\n";
  local printed_output::IOToken =
        if full_result.parseSuccess
        then if config.showUser
             then printT(output_output, debug_back_output)
             else debug_back_output
        else error("BUG:  Unable to parse Abella's output:\n\n" ++
                   back_from_abella.iovalue ++ "\n\n" ++ full_result.parseErrors ++
                   "\n\nPlease report this");


  {-
    EXIT
  -}
  --We can't use our normal send/read function because that looks for a new prompt
  local exit_out_to_abella::IOToken =
        sendToProcess(abella, implode("\n", map((.pp), any_a.translation)), debug_output);
  local wait_on_exit::IOToken = waitForProcess(abella, exit_out_to_abella);
  --Guaranteed to get all the output because we waited for the process to exit first
  local any_last_words::IOVal<String> = readAllFromProcess(abella, wait_on_exit);
  local output_last::IOToken =
        if config.showUser
        then printT(any_last_words.iovalue, any_last_words.io)
        else any_last_words.io;
  local exit_message::IOToken =
        if config.showUser
        then printT("Quitting.\n", output_last)
        else output_last;


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
        run_step(tail(inputCommands), filename, silverContext,
                 completeStateList, config, abella, printed_output);


  return
     case inputCommands of
     | [] ->
       if config.runningFile
       then if state.inProof
            then ioval(printT("Proof in progress at end of file " ++
                              filename ++ "\n", ioin), 1)
            else if !null(head(stateList).2.remainingObligations)
            then ioval(printT("Not all proof obligations fulfilled" ++
                              " in file " ++ filename ++ "\n", ioin),
                       1)
            else ioval(printT("Successfully processed file " ++
                              filename ++ "\n", ioin), 0)
       else ioval(ioin, 0)
     | _::tl ->
       if any_a.isQuit
       then ioval(exit_message, 0)
       else if config.runningFile --running file should end on error
            then if any_a.isError
                 then ioval(printT("Could not process full file " ++
                                   filename ++ ":\n" ++
                                   any_a.ownOutput ++ "\n",
                                   back_from_abella.io),
                            1)
                 else if full_a.isError
                 then ioval(printT("Could not process full file " ++
                                   filename ++ ":\n" ++ full_a.pp,
                                   back_from_abella.io), 1)
                 else again
            else again
     end;
}

