grammar interface_:composed;


--Run a REPL for the theorem prover
--First entry must be a grammar declaration (Grammar na:me.)
function run_interactive
IOVal<Integer> ::= ioin::IO
{
  local grammarName::IOVal<String> = get_grammar_interactive(ioin);
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
        processGrammarDecl(grammarName.iovalue, grammarName.io);
  --
  local started::IOVal<Either<String ProcessHandle>> =
        startAbella(grammarName.io);
  --
  local build_context::IOVal<Decorated SilverContext> =
        set_up_abella_silver(grammarName.iovalue,
           processed.iovalue.fromRight.1,
           processed.iovalue.fromRight.2,
           started.iovalue.fromRight, started.io);
  --
  local handleIncoming::IOVal<(Integer, ProverState, String)> =
        handleIncomingThms(
           (0, defaultProverState(processed.iovalue.fromRight.3)),
           build_context.iovalue, started.iovalue.fromRight,
           build_context.io);

  return
     if !processed.iovalue.isRight
     then ioval(print("Error:  " ++ processed.iovalue.fromLeft ++
                      "\n", processed.io), 1)
     else if !started.iovalue.isRight
     then ioval(print("Error:  " ++ started.iovalue.fromLeft ++
                      "\n", started.io), 1)
     else run_step_interactive(
             [(-1, handleIncoming.iovalue.2)],
             build_context.iovalue, started.iovalue.fromRight,
             handleIncoming.io);
}


--Continue trying to get a grammar declaration from the user until
--   they actually give one
function get_grammar_interactive
IOVal<String> ::= ioin::IO
{
  local printed_prompt::IO = print(" < ", ioin);
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExternalWhiteSpace(raw_input.iovalue);
  --
  local result::ParseResult<GrammarDecl_c> =
        grammar_decl_parse(input, "<<input>>");
  return
     if result.parseSuccess
     then ioval(raw_input.io, result.parseTree.ast)
     else get_grammar_interactive(
             print("Error:  First entry must be a grammar\n" ++
                   result.parseErrors ++ "\n\n", raw_input.io));
}


{--
  - Take input from the user, process it, send it through Abella, process the result, and output it.
  -
  - @statelist  The state of the prover after each command issued to the prover.
  -             The current state of the prover is the first element of the list.
  - @abella  The process in which Abella is running
  - @ioin  The incoming IO token
  - @return  The resulting IO token and exit status
-}
function run_step_interactive
IOVal<Integer> ::=
   stateList::[(Integer, ProverState)]
   silverContext::Decorated SilverContext
   abella::ProcessHandle ioin::IO
{
  local currentProverState::ProverState = head(stateList).snd;
  local state::ProofState = currentProverState.state;
  state.silverContext = silverContext;
  local debug::Boolean = currentProverState.debug;

  {-
    PROCESS COMMAND
  -}
  --Read command
  ----------------------------
  local printed_prompt::IO = print(" < ", ioin);
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExternalWhiteSpace(raw_input.iovalue);
  --Translate command
  ----------------------------
  local result::ParseResult<AnyCommand_c> = cmd_parse(input, "<<input>>");
  local any_a::AnyCommand =
        if result.parseSuccess
        then result.parseTree.ast
        else anyParseFailure(result.parseErrors);
  any_a.silverContext = silverContext;
  any_a.currentState = currentProverState;
  any_a.translatedState = state.translation;
  any_a.inProof = state.inProof;
  any_a.stateListIn = stateList;
  local is_blank::Boolean = isSpace(input);
  --whether we have an actual command to send to Abella
  local speak_to_abella::Boolean = !is_blank && any_a.sendCommand;
  --an error or message based on our own checking
  local our_own_output::String =
        if is_blank
        then ""
        else any_a.ownOutput;
  --Send to abella
  ----------------------------
  local debug_output::IO =
       if debug
       then print(if speak_to_abella
                  then "Command sent:  " ++ any_a.translation
                  else "Nothing to send to Abella",
                  raw_input.io)
       else raw_input.io;
  local out_to_abella::IO =
        if speak_to_abella
        then sendToProcess(abella, any_a.translation, debug_output)
        else debug_output;


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
  local cleaned::(String, Integer, FullDisplay, [[Integer]], IO) =
        if shouldClean
        then cleanState(decorate full_a with
                        {replaceState = head(any_a.stateListOut).snd.state;}.replacedState,
                        silverContext, abella, back_from_abella.io)
        else ("", 0, decorate full_a with
                     {replaceState = head(any_a.stateListOut).snd.state;}.replacedState,
              [], back_from_abella.io);
  local outputCleanCommands::IO =
        if debug
        then print(cleaned.1 ++
                   "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n",
                   cleaned.5)
        else cleaned.5;
  local newStateList::[(Integer, ProverState)] =
        (head(any_a.stateListOut).fst + cleaned.2,
         --just replace the proof state in the ProverState
         decorate head(any_a.stateListOut).snd with
           {replaceState = cleaned.3.proof;}.replacedState)::tail(any_a.stateListOut);
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
  local outputIncomingThms::IO =
        if debug
        then print(handleIncoming.iovalue.3 ++
                   "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n", handleIncoming.io)
        else handleIncoming.io;
  --Show to user
  ----------------------------
  local debug_back_output::IO =
        if debug && speak_to_abella
        then print("***** Read back from Abella: *****\n\n" ++
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
  local printed_output::IO =
        if full_result.parseSuccess
        then print(output_output, debug_back_output)
        else error("BUG:  Unable to parse Abella's output:\n\n" ++
                   back_from_abella.iovalue ++ "\n\n" ++ full_result.parseErrors ++
                   "\n\nPlease report this");


  {-
    EXIT
  -}
  local wait_on_exit::IO = waitForProcess(abella, printed_output);
  --We can't use our normal read function because that looks for a new prompt
  --Guaranteed to get all the output because we waited for the process to exit first
  local any_last_words::IOVal<String> = readAllFromProcess(abella, wait_on_exit);
  local output_last::IO = print(any_last_words.iovalue, any_last_words.io);
  local exit_message::IO = print("Quitting.\n", output_last);


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
        run_step_interactive(completeStateList, silverContext,
                             abella, printed_output);


  return if any_a.isQuit
         then ioval(exit_message, 0)
         else again;
}






{--------------------------------------------------------------------
                           READ USER INPUT                           
 --------------------------------------------------------------------}
{-
  Read the command, which may be several lines, from stdin.
-}
function read_full_input
IOVal<String> ::= ioin::IO
{
  return read_full_input_comments(ioin, 0);
}
{-
  Read the command, keeping track of open multi-line comments to
  ensure reading in a full command, rather than just part of one and
  part of an open comment
-}
function read_full_input_comments
IOVal<String> ::= ioin::IO openComments::Integer
{
  local read::IOVal<Maybe<String>> = readLineStdin(ioin);
  local newOpenComments::Integer =
        count_comments(read.iovalue.fromJust, openComments);
  local readRest::IOVal<String> =
        read_full_input_comments(read.io, newOpenComments);
  local noWhiteSpace::String =
        stripExternalWhiteSpace(read.iovalue.fromJust);
  local shouldEnd::Boolean = endsWith(".", noWhiteSpace);
  return
     if openComments < 0
     then ioval(read.io, read.iovalue.fromJust) --syntax error
     else if openComments > 0
     then ioval(readRest.io,
                read.iovalue.fromJust ++ "\n" ++ readRest.iovalue)
     else if shouldEnd
     then ioval(read.io, read.iovalue.fromJust)
     else ioval(readRest.io,
                read.iovalue.fromJust ++ "\n" ++ readRest.iovalue);
}
--Return number of open comments after line
function count_comments
Integer ::= line::String openComments::Integer
{
  local stringStart::Integer = indexOf("\"", line);
  local lineStart::Integer = indexOf("%", line);
  local multiStart::Integer = indexOf("/*", line);
  local multiEnd::Integer = indexOf("*/", line);
  return
     if openComments < 0
     then openComments --syntax error
     else if openComments > 0
     then if multiEnd >= 0
          then count_comments(substring(multiEnd + 2, length(line),
                                        line), openComments - 1)
          else openComments
     --openComments == 0
     else if lineStart >= 0 &&
             (stringStart < 0 || lineStart < stringStart) &&
             (multiStart < 0 || lineStart < multiStart)
     then 0 --is line comment, so nothing else matters
     else if stringStart >= 0 &&
             (multiStart < 0 || stringStart < lineStart)
     then count_comments(clear_string(substring(stringStart + 1,
                                                length(line), line)),
                         openComments)
     else if multiStart >= 0
     then count_comments(substring(multiStart + 2, length(line), line),
                         openComments + 1)
     else 0; --nothing special in this line
}
--Remove a quoted string from the beginning of a line
function clear_string
String ::= line::String
{
  local quote::Integer = indexOf("\"", line);
  local slashquote::Integer = indexOf ("\\\"", line); --\"
  return
     if quote < slashquote --quote must be found for valid syntax
     then substring(quote + 1, length(line), line)
     else clear_string(substring(slashquote + 2, length(line), line));
}

