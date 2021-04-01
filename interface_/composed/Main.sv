grammar interface_:composed;

imports interface_:fromAbella;
imports interface_:toAbella;
imports interface_:common;

imports silver:util:subprocess;


{-
  All the parsers we will need
-}
parser from_parse::FullDisplay_c
{
  interface_:fromAbella:concreteSyntax;
}

parser cmd_parse::AnyCommand_c
{
  interface_:toAbella:concreteSyntax;
}




function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local abella::IOVal<ProcessHandle> = spawnProcess("abella", [], ioin);
  --Abella outputs a welcome message, which we want to clean out
  local abella_initial_string::IOVal<String> =
        read_abella_outputs(just(1), abella.iovalue, abella.io);

  local knownAttrs::[(String, Type)] =
        [  ("env", functorType(nameType("list"),
                      functorType(functorType(nameType("$pair"),
                         functorType(nameType("list"), nameType("$char"))),
                         nameType("integer"))) ), --list (pair string integer)
           ("value", nameType("integer")),
           ("knownNames", functorType(nameType("list"), --list string
                             functorType(nameType("list"), nameType("$char"))) ),
           ("valExists", nameType("$bool"))
        ];
  local attrOccurrences::[(String, [Type])] =
        [  ("env", [nameType("nt_Expr")]),
           ("value", [nameType("nt_Expr"), nameType("nt_Root")]),
           ("knownNames", [nameType("nt_Expr")]),
           ("valExists", [nameType("nt_Expr"), nameType("nt_Root")])
        ];
  local knownProds::[(String, Type)] =
        [  ("prod_intConst", arrowType(nameType("integer"), nameType("nt_Expr")) ),
           ("prod_plus", arrowType(nameType("nt_Expr"),
                            arrowType(nameType("nt_Expr"), nameType("nt_Expr"))) ),
           ("prod_minus", arrowType(nameType("nt_Expr"),
                             arrowType(nameType("nt_Expr"), nameType("nt_Expr"))) ),
           ("prod_mult", arrowType(nameType("nt_Expr"),
                            arrowType(nameType("nt_Expr"), nameType("nt_Expr"))) ),
           ("prod_letBind", arrowType(functorType(nameType("list"), nameType("$char")),
                               arrowType(nameType("nt_Expr"),
                                  arrowType(nameType("nt_Expr"), nameType("nt_Expr")))) ),
           ("prod_name", arrowType(functorType(nameType("list"), nameType("$char")),
                            nameType("nt_Expr")) ),
           ("prod_root", arrowType(nameType("nt_Expr"), nameType("nt_Root")))
        ];
  local wpdRelations::[(String, Type, [String])] =
        [  ("$wpd_nt_Expr", nameType("nt_Expr"),
            ["prod_intConst", "prod_plus", "prod_minus",
             "prod_mult", "prod_letBind", "prod_name"]),
           ("$wpd_nt_Root", nameType("nt_Root"), ["prod_root"])
        ];
  local knownInheritedAttrs::[String] = ["env", "knownNames"];

  return
     run_step([(-1, proverState(noProof(),false, knownAttrs, attrOccurrences,
                                knownProds, wpdRelations, knownInheritedAttrs, true))],
              abella.iovalue, abella_initial_string.io);
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
function run_step
IOVal<Integer> ::=
   stateList::[(Integer, ProverState)]
   abella::ProcessHandle ioin::IO
{
  local state::ProofState = head(stateList).snd.state;
  local debug::Boolean = head(stateList).snd.debug;
  local attrs::[(String, Type)] = head(stateList).snd.knownAttrs;
  --local attrOccurrences::[(String, [Type])] = head(stateList).snd.knownAttrOccurrences;
  local prods::[(String, Type)] = head(stateList).snd.knownProductions;

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
  any_a.currentState = head(stateList).snd;
  any_a.translatedState = head(stateList).snd.state.translation;
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
  local should_count_outputs::Maybe<Integer> = any_a.numCommandsSent;
  local back_from_abella::IOVal<String> =
        if speak_to_abella
        then read_abella_outputs(should_count_outputs, abella, out_to_abella)
        else ioval(out_to_abella, "");
  --Translate output
  ----------------------------
  local full_result::ParseResult<FullDisplay_c> =
        from_parse(back_from_abella.iovalue, "<<output>>");
  local full_a::FullDisplay = full_result.parseTree.ast;
  any_a.wasError =
        if speak_to_abella
        then !full_result.parseSuccess || full_a.isError
        else false;
  any_a.newProofState = full_a.proof;
  --Clean up state
  ----------------------------
  local shouldClean::Boolean =
        full_result.parseSuccess && !full_a.isError && any_a.shouldClean &&
        (head(stateList).snd.clean || any_a.mustClean);
  local cleaned::(String, Integer, FullDisplay, [[Integer]], IO) =
        if shouldClean
        then cleanState(decorate full_a with
                        {replaceState = head(any_a.stateListOut).snd.state;}.replacedState,
                        abella, back_from_abella.io)
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
  --Show to user
  ----------------------------
  local debug_back_output::IO =
        if debug && speak_to_abella
        then print("***** Read back from Abella: *****\n\n" ++
                 ( if shouldClean
                   then cleaned.3.pp
                   else back_from_abella.iovalue ) ++
                  "\n\n*****   End Abella output    *****\n\n\n",
                 outputCleanCommands)
        else outputCleanCommands;
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
                        "\n", cleaned.4) ++ cleaned.3.translation.pp ++ "\n"
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
  local wait_on_exit::IO = waitForProcess(abella, out_to_abella);
  --We can't use our normal read function because that looks for a new prompt
  --Guaranteed to get all the output because we waited for the process to exit first
  local any_last_words::IOVal<String> = readAllFromProcess(abella, wait_on_exit);
  local output_last::IO = print(any_last_words.iovalue, any_last_words.io);
  local exit_message::IO = print("Quitting.\n", output_last);


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
        run_step(newStateList, abella, printed_output);


  return if any_a.isQuit
         then ioval(exit_message, 0)
         else again;
}


{-
 - Clean up the current proof state by doing actions dictated by the state
 -
 - @param currentState   Current state of the proof
 - @param abella   Process in which Abella is running
 - @param ioin   IO token
 - @return   A tuple of a string of the commands sent, the number of
 -           commands sent, the final FullDisplay including the proof
 -           state which has been cleaned, the list of subgoals
 -           completed automatically, and the IO token after cleaning
-}
function cleanState
(String, Integer, FullDisplay, [[Integer]], IO) ::=
         currentDisplay::FullDisplay abella::ProcessHandle ioin::IO
{
  local currentState::ProofState = currentDisplay.proof;
  --Send to Abella
  local send::IO = sendToProcess(abella, currentState.cleanUpCommands, ioin);
  --Read back from Abella
  local back::IOVal<String> =
        read_abella_outputs(just(currentState.numCleanUpCommands), abella, send);
  local parsed::ParseResult<FullDisplay_c> =
        from_parse(back.iovalue, "<<output>>");
  currentState.nextStateIn =
     if parsed.parseSuccess
     then if parsed.parseTree.ast.isError
          then error("BUG:  Cleaning command \"" ++
                     currentState.cleanUpCommands ++
                     "\" resulted in an error:\n\n" ++
                     parsed.parseTree.ast.pp)
          else parsed.parseTree.ast.proof
     else error("BUG:  Unable to parse Abella's output:\n\n" ++
                back.iovalue ++ "\n\n" ++ parsed.parseErrors ++
                "\n\nPlease report this");
  local cleanedDisplay::FullDisplay =
        decorate parsed.parseTree.ast with
        {replaceState = currentState.nextStateOut;}.replacedState;
  --See if we completed a subgoal
  local subgoalCompletedNow::[[Integer]] =
        if subgoalCompleted(currentState.currentSubgoal,
                            currentState.nextStateOut.currentSubgoal)
        then [currentState.currentSubgoal]
        else [];
  --See if there is more to clean
  local sub::(String, Integer, FullDisplay, [[Integer]], IO) =
        cleanState(cleanedDisplay, abella, back.io);

  return
     if currentState.numCleanUpCommands == 0
     then ("", 0, currentDisplay, [], ioin)
     else (currentState.cleanUpCommands ++ sub.1,
           currentState.numCleanUpCommands + sub.2,
           sub.3, subgoalCompletedNow ++ sub.4, sub.5);
}


{-
  Read the command, which may be several lines, from stdin.
-}
function read_full_input
IOVal<String> ::= ioin::IO
{
  local read::IOVal<String> = readLineStdin(ioin);
  local readRest::IOVal<String> = read_full_input(read.io);
  local noWhiteSpace::String = stripExternalWhiteSpace(read.iovalue);
  local shouldEnd::Boolean =
        lastIndexOf(".", noWhiteSpace) == length(noWhiteSpace) - 1;
  return if shouldEnd
         then ioval(ioin, read.iovalue)
         else ioval(readRest.io, read.iovalue ++ readRest.iovalue);
}


--Read the given number of Abella outputs (prompt-terminated), if given
--Otherwise read until one ends with a prompt
--Returns the text of the last output
function read_abella_outputs
IOVal<String> ::= n::Maybe<Integer> abella::ProcessHandle ioin::IO
{
  return
     case n of
     | nothing() -> read_abella_outputs_until_done(abella, ioin)
     | just(x) -> read_n_abella_outputs(x, abella, ioin)
     end;
}
--Read from Abella until reaching the end, known from a theorem called "$$done" which is aborted
--Can do this because should only be used with an Import Abella itself doesn't like
function read_abella_outputs_until_done
IOVal<String> ::= abella::ProcessHandle ioin::IO
{
  local read1::IOVal<String> = readUntilFromProcess(abella, "< ", ioin);
  local readAgain::IOVal<String> = readUntilFromProcess(abella, "< ", ioin);

  return
     if endsWith("$$done < ", read1.iovalue)
     then ioval(readAgain.io, "") --get the aborting of $$done, but don't show it
     else read_abella_outputs_until_done(abella, read1.io);
}
--Read the given number of outputs from Abella
function read_n_abella_outputs
IOVal<String> ::= n::Integer abella::ProcessHandle ioin::IO
{
  local read::IOVal<String> = readUntilFromProcess(abella, "< ", ioin);
  return
     case n of
     | x when x <= 0 -> error("Should not call read_n_abella_outputs with n <= 0")
     | 1 -> ioval(read.io, removeLastWord(read.iovalue))
     | x -> read_n_abella_outputs(x - 1, abella, read.io)
     end;
}

--Remove the last word in a string
--We use this because the Abella prompt has the form "name < ", which
--   is guaranteed to be the last thing in the given string.
function removeLastWord
String ::= str::String
{
  local space::Integer = lastIndexOf("\n", str);
  local noWord::String = substring(0, space, str);
  return if space >= 0 then noWord else "";
}


--Remove white space from the front and end
function stripExternalWhiteSpace 
String ::= str::String
{
  local split::[String] = explode("", str);
  local cleanedHead::[String] = removeInitialSpaces(split);
  local reversedList::[String] = reverse(cleanedHead);
  local cleanedTail::[String] = removeInitialSpaces(reversedList);
  local forwardList::[String] = reverse(cleanedTail);
  return implode("", forwardList);
}
--Helper---takes a list of single characters
function removeInitialSpaces
[String] ::= lst::[String]
{
  return
    case lst of
    | [] -> []
    | h::t ->
      if isSpace(h)
      then removeInitialSpaces(t)
      else lst
    end;
}

