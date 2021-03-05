grammar interface_:composed;

imports interface_:toAbella;
imports interface_:fromAbella;
--need to import common just to get pp
imports interface_:common;

imports silver:util:subprocess;


{-
  All the parsers we will need
-}
parser from_parse::FullDisplay_c
{
  interface_:fromAbella:concreteSyntax;
}

parser top_parse::TopCommand_c
{
  interface_:toAbella:concreteSyntax;
}


parser proof_parse::Command_c
{
  interface_:toAbella:concreteSyntax;
}




function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local abella::IOVal<ProcessHandle> = spawnProcess("abella", [], ioin);
  --Abella outputs a welcome message, which we want to clean out
  local abella_initial_string::IOVal<String> =
        read_n_abella_outputs(just(1), abella.iovalue, abella.io);
  return run_step(noProof(), [], false, [("a", [nameType("$nt_Term")])],
                  abella.iovalue, abella_initial_string.io);
}


{--
  - Take input from the user, process it, send it through Abella, process the result, and output it.
  -
  - @state  The current proof state
  - @undolist  How many `undo` commands to issue to Abella for each of the user commands issued
  - @debug  Whether to print out the input to and output from Abella for debugging
  - @abella  The process in which Abella is running
  - @ioin  The incoming IO token
  - @return  The resulting IO token and exit status
-}
function run_step
IOVal<Integer> ::=
   state::ProofState undolist::[Integer] debug::Boolean
   attrOccurrences::[(String, [Type])] abella::ProcessHandle ioin::IO
{
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
  local top_result::ParseResult<TopCommand_c> = top_parse(input, "<<top input>>");
  local top_c::TopCommand_c = top_result.parseTree;
  local top_a::TopCommand = top_c.ast;
  top_a.attrOccurrences = attrOccurrences;
  local proof_result::ParseResult<Command_c> = proof_parse(input, "<<proof input>>");
  local proof_c::Command_c = proof_result.parseTree;
  local proof_a::ProofCommand = proof_c.ast;
  proof_a.attrOccurrences = attrOccurrences;
  proof_a.hypList = state.hypList;
  local proof_a_trans::[ProofCommand] = proof_a.translation;
  local is_blank::Boolean = isSpace(input);
  local output_command::String =
        if state.inProof
        then if proof_result.parseSuccess
             then implode("", map(\ p::ProofCommand -> p.pp, proof_a_trans)) ++ "\n"
             else ""
        else if top_result.parseSuccess
             then top_a.translation.pp ++ "\n"
             else "";
  --whether we have an actual command to send to Abella
  local speak_to_abella::Boolean =
        if is_blank
        then false
        else if state.inProof
             then if proof_result.parseSuccess
                  then --Set our own debug option
                       !proof_a.isDebug.fst
                  else --Nothing to send if we can't parse it
                       false
             else if top_result.parseSuccess
                  then --Set our own debug option
                       !top_a.isDebug.fst
                  else --Nothing to send if we can't parse it
                       false;
  --an error or message based on our own checking
  local our_own_output::String =
        if is_blank
        then ""
        else if state.inProof
             then if proof_result.parseSuccess
                  then ""
                  else if top_result.parseSuccess
                       then "Error:  Cannot use top commands in a proof\n\n"
                       else "Error:  Could not parse:\n" ++ proof_result.parseErrors --not an actual command
             else if top_result.parseSuccess
                  then ""
                  else if proof_result.parseSuccess
                       then "Error:  Cannot use proof commands outside a proof\n\n"
                       else "Error:  Could not parse:\n" ++ top_result.parseErrors; --not an actual command
  local num_commands_sent::Integer =
        if state.inProof
        then length(proof_a_trans)
        else 1;
  --Send to abella
  ----------------------------
  local debug_output::IO =
       if debug
       then if speak_to_abella
            then print("Command sent:  " ++ output_command ++ "\n\n", raw_input.io)
            else print("Nothing to send to Abella\n\n", raw_input.io)
       else raw_input.io;
  local out_to_abella::IO =
        if speak_to_abella
        then sendToProcess(abella, output_command, debug_output)
        else debug_output;


  local should_exit::Boolean =
        if state.inProof
        then proof_result.parseSuccess && proof_a.isQuit
        else top_result.parseSuccess && top_a.isQuit;


  {-
    PROCESS OUTPUT
  -}
  --Read output
  ----------------------------
  local should_count::Maybe<Integer> =
        if !state.inProof
        then case top_a.translation of
             | textCommand(_) -> nothing()
             | _ -> just(num_commands_sent)
             end
        else just(num_commands_sent);
  local back_from_abella::IOVal<String> =
        if speak_to_abella
        then read_n_abella_outputs(should_count, abella, out_to_abella)
        else ioval(out_to_abella, "");
  local debug_back_output::IO =
        if debug && speak_to_abella
        then print("***** Read back from Abella: *****\n\n" ++ back_from_abella.iovalue ++
               "\n\n***** End Abella output *****\n\n\n", back_from_abella.io)
        else back_from_abella.io;
  --Translate output
  ----------------------------
  local full_result::ParseResult<FullDisplay_c> =
        from_parse(back_from_abella.iovalue, "<<output>>");
  local full_c::FullDisplay_c = full_result.parseTree;
  local full_a::FullDisplay = full_c.ast;
  local new_proof_state::ProofState =
        if speak_to_abella
        then if full_result.parseSuccess
             then full_a.proof
             else state
        else state;
  local new_undolist::[Integer] =
        if speak_to_abella
        then if new_proof_state.inProof
             then length(proof_a_trans)::undolist
             else [] --no proof going on, so nothing to undo
        else undolist;
  local new_debug::Boolean =
        --only need to check top_result because Set is included in both
        if top_result.parseSuccess && top_a.isDebug.fst
        then top_a.isDebug.snd
        else debug;
  --Show to user
  ----------------------------
  local output_output::String =
        if speak_to_abella
        then full_a.translation.pp ++ "\n"
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
  --we can't use our normal read function because that looks for a new prompt
  --guaranteed to get all the output because we waited for the process to exit first
  local any_last_words::IOVal<String> = readAllFromProcess(abella, wait_on_exit);
  local output_last::IO = print(any_last_words.iovalue, any_last_words.io);
  local exit_message::IO = print("Quitting.\n", output_last);


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
        run_step(new_proof_state, new_undolist, new_debug,
                 attrOccurrences,
                 abella, printed_output);


  return if should_exit
         then ioval(exit_message, 0)
         else again;
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
function read_n_abella_outputs
IOVal<String> ::= n::Maybe<Integer> abella::ProcessHandle ioin::IO
{
  return read_n_abella_outputs_helper(n, "", abella, ioin);
}
function read_n_abella_outputs_helper
IOVal<String> ::= n::Maybe<Integer> thusFar::String abella::ProcessHandle ioin::IO
{
  {-
    NOTE:  If we ever need to handle an error output in the middle,
    this will need to check each last-read step to see if it is an
    error state (requires parsing it), then abort based on that.  In
    that case, we should also return a pair of the last state and the
    number of states we mananged to get through.
  -}
  local read::IOVal<String> = readAllFromProcess(abella, ioin);
  local lastComplete::Boolean = endsWith("< ", read.iovalue);
  local split::[String] = explode("<", thusFar ++ read.iovalue);
  local noWhiteSpace::[String] = map(stripExternalWhiteSpace, split);
  local noBlanks::[String] = filter(\ x::String -> x != "", noWhiteSpace);
  local len::Integer =
        if null(noBlanks)
        then 0
        else length(noBlanks) - (if lastComplete then 0 else 1);

  local newCarry::String =
        if null(noBlanks) || lastComplete
        then ""
        else last(noBlanks);

  {-
    If we are not counting, we assume that if what we read ends with a
    prompt. it is actually done.  This could be wrong, but it is
    unlikely to end up being wrong in any particular case.  We can't
    do anything better without a count.

    The only reason we wouldn't count should be when we are handling
    our import problems, described in a comment on the importCommand
    production in toAbella/abstractSyntax/TopCommand.sv.
  -}
  return
     case n of
     | nothing() ->
       if lastComplete
       then ioval(read.io, removeLastWord(last(noBlanks)))
       else read_n_abella_outputs_helper(nothing(), newCarry, abella, read.io)
     | just(n2) ->
       if len < n2
       then --read more
         read_n_abella_outputs_helper(just(n2 - len), newCarry, abella, read.io)
       else
         --We can have more outputs come back, but we'll assume that when
         --   we get at least the expected number back we are done
         --We could get less with errors, maybe.
         ioval(read.io, removeLastWord(last(noBlanks)))
     end;
}

--Remove the last word in a string
--We use this because the Abella prompt has the form "name < "
function removeLastWord
String ::= str::String
{
  local noExtraSpace::String = stripExternalWhiteSpace(str);
  local space::Integer = lastIndexOf("\n", noExtraSpace);
  local noWord::String = substring(0, space, noExtraSpace);
  return
     --might not have a space, if the last command resulted in blank output
     if space >= 0
     then noWord
     else "";
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

