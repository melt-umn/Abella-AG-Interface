grammar interface_:composed;

imports interface_:fromAbella;
imports interface_:toAbella;
imports interface_:common;
imports interface_:thm_interface_file;

imports silver:util:subprocess;


{-
  All the parsers we will need
-}
parser from_parse::FullDisplay_c
{
  interface_:fromAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

parser cmd_parse::AnyCommand_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

parser grammar_decl_parse::GrammarDecl_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

--Read a theorem interface file
parser interface_parse::Interface_c
{
  interface_:thm_interface_file;
  interface_:common:concreteSyntax;
}

--Process a theorem file
parser file_parse::FullFile_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

--Read a definition file
parser import_parse::ListOfCommands_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}




function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local filename::String = head(largs);
  --
  return
     case largs of
     | [] -> run_interactive(ioin)
     | [filename] ->
       run_file(ioin, filename)
     | _ ->
       ioval(print("Can only process one file at a time\n", ioin), 1)
     end;
}






{--------------------------------------------------------------------
                                FILES                                
 --------------------------------------------------------------------}
function run_file
IOVal<Integer> ::= ioin::IO filename::String
{
  local fileExists::IOVal<Boolean> = isFile(filename, ioin);
  local fileContents::IOVal<String> =
        readFile(filename, fileExists.io);
  local fileParsed::ParseResult<FullFile_c> =
        file_parse(fileContents.iovalue, filename);
  local fileAST::(String, ListOfCommands) = fileParsed.parseTree.ast;
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ParsedElement])>> =
        processGrammarDecl(fileAST.1, fileContents.io);
  --
  local started::IOVal<Either<String ProcessHandle>> =
        startAbella(processed.io);
  --
  local sendToAbella::String =
        processed.iovalue.fromRight.1.pp ++
        implode("", map((.pp), processed.iovalue.fromRight.2));
  local numCommands::Integer =
        processed.iovalue.fromRight.1.numCommandsSent +
        length(processed.iovalue.fromRight.2);
  local sent::IO =
        sendToProcess(started.iovalue.fromRight, sendToAbella,
                      started.io);
  local back::IOVal<String> =
        read_abella_outputs(numCommands, started.iovalue.fromRight,
                            sent);
  local parsedOutput::ParseResult<FullDisplay_c> =
        from_parse(back.iovalue, "<<output>>");

  return
     if !fileExists.iovalue
     then ioval(print("Given file " ++ filename ++ " does not exist",
                      fileExists.io), 1)
     else if !fileParsed.parseSuccess
     then ioval(print("Syntax error:\n" ++ fileParsed.parseErrors ++
                      "\n", fileContents.io), 1)
     else if !processed.iovalue.isRight
     then ioval(print("Error:  " ++ processed.iovalue.fromLeft ++
                      "\n", processed.io), 1)
     else if !started.iovalue.isRight
     then ioval(print("Error:  " ++ started.iovalue.fromLeft ++
                      "\n", started.io), 1)
     else if !parsedOutput.parseSuccess
     then error("Could not parse Abella output:\n\n" ++ back.iovalue)
     else run_step_file(fileAST.2.commandList,
                        [(-1, defaultProverState())],
                        started.iovalue.fromRight, started.io);
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
   stateList::[(Integer, ProverState)]
   abella::ProcessHandle ioin::IO
{
  local state::ProofState = head(stateList).snd.state;
  local attrs::[String] = head(stateList).snd.knownAttrs;
  local prods::[(String, Type)] = head(stateList).snd.knownProductions;

  {-
    PROCESS COMMAND
  -}
  --Translate command
  ----------------------------
  local any_a::AnyCommand = head(inputCommands);
  any_a.currentState = head(stateList).snd;
  any_a.translatedState = head(stateList).snd.state.translation;
  any_a.inProof = state.inProof;
  any_a.stateListIn = stateList;
  any_a.abellaFileParser =
        \ fileContents::String fileName::String ->
          let result::ParseResult<ListOfCommands_c> =
              import_parse(fileContents, fileName)
          in
            if result.parseSuccess
            then right(result.parseTree.ast)
            else left(result.parseErrors)
          end;
  --whether we have an actual command to send to Abella
  local speak_to_abella::Boolean = any_a.sendCommand;
  --Send to abella
  ----------------------------
  local out_to_abella::IO =
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
  local newStateList::[(Integer, ProverState)] =
        (head(any_a.stateListOut).fst + cleaned.2,
         --just replace the proof state in the ProverState
         decorate head(any_a.stateListOut).snd with
           {replaceState = cleaned.3.proof;}.replacedState)::tail(any_a.stateListOut);
  --Show to user
  ----------------------------


  {-
    EXIT
  -}
  local wait_on_exit::IO = waitForProcess(abella, out_to_abella);
  --We can't use our normal read function because that looks for a new prompt
  --Guaranteed to get all the output because we waited for the process to exit first
  local exit_message::IOVal<String> =
        readAllFromProcess(abella, wait_on_exit);


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
        run_step_file(tail(inputCommands), newStateList, abella,
                      back_from_abella.io);


  return
     case inputCommands of
     | [] ->
       if state.inProof
       then ioval(print("Proof in progress at end of file\n", ioin), 1)
       else ioval(print("Successfully processed file\n", ioin), 0)
     | _::tl ->
       if any_a.isQuit
       then ioval(exit_message.io, 0)
       else if any_a.isError
       then ioval(print("Could not process full file:\n" ++
                        any_a.ownOutput ++ "\n", back_from_abella.io),
                  1)
       else if full_a.isError
       then ioval(print("Could not process full file:\n" ++ full_a.pp,
                        back_from_abella.io), 1)
       else again
     end;
}






{--------------------------------------------------------------------
                             INTERACTIVE                             
 --------------------------------------------------------------------}
function run_interactive
IOVal<Integer> ::= ioin::IO
{
  local started::IOVal<Either<String ProcessHandle>> =
        startAbella(ioin);

  return
     case started.iovalue of
     | left(msg) ->
       ioval(print("Error:  " ++ msg ++ "\n", started.io), 1)
     | right(abella) ->
       run_step_interactive([(-1, defaultProverState())],
                            abella, started.io)
     end;
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
   abella::ProcessHandle ioin::IO
{
  local state::ProofState = head(stateList).snd.state;
  local debug::Boolean = head(stateList).snd.debug;
  local attrs::[String] = head(stateList).snd.knownAttrs;
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
  any_a.abellaFileParser =
        \ fileContents::String fileName::String ->
          let result::ParseResult<ListOfCommands_c> =
              import_parse(fileContents, fileName)
          in
            if result.parseSuccess
            then right(result.parseTree.ast)
            else left(result.parseErrors)
          end;
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
        run_step_interactive(newStateList, abella, printed_output);


  return if any_a.isQuit
         then ioval(exit_message, 0)
         else again;
}






{--------------------------------------------------------------------
                          CLEAN PROOF STATE                          
 --------------------------------------------------------------------}
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
        read_abella_outputs(currentState.numCleanUpCommands, abella, send);
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
  local read::IOVal<String> = readLineStdin(ioin);
  local newOpenComments::Integer =
        count_comments(read.iovalue, openComments);
  local readRest::IOVal<String> =
        read_full_input_comments(read.io, newOpenComments);
  local noWhiteSpace::String = stripExternalWhiteSpace(read.iovalue);
  local shouldEnd::Boolean = endsWith(".", noWhiteSpace);
  return
     if openComments < 0
     then read --syntax error
     else if openComments > 0
     then ioval(readRest.io, read.iovalue ++ "\n" ++ readRest.iovalue)
     else if shouldEnd
     then ioval(read.io, read.iovalue)
     else ioval(readRest.io, read.iovalue ++ "\n" ++ readRest.iovalue);
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






{--------------------------------------------------------------------
                           ABELLA FUNCTIONS                          
 --------------------------------------------------------------------}
--Either start Abella or fail with an error message
function startAbella
IOVal<Either<String ProcessHandle>> ::= ioin::IO
{
  --Find the library location (env variable set by startup script)
  local library_loc::IOVal<String> =
        envVar("SILVERABELLA_LIBRARY", ioin);
  local library_string::String =
        "Kind bool   type.\n" ++
        "Import \"" ++ library_loc.iovalue ++ "bools\".\n" ++
        "Kind nat   type.\n" ++
        "Import \"" ++ library_loc.iovalue ++ "integer_addition\".\n" ++
        "Import \"" ++ library_loc.iovalue ++ "integer_multiplication\".\n" ++
        "Import \"" ++ library_loc.iovalue ++ "integer_comparison\".\n" ++
        "Import \"" ++ library_loc.iovalue ++ "lists\".\n" ++
        "Import \"" ++ library_loc.iovalue ++ "strings\".\n" ++
        "Kind $pair   type -> type -> type.\n" ++
        "Import \"" ++ library_loc.iovalue ++ "pairs\".\n" ++
        "Kind $attrVal   type -> type.\n" ++
        "Import \"" ++ library_loc.iovalue ++ "attr_val\".\n\n";

  local abella::IOVal<ProcessHandle> =
        spawnProcess("abella", [], library_loc.io);
  --Send the library imports to Abella
  local send_imports::IO =
        sendToProcess(abella.iovalue, library_string, abella.io);
  --Read Abella's outputs from the library imports, in addition to the
  --   welcome message
  local abella_initial_string::IOVal<String> =
        read_abella_outputs(13, abella.iovalue, send_imports);

  return
     if library_loc.iovalue == ""
     then ioval(library_loc.io,
                left("Interface library location not set"))
     else ioval(abella_initial_string.io, right(abella.iovalue));
}


--Read the given number of Abella outputs (prompt-terminated)
--Returns the text of the last output
function read_abella_outputs
IOVal<String> ::= n::Integer abella::ProcessHandle ioin::IO
{
  local read::IOVal<String> = readUntilFromProcess(abella, "< ", ioin);
  return
     case n of
     | x when x <= 0 -> error("Should not call read_n_abella_outputs with n <= 0")
     | 1 -> ioval(read.io, removeLastWord(read.iovalue))
     | x -> read_abella_outputs(x - 1, abella, read.io)
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






{--------------------------------------------------------------------
                     PROCESS GRAMMAR DECLARATION                     
 --------------------------------------------------------------------}
--Read the interface file for a grammar and import all the imported
--   specifications
function processGrammarDecl
IOVal<Either<String
             (ListOfCommands, [DefElement], [ParsedElement])>> ::=
   grammarName::String ioin::IO
{
  local silver_gen::IOVal<String> = envVar("SILVER_GEN", ioin);
  local interface_file::String =
        silver_gen.iovalue ++ substitute(":", "/", grammarName) ++
        "/thm_interface.svthmi";
  local interface_is_file::IOVal<Boolean> =
        isFile(interface_file, silver_gen.io);
  local interface_file_contents::IOVal<String> =
        readFile(interface_file, interface_is_file.io);
  local parsed_interface::ParseResult<Interface_c> =
        interface_parse(interface_file_contents.iovalue,
                        interface_file);
  local interface_info::(String, [String], [DefElement], [ParsedElement]) =
        parsed_interface.parseTree.ast;

  local modules_read::IOVal<Either<String ListOfCommands>> =
        readImports(interface_info.2, silver_gen.iovalue,
                    interface_file_contents.io);

  return
     if silver_gen.iovalue == ""
     then ioval(silver_gen.io,
                left("Silver generated location not set"))
     else if !interface_is_file.iovalue
     then ioval(interface_is_file.io,
                left("Could not find interface file for grammar " ++
                     grammarName))
     else if !parsed_interface.parseSuccess
     then ioval(interface_file_contents.io,
                left("Could not parse interface file for grammar " ++
                     grammarName))
     else case modules_read.iovalue of
          | left(msg) -> ioval(modules_read.io, left(msg))
          | right(lst) ->
            ioval(modules_read.io,
                  right( (lst, interface_info.3, interface_info.4) ))
          end;
}

--Read all the grammars to be imported, in the order
--Should include the current grammar at the end
function readImports
IOVal<Either<String ListOfCommands>> ::=
   grammars::[String] silver_gen::String ioin::IO
{
  local this_grammar::String = head(grammars);
  local filename::String =
        silver_gen ++ substitute(":", "/", this_grammar) ++
        "/definitions.thm";
  local filename_is_file::IOVal<Boolean> = isFile(filename, ioin);
  local file_contents::IOVal<String> =
        readFile(filename, filename_is_file.io);
  local parsed_file::ParseResult<ListOfCommands_c> =
        import_parse(file_contents.iovalue, filename);
  local subcall::IOVal<Either<String ListOfCommands>> =
        readImports(tail(grammars), silver_gen, file_contents.io);

  return
     case grammars of
     | [] -> ioval(ioin, right(emptyListOfCommands()))
     | _::tl -> if !filename_is_file.iovalue
                then ioval(filename_is_file.io,
                           left("Definition file could not be " ++
                                "found for " ++ this_grammar))
                else if !parsed_file.parseSuccess
                then ioval(file_contents.io,
                           left("Could not parse definition file " ++
                                "for grammar " ++ this_grammar))
                else case subcall.iovalue of
                     | left(msg) -> ioval(subcall.io, left(msg))
                     | right(cmds) ->
                       ioval(subcall.io,
                             right(joinListOfCommands(
                                   parsed_file.parseTree.ast, cmds)))
                     end
     end;
}

