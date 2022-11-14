grammar interface_:composed;


--Either start Abella or fail with an error message
function startAbella
IOVal<Either<String ProcessHandle>> ::= ioin::IOToken
{
  --Find the library location (env variable set by startup script)
  local library_loc::IOVal<String> =
        envVarT("SILVERABELLA_LIBRARY", ioin);
  local library_cmds::[String] =
       ["Kind bool   type.",
        "Import \"" ++ library_loc.iovalue ++ "bools\".",
        "Kind nat   type.",
        "Import \"" ++ library_loc.iovalue ++ "integer_addition\".",
        "Import \"" ++ library_loc.iovalue ++ "integer_multiplication\".",
        "Import \"" ++ library_loc.iovalue ++ "integer_division\".",
        "Import \"" ++ library_loc.iovalue ++ "integer_comparison\".",
        "Import \"" ++ library_loc.iovalue ++ "lists\".",
        "Import \"" ++ library_loc.iovalue ++ "strings\".",
        "Kind $pair   type -> type -> type.",
        "Import \"" ++ library_loc.iovalue ++ "pairs\".",
        "Kind $attrVal   type -> type.",
        "Import \"" ++ library_loc.iovalue ++ "attr_val\"."];

  local abella::IOVal<ProcessHandle> =
        spawnProcess("abella", [], library_loc.io);
  --Read Abella's outputs from the library imports, in addition to the
  --   welcome message
  local abella_initial_string::IOVal<String> =
        read_abella_output(abella.iovalue, abella.io);
  --Send the library imports to Abella
  local send_imports::IOVal<String> =
        sendCmdsToAbella(library_cmds, abella.iovalue,
                         abella_initial_string.io);

  return
     if library_loc.iovalue == ""
     then ioval(library_loc.io,
                left("Interface library location not set; " ++
                     "must run through given script"))
     else ioval(send_imports.io, right(abella.iovalue));
}



--Send each of the given Abella commands to Abella in order
--Returns the output text of the last one
function sendCmdsToAbella
IOVal<String> ::= cmds::[String] abella::ProcessHandle ioin::IOToken
{
  return
     case cmds of
     | [] -> ioval(ioin, "")
     | [c] -> sendCmdToAbella(c, abella, ioin)
     | c::tl ->
       sendCmdsToAbella(tl, abella,
                        sendCmdToAbella(c, abella, ioin).io)
     end;
}

--Send a single command to Abella and get its output text back
function sendCmdToAbella
IOVal<String> ::= cmd::String abella::ProcessHandle ioin::IOToken
{
  local sent::IOToken = sendToProcess(abella, cmd, ioin);
  local dumped::IOToken =
        if DUMP_ABELLA
        then appendFileT(DUMP_FILE, cmd ++ "\n", sent)
        else sent;
  return read_abella_output(abella, dumped);
}


--Read the full Abella output (prompt-terminated) for one command
--Returns the text of the output
function read_abella_output
IOVal<String> ::= abella::ProcessHandle ioin::IOToken
{
  local read::IOVal<String> = readUntilFromProcess(abella, "< ", ioin);
  return ioval(read.io, removeLastWord(read.iovalue));
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
(String, Integer, FullDisplay, [[Integer]], IOToken) ::=
         currentDisplay::FullDisplay
         silverContext::Decorated SilverContext
         abella::ProcessHandle ioin::IOToken
{
  local currentState::ProofState = currentDisplay.proof;
  currentState.silverContext = silverContext;
  --Send to and read back from Abella
  local back::IOVal<String> =
        sendCmdsToAbella(currentState.cleanUpCommands, abella, ioin);
  local parsed::ParseResult<FullDisplay_c> =
        from_parse(back.iovalue, "<<output>>");
  currentState.nextStateIn =
     if parsed.parseSuccess
     then if parsed.parseTree.ast.isError
          then error("BUG:  Cleaning command \"" ++
                     implode("\n", currentState.cleanUpCommands) ++
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
  local sub::(String, Integer, FullDisplay, [[Integer]], IOToken) =
        cleanState(cleanedDisplay, silverContext, abella, back.io);

  return
     if currentState.numCleanUpCommands == 0
     then ("", 0, currentDisplay, [], ioin)
     else (implode("\n", currentState.cleanUpCommands) ++ sub.1,
           currentState.numCleanUpCommands + sub.2,
           sub.3, subgoalCompletedNow ++ sub.4, sub.5);
}

