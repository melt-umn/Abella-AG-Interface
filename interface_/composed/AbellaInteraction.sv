grammar interface_:composed;


--Either start Abella or fail with an error message
function startAbella
IOVal<Either<String ProcessHandle>> ::= ioin::IOToken
{
  --Find the library location (env variable set by startup script)
  local library_loc::IOVal<String> =
        envVarT("SILVERABELLA_LIBRARY", ioin);
  local library_string::String =
        "Kind bool   type.\n" ++
        "Import \"" ++ library_loc.iovalue ++ "bools\".\n" ++
        "Kind nat   type.\n" ++
        "Import \"" ++ library_loc.iovalue ++ "integer_addition\".\n" ++
        "Import \"" ++ library_loc.iovalue ++ "integer_multiplication\".\n" ++
        "Import \"" ++ library_loc.iovalue ++ "integer_division\".\n" ++
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
  local send_imports::IOToken =
        sendToProcess(abella.iovalue, library_string, abella.io);
  --Read Abella's outputs from the library imports, in addition to the
  --   welcome message
  local abella_initial_string::IOVal<String> =
        read_abella_outputs(14, abella.iovalue, send_imports);

  return
     if library_loc.iovalue == ""
     then ioval(library_loc.io,
                left("Interface library location not set"))
     else ioval(abella_initial_string.io, right(abella.iovalue));
}


--Read the given number of Abella outputs (prompt-terminated)
--Returns the text of the last output
function read_abella_outputs
IOVal<String> ::= n::Integer abella::ProcessHandle ioin::IOToken
{
  local read::IOVal<String> = readUntilFromProcess(abella, "< ", ioin);
  return
     case n of
     | x when x <= 0 -> error("Should not call read_abella_outputs with n <= 0 (n = " ++ toString(x) ++ ")")
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
  --Send to Abella
  local send::IOToken = sendToProcess(abella, currentState.cleanUpCommands, ioin);
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
  local sub::(String, Integer, FullDisplay, [[Integer]], IOToken) =
        cleanState(cleanedDisplay, silverContext, abella, back.io);

  return
     if currentState.numCleanUpCommands == 0
     then ("", 0, currentDisplay, [], ioin)
     else (currentState.cleanUpCommands ++ sub.1,
           currentState.numCleanUpCommands + sub.2,
           sub.3, subgoalCompletedNow ++ sub.4, sub.5);
}

