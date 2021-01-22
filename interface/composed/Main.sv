grammar composed;

imports toAbella;
imports fromAbella;

imports silver:util:subprocess;


{-
  All the parsers we will need
-}
parser from_parse::FullDisplay_c
{
  fromAbella:concreteSyntax;
}

parser top_parse::TopCommand_c
{
  toAbella:concreteSyntax;
}


parser proof_parse::Command_c
{
  toAbella:concreteSyntax;
}




function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local abella::IOVal<ProcessHandle> = spawnProcess("abella", [], ioin);
  --Abella outputs a welcome message, which we want to clean out
  local abella_initial_string::IOVal<String> =
        read_abella_output(abella.iovalue, abella.io);
  return run_step(noProof(), [], abella.iovalue, abella_initial_string.io);
}


function run_step
IOVal<Integer> ::= state::ProofState undolist::[Integer] abella::ProcessHandle ioin::IO
{
  {-
    PROCESS COMMAND
  -}
  --Read command
  ----------------------------
  local printed_prompt::IO = print(" < ", ioin);
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExtraWhiteSpace(raw_input.iovalue);
  --Translate command
  ----------------------------
  local top_result::ParseResult<TopCommand_c> = top_parse(input, "<<input>>");
  local top_c::TopCommand_c = top_result.parseTree;
  local top_a::TopCommand = top_c.ast;
  local proof_result::ParseResult<Command_c> = proof_parse(input, "<<input>>");
  local proof_c::Command_c = proof_result.parseTree;
  local proof_a::ProofCommand = proof_c.ast;
  local proof_a_trans::[ProofCommand] = proof_a.translation; --If we send multiple commands, we need to be ready to take multiple outputs back.
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
        if state.inProof
        then proof_result.parseSuccess
        else top_result.parseSuccess;
  --an error based on our own checking
  local our_own_error::String =
        if state.inProof
        then if proof_result.parseSuccess
             then ""
             else "Error:  Cannot use top commands in a proof\n\n"
        else if top_result.parseSuccess
             then ""
             else "Error:  Cannot use proof commands outside a proof\n\n";
  --Send to abella
  ----------------------------
  local out_to_abella::IO =
        if speak_to_abella
        then sendToProcess(abella, output_command, raw_input.io)
        else raw_input.io;


  local should_exit::Boolean = input == "exit.";


  {-
    PROCESS OUTPUT
  -}
  --Read output
  ----------------------------
  local back_from_abella::IOVal<String> =
        if speak_to_abella
        then read_abella_output(abella, out_to_abella)
        else ioval(raw_input.io, "");
  --Translate output
  ----------------------------
  local full_result::ParseResult<FullDisplay_c> =
        from_parse(back_from_abella.iovalue, "<<output>>");
  local full_c::FullDisplay_c = full_result.parseTree;
  local full_a::FullDisplay = full_c.ast;
  local new_proof_state::ProofState =
        if speak_to_abella
        then full_a.proof
        else state;
  local new_undolist::[Integer] =
        if speak_to_abella
        then if new_proof_state.inProof
             then length(proof_a_trans)::undolist
             else [] --no proof going on, so nothing to undo
        else undolist;
  --Show to user
  ----------------------------
  local output_output::String =
        if speak_to_abella
        then full_a.translation.pp ++ "\n"
        else our_own_error ++ state.translation.pp ++ "\n";
  local printed_output::IO =
        if full_result.parseSuccess
        then print(output_output, back_from_abella.io)
        else error("BUG:  Unable to parse Abella's output:\n\n" ++
                   back_from_abella.iovalue ++
                   "\n\nPlease report this");


  {-
    RUN REPL AGAIN
  -}
  local again::IOVal<Integer> =
        run_step(new_proof_state, new_undolist, abella, printed_output);


  return if should_exit
         then ioval(printed_output, 0)
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
  local noWhiteSpace::String = stripExtraWhiteSpace(read.iovalue);
  local shouldEnd::Boolean =
        lastIndexOf(".", noWhiteSpace) == length(noWhiteSpace) - 1;
  return if shouldEnd
         then ioval(ioin, read.iovalue)
         else ioval(readRest.io, read.iovalue ++ readRest.iovalue);
}


{-
  This needs to be recursive, even though we tell it to read all the
  output available from Abella, because there might not be any output
  available initially (we need to wait for it to finish processing) or
  not all the output might be available at once, and we need to keep
  going until we find the true end (the next prompt).
-}
function read_full_abella_output
IOVal<String> ::= abella::ProcessHandle ioin::IO
{
  local read::IOVal<String> = readAllFromProcess(abella, ioin);
  local readRest::IOVal<String> =
        read_full_abella_output(abella, read.io);
  local shouldEnd::Boolean = endsWith("< ", read.iovalue);
  return if shouldEnd
         then ioval(ioin, read.iovalue)
         else ioval(readRest.io, read.iovalue ++ readRest.iovalue);
}

--Read the output and remove the prompt
function read_abella_output
IOVal<String> ::= abella::ProcessHandle ioin::IO
{
  --Get the output including the prompt
  local text::IOVal<String> = read_full_abella_output(abella, ioin);
  local len::Integer = length(text.iovalue);
  --Remove " < "
  local short_text::String = substring(0, len - 3, text.iovalue);
  --Remove the current name (either Abella or the theorem being proven)
  local space::Integer = lastIndexOf("\n", short_text);
  local no_prompt::String = substring(0, space, short_text);

  return ioval(text.io, no_prompt);
}
