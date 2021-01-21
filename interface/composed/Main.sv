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
  local printed_prompt::IO = print(" < ", ioin);
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExtraWhiteSpace(raw_input.iovalue);
  local output_command::String = input ++ "\n";
  local out_to_abella::IO = sendToProcess(abella, output_command, raw_input.io);

  local should_exit::Boolean = input == "exit.";

  local back_from_abella::IOVal<String> = read_abella_output(abella, out_to_abella);
  local output_output::String = back_from_abella.iovalue ++ "\n";
  local attribute new_proof_state::ProofState = state;
  local attribute new_undolist::[Integer] = undolist;
  local printed_output::IO = print(output_output, back_from_abella.io);


  local again::IOVal<Integer> =
        run_step(new_proof_state, new_undolist, abella, printed_output);

  return if should_exit
         then ioval(raw_input.io, 0)
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
