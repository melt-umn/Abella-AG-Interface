grammar interface_:composed;


--Run a REPL for the theorem prover
--First entry must be a grammar declaration (Grammar na:me.)
function run_interactive
IOVal<Integer> ::= ioin::IOToken config::Decorated CmdArgs
{
  local grammarName::IOVal<String> = get_grammar_interactive(ioin);
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
        processGrammarDecl(grammarName.iovalue, grammarName.io);
  --
  local started::IOVal<Either<String ProcessHandle>> =
        startAbella(grammarName.io, config);
  --
  local build_context::IOVal<Decorated SilverContext> =
        set_up_abella_silver(grammarName.iovalue,
           processed.iovalue.fromRight.1,
           processed.iovalue.fromRight.2,
           started.iovalue.fromRight, started.io, config);
  --
  local handleIncoming::IOVal<(Integer, ProverState, String)> =
        handleIncomingThms(
           (0, defaultProverState(processed.iovalue.fromRight.3)),
           build_context.iovalue, started.iovalue.fromRight,
           build_context.io, config);

  return
     if !processed.iovalue.isRight
     then ioval(printT("Error:  " ++ processed.iovalue.fromLeft ++
                       "\n", processed.io), 1)
     else if !started.iovalue.isRight
     then ioval(printT("Error:  " ++ started.iovalue.fromLeft ++
                       "\n", started.io), 1)
     else run_step(
             build_interactive_commands(),
             "<<user input>>",
             build_context.iovalue,
             [(-1, handleIncoming.iovalue.2)],
             config,
             started.iovalue.fromRight,
             handleIncoming.io);
}


--Continue trying to get a grammar declaration from the user until
--   they actually give one
function get_grammar_interactive
IOVal<String> ::= ioin::IOToken
{
  local printed_prompt::IOToken = printT(" < ", ioin);
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExternalWhiteSpace(raw_input.iovalue);
  --
  local result::ParseResult<GrammarDecl_c> =
        grammar_decl_parse(input, "<<input>>");
  return
     if result.parseSuccess
     then ioval(raw_input.io, result.parseTree.ast)
     else get_grammar_interactive(
             printT("Error:  First entry must be a grammar\n" ++
                    result.parseErrors ++ "\n\n", raw_input.io));
}


--Create a list of commands by reading them from the user
function build_interactive_commands
[AnyCommand] ::=
{
  local printed_prompt::IOToken = printT(" < ", unsafeIO());
  local raw_input::IOVal<String> = read_full_input(printed_prompt);
  local input::String = stripExternalWhiteSpace(raw_input.iovalue);
  local result::ParseResult<AnyCommand_c> =
        cmd_parse(input, "<<input>>");
  local any_a::AnyCommand =
        if result.parseSuccess
        then result.parseTree.ast
        else anyParseFailure(result.parseErrors);
  return if isSpace(input)
         then build_interactive_commands()
         else any_a::build_interactive_commands();
}






{--------------------------------------------------------------------
                           READ USER INPUT                           
 --------------------------------------------------------------------}
{-
  Read the command, which may be several lines, from stdin.
-}
function read_full_input
IOVal<String> ::= ioin::IOToken
{
  return read_full_input_comments(ioin, 0);
}
{-
  Read the command, keeping track of open multi-line comments to
  ensure reading in a full command, rather than just part of one and
  part of an open comment
-}
function read_full_input_comments
IOVal<String> ::= ioin::IOToken openComments::Integer
{
  local read::IOVal<Maybe<String>> = readLineStdinT(ioin);
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

