grammar interface_:composed;


--Read the interface file for a grammar and all the imported
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
        readImports(interface_info.2 ++ [grammarName],
                    silver_gen.iovalue,
                    interface_file_contents.io);

  return
     if silver_gen.iovalue == ""
     then ioval(silver_gen.io,
                left("Silver generated location not set"))
     else if !interface_is_file.iovalue
     then ioval(interface_is_file.io,
                left("Could not find interface file for grammar " ++
                     grammarName ++ "; must compile grammar first"))
     else if !parsed_interface.parseSuccess
     then ioval(interface_file_contents.io,
                left("Could not parse interface file for grammar " ++
                     grammarName ++ ":\n" ++
                     parsed_interface.parseErrors ++ "\n"))
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
                                "for grammar " ++ this_grammar ++
                                ":\n" ++ parsed_file.parseErrors ++
                                "\n"))
                else case subcall.iovalue of
                     | left(msg) -> ioval(subcall.io, left(msg))
                     | right(cmds) ->
                       ioval(subcall.io,
                             right(joinListOfCommands(
                                   parsed_file.parseTree.ast, cmds)))
                     end
     end;
}


--Send the commands from importing grammar specifications and build
--   the Silver context from the same
function set_up_abella_silver
IOVal<Decorated SilverContext> ::=
     currentGrammar::String comms::ListOfCommands defs::[DefElement]
     abella::ProcessHandle ioin::IO
{
  local sendToAbella::String =
        comms.pp ++ implode("", map((.pp), defs));
  local numComms::Integer =
        comms.numCommandsSent + length(defs);
  local sent::IO = sendToProcess(abella, sendToAbella, ioin);
  local back::IOVal<String> =
        if numComms > 0
        then read_abella_outputs(numComms, abella, sent)
        else ioval(sent, "");
  local parsedOutput::ParseResult<FullDisplay_c> =
        from_parse(back.iovalue, "<<output>>");
  --
  local newSilverContext::SilverContext =
        buildSilverContext(currentGrammar, comms);

  return
     if numComms > 0 && !parsedOutput.parseSuccess
     then error("Could not parse Abella output:\n\n" ++ back.iovalue)
     else if parsedOutput.parseTree.ast.isError
     then error("Error passing grammar specifications to Abella")
     else ioval(back.io, newSilverContext);
}

