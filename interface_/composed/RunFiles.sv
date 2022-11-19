grammar interface_:composed;


--Run through a list of files, checking them for validity
function run_files
IOVal<Integer> ::= ioin::IOToken filenames::[String] config::Decorated CmdArgs
{
  local ran::IOVal<Integer> = run_file(ioin, head(filenames), config);
  return
     case filenames of
     | [] -> ioval(ioin, 0)
     | hd::tl ->
       if ran.iovalue != 0
       then ran --error in that file, so quit
       else run_files(ran.io, tl, config)
     end;
}


--Run through a file to check that all the proofs are done correctly
function run_file
IOVal<Integer> ::= ioin::IOToken filename::String config::Decorated CmdArgs
{
  local fileExists::IOVal<Boolean> = isFileT(filename, ioin);
  local fileContents::IOVal<String> =
        readFileT(filename, fileExists.io);
  local fileParsed::ParseResult<FullFile_c> =
        file_parse(fileContents.iovalue, filename);
  local fileAST::(String, ListOfCommands) = fileParsed.parseTree.ast;
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
        processGrammarDecl(fileAST.1, fileContents.io);
  --
  local started::IOVal<Either<String ProcessHandle>> =
        startAbella(processed.io, config);
  --
  local ourSilverContext::IOVal<Decorated SilverContext> =
        set_up_abella_silver(
           fileAST.1, processed.iovalue.fromRight.1,
           processed.iovalue.fromRight.2, started.iovalue.fromRight,
           started.io, config);
  --
  local handleIncoming::IOVal<(Integer, ProverState, String)> =
        handleIncomingThms(
           (0, defaultProverState(processed.iovalue.fromRight.3)),
           ourSilverContext.iovalue, started.iovalue.fromRight,
           ourSilverContext.io, config);

  return
     if !fileExists.iovalue
     then ioval(printT("Given file " ++ filename ++ " does not exist\n",
                       fileExists.io), 1)
     else if !fileParsed.parseSuccess
     then ioval(printT("Syntax error:\n" ++ fileParsed.parseErrors ++
                       "\n", fileContents.io), 1)
     else if !processed.iovalue.isRight
     then ioval(printT("Error:  " ++ processed.iovalue.fromLeft ++
                       "\n", processed.io), 1)
     else if !started.iovalue.isRight
     then ioval(printT("Error:  " ++ started.iovalue.fromLeft ++
                       "\n", started.io), 1)
     else run_step(
             fileAST.2.commandList,
             filename,
             ourSilverContext.iovalue,
             [(-1, handleIncoming.iovalue.2)],
             config,
             started.iovalue.fromRight,
             handleIncoming.io);
}
