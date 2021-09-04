grammar interface_:composed;


--Run through a list of files, compiling them
function compile_files
IOVal<Integer> ::= ioin::IO filenames::[String]
{
  local compiled::IOVal<Integer> =
        compile_file(ioin, head(filenames));
  return
     case filenames of
     | [] -> ioval(ioin, 0)
     | hd::tl ->
       if compiled.iovalue != 0
       then compiled --error in compiling that file, so quit
       else compile_files(compiled.io, tl)
     end;
}


--Run through a list of files, checking and compiling them
function check_compile_files
IOVal<Integer> ::= ioin::IO filenames::[String]
{
  local ran::IOVal<Integer> = run_file(ioin, head(filenames));
  local compiled::IOVal<Integer> =
        compile_file(ran.io, head(filenames));
  return
     case filenames of
     | [] -> ioval(ioin, 0)
     | hd::tl ->
       if ran.iovalue != 0
       then ran --error in checking that file, so quit
       else if compiled.iovalue != 0
       then compiled --error in compiling that file, so quit
       else compile_files(compiled.io, tl)
     end;
}


--Compile a file, outputting it into the generated directory
function compile_file
IOVal<Integer> ::= ioin::IO filename::String
{
  local fileExists::IOVal<Boolean> = isFile(filename, ioin);
  local fileContents::IOVal<String> =
        readFile(filename, fileExists.io);
  local fileParsed::ParseResult<FullFile_c> =
        file_parse(fileContents.iovalue, filename);
  local fileAST::(String, ListOfCommands) = fileParsed.parseTree.ast;
  local processed::IOVal<Either<String (ListOfCommands, [DefElement],
                                        [ThmElement])>> =
        processGrammarDecl(fileAST.1, fileContents.io);
  local fileErrors::[Error] = fileAST.2.fileErrors;
  --
  local ourSilverContext::Decorated SilverContext =
        decorate buildSilverContext(fileAST.1, processed.iovalue.fromRight.1) with {};
  --
  local compiledContents::String =
        buildCompiledOutput(fileAST.1, fileAST.2, ourSilverContext);
  local silverGen::IOVal<String> =
        envVar("SILVER_GEN", processed.io);
  local outputFile::String =
        silverGen.iovalue ++ substitute(":", "/", fileAST.1) ++
        "/thm_outerface.svthmi";
  local written::IO =
        writeFile(outputFile, compiledContents, silverGen.io);

  return
     if !fileExists.iovalue
     then ioval(print("Given file " ++ filename ++ " does not exist\n",
                      fileExists.io), 1)
     else if !fileParsed.parseSuccess
     then ioval(print("Syntax error:\n" ++ fileParsed.parseErrors ++
                      "\n", fileContents.io), 1)
     else if !processed.iovalue.isRight
     then ioval(print("Error:  " ++ processed.iovalue.fromLeft ++
                      "\n", processed.io), 1)
     else if !null(fileErrors)
     then ioval(print("Processing errors:\n" ++
                      implode("\n", map((.pp), fileErrors)) ++ "\n",
                      processed.io), 1)
     else if silverGen.iovalue == ""
     then ioval(print("Silver generated location not set\n",
                      silverGen.io), 1)
     else ioval(print("Successfully compiled file " ++ filename ++ "\n",
                      written), 0);
}

