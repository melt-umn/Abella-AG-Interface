grammar interface_:composed;


function generateSkeletonFiles
IOVal<Boolean> ::= gen::[(String, String)] ioin::IO
{
  local grmmr::String = head(gen).1;
  local filename::String = head(gen).2;
  --
  local processGrammar::IOVal<Either<String
                             (ListOfCommands, [DefElement],
                              [ThmElement])>> =
        processGrammarDecl(grmmr, ioin);
  local outputThms::[ThmElement] =
        filter(\ p::ThmElement ->
                 case p of
                 | extensibleMutualTheoremGroup(_) -> true
                 | _ -> false
                 end,
               processGrammar.iovalue.fromRight.3);
  local outputString::String =
        "Grammar " ++ grmmr ++ ".\n\n\n" ++
        implode("\n\n\n",
           map(\ p::ThmElement ->
                 case p of
                 | extensibleMutualTheoremGroup(thms) ->
                   "Prove " ++ implode("\n      ",
                                       map(fst, thms)) ++ "."
                 | _ -> error("Impossible after filtration")
                 end,
               outputThms)) ++ "\n\n";
  --
  local fileExists::IOVal<Boolean> =
        isFile(filename, processGrammar.io);
  local askReplace::IOVal<String> =
        if fileExists.iovalue
        then let replace::IOVal<Maybe<String>> =
                 readLineStdin(
                    print("File " ++ filename ++ " exists; replace? (Y/n) ",
                          fileExists.io))
             in
               ioval(replace.io, replace.iovalue.fromJust)
             end
        else ioval(fileExists.io, "");
  local doOutput::Boolean =
        !fileExists.iovalue ||
        askReplace.iovalue == "" ||
        substring(0, 1, askReplace.iovalue) == "Y" ||
        substring(0, 1, askReplace.iovalue) == "y";
  local message::IO =
        if doOutput
        then print("Writing contents for " ++ grmmr ++ " into " ++
                   filename ++ "\n", askReplace.io)
        else print("Skipping grammar " ++ grmmr ++ "\n",
                   askReplace.io);
  local output::IO =
        if doOutput
        then writeFile(filename, outputString, message)
        else message;
  --
  local rest::IOVal<Boolean> =
        generateSkeletonFiles(tail(gen), output);

  return
     case gen of
     | [] -> ioval(ioin, true)
     | hd::tl ->
       case processGrammar.iovalue of
       | left(err) ->
         ioval(print("Error:  " ++ err ++ "\n", processGrammar.io),
               false)
       | right(_) -> rest
       end
     end;
}
