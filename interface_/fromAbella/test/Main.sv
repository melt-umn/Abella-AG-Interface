grammar interface_:fromAbella:test;


imports interface_:fromAbella:concreteSyntax;
imports interface_:fromAbella:abstractSyntax;


{-
  This is just to test parsing.
-}


parser topparse::FullDisplay_c
{
  interface_:fromAbella:concreteSyntax;
}


function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local print_parse_test::IO = print("\n\n" ++ "Parsing Tests\n" ++ "========================================\n", ioin);
  local attribute parse_test::IOVal<Boolean> = test_parsing("parsing_tests", print_parse_test);

  return ioval(parse_test.io, 0);
}



function test_parsing
IOVal<Boolean> ::= dirname::String ioin::IO
{
  local isDir::IOVal<Boolean> = isDirectory(dirname, ioin);
  local dirContents::IOVal<[String]> = listContents(dirname, isDir.io);
  local prepared_files::[String] = map(\ x::String -> dirname ++ "/" ++ x, dirContents.iovalue);
  local files_parsed::IOVal<Integer> = parse_files(prepared_files, dirContents.io);
  local outputResult::IO =
        if files_parsed.iovalue == 0
        then print("All parsing tests passed.\n\n", files_parsed.io)
        else print(toString(files_parsed.iovalue) ++ " TESTS FAILED.\n\n", files_parsed.io);
  local printNotDir::IO = print(dirname ++ " is not a directory.\n\n", isDir.io);
  return if isDir.iovalue
         then ioval(outputResult, true)
         else ioval(printNotDir, false);
}

function parse_files
IOVal<Integer> ::= filenames::[String] ioin::IO
{
  --check if the first one is a file
  local fname::String = head(filenames);
  local isfile::IOVal<Boolean> = isFile(fname, ioin);

  --if it is a file, try to parse it
  local fcontents::IOVal<String> = readFile(fname, isfile.io);
  local pars_res::ParseResult<FullDisplay_c> = topparse(fcontents.iovalue, fname);
  local print_res::IO =
        if pars_res.parseSuccess
        then fcontents.io --print(fname ++ " parsed successfully\n\n", fcontents.io)
        else print(fname ++ " PARSE FAILURE\n\n", fcontents.io);
  local rest::IOVal<Integer> = parse_files(tail(filenames), print_res);

  --it isn't a file
  local first_not_file::IO = print(fname ++ " isn't a file\n\n", isfile.io);
  local rest_skip_first::IOVal<Integer> = parse_files(tail(filenames), first_not_file);

  return
    case filenames of
    | [] -> ioval(ioin, 0)
    | h::t ->
      if isfile.iovalue
      then ioval(rest.io, rest.iovalue + if pars_res.parseSuccess then 0 else 1)
      else rest_skip_first
    end;
}

