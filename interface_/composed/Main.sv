grammar interface_:composed;

imports interface_:fromAbella;
imports interface_:toAbella;
imports interface_:common;
imports interface_:thmInterfaceFile;

imports silver:util:subprocess;
import silver:util:cmdargs;


function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local parsedArgs::Either<String Decorated CmdArgs> =
        parseArgs(largs);
  return
     case parsedArgs of
     | left(errs) -> ioval(print(errs, ioin), 1)
     | right(args) ->
       if args.compileFile && args.checkFile
       then check_compile_files(ioin, args.filenames)
       else if args.compileFile
       then compile_files(ioin, args.filenames)
       else if args.checkFile
       then run_files(ioin, args.filenames)
       else run_interactive(ioin)
     end;
}




synthesized attribute checkFile::Boolean occurs on CmdArgs;
synthesized attribute compileFile::Boolean occurs on CmdArgs;
synthesized attribute filenames::[String] occurs on CmdArgs;


aspect production endCmdArgs
top::CmdArgs ::= l::[String]
{
  top.checkFile = false;
  top.compileFile = false;
  top.filenames = l;
}


abstract production checkFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = true;
  top.compileFile = rest.compileFile;
  top.filenames = rest.filenames;
  forwards to rest;
}


abstract production compileFlag
top::CmdArgs ::= rest::CmdArgs
{
  top.checkFile = rest.checkFile;
  top.compileFile = true;
  top.filenames = rest.filenames;
  forwards to rest;
}



function parseArgs
Either<String  Decorated CmdArgs> ::= args::[String]
{
  production attribute flags::[Pair<String Flag>] with ++;
  flags := [];
  production attribute flagdescs::[String] with ++;
  flagdescs := [];

  flags <-
    [pair("--check",   flag(checkFlag)),
     pair("--compile", flag(compileFlag))
    ];
  flagdescs <- 
    ["   --check : check file for correctness and completion",
     "   --compile : compile file for importing into other grammars"
    ];

  local usage::String = 
        "Usage: silverabella [options] [filenames]\n\n" ++
        "Flag options:\n" ++ implode("\n", sort(flagdescs)) ++ "\n";

  -- Parse the command line
  production a::CmdArgs = interpretCmdArgs(flags, args);

  production attribute errors::[String] with ++;
  errors := if a.cmdError.isJust then [a.cmdError.fromJust] else [];

  errors <-
     if (a.checkFile || a.compileFile) && null(a.filenames)
     then ["Must give filename(s) with --check and --compile flags"]
     else [];

  errors <-
     if !null(a.filenames) && !(a.checkFile || a.compileFile)
     then ["Must specify at least one of --check or --compile " ++
           "when giving filename(s)"]
     else [];

  return if !null(errors)
         then left(implode("\n", errors) ++ "\n\n" ++ usage)
         else right(a);
}

