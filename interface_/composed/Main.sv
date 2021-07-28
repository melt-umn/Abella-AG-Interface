grammar interface_:composed;

imports interface_:fromAbella;
imports interface_:toAbella;
imports interface_:common;
imports interface_:thmInterfaceFile;

imports silver:util:subprocess;


function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  return
     case largs of
     | [] -> run_interactive(ioin)
     | [filename] ->
       run_file(ioin, filename)
     | _ ->
       ioval(print("Can only process one file at a time\n", ioin), 1)
     end;
}

