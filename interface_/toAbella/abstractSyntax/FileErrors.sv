grammar interface_:toAbella:abstractSyntax;

{-
  There are some commands which we can't handle in compilation, since
  they could mean some theorem or theorems which appear in the file
  are not actually part of what is being proven.
-}
monoid attribute fileErrors::[Error] with [], ++;
propagate fileErrors on
   ListOfCommands, AnyCommand, TopCommand, ProofCommand, NoOpCommand;

attribute fileErrors occurs on
   ListOfCommands, AnyCommand, TopCommand, ProofCommand, NoOpCommand;


aspect production abortCommand
top::ProofCommand ::=
{
  top.fileErrors <-
      [errorMsg("abort command not allowed in file processing")];
}


aspect production undoCommand
top::ProofCommand ::=
{
  top.fileErrors <-
      [errorMsg("undo command not allowed in file processing")];
}


aspect production quitCommand
top::NoOpCommand ::=
{
  top.fileErrors <-
      [errorMsg("Quit command not allowed in file processing")];
}


aspect production backCommand
top::NoOpCommand ::= i::Integer
{
  top.fileErrors <-
      [errorMsg("#back command not allowed in file processing")];
}


aspect production resetCommand
top::NoOpCommand ::=
{
  top.fileErrors <-
      [errorMsg("#reset command not allowed in file processing")];
}

