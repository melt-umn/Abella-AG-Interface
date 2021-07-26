grammar interface_:composed;


{-
  All the parsers we will need
-}
parser from_parse::FullDisplay_c
{
  interface_:fromAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

parser cmd_parse::AnyCommand_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

parser grammar_decl_parse::GrammarDecl_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

--Read a theorem interface file
parser interface_parse::Interface_c
{
  interface_:thm_interface_file;
  interface_:common:concreteSyntax;
}

--Process a theorem file
parser file_parse::FullFile_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

--Read a definition file
parser import_parse::ListOfCommands_c
{
  interface_:toAbella:concreteSyntax;
  interface_:common:concreteSyntax;
}

