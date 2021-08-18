grammar interface_:toAbella:abstractSyntax;

import interface_:thmInterfaceFile:abstractSyntax;

{-
  This file is to allow us to compile our current definitions and
  theorems into a file which can be read by Silver to compile an
  interface file for other grammars which import the current one.
  This file will have the same format as the interface files.

  We put these definitions in a separate file because they are
  separate from general running.
-}


function buildCompiledOutput
String ::= currentGrammar::String comms::ListOfCommands
           silverContext::Decorated SilverContext
{
  comms.silverContext = silverContext;
  return
     currentGrammar ++ ". " ++ --current grammar
     ". " ++ --no imports defined here
     implode("", map((.pp), comms.defs)) ++ " " ++ --definitions
     implode("", map((.pp), comms.thms)); --theorems/splits
}



monoid attribute thms::[ParsedElement] with [], ++;
propagate thms on ListOfCommands, AnyCommand, TopCommand;

monoid attribute defs::[DefElement] with [], ++;
propagate defs on ListOfCommands, AnyCommand, TopCommand;


attribute thms, defs occurs on ListOfCommands;

attribute thms, defs occurs on AnyCommand;

attribute thms, defs occurs on TopCommand;


aspect production theoremDeclaration
top::TopCommand ::= name::String params::[String] body::Metaterm
{
  top.thms <- [nonextensibleTheorem(name, body.translation)];
}


aspect production extensibleTheoremDeclaration
top::TopCommand ::= depth::Integer thms::[(String, Metaterm, String)]
{
  local full_thms::[(String, Metaterm, String)] =
        translate_bodies(thms, top.silverContext);
  top.thms <- [extensibleMutualTheoremGroup(full_thms)];
}


aspect production splitTheorem
top::TopCommand ::= theoremName::String newTheoremNames::[String]
{
  --When we qualify theorem names, this needs to be cleaned up to
  --   qualify the new theorem names and, if the original split name
  --   isn't qualified, add qualification to that as well
  top.thms <- [splitElement(theoremName, newTheoremNames)];
}


aspect production definitionDeclaration
top::TopCommand ::= preds::[(String, Type)] defs::Defs
{
  --I need to fully qualify these predicates as well
  top.defs <- [defineElement(preds, defs.compileClauses)];
}


synthesized attribute compileClauses::[(Metaterm, Maybe<Metaterm>)]
   occurs on Defs, Def;

aspect production singleDefs
top::Defs ::= d::Def
{
  top.compileClauses = d.compileClauses;
}


aspect production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.compileClauses = d.compileClauses ++ rest.compileClauses;
}


aspect production factDef
top::Def ::= clausehead::Metaterm
{
  top.compileClauses = [(clausehead.translation, nothing())];
}


aspect production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.compileClauses =
      [(clausehead.translation, just(body.translation))];
}

