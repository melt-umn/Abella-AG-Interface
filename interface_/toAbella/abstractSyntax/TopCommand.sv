grammar interface_:toAbella:abstractSyntax;


--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp,
   translation<TopCommand>, currentState,
   errors, sendCommand, ownOutput,
   translatedTheorem, numRelevantProds;



aspect default production
top::TopCommand ::=
{
  top.sendCommand = true;
  top.ownOutput = "";

  --These are only relevant to extensible theorems
  top.translatedTheorem = error("Should only access translatedTheorem on extensibleTheoremDeclaration");
  top.numRelevantProds = error("Should only access numRelevantProds on extensibleTheoremDeclaration");
}



abstract production extensibleTheoremDeclaration
top::TopCommand ::= name::String depth::Integer body::Metaterm tree::String
{
  top.pp =
      "Extensible_Theorem " ++ name ++ "[" ++ toString(depth) ++ "]" ++
      " : " ++ body.pp ++ " on " ++ tree ++ ".\n";

  body.attrOccurrences = top.currentState.knownAttrOccurrences;
  body.boundVars = [];

  top.errors <-
      case treeTy of
      | left(msg) -> [errorMsg(msg)]
      | right(ty) ->
        if tyIsNonterminal(ty)
        then --This needs to be in here (not separate) because it relies on treeTy = right(_)
             case correctWPDRelation of
             | just(_) -> []
             | nothing() ->
               [errorMsg("Unknown nonterminal type " ++ ty.pp ++
                         "; did you modify the definition file?")]
             end
        else [errorMsg("Cannot prove an extensible theorem based on a " ++
                       "variable of type " ++ ty.pp ++ "; must be a tree")]
      end;

  body.findNameType = tree;
  local treeTy::Either<String Type> = body.foundNameType;
  local correctWPDRelation::Maybe<(Type, [String])> =
        findAssociated(wpdTypeName(treeTy.fromRight), top.currentState.knownWPDRelations);
  local expandedBody::Metaterm =
        buildExtensibleTheoremBody(
           body.translation, tree, treeTy.fromRight,
           correctWPDRelation.fromJust, nub(body.usedNames),
           top.currentState.knownProductions);
  top.translation = theoremDeclaration("$" ++ name, [], expandedBody);
  --we probably also want to send a "split" after this

  top.translatedTheorem = body.translation;
  body.knownTrees = tree::body.gatheredTrees;
  top.numRelevantProds = length(correctWPDRelation.fromJust.snd);
}


abstract production theoremDeclaration
top::TopCommand ::= name::String params::[String] body::Metaterm
{
  local buildParams::(String ::= [String]) =
     \ p::[String] ->
       case p of
       | [] ->
         error("Should not reach here; theoremDeclaration production")
       | [a] -> a
       | a::rest ->
         a ++ ", " ++ buildParams(rest)
       end;
  local paramsString::String =
     if null(params)
     then ""
     else " [" ++ buildParams(params) ++ "] ";
  top.pp =
      "Theorem " ++ name ++ " " ++ paramsString ++
      " : " ++ body.pp ++ ".\n";

  body.boundVars = [];
  body.attrOccurrences = top.currentState.knownAttrOccurrences;
  body.knownTrees = body.gatheredTrees;
  top.translation = theoremDeclaration(name, params, body.translation);
}


abstract production definitionDeclaration
top::TopCommand ::= preds::[(String, Type)] defs::Defs
{
  local buildPreds::(String ::= [(String, Type)]) =
     \ w::[Pair<String Type>] ->
       case w of
       | [] ->
         error("Should not reach here; definitionDeclaration production")
       | [pair(a, b)] -> a ++ " : " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " := " ++ b.pp ++ ", " ++ buildPreds(rest)
       end;
  local predsString::String =
     if null(preds)
     then error("Definition should not be empty; definitionDeclaration")
     else buildPreds(preds);
  top.pp = "Define " ++ predsString ++ " by " ++ defs.pp ++ ".";

  top.translation = error("Translation not done in definitionDeclaration yet");
}


abstract production codefinitionDeclaration
top::TopCommand ::= preds::[(String, Type)] defs::Defs
{
  local buildPreds::(String ::= [(String, Type)]) =
     \ w::[Pair<String Type>] ->
       case w of
       | [] ->
         error("Should not reach here; codefinitionDeclaration production")
       | [pair(a, b)] -> a ++ " : " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " := " ++ b.pp ++ ", " ++ buildPreds(rest)
       end;
  local predsString::String =
     if null(preds)
     then error("CoDefinition should not be empty; codefinitionDeclaration")
     else buildPreds(preds);
  top.pp = "CoDefine " ++ predsString ++ " by " ++ defs.pp ++ ".";

  top.translation = error("Translation not done in codefinitionDeclaration yet");
}


abstract production importCommand
top::TopCommand ::= importFile::String withs::[(String, String)]
{
  local buildWiths::(String ::= [(String, String)]) =
     \ w::[Pair<String String>] ->
       case w of
       | [] ->
         error("Should not reach here; importCommand production")
       | [pair(a, b)] -> a ++ " := " ++ b
       | pair(a,b)::rest ->
         a ++ " := " ++ b ++ ", " ++ buildWiths(rest)
       end;
  local withString::String =
     if null(withs)
     then ""
     else " with " ++ buildWiths(withs);
  top.pp = "Import \"" ++ importFile ++ "\"" ++ withString ++ ".\n";

  {-
    We can't import Abella files which include defined relations
    (constants with result type prop).  We use such constants all over
    in component definitions, so we are going to read the files and
    pass their text to Abella directly.  I'm not handling withs in
    that case, but there shouldn't be any withs any.

    For simplicity, we are going to import our library files normally,
    since they don't include any declared relations.
  -}
  local libraryFiles::[String] =
        ["bools", "integers", "integer_addition", "integer_multiplication",
         "integer_division", "integer_comparison", "lists", "pairs",
         "strings", "attr_val"];
  local readFilename::String = importFile ++ ".thm";
  local fileExists::Boolean = isFile(readFilename, unsafeIO()).iovalue;
  top.translation =
      if contains(fileNameInFilePath(importFile), libraryFiles)
      then importCommand(importFile, withs)
      else textCommand(readFile(importFile ++ ".thm", unsafeIO()).iovalue);

  top.errors <-
      if fileExists
      then []
      else [errorMsg("File \"" ++ readFilename ++ "\" does not exist")];
}


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = "Query " ++ m.pp ++ ".\n";

  m.attrOccurrences = top.currentState.knownAttrOccurrences;
  m.boundVars = [];

  top.translation = error("Translation not done in queryCommand yet");
}


abstract production splitTheorem
top::TopCommand ::= theoremName::String newTheoremNames::[String]
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; splitTheorem production")
       | [a] -> a
       | a::rest -> a ++ ", " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(newTheoremNames)
     then ""
     else " as " ++ buildNames(newTheoremNames);
  top.pp = "Split " ++ theoremName ++ namesString ++ ".\n";

  top.translation = splitTheorem(theoremName, newTheoremNames);
}


--I'm not sure we need new kinds and types declared by the user, but I'll put it in
abstract production kindDeclaration
top::TopCommand ::= names::[String] k::Kind
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; splitTheorem production")
       | [a] -> a
       | a::rest -> a ++ ", " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(names)
     then ""
     else " " ++ buildNames(names);
  top.pp = "Kind " ++ namesString ++ "   " ++ k.pp ++ ".\n";

  top.translation = --error("Translation not done in kindDeclaration yet");
      kindDeclaration(names, k);
}


abstract production typeDeclaration
top::TopCommand ::= names::[String] ty::Type
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; splitTheorem production")
       | [a] -> a
       | a::rest -> a ++ ", " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(names)
     then ""
     else " as " ++ buildNames(names);
  top.pp = "Type " ++ namesString ++ "   " ++ ty.pp ++ ".\n";

  top.translation = error("Translation not done in typeDeclaration yet");
}


abstract production closeCommand
top::TopCommand ::= tys::[Type]
{
  local buildTypes::(String ::= [Type]) =
     \ n::[Type] ->
       case n of
       | [] ->
         error("Should not reach here; closeCommand production")
       | [a] -> a.pp
       | a::rest -> a.pp ++ ", " ++ buildTypes(rest)
       end;
  local typesString::String =
     if null(tys)
     then error("Close commands should not be devoid of tyes")
     else buildTypes(tys);
  top.pp = "Close " ++ typesString ++ ".\n";

  top.translation = error("Translation not done in closeCommand yet");
}



--This is to handle imports for reasons described there
abstract production textCommand
top::TopCommand ::= text::String
{
  top.pp = text;
  top.translation = textCommand(text);
}

