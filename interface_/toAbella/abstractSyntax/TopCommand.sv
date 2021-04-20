grammar interface_:toAbella:abstractSyntax;


--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp,
   translation<TopCommand>, numCommandsSent, currentState,
   abellaFileParser,  newKnownAttrs, newKnownAttrOccurrences,
     newKnownProductions, newKnownWPDRelations, newKnownTheorems,
     newKnownInheritedAttrs,
   errors, sendCommand, ownOutput,
   translatedTheorem, numRelevantProds;



aspect default production
top::TopCommand ::=
{
  top.sendCommand = true;
  top.ownOutput = "";

  top.numCommandsSent = 1;

  --These are only relevant to extensible theorems
  top.translatedTheorem = error("Should only access translatedTheorem on extensibleTheoremDeclaration");
  top.numRelevantProds = error("Should only access numRelevantProds on extensibleTheoremDeclaration");

  --Most commands aren't adding anything new
  top.newKnownTheorems = top.currentState.knownTheorems;
  top.newKnownAttrs = top.currentState.knownAttrs;
  top.newKnownAttrOccurrences = top.currentState.knownAttrOccurrences;
  top.newKnownProductions = top.currentState.knownProductions;
  top.newKnownWPDRelations = top.currentState.knownWPDRelations;
  top.newKnownInheritedAttrs = top.currentState.knownInheritedAttrs;
}



abstract production extensibleTheoremDeclaration
top::TopCommand ::= name::String depth::Integer body::Metaterm trees::[String]
{
  local join::(String ::= [String]) =
        \ l::[String] ->
          case l of
          | [] -> ""
          | [h] -> h
          | h::t -> h ++ " " ++ join(t)
          end;
  top.pp =
      "Extensible_Theorem " ++ name ++ "[" ++ toString(depth) ++ "]" ++
      " : " ++ body.pp ++ " on " ++ join(trees) ++ ".\n";

  body.attrOccurrences = top.currentState.knownAttrOccurrences;
  body.boundVars = [];
  body.finalTys = [];

  local thms::[Metaterm] = splitMetaterm(body);

  top.errors <-
      if startsWith("$", name)
      then [errorMsg("Cannot start theorem names with \"$\"")]
      else [];
  top.errors <-
      foldr(\ s::String rest::[Error] ->
              if startsWith("$", s)
              then [errorMsg("Identifiers cannot start with \"$\"")] ++ rest
              else rest,
            [], trees);
  top.errors <-
      if length(trees) != length(thms)
      then [errorMsg("Expecting " ++ toString(length(thms)) ++
                     " induction arguments but got " ++
                     toString(length(trees)))]
      else [];
  top.errors <-
      foldr(\ p::(String, Metaterm) rest::[Error] ->
              case decorate p.2 with {
                      findNameType = p.1;
                      attrOccurrences =
                         top.currentState.knownAttrOccurrences;
                      boundVars = [];
                   }.foundNameType of
              | left(msg) -> [errorMsg(msg)]
              | right(ty) ->
                if tyIsNonterminal(ty)
                then
                  case findWPDRelations(ty,
                          top.currentState.knownWPDRelations) of
                  | h::t -> []
                  | [] ->
                    [errorMsg("Unknown nonterminal type " ++ ty.pp)]
                  end
                else [errorMsg("Cannot prove an extensible theorem based on a " ++
                               "variable of type " ++ ty.pp ++ "; must be a tree")]
              end,
            [], zipLists(trees, thms));

  local groupings::[(Metaterm, String, Type, [String])] =
        map(\ p::(String, Metaterm) ->
              let ty::Type = decorate p.2 with {
                                findNameType = p.1;
                                attrOccurrences =
                                   top.currentState.knownAttrOccurrences;
                                boundVars = [];
                             }.foundNameType.fromRight
              in
              let trans::Metaterm =
                  decorate p.2 with {
                     knownTrees = p.1::body.gatheredTrees;
                     finalTys = [];
                     boundVars = [];
                     attrOccurrences =
                        top.currentState.knownAttrOccurrences;
                  }.translation
              in
                (trans, p.1, ty,
                 head(findWPDRelations(ty,
                         top.currentState.knownWPDRelations)).3)
              end
              end, zipLists(trees, thms));

  local expandedBody::Metaterm =
        buildExtensibleTheoremBody(
           groupings, nub(body.usedNames),
           top.currentState.knownProductions);
  top.translation = theoremDeclaration("$" ++ name, [], expandedBody);

  body.knownTrees = trees ++ body.gatheredTrees;
  top.translatedTheorem = body.translation;

  --The number of splits to do when the theorem is done
  top.numRelevantProds =
      foldr(\ p::(Metaterm, String, Type, [String]) sum::Integer ->
              sum + length(p.4),
            0, groupings);

  top.newKnownTheorems =
      [(name, body.translation)] ++ top.currentState.knownTheorems;
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

  top.errors <-
      if startsWith("$", name)
      then [errorMsg("Cannot start theorem names with \"$\"")]
      else [];

  body.boundVars = [];
  body.finalTys = [];
  body.attrOccurrences = top.currentState.knownAttrOccurrences;
  body.knownTrees = body.gatheredTrees;
  top.translation = theoremDeclaration(name, params, body.translation);

  top.newKnownTheorems =
      [(name, body.translation)] ++ top.currentState.knownTheorems;
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
    that case, but there shouldn't be any withs anyway.

    For simplicity, we are going to import our library files normally,
    since they don't include any declared relations.
  -}
  local libraryFiles::[String] =
        ["bools", "integers", "integer_addition", "integer_multiplication",
         "integer_division", "integer_comparison", "lists", "pairs",
         "strings", "attr_val"];
  local readFilename::String = importFile ++ ".thm";
  local isLibrary::Boolean =
        contains(fileNameInFilePath(importFile), libraryFiles);
  local fileExists::Boolean = isFile(readFilename, unsafeIO()).iovalue;
  local fileContents::String = readFile(readFilename, unsafeIO()).iovalue;
  local fileParsed::Either<String ListOfCommands> =
        top.abellaFileParser(fileContents, readFilename);
  local fileAST::ListOfCommands = fileParsed.fromRight;
  top.translation =
      if isLibrary
      then importCommand(importFile, withs)
      else textCommand(fileAST.pp);

  top.numCommandsSent =
      if isLibrary
      then 1
      else fileAST.numCommandsSent;

  top.newKnownAttrs =
      fileAST.newAttrs ++ top.currentState.knownAttrs;
  top.newKnownAttrOccurrences =
      combineAssociations(fileAST.newAttrOccurrences,
                          top.currentState.knownAttrOccurrences);
  top.newKnownProductions =
      fileAST.newProductions ++ top.currentState.knownProductions;
  top.newKnownWPDRelations =
      fileAST.newWPDRelations ++ top.currentState.knownWPDRelations;
  top.newKnownTheorems =
      fileAST.newTheorems ++ top.currentState.knownTheorems;
  top.newKnownInheritedAttrs =
      fileAST.newInheritedAttrs ++ top.currentState.knownInheritedAttrs;

  top.errors <-
      if fileExists
      then if !isLibrary && fileParsed.isRight
           then []
           else [errorMsg("File \"" ++ readFilename ++
                          "\" could not be parsed:\n" ++
                          fileParsed.fromLeft)]
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

  top.errors <-
      if startsWith("$", theoremName)
      then [errorMsg("Cannot start theorem names with \"$\"")]
      else [];
  top.errors <-
      foldr(\ s::String rest::[Error] ->
              if startsWith("$", s)
              then [errorMsg("Cannot start theorem names with \"$\"")] ++ rest
              else rest,
            [], newTheoremNames);

  local buildnames::([(String, Metaterm)] ::= [Metaterm] [String] Integer) =
        \ splits::[Metaterm] givenNames::[String] i::Integer ->
          case splits, givenNames of
          | [], _ -> []
          | mt::mttl, [] ->
            (theoremName ++ toString(i), mt)::buildnames(mttl, [], i + 1)
          | mt::mttl, n::ntl ->
            (n, mt)::buildnames(mttl, ntl, i + 1)
          end;  
  top.newKnownTheorems =
      case findAssociated(theoremName, top.currentState.knownTheorems) of
      | nothing() -> []
      | just(mt) ->
        buildnames(mt.conjunctionSplit, newTheoremNames, 1)
      end ++ top.currentState.knownTheorems;
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
     else buildNames(names);
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

