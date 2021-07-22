grammar interface_:toAbella:abstractSyntax;


--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp,
   translation<TopCommand>, numCommandsSent, currentState,
   abellaFileParser,  newKnownAttrs, newKnownAttrOccurrences,
     newKnownProductions, newKnownWPDRelations, newKnownTheorems,
     newKnownInheritedAttrs, newKnownLocalAttrs, newKnownFunctions,
   errors, sendCommand, ownOutput,
   translatedTheorems, numRelevantProds;



aspect default production
top::TopCommand ::=
{
  top.sendCommand = true;
  top.ownOutput = "";

  top.numCommandsSent = 1;

  --These are only relevant to extensible theorems
  top.translatedTheorems = error("Should only access translatedTheorem on extensibleTheoremDeclaration");
  top.numRelevantProds = error("Should only access numRelevantProds on extensibleTheoremDeclaration");

  --Most commands aren't adding anything new
  top.newKnownTheorems = top.currentState.knownTheorems;
  top.newKnownAttrs = top.currentState.knownAttrs;
  top.newKnownAttrOccurrences = top.currentState.knownAttrOccurrences;
  top.newKnownProductions = top.currentState.knownProductions;
  top.newKnownFunctions = top.currentState.knownFunctions;
  top.newKnownWPDRelations = top.currentState.knownWPDRelations;
  top.newKnownInheritedAttrs = top.currentState.knownInheritedAttrs;
  top.newKnownLocalAttrs = top.currentState.knownLocalAttrs;
}



abstract production extensibleTheoremDeclaration
top::TopCommand ::= depth::Integer thms::[(String, Metaterm, String)]
{
  local join::(String ::= [(String, Metaterm, String)]) =
        \ l::[(String, Metaterm, String)] ->
          case l of
          | [] -> ""
          | [(thm, body, tr)] ->
            thm ++ " : " ++ body.pp ++ " on " ++ tr
          | (thm, body, tr)::t ->
            thm ++ " : " ++ body.pp ++ " on " ++ tr ++ ", " ++ join(t)
          end;
  top.pp = "Extensible_Theorem " ++ join(thms) ++ ".\n";


  top.errors <-
      foldr(\ p::(String, Metaterm, String) rest::[Error] ->
              if startsWith("$", p.1)
              then [errorMsg("Theorem names cannot start with \"$\"")] ++ rest
              else rest,
            [], thms);
  top.errors <-
      foldr(\ p::(String, Metaterm, String) rest::[Error] ->
              if startsWith("$", p.3)
              then [errorMsg("Identifiers cannot start with \"$\"")] ++ rest
              else rest,
            [], thms);
  top.errors <-
      foldr(\ p::(String, Metaterm, String) rest::[Error] ->
              case decorate p.2 with {
                      findNameType = p.3;
                      attrOccurrences =
                         top.currentState.knownAttrOccurrences;
                      boundVars = [];
                      knownTyParams = []; --we disallow parameterization currently
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
                else [errorMsg("Cannot prove an extensible theorem based on " ++
                               "variable " ++ p.3 ++ " of type " ++ ty.pp ++
                               "; must be a tree")]
              end,
            [], thms);

  local translated::[(String, Metaterm, String)] =
        translate_bodies(thms, top.currentState.knownAttrOccurrences);

  --(translated theorem body, induction tree, induction type, prods, thm name)
  local groupings::[(Metaterm, String, Type, [String], String)] =
        map(\ p::(String, Metaterm, String) ->
              let ty::Type =
                  decorate p.2 with {
                     findNameType = p.3;
                     attrOccurrences =
                        top.currentState.knownAttrOccurrences;
                     boundVars = [];
                     knownTyParams = []; --we disallow parameterization currently
                  }.foundNameType.fromRight
              in
                (p.2, p.3, ty,
                 head(findWPDRelations(ty,
                         top.currentState.knownWPDRelations)).3, p.1)
              end, translated);

  local allUsedNames::[String] =
        nub(flatMap(\ p::(String, Metaterm, String) ->
                      p.2.usedNames, thms));
  local expandedBody::Metaterm =
        buildExtensibleTheoremBody(
           map(\ p::(Metaterm, String, Type, [String], String) ->
                 (p.1, p.2, p.3, p.4), groupings), allUsedNames,
           top.currentState.knownProductions,
           top.currentState.knownLocalAttrs);
  --number of pieces in the generated theorem
  local numBodies::Integer =
        foldr(\ p::(Metaterm, String, Type, [String], String) rest::Integer ->
                rest + length(p.4),
              0, groupings);
  local combinedName::String =
        case thms of
        | (name, _, _)::_ -> extensible_theorem_name(name)
        | [] -> error("Cannot have no theorems in Extensible_Theorem declaration")
        end;
  top.translation =
      if numBodies > 1
      then theoremAndProof(combinedName, [], expandedBody, [splitTactic()])
      else theoremDeclaration(combinedName, [], expandedBody);
  top.numCommandsSent =
      if numBodies > 1
      then 2
      else 1;

  top.translatedTheorems =
      map(\ p::(String, Metaterm, String) -> (p.1, p.2), translated);

  --The number of splits to do when the theorem is done
  top.numRelevantProds =
      map(\ p::(Metaterm, String, Type, [String], String) ->
            (p.5, length(p.5)), groupings);

  top.newKnownTheorems =
      map(\ p::(String, Metaterm, String) -> (p.1, p.2), translated) ++
      top.currentState.knownTheorems;
}

--Simply translate the metaterms in the thms argument
--This is best done in a function where we can have each body be a local
function translate_bodies
[(String, Metaterm, String)] ::= thms::[(String, Metaterm, String)]
      attrOccurs::[(String, [(Type, Type)])]
{
  local body::Metaterm = head(thms).2;
  body.attrOccurrences = attrOccurs;
  body.boundVars = [];
  body.finalTys = [];
  body.knownNames = [head(thms).3];
  body.knownTrees = head(thms).3::body.gatheredTrees;
  body.knownDecoratedTrees = body.gatheredDecoratedTrees;
  body.knownTyParams = [];
  return
     case thms of
     | [] -> []
     | (name, _, tr)::tl -> 
       (name, body.translation, tr)::translate_bodies(tl, attrOccurs)
     end;
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
  body.knownNames = [];
  body.attrOccurrences = top.currentState.knownAttrOccurrences;
  body.knownTrees = body.gatheredTrees;
  body.knownDecoratedTrees = body.gatheredDecoratedTrees;
  body.knownTyParams = params;
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
         a ++ " : " ++ b.pp ++ ", " ++ buildPreds(rest)
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


abstract production grammarCommand
top::TopCommand ::= importGrammar::String
{
  top.pp = "Grammar " ++ importGrammar ++ ".\n";

  {-
    We can't import Abella files which include defined relations
    (constants with result type prop).  We use such constants all over
    in component definitions, so we are going to read the files and
    pass their text to Abella directly.
  -}
  --Get the location of the generated directory
  local gen_loc::IOVal<String> = envVar("SILVER_GEN", unsafeIO());
  local gen_loc_exists::Boolean = gen_loc.iovalue != "";
  --Make the correct filename for the grammar
  local grammar_components::[String] = explode(":", importGrammar);
  local readFilename::String =
        gen_loc.iovalue ++ "/" ++ implode("/", grammar_components) ++
        "/definitions.thm";
  --TODO:  Currently not handling imports, interface file in general
  local fileExists::IOVal<Boolean> =
        isFile(readFilename, gen_loc.io);
  local fileContents::IOVal<String> =
        readFile(readFilename, fileExists.io);
  local fileParsed::Either<String ListOfCommands> =
        top.abellaFileParser(fileContents.iovalue, readFilename);
  local fileAST::ListOfCommands = fileParsed.fromRight;
  top.translation = textCommand(fileAST.pp);

  top.numCommandsSent = fileAST.numCommandsSent;

  top.newKnownAttrs =
      fileAST.newAttrs ++ top.currentState.knownAttrs;
  top.newKnownAttrOccurrences =
      combineAssociations(fileAST.newAttrOccurrences,
                          top.currentState.knownAttrOccurrences);
  top.newKnownProductions =
      fileAST.newProductions ++ top.currentState.knownProductions;
  top.newKnownFunctions =
      fileAST.newFunctions ++ top.currentState.knownFunctions;
  top.newKnownWPDRelations =
      fileAST.newWPDRelations ++ top.currentState.knownWPDRelations;
  top.newKnownTheorems =
      fileAST.newTheorems ++ top.currentState.knownTheorems;
  top.newKnownInheritedAttrs =
      fileAST.newInheritedAttrs ++ top.currentState.knownInheritedAttrs;
  top.newKnownLocalAttrs =
      fileAST.newLocalAttrs ++ top.currentState.knownLocalAttrs;

  top.errors <-
      if !fileExists.iovalue
      then [errorMsg("File \"" ++ readFilename ++ "\" does not exist")]
      else if !gen_loc_exists
      then [errorMsg("Silver generated directory location not set")]
      else if !fileParsed.isRight
      then [errorMsg("File \"" ++ readFilename ++ "\" could not " ++
                     "be parsed:\n" ++ fileParsed.fromLeft)]
      else [];
}


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = "Query " ++ m.pp ++ ".\n";

  m.attrOccurrences = top.currentState.knownAttrOccurrences;
  m.boundVars = [];
  m.knownNames = [];
  m.knownTyParams = [];

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


{-
  The purpose of this production is to allow us to declare a theorem
  *AND* do some number of steps of the proof as well.  I don't know
  that we will ever want to do more than one step of the proof, but
  this allows it if we do want to do so.
-}
abstract production theoremAndProof
top::TopCommand ::= name::String params::[String] body::Metaterm prf::[ProofCommand]
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
      " : " ++ body.pp ++ ".\n" ++
      implode("", map((.pp), prf));
  top.translation = error("Should not be translating theoremAndProof");
  top.numCommandsSent = 1 + length(prf);

  top.newKnownTheorems =
      [(name, new(body))] ++ top.currentState.knownTheorems;
}

