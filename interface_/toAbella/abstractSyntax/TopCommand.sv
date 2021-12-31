grammar interface_:toAbella:abstractSyntax;

import interface_:thmInterfaceFile:abstractSyntax;

--things you can do outside of proofs

nonterminal TopCommand with
   --pp should always end with a newline
   pp,
   translation<TopCommand>, numCommandsSent, currentState, silverContext,
   newKnownTheorems, provingTheorems,
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

  --Most commands aren't declaring anything to prove
  top.provingTheorems = [];
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
              if indexOf("$", p.1) >= 0
              then [errorMsg("Theorem names cannot contain \"$\"")] ++ rest
              else rest,
            [], thms);
  top.errors <-
      foldr(\ p::(String, Metaterm, String) rest::[Error] ->
              if indexOf("$", p.3) >= 0
              then [errorMsg("Identifiers cannot contain \"$\"")] ++ rest
              else rest,
            [], thms);
  top.errors <-
      gather_bodies_errors(
         thms, top.currentState, top.silverContext);

  local translated::[(String, Metaterm, String)] =
        translate_bodies(thms, top.silverContext);

  --(translated theorem body, induction tree, induction type, prods, thm name)
  local groupings::[(Metaterm, String, Type, [String], String)] =
        map(\ p::(String, Metaterm, String) ->
              let ty::Type =
                  decorate p.2 with {
                     findNameType = p.3;
                     boundVars = [];
                     knownTyParams = []; --we disallow parameterization currently
                     silverContext = top.silverContext;
                  }.foundNameType.fromRight
              in
                case ty of
                | nameType(nt) ->
                  (p.2, p.3, nameType(encodedToColons(nt)),
                   head(findWPDRelations(nameType(encodedToColons(nt)),
                           top.silverContext.knownWPDRelations)).3, p.1)
                | _ -> error("WPD relations only exist for nonterminal types")
                end
              end, translated);

  local allUsedNames::[String] =
        nub(flatMap(\ p::(String, Metaterm, String) ->
                      decorate p.2 with
                      {silverContext = top.silverContext;}.usedNames,
                    thms));
  local expandedBody::Metaterm =
        buildExtensibleTheoremBody(
           map(\ p::(Metaterm, String, Type, [String], String) ->
                 (p.1, p.2, p.3, p.4), groupings), allUsedNames,
           top.silverContext);
  --number of pieces in the generated theorem
  local numBodies::Integer =
        foldr(\ p::(Metaterm, String, Type, [String], String) rest::Integer ->
                rest + length(p.4),
              0, groupings);
  local combinedName::String =
        case thms of
        | (name, _, _)::_ ->
          extensible_theorem_name(name,
             top.silverContext.currentGrammar)
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
      map(\ p::(String, Metaterm, String) ->
            (colonsToEncoded(top.silverContext.currentGrammar ++
                             ":" ++ p.1), p.2),
          translated);

  --The number of splits to do when the theorem is done
  top.numRelevantProds =
      map(\ p::(Metaterm, String, Type, [String], String) ->
            (p.5, length(p.5)), groupings);

  top.provingTheorems =
      map(\ p::(String, Metaterm, String) ->
            (p.1, top.silverContext.currentGrammar, p.2),
          translated);
}

--Simply translate the metaterms in the thms argument
--This is best done in a function where we can have each body be a local
function translate_bodies
[(String, Metaterm, String)] ::= thms::[(String, Metaterm, String)]
          silverContext::Decorated SilverContext
{
  local body::Metaterm = head(thms).2;
  body.boundVars = [];
  body.finalTys = [];
  body.knownNames = [head(thms).3];
  body.knownTrees = head(thms).3::body.gatheredTrees;
  body.knownDecoratedTrees = body.gatheredDecoratedTrees;
  body.knownTyParams = [];
  body.silverContext = silverContext;
  return
     case thms of
     | [] -> []
     | (name, _, tr)::tl -> 
       (name, body.translation, tr)::
       translate_bodies(tl, silverContext)
     end;
}

function gather_bodies_errors
[Error] ::= thms::[(String, Metaterm, String)]
            currentState::ProverState
            silverContext::Decorated SilverContext
{
  local fst_thm::(String, Metaterm, String) =
        case thms of
        | h::_ -> h
        | _ -> error("Should not access fst_thm if empty")
        end;
  local body::Metaterm = fst_thm.2;
  body.boundVars = [];
  body.finalTys = [];
  body.knownNames = [fst_thm.3];
  body.knownTrees = fst_thm.3::body.gatheredTrees;
  body.knownDecoratedTrees = body.gatheredDecoratedTrees;
  body.knownTyParams = [];
  body.silverContext = silverContext;
  body.currentState = currentState;
  body.findNameType = fst_thm.3;
  return
     case thms of
     | [] -> []
     | (name, _, tr)::tl ->
       ( if null(body.errors)
         then case body.foundNameType of
              | left(msg) -> [errorMsg(msg)]
              | right(ty) ->
                if tyIsNonterminal(ty)
                then --NT type exists if a WPD relation exists
                  case findWPDRelations(ty,
                          silverContext.knownWPDRelations) of
                  | h::t -> []
                  | [] ->
                    [errorMsg("Unknown nonterminal type " ++ ty.pp)]
                  end
                else [errorMsg("Cannot prove an extensible theorem based on " ++
                               "variable " ++ tr ++ " of type " ++ ty.pp ++
                               "; must be a tree")]
              end
         else body.errors ) ++
       gather_bodies_errors(tl, currentState, silverContext)
     end;
}


abstract production proveObligations
top::TopCommand ::= names::[String]
{
  top.pp = "Prove " ++ implode(", ", names) ++ ".\n";

  top.errors <-
      flatMap(\ s::String ->
                if indexOf("$", s) >= 0
                then [errorMsg("Theorem names cannot contain \"$\"")]
                else [],
              names);
  top.errors <-
      case top.currentState.remainingObligations of
      | [] -> [errorMsg("No obligations remaining to prove")]
      | extensibleMutualTheoremGroup(thms)::_ ->
        if map(fst, thms) == names
        then []
        else [errorMsg("Next obligation is " ++ implode(", ", map(fst, thms)))]
      | _::_ -> error("Should not have anything else to start")
      end;

  local thms::[(String, Metaterm, String)] =
        case top.currentState.remainingObligations of
        | extensibleMutualTheoremGroup(thms)::_ -> thms
        | _ -> error("Should not access local thms with errors")
        end;
  local translated::[(String, Metaterm, String)] =
        translate_bodies(thms, top.silverContext);

  --(translated theorem body, induction tree, induction type, prods, thm name)
  local groupings::[(Metaterm, String, Type, [String], String)] =
        map(\ p::(String, Metaterm, String) ->
              let ty::Type =
                  decorate p.2 with {
                     findNameType = p.3;
                     boundVars = [];
                     knownTyParams = []; --we disallow parameterization currently
                     silverContext = top.silverContext;
                  }.foundNameType.fromRight
              in
                case ty of
                | nameType(nt) ->
                  (p.2, p.3, nameType(encodedToColons(nt)),
                   case findSpecificWPDRelation(
                           nameType(encodedToColons(nt)),
                           top.silverContext.knownWPDRelations,
                           top.silverContext.currentGrammar) of
                   | just((_, _, prods)) -> prods
                   | nothing() -> [] --Can legitimately not have any prods for a known NT
                   end, p.1)
                | _ -> error("WPD relations only exist for nonterminal types")
                end
              end, translated);

  local allUsedNames::[String] =
        nub(flatMap(\ p::(String, Metaterm, String) ->
                      decorate p.2 with
                      {silverContext = top.silverContext;}.usedNames,
                    thms));
  local expandedBody::Metaterm =
        buildExtensibleTheoremBody(
           map(\ p::(Metaterm, String, Type, [String], String) ->
                 (p.1, p.2, p.3, p.4), groupings), allUsedNames,
           top.silverContext);
  --number of pieces in the generated theorem
  local numBodies::Integer =
        foldr(\ p::(Metaterm, String, Type, [String], String) rest::Integer ->
                rest + length(p.4),
              0, groupings);
  local combinedName::String =
        case thms of
        | (name, _, _)::_ ->
          extensible_theorem_name(encodedToColons(name),
             top.silverContext.currentGrammar)
        | [] -> error("Cannot have no theorems in Extensible_Theorem declaration")
        end;

  top.translation =
      if numBodies > 1
      then theoremAndProof(combinedName, [], expandedBody, [splitTactic()])
      else if numBodies == 0
      then --if no new prods, nothing to prove---just make it enter the thms
           theoremAndProof(combinedName, [], trueMetaterm(), [skipTactic()])
      else theoremDeclaration(combinedName, [], expandedBody); --one production
  top.numCommandsSent =
      if numBodies == 1
      then 1
      else 2;

  top.translatedTheorems =
      map(\ p::(String, Metaterm, String) ->
            (colonsToEncoded(p.1), p.2),
          translated);

  --The number of splits to do when the theorem is done
  top.numRelevantProds =
      map(\ p::(Metaterm, String, Type, [String], String) ->
            (p.5, length(p.5)), groupings);

  top.provingTheorems =
      map(\ p::(String, Metaterm, String) ->
            let split::(String, String) = splitQualifiedName(p.1)
            in
              (split.2, split.1, p.2)
            end,
          translated);
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
      if indexOf("$", name) >= 0
      then [errorMsg("Theorem names cannot contain \"$\"")]
      else [];

  body.boundVars = [];
  body.finalTys = [];
  body.knownNames = [];
  body.knownTrees = body.gatheredTrees;
  body.knownDecoratedTrees = body.gatheredDecoratedTrees;
  body.knownTyParams = params;
  top.translation =
      theoremDeclaration(
         colonsToEncoded(top.silverContext.currentGrammar ++ ":" ++ name),
         params, body.translation);

  top.provingTheorems =
      [(name, top.silverContext.currentGrammar, body.translation)];
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


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = "Query " ++ m.pp ++ ".\n";

  m.boundVars = [];
  m.knownNames = [];
  m.knownTyParams = [];
  m.finalTys = [];
  m.knownTrees = m.gatheredTrees;

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

  top.translation =
      splitTheorem(head(foundThm).1,
                   map(\ p::(String, String) ->
                         colonsToEncoded(p.2 ++ ":" ++ p.1),
                       expandedNewNames));

  top.errors <-
      if indexOf("$", theoremName) >= 0
      then [errorMsg("Theorem names cannot contain \"$\"")]
      else [];
  top.errors <-
      foldr(\ s::String rest::[Error] ->
              if indexOf("$", s) >= 0
              then [errorMsg("Theorem names cannot contain \"$\"")] ++ rest
              else rest,
            [], newTheoremNames);
  top.errors <-
      case foundThm of
      | [] -> [errorMsg("Unknown theorem " ++ theoremName)]
      | [_] -> []
      | lst ->
        [errorMsg("Uncertain theorem " ++ theoremName ++
                  "; options are " ++ implode(", ", map(fst, lst)))]
      end;

  local foundThm::[(String, Metaterm)] =
        findTheorem(theoremName, top.currentState);
  local splitThm::[Metaterm] =
        decorate head(foundThm).2 with {
           silverContext = top.silverContext;
        }.conjunctionSplit;
  --To fit the grammar naming scheme, we need to name everything
  local expandedNewNames::[(String, String)] =
        map(\ s::String ->
              (s, top.silverContext.currentGrammar),
            newTheoremNames) ++
        foldr(\ m::Metaterm rest::[(String, String)] ->
                (splitQualifiedName(head(foundThm).1).2 ++ "_" ++
                   toString(genInt()),
                 top.silverContext.currentGrammar)::rest,
              [], drop(length(newTheoremNames), splitThm));

  top.newKnownTheorems =
      zipWith(\ a::(String, String) b::Metaterm -> (a.1, a.2, b),
              expandedNewNames, splitThm) ++
      top.currentState.knownTheorems;
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

  ty.knownTyParams = [];

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
  --Assume the proof is fine
  top.translation =
      theoremAndProof(colonsToEncoded(name), params,
                      body.translation, prf);
  top.numCommandsSent = 1 + length(prf);

  body.knownTyParams = params;
  body.boundVars = [];
  body.finalTys = [];
  body.knownTrees = body.gatheredTrees;
  body.knownNames = [];
  body.knownDecoratedTrees = [];

  top.provingTheorems =
      error("Should never be access provingTheorems on theoremAndProof");
}

