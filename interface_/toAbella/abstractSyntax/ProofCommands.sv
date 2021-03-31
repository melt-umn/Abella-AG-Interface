grammar interface_:toAbella:abstractSyntax;


--things you can do inside of proofs

nonterminal ProofCommand with
   pp, --pp should end with two spaces
   translation<[ProofCommand]>, currentState, translatedState,
   errors, sendCommand, ownOutput,
   isUndo, shouldClean,
   stateListIn, stateListOut;



aspect default production
top::ProofCommand ::=
{
  top.sendCommand = true;
  top.ownOutput = "";

  --Only 'undo' is an undo
  top.isUndo = false;
  top.stateListOut = top.stateListIn;
}



abstract production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  local buildInts::(String ::= [Integer]) =
     \ nl::[Integer] ->
       case nl of
       | [] -> error("Empty list of induction premises in inductionTactic")
       | [n] -> toString(n)
       | n::rest -> toString(n) ++ " " ++ buildInts(rest)
       end;
  top.pp = h.pp ++ "induction on " ++ buildInts(nl) ++ ".  ";

  top.translation = [inductionTactic(h, nl)];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.pp = h.pp ++ "coinduction.  ";

  top.translation = [coinductionTactic(h)];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production introsTactic
top::ProofCommand ::= names::[String]
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; introsTactic production")
       | [a] -> a
       | a::rest -> a ++ " " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(names)
     then ""
     else " " ++ buildNames(names);
  top.pp = "intros" ++ namesString ++ ".  ";

  {-
    Need to keep track of introduced names for turning them into structures/nodes.
    e.g. forall (t : nt_Tree), ...
         We might introduce it as tree, in which case we want $tree_Structure and $tree_Node
  -}
  top.translation = --error("Translation not done in introsTactic yet");
      [introsTactic(names)];

  --it would be confusing if intros killed the proof
  top.shouldClean = false;
}


abstract production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable
                      args::[ApplyArg] withs::[Pair<String Term>]
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local buildArgs::(String ::= [ApplyArg]) =
    \ al::[ApplyArg] ->
      case al of
      | [] -> error("Should not reach here; applyTactic production")
      | [a] -> a.pp
      | a::rest -> a.pp ++ " " ++ buildArgs(rest)
      end;
  local argsString::String =
     if null(args)
     then ""
     else " to " ++ buildArgs(args);
  local buildWiths::(String ::= [Pair<String Term>]) =
    \ wl::[Pair<String Term>] ->
      case wl of
      | [] -> error("Should not reach here; applyTactic production")
      | [pair(a, b)] -> a ++ " = " ++ b.pp
      | pair(a, b)::rest -> a ++ " = " ++ b.pp ++ ", " ++ buildWiths(rest)
      end;
  local withsString::String =
     if null(withs)
     then ""
     else " with " ++ buildWiths(withs);
  top.pp = h.pp ++ "apply " ++ depthString ++ theorem.pp ++ argsString ++ withsString ++ ".  ";

  top.errors <-
      case err_trans of
      | left(err) -> [errorMsg(err)]
      | right(_) -> []
      end;

  top.translation =
      case err_trans of
      | left(err) ->
        error("Should not access translation with errors (applyTactic)")
      | right(prf) -> prf
      end;

  local err_trans::Either<String [ProofCommand]> =
      case theorem of
      | clearable(_, "is_list_member", _) ->
        case theorem__is_list_member(h, depth, args, withs,
                top.translatedState.hypList) of
        | right(prf) -> right(prf)
        | left(err) -> left(err)
        end
      | clearable(_, "is_list_append", _) ->
        case theorem__is_list_append(h, depth, args, withs,
                top.translatedState.hypList) of
        | right(prf) -> right(prf)
        | left(err) -> left(err)
        end
      | clearable(x, "attr_unique", y) ->
        case theorem__attr_unique(args, withs,
                top.currentState.state.hypList) of
        | right(thm) -> right([applyTactic(h, depth, clearable(x, thm, y), args, [])])
        | left(err) -> left(err)
        end
      | clearable(x, "attr_is", y) ->
        case theorem__attr_is(h, depth, args, withs,
                top.currentState.state.hypList) of
        | right(thm) -> right([thm])
        | left(err) -> left(err)
        end
      | _ ->
        right([applyTactic(h, depth, theorem, args,
                 map(\ p::Pair<String Term> -> pair(p.fst, p.snd.translation), withs))])
      end;

  top.shouldClean = true;
}


abstract production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable withs::[Pair<String Term>]
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local buildWiths::(String ::= [Pair<String Term>]) =
    \ wl::[Pair<String Term>] ->
      case wl of
      | [] -> error("Should not reach here; backchainTactic production")
      | [pair(a, b)] -> a ++ " = " ++ b.pp
      | pair(a, b)::rest -> a ++ " = " ++ b.pp ++ ", " ++ buildWiths(rest)
      end;
  local withsString::String =
     if null(withs)
     then ""
     else "with " ++ buildWiths(withs);
  top.pp = "backchain " ++ depthString ++ theorem.pp ++ withsString ++ ".  ";

  top.translation = --error("Translation not done in backchainTactic yet");
      [backchainTactic(depth, theorem, map(\ p::Pair<String Term> -> pair(p.fst, p.snd.translation), withs))];

  top.shouldClean = true;
}


abstract production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.pp = h.pp ++ "case " ++ hyp ++ if keep then " (keep).  " else ".  ";

  top.translation = --error("Translation not done in caseTactic yet");
      [caseTactic(h, hyp, keep)];

  top.errors <-
      case findAssociated(hyp, top.translatedState.hypList) of
      --Unknown hypotheses---could also let it go through and Abella catch it
      | nothing() -> [errorMsg("Unknown hypothesis " ++ hyp)]
      --Hidden hypotheses should be left alone
      | just(termMetaterm(applicationTerm(nameTerm(str, _), _), _))
        when startsWith("$", str) ->
        [errorMsg("Unknown hypothesis " ++ hyp)]
      --Disallow case analysis on structure-showing "$<tree>_Tm = <structure>"
      | just(eqMetaterm(nameTerm(str, _), structure)) ->
        [errorMsg("Cannot do case analysis on tree structure hypothesis")]
      --Case analysis on an access doesn't make sense
      | just(attrAccessMetaterm(tree, attr, _)) ->
        [errorMsg("Cannot do case analysis on this hypothesis; to do case " ++
                  "analysis on equation for " ++ tree ++ "." ++ attr ++
                  ", use \"case " ++ tree ++ "." ++ attr ++ "\"")]
      | just(attrAccessEmptyMetaterm(tree, attr)) ->
        [errorMsg("Cannot do case analysis on this hypothesis; to do case " ++
                  "analysis on equation for " ++ tree ++ "." ++ attr ++
                  ", use \"case " ++ tree ++ "." ++ attr)]
      --Anything else is fine
      | just(_) -> []
      end;

  top.shouldClean = true;
}


abstract production caseAttrAccess
top::ProofCommand ::= h::HHint tree::String attr::String
{
  top.pp = h.pp ++ "case " ++ tree ++ "." ++ attr ++ ".  ";

  top.errors <- --need to check for tree existing, as a tree
      if !contains(attr, map(fst, top.currentState.knownAttrs))
      then [errorMsg("Unknown attribute " ++ attr)]
      else case findAssociated(attr, top.currentState.knownAttrOccurrences) of
           | nothing() -> [] --covered by checking if attr exists, so impossible here
           | just(nts) ->
             if isInherited
             then case findParent of
                  | nothing() ->
                    [errorMsg("Cannot do case analysis on inherited attribute "++
                              "equation when parent of tree is unknown")]
                  | just(_) ->
                    case wpdNodeHyp of
                    | nothing() ->
                      [errorMsg("Cannot do case analysis on " ++ tree ++ "." ++ attr ++ " for reasons I can't come up with at the moment; please report this error")]
                    | just(_) -> []
                    end
                  end
             else if containsBy(tysEqual, treeTy, nts)
                  then []
                  else [errorMsg("Attribute " ++ attr ++ " does not occur on " ++ tree)]
           end;

  local newNum::String = toString(genInt());
  local eqHypName::String = "$Eq_" ++ newNum;
  local componentHypName::String = "$EqComp_" ++ newNum;
  --
  local isInherited::Boolean =
        contains(attr, top.currentState.knownInheritedAttrs);
  local findParent::Maybe<(String, Term)> =
        find_parent_tree(tree, top.translatedState.hypList);
  local associatedTree::String =
        if isInherited
        then case findParent of
             | just((tr, _)) -> tr
             | nothing() -> error("findParent should not be nothing")
             end
        else tree;
  local associatedProd::String =
        case find_structure_hyp(associatedTree,
                top.translatedState.hypList) of
        | just(applicationTerm(nameTerm(prod, _), _)) -> prod
        | just(_) -> error("It should be a production (associatedProd)")
        | nothing() -> error("It should have a value (associatedProd)")
        end;
  local makeEqHypThm::Clearable =
        clearable(false, wpdNode_to_AttrEq(attr, treeTy), []);
  local wpdNodeHyp::Maybe<(String, Metaterm)> =
        find_WPD_node_hyp(associatedTree, top.translatedState.hypList);
  local treeTy::Type =
        if isInherited
        then case decorate findParent.fromJust.snd with
                  {findParentOf = tree;}.foundParent of
             | nothing() -> error("We picked this term based on it being included")
             | just((prod, index)) ->
                case findAssociated(prod, top.currentState.knownProductions) of
                | just(val) -> val.resultType
                | nothing() -> error("Production " ++ prod ++ " must exist")
                end
             end
        else case wpdNodeHyp of
             | just((_, termMetaterm(applicationTerm(nameTerm(rel, _), _), _))) ->
               wpdNode_type(rel)
             | just((_, tm)) -> error("Should not get here (caseAttrAccess bad just)")
             | nothing() -> error("Should not get here (caseAttrAccess nothing)")
             end;
  local pcTheorem::Clearable =
        clearable(false, primaryComponent(attr, treeTy, associatedProd), []);
  top.translation =
      [applyTactic(nameHint(eqHypName), nothing(), makeEqHypThm,
                   [hypApplyArg(wpdNodeHyp.fromJust.1, [])], []),
       applyTactic(nameHint(componentHypName), nothing(), pcTheorem,
                   [hypApplyArg(eqHypName, [])], []),
       caseTactic(h, componentHypName, true),
       clearCommand([eqHypName, componentHypName], false)];

  top.shouldClean = true;
}


abstract production assertTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> m::Metaterm
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  top.pp = h.pp ++ "assert " ++ depthString ++ m.pp ++ ".  ";

  m.attrOccurrences = top.currentState.knownAttrOccurrences;

  m.boundVars = [];
  top.translation = --error("Translation not done in assertTactic yet");
      [assertTactic(h, depth, m.translation)];

  --no real change to proof state, just goal
  top.shouldClean = false;
}


abstract production existsTactic
top::ProofCommand ::= ew::[EWitness]
{
  local buildWitnesses::(String ::= [EWitness]) =
   \ ew::[EWitness] ->
     case ew of
     | [] ->
       error("Cannot have an empty list in existsTactic")
     | [e] -> e.pp
     | e::rest -> e.pp ++ ", " ++ buildWitnesses(rest)
     end;
  top.pp = "exists " ++ buildWitnesses(ew) ++ ".  ";

  top.translation = --error("Translation not done in existsTactic yet");
      [existsTactic(map(\ e::EWitness -> e.translation, ew))];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production witnessTactic
top::ProofCommand ::= ew::[EWitness]
{
  local buildWitnesses::(String ::= [EWitness]) =
   \ ew::[EWitness] ->
     case ew of
     | [] ->
       error("Cannot have an empty list in existsTactic")
     | [e] -> e.pp
     | e::rest -> e.pp ++ ", " ++ buildWitnesses(rest)
     end;
  top.pp = "witness " ++ buildWitnesses(ew) ++ ".  ";

  top.translation = --error("Translation not done in witnessTactic yet");
      [witnessTactic(map(\ e::EWitness -> e.translation, ew))];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production searchTactic
top::ProofCommand ::=
{
  top.pp = "search.  ";

  top.translation = [searchTactic()];

  top.shouldClean = true;
}


abstract production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.pp = "search " ++ toString(n) ++ ".  ";

  top.translation = [searchDepthTactic(n)];

  top.shouldClean = true;
}


abstract production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.pp = "search with " ++ sw.pp ++ ".  ";

  top.translation = error("Translation not done in searchWitnessTactic yet");

  top.shouldClean = true;
}


abstract production asyncTactic
top::ProofCommand ::=
{
  top.pp = "async.  ";
  top.translation = [asyncTactic()];

  top.shouldClean = true;
}


abstract production splitTactic
top::ProofCommand ::=
{
  top.pp = "split.  ";

  top.translation = [splitTactic()];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production splitStarTactic
top::ProofCommand ::=
{
  top.pp = "split*.  ";

  top.translation = [splitStarTactic()];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production leftTactic
top::ProofCommand ::=
{
  top.pp = "left.  ";

  top.translation = [leftTactic()];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production rightTactic
top::ProofCommand ::=
{
  top.pp = "right.  ";

  top.translation = [rightTactic()];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production skipTactic
top::ProofCommand ::=
{
  top.pp = "skip.  ";

  top.translation = [skipTactic()];

  top.shouldClean = true;
}


abstract production abortCommand
top::ProofCommand ::=
{
  top.pp = "abort.  ";

  top.translation = [abortCommand()];

  --no proof state afterward
  top.shouldClean = false;
}


abstract production undoCommand
top::ProofCommand ::=
{
  top.pp = "undo.  ";

  {-
    The number of undos we really need to generate depends on our last
    command the user entered.  If that turned into multiple commands,
    we should undo them all.
  -}
  top.translation =
      repeat(undoCommand(), head(top.stateListIn).fst);

  top.errors <-
      if head(top.stateListIn).fst == -1
      then [errorMsg("Can't undo command")]
      else [];

  top.isUndo = true;
  top.stateListOut =
      if length(top.stateListIn) == 0
      then --We shouldn't ever have nothing in the undo list
        error("Empty stateListIn (undoCommand)")
      else tail(top.stateListIn);

  --"new" state should already be clean
  top.shouldClean = false;
}


--I have no idea what the arrow does, but there are clears with and without it
abstract production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  local buildHyps::(String ::= [String]) =
   \ hl::[String] ->
     case hl of
     | [] ->
       error("Cannot have an empty list in clearCommand")
     | [h] -> h
     | h::rest -> h ++ " " ++ buildHyps(rest)
     end;
  top.pp = "clear " ++ (if hasArrow then "-> " else "") ++ buildHyps(removes) ++ ".  ";

  --TODO Should be checking this is an actual hypothesis the user can see
  top.translation = [clearCommand(removes, hasArrow)];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";

  {-
    Depending on what they want you to rename, you might have to
    rename a couple of things which map together (renaming a tree
    needs to rename its structure and nodes)
  -}
  top.translation = --error("Translation not done in renameTactic yet");
      [renameTactic(original, renamed)];

  --no real change to proof state
  top.shouldClean = false;
}


--this assumes newText does NOT include the quotation marks
abstract production abbrevCommand
top::ProofCommand ::= hyps::[String] newText::String
{
  local buildHyps::(String ::= [String]) =
   \ hl::[String] ->
     case hl of
     | [] ->
       error("Cannot have an empty list in abbrevCommand")
     | [h] -> h
     | h::rest -> h ++ " " ++ buildHyps(rest)
     end;
  top.pp = "abbrev " ++ buildHyps(hyps) ++ " \"" ++ newText ++ "\".  ";

  top.translation = [abbrevCommand(hyps, newText)];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production unabbrevCommand
top::ProofCommand ::= hyps::[String]
{
  local buildHyps::(String ::= [String]) =
   \ hl::[String] ->
     case hl of
     | [] ->
       error("Cannot have an empty list in abbrevCommand")
     | [h] -> h
     | h::rest -> h ++ " " ++ buildHyps(rest)
     end;
  top.pp = "unabbrev " ++ buildHyps(hyps) ++ "\".  ";

  top.translation = [unabbrevCommand(hyps)];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  local hypString::String = case hyp of | just(h) -> " " ++ h | nothing() -> "" end;
  top.pp = "permute " ++ foldr1(\a::String b::String -> a ++ " " ++ b, names) ++ hypString ++ ".  ";

  top.translation = [permuteTactic(names, hyp)];

  top.shouldClean = true;
}


abstract production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.pp = "unfold " ++ toString(steps) ++ if all then "(all).  " else ".  ";

  top.translation = error("Translation not done in unfoldStepsTactic yet");

  --no real change to proof state
  top.shouldClean = false;
}


abstract production unfoldIdentifierTactic
top::ProofCommand ::= id::String all::Boolean
{
  top.pp = "unfold " ++ id ++ if all then "(all).  " else ".  ";

  top.translation = error("Translation not done in unfoldIdentifierTactic yet");

  --no real change to proof state
  top.shouldClean = false;
}


abstract production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.pp = "unfold " ++ if all then "(all).  " else ".  ";

  top.translation = error("Translation not done in unfoldTactic yet");

  --no real change to proof state
  top.shouldClean = false;
}





nonterminal Clearable with pp;

--I don't know what the star is, but some have it
abstract production clearable
top::Clearable ::= star::Boolean hyp::String instantiation::[Type]
{
  local instString::String =
     if null(instantiation)
     then ""
     else "[" ++ foldr1(\a::String b::String -> a ++ ", " ++ b,
                        map((.pp), instantiation)) ++ "]";
  top.pp = (if star then "*" else "") ++ hyp ++ instString;
}





nonterminal ApplyArg with
   pp,
   name;

abstract production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::[Type]
{
  local instString::String =
     if null(instantiation)
     then ""
     else "[" ++ foldr1(\a::String b::String -> a ++ ", " ++ b,
                        map((.pp), instantiation)) ++ "]";
  top.pp = hyp ++ instString;

  top.name = hyp;
}

abstract production starApplyArg
top::ApplyArg ::= name::String instantiation::[Type]
{
  local instString::String =
     if null(instantiation)
     then ""
     else "[" ++ foldr1(\a::String b::String -> a ++ ", " ++ b,
                        map((.pp), instantiation)) ++ "]";
  top.pp = "*" ++ name ++ instString;

  top.name = name;
}





nonterminal EWitness with
   pp,
   translation<EWitness>;

abstract production termEWitness
top::EWitness ::= t::Term
{
  top.pp = t.pp;

  top.translation = termEWitness(t.translation);
}


abstract production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.pp = name ++ " = " ++ t.pp;

  top.translation = nameEWitness(name, t.translation);
}





nonterminal HHint with pp;

abstract production nameHint
top::HHint ::= name::String
{
  top.pp = name ++ ": ";
}


abstract production noHint
top::HHint ::=
{
  top.pp = "";
}

