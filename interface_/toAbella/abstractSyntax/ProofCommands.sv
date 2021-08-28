grammar interface_:toAbella:abstractSyntax;


--things you can do inside of proofs

nonterminal ProofCommand with
   pp, --pp should end with two spaces
   translation<[ProofCommand]>, currentState, translatedState,
   silverContext,
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

  top.errors <-
      --must have a goal if we are in a proof, so we shouldn't get an error here
      case top.currentState.state.goal of
      | nothing() -> [errorMsg("Cannot use proof commands outside of a proof")]
      | just(_) -> []
      end;
  top.errors <-
      foldr(\ s::String rest::[Error] ->
              if indexOf("$", s) >= 0
              then [errorMsg("Identifiers cannot contain \"$\"")] ++ rest
              else rest,
            [], names);

  local goalPremises::[Metaterm] =
        decorate
           decorate top.currentState.state with
           {silverContext = top.silverContext;}.goal.fromJust with
        {silverContext = top.silverContext;}.implicationPremises;
  local hidePremises::[Boolean] =
        map(\ mt::Metaterm ->
              decorate mt with
              {silverContext = top.silverContext;}.shouldHide,
            goalPremises);
  local setUpPremises::([String] ::= [String] [Boolean]) =
        \ names::[String] hides::[Boolean] ->
          case names, hides of
          | [], _ -> []
          | names, true::rest -> "_"::setUpPremises(names, rest)
          | nm::tl, false::rest -> nm::setUpPremises(tl, rest)
          | names, [] -> names
          end;
  top.translation = [introsTactic(setUpPremises(names, hidePremises))];

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
      case theorem.errors, err_trans of
      | [], left(err) -> [errorMsg(err)]
      | _, _ -> []
      end;
  top.errors <-
      foldr(\ a::ApplyArg rest::[Error]->
              if a.name == "_"
              then []
              else case decorate findAssociated(a.name,
                                    top.translatedState.hypList).fromJust with
                        {silverContext = top.silverContext;} of
                   --Hidden hypotheses cannot be what the user meant
                   | mt when !mt.shouldHide -> rest
                   | _ ->
                     errorMsg("Unknown hypothesis " ++ a.name)::rest
                   end,
            [], args);
  top.errors <-
      foldr(\ a::ApplyArg rest::[Error] ->
              if indexOf("$", a.name) >= 0
              then [errorMsg("Identifiers cannot contain \"$\"")] ++ rest
              else rest,
            [], args);
  top.errors <-
      if indexOf("$", theorem.name) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];

  top.translation =
      case err_trans of
      | left(err) ->
        error("Should not access translation with errors (applyTactic)")
      | right(prf) -> prf
      end;

  local foundTheorem::Maybe<(String, Metaterm)> =
        case findAssociated(theorem.name, top.currentState.state.hypList) of
        | just(mt) -> just((theorem.name, mt))
        | nothing() ->
          case findTheorem(theorem.name, top.currentState) of
          | [(name, mt)] -> just((name, mt))
          | _ -> nothing()
          end
        end;
  --Add an extra arg for each WPD assumption
  --Only hidden premises should be WPD NT, but include WPD node to be safe
  local buildExpandedArgs::([ApplyArg] ::= [Metaterm] [ApplyArg]) =
        \ l::[Metaterm] args::[ApplyArg] ->
          case l, args of
          | [], _ -> args
          | hd::tl, args ->
            case decorate hd with
                 {silverContext = top.silverContext;}, args of
            | termMetaterm(applicationTerm(nameTerm(rel, _), _), _), _
              when isWpdTypeName(rel) || isWPD_NodeRelName(rel) ->
              hypApplyArg("_", [])::buildExpandedArgs(tl, args)
            | _, a::argRest ->
              a::buildExpandedArgs(tl, argRest)
            | _, [] -> args
            end
          --Going to be an error because there aren't enough arguments
          | _, [] -> args
          end;
  local expandedArgs::[ApplyArg] =
        case foundTheorem of
        | nothing() ->
          error("Should not access expandedArgs without known theorem/hyp")
        | just((_, mt)) ->
          buildExpandedArgs(
             decorate mt with
             {silverContext = top.silverContext;}.implicationPremises,
             args)
        end;
  local err_trans::Either<String [ProofCommand]> =
      case foundTheorem of
      | just(("silver:core:is_list_member", _)) ->
        case theorem__is_list_member(h, depth, args, withs,
                top.translatedState.hypList, top.silverContext) of
        | right(prf) -> right(prf)
        | left(err) -> left(err)
        end
      | just(("silver:core:is_list_append", _)) ->
        case theorem__is_list_append(h, depth, args, withs,
                top.translatedState.hypList, top.silverContext) of
        | right(prf) -> right(prf)
        | left(err) -> left(err)
        end
      | just(("silver:core:symmetry", _)) ->
        case theorem__symmetry(h, depth, args,
                map(\ p::(String, Term) ->
                      (p.1, decorate p.2 with
                            {knownTrees =
                             top.currentState.state.gatheredTrees;
                             silverContext = top.silverContext;}.translation),
                    withs),
                top.currentState.state.hypList,
                top.silverContext) of
        | right(prf) -> right(prf)
        | left(err) -> left(err)
        end
      | just(("silver:core:attr_unique", _)) ->
        case theorem__attr_unique(args, withs,
                top.currentState.state.hypList, top.silverContext) of
        | right(thm) ->
          right([applyTactic(h, depth, clearable(false, thm, []), args, [])])
        | left(err) -> left(err)
        end
      | just(("silver:core:attr_is", _)) ->
        case theorem__attr_is(h, depth, args, withs,
                top.currentState.state.hypList, top.silverContext) of
        | right(thm) -> right([thm])
        | left(err) -> left(err)
        end
      | just((_, _)) ->
        right([applyTactic(h, depth, theorem.translation, expandedArgs,
                 map(\ p::Pair<String Term> ->
                       pair(p.fst, decorate p.snd with
                         {knownTrees = top.currentState.state.gatheredTrees;
                          silverContext = top.silverContext;
                         }.translation), withs))])
      | nothing() -> left("Unknown lemma or hypothesis in application")
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

  top.translation =
      [backchainTactic(depth, theorem.translation,
          map(\ p::Pair<String Term> ->
                pair(p.fst,
                     decorate p.snd with
                       {knownTrees = top.currentState.state.gatheredTrees;
                        silverContext = top.silverContext;
                       }.translation),
              withs))];

  top.shouldClean = true;
}


abstract production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.pp = h.pp ++ "case " ++ hyp ++ if keep then " (keep).  " else ".  ";

  top.translation = [caseTactic(h, hyp, keep)];

  top.errors <-
      case findAssociated(hyp, top.translatedState.hypList) of
      --Unknown hypotheses---could also let it go through and Abella catch it
      | nothing() -> [errorMsg("Unknown hypothesis " ++ hyp)]
      | just(mt) ->
        case decorate mt with
             {silverContext = top.silverContext;} of
        --Hidden hypotheses should be left alone
        | mt when mt.shouldHide ->
          [errorMsg("Unknown hypothesis " ++ hyp)]
        --Disallow case analysis on structure-showing "$<tree>_Tm = <structure>"
        | eqMetaterm(nameTerm(str, _), structure)
          when contains(str, decorate top.currentState.state with
                             {silverContext = top.silverContext;}.gatheredTrees) ->
          [errorMsg("Cannot do case analysis on tree structure hypothesis")]
        | eqMetaterm(structure, nameTerm(str, _))
          when contains(str, decorate top.currentState.state with
                             {silverContext = top.silverContext;}.gatheredTrees) ->
          [errorMsg("Cannot do case analysis on tree structure hypothesis")]
        --Case analysis on an access doesn't make sense
        | attrAccessMetaterm(tree, attr, _) ->
          [errorMsg("Cannot do case analysis on this hypothesis; to do case " ++
                    "analysis on equation for " ++ tree ++ "." ++ attr ++
                    ", use \"case " ++ tree ++ "." ++ attr ++ "\"")]
        | attrAccessEmptyMetaterm(tree, attr) ->
          [errorMsg("Cannot do case analysis on this hypothesis; to do case " ++
                    "analysis on equation for " ++ tree ++ "." ++ attr ++
                    ", use \"case " ++ tree ++ "." ++ attr ++ "\"")]
        --Anything else is fine
        | _ -> []
        end
      end;

  top.shouldClean = true;
}


abstract production caseLocalAttr
top::ProofCommand ::= h::HHint tree::String attr::String
{
  top.pp = h.pp ++ "case_local " ++ tree ++ "." ++ attr ++ ".  ";

  top.errors <-
      if treeExists
      then []
      else [errorMsg("Unknown tree " ++ tree)];
  top.errors <-
      if attrExists
      then []
      else [errorMsg("Unknown local attribute " ++ attr)];
  top.errors <-
      if treeExists && attrExists
      then if structureKnown
           then []
           else [errorMsg("Cannot do case analysis on local attribute " ++
                          attr ++ " for tree " ++ tree ++ " of unknown structure")]
      else [];
  top.errors <-
      if treeExists && attrExists && structureKnown
      then if attrOccursOn
           then []
           else [errorMsg("No local attribute named " ++ attr ++
                          " occurs on trees built by production " ++
                          associatedProd)]
      else [];

  local treeExists::Boolean =
        contains(tree,
           decorate top.currentState.state with
           {silverContext = top.silverContext;}.gatheredTrees);
  local attrExists::Boolean = contains(attr, map(fst, top.silverContext.knownLocalAttrs));
  local structureKnown::Boolean =
        if structure.isJust
        then case decorate structure.fromJust.2 with
                  {silverContext = top.silverContext;} of
             | applicationTerm(nameTerm(prod, _), _)
               when isProd(prod) -> true
             | nameTerm(prod, _) when isProd(prod) -> true
             | _ -> false
             end
        else false;
  local attrOccursOn::Boolean =
        localAttrOccurrenceType(attr, associatedProd,
                                top.silverContext).isJust;
  --
  local newNum::String = toString(genInt());
  local eqHypName::String = "$Eq_" ++ newNum;
  local equalityName::String = "$Equality_" ++ newNum;
  --
  local structure::Maybe<(String, Term)> =
        case find_structure_hyp(tree, top.translatedState.hypList,
                                top.silverContext) of
        | nothing() -> nothing()
        | just((hyp, _)) ->
          --This must exist and have the form of "$structure_eq T Structure" or symm
          case findAssociated(hyp, top.currentState.state.hypList) of
          | just(mtm) ->
            case decorate mtm with
                {silverContext = top.silverContext;} of
            | termMetaterm(
                 applicationTerm(_,
                    consTermList(
                       nameTerm(tr, _),
                       singleTermList(structure))), _)
              when tr == tree ->
              just((hyp, new(structure)))
            | termMetaterm(
                 applicationTerm(_,
                    consTermList(
                       structure,
                       singleTermList(nameTerm(tr, _)))), _)
              when tr == tree ->
              just((hyp, new(structure)))
            end
          | _ -> nothing()
          end
        end;
  local associatedProd::String =
        case decorate structure.fromJust.2 with
             {silverContext = top.silverContext;} of
        | applicationTerm(nameTerm(prod, _), _) -> prodToName(prod)
        | nameTerm(prod, _) -> prodToName(prod)
        | tm -> error("It should be a production (associatedProd):  " ++ tm.pp)
        end;
  local wpdNtHyp::Maybe<(String, Metaterm)> =
        find_WPD_nt_hyp(tree, top.translatedState.hypList, top.silverContext);
  local treeTy::Type =
        case decorate wpdNtHyp.fromJust.2 with
             {silverContext = top.silverContext;} of
        | termMetaterm(applicationTerm(nameTerm(rel, _), _), _) ->
          wpdNt_type(rel)
        | _ -> error("Should not get here (caseLocalAttrAccess)")
        end;
  local makeEqHypThm::Clearable =
        clearable(false, wpdNt_to_LocalAttrEq(associatedProd, attr, treeTy), []);
  --
  top.translation =
      [
       --Get structure assumption of correct form (treename = prod_<name> <children>)
       assertTactic(nameHint(equalityName), nothing(),
                    termMetaterm(
                       buildApplication(
                          nameTerm(typeToStructureEqName(treeTy), nothing()),
                          [nameTerm(tree, nothing()),
                           structure.fromJust.2]),
                       emptyRestriction()))
      ] ++
       --Need to solve previous goal by case analysis if structure hyp is backward
      ( case findAssociated(structure.fromJust.fst, top.translatedState.hypList) of
        | nothing() -> error("This hypothesis must exist")
        | just(mtm) ->
          case decorate mtm with
               {silverContext = top.silverContext;} of
          | treeEqMetaterm(nameTerm(str, _), _) -> []
          | treeEqMetaterm(_, nameTerm(str, _)) ->
            [ backchainTactic(nothing(),
                 clearable(false, typeToStructureEq_Symm(treeTy), []), []) ]
          | _ ->
            error("This hypothesis must be \"<tree> = structure\" or \"structure = <tree>\"")
          end
        end
      ) ++
      [
       --Go from WPD nonterminal to equation relation
       applyTactic(nameHint(eqHypName), nothing(), makeEqHypThm,
                   [hypApplyArg(equalityName, []),
                    hypApplyArg(wpdNtHyp.fromJust.1, [])], []),
       --Actual case analysis on equation relation
       caseTactic(h, eqHypName, true),
       --Remove our extra assumptions (unnecessary, but nice)
       clearCommand([eqHypName, equalityName], false)
      ];

  top.shouldClean = true;
}


abstract production caseAttrAccess
top::ProofCommand ::= h::HHint tree::String attr::String
{
  top.pp = h.pp ++ "case " ++ tree ++ "." ++ attr ++ ".  ";

  --We could do this error checking nested, but that gets hard to follow
  top.errors <-
      if treeExists
      then []
      else [errorMsg("Unknown tree " ++ tree)];
  top.errors <-
      case possibleAttrs of
      | [] -> [errorMsg("Unknown attribute " ++ attr)]
      | lst ->
        if length(filteredAttrs) == 1
        then []
        else if length(filteredAttrs) == 0
        then [errorMsg("Attribute " ++ attr ++
                        " does not occur on " ++ tree)]
        else 
             [errorMsg("Undetermined attribute " ++ attr ++
                 "; options are " ++
                 implode(", ",
                    map(\ p::(String, [(Type, Type)]) -> p.1,
                        filteredAttrs)))]
      end;
  top.errors <-
      if treeExists && attrExists
      then case findAttrOccurrences(attr, top.silverContext) of
           | [] -> [] --covered by checking if attr exists, so impossible here
           | [(_, ntstys)] ->
             if  wpdNtHyp.isJust
             then if containsBy(tysEqual, errCheckTy, map(fst, ntstys))
                  then []
                  else [errorMsg("Attribute " ++ attr ++ " does not occur on " ++ tree)]
             else []
           | lst ->
             case filter(\ p::(String, [(Type, Type)]) ->
                           containsBy(tysEqual, errCheckTy, map(fst, p.2)),
                         lst) of
             | [] -> [errorMsg("No attribute named " ++ attr ++ " occurs on " ++ tree)]
             | [_] -> []
             | lst ->
               [errorMsg("Undetermined attribute " ++ attr ++ "; " ++
                         "options are " ++ implode(", ", map(fst, lst)))]
             end
           end
      else [];
  top.errors <-
      if treeExists && attrExists
      then if isInherited
           then case findParent of
                | nothing() ->
                  [errorMsg("Cannot do case analysis on inherited attribute "++
                            "equation when parent of tree is unknown")]
                | just(_) -> []
                end
           else []
      else [];
  top.errors <-
      if treeExists && attrExists
      then if (isInherited && findParent.isJust) || !isInherited
           then case wpdNtHyp of
                | nothing() ->
                  [errorMsg("Cannot do case analysis on " ++ tree ++ "." ++ attr ++ " for reasons I can't come up with at the moment; please report this error")]
                | just(_) -> []
                end
           else []
      else [];
  top.errors <-
      if treeExists && attrExists
      then case structure of
           | just((hyp, tm)) ->
             case decorate tm with
                  {silverContext = top.silverContext;} of
             | applicationTerm(nameTerm(prod, _), _)
               when isProd(prod) -> []
             | nameTerm(prod, _) when isProd(prod) -> []
             | tm ->
               [errorMsg("Cannot do case analysis on attribute access" ++
                         " for tree of unknown structure (" ++ hyp ++ ", just(" ++ tm.pp ++ "))")]
             end
           | nothing() ->
             [errorMsg("Cannot do case analysis on attribute access" ++
                       " for tree of unknown structure (nothing)")]
           end
      else [];

  local treeExists::Boolean =
        contains(tree,
           decorate top.currentState.state with
           {silverContext = top.silverContext;}.gatheredTrees);
  local attrExists::Boolean =
        length(findAttrOccurrences(attr, top.silverContext)) == 1;
  --
  local newNum::String = toString(genInt());
  local eqHypName::String = "$Eq_" ++ newNum;
  local componentHypName::String = "$EqComp_" ++ newNum;
  local equalityName::String = "$Equality_" ++ newNum;
  --
  local possibleAttrs::[(String, [(Type, Type)])] =
        findAttrOccurrences(attr, top.silverContext);
  local filteredAttrs::[(String, [(Type, Type)])] =
        filter(\ p::(String, [(Type, Type)]) ->
                 containsBy(tysEqual, errCheckTy, map(fst, p.2)),
               possibleAttrs);
  local rightAttr::String = head(filteredAttrs).1;
  local isInherited::Boolean =
        isInheritedAttr(rightAttr, top.silverContext);
  local findParent::Maybe<(String, Term)> =
        find_parent_tree(tree, top.translatedState.hypList, top.silverContext);
  local associatedTree::String =
        if isInherited
        then case findParent of
             | just((tr, _)) -> tr
             | nothing() -> error("findParent should not be nothing")
             end
        else tree;
  local structure::Maybe<(String, Term)> =
        case find_structure_hyp(associatedTree,
                                top.translatedState.hypList,
                                top.silverContext) of
        | nothing() -> nothing()
        | just((hyp, _)) ->
          --This must exist and have the form of "$structure_eq T Structure" or symm
          case findAssociated(hyp, top.currentState.state.hypList) of
          | just(mtm) ->
            case decorate mtm with
                 {silverContext = top.silverContext;} of
            | termMetaterm(
                 applicationTerm(_,
                    consTermList(
                       nameTerm(tr, _),
                       singleTermList(structure))), _)
              when tr == associatedTree ->
              just((hyp, new(structure)))
            | termMetaterm(
                 applicationTerm(_,
                    consTermList(
                       structure,
                       singleTermList(nameTerm(tr, _)))), _)
              when tr == associatedTree ->
              just((hyp, new(structure)))
            end
          | _ -> nothing()
          end
        end;
  local associatedProd::String =
        case decorate structure.fromJust.2 with
             {silverContext = top.silverContext;} of
        | applicationTerm(nameTerm(prod, _), _) -> prod
        | nameTerm(prod, _) -> prod
        | tm -> error("It should be a production (associatedProd):  " ++ tm.pp)
        end;
  local makeEqHypThm::Clearable =
        clearable(false, wpdNt_to_AttrEq(rightAttr, treeTy), []);
  local wpdNtHyp::Maybe<(String, Metaterm)> =
        find_WPD_nt_hyp(associatedTree, top.translatedState.hypList, top.silverContext);
  local treeTy::Type =
        let synCase::Type =
            case decorate find_WPD_nt_hyp(tree, top.translatedState.hypList,
                                          top.silverContext).fromJust.2 with
                 {silverContext = top.silverContext;} of
            | termMetaterm(applicationTerm(nameTerm(rel, _), _), _) ->
              wpdNt_type(rel)
            | _ -> error("Should not get here (caseAttrAccess)")
            end
        in
          case findParent of
          | just(fp) ->
            case decorate fp.snd with
                 {findParentOf = tree;
                  silverContext = top.silverContext;}.foundParent of
            | just((prod, index)) ->
              case findProd(prodToName(prod), top.silverContext) of
              | [(_, val)] -> val.resultType
              | _ -> error("Production " ++ prod ++ " must exist")
              end
            | _ -> synCase
            end
          | _ -> synCase
          end
        end;
  --We need this to check that the attribute occurs on the tree we said, not the associated tree
  local errCheckTy::Type =
        case findParent of
        | just(fp) ->
          case decorate fp.2 with
               {silverContext = top.silverContext;} of
          | applicationTerm(nameTerm(prod, _), args) ->
            case decorate args with
                 {findParentOf = tree;
                  silverContext = top.silverContext;}.isArgHere of
            | nothing() -> treeTy
            | just(ind) ->
              case findProd(prodToName(prod), top.silverContext) of
              | [(_, prodTy)] -> elemAtIndex(prodTy.argumentTypes, ind)
              | _ -> error("Production must exist 1 (" ++ prod ++ ")")
              end
            end
          | prodTerm(prod, args) ->
            case decorate args with
                 {findParentOf = tree;
                  silverContext = top.silverContext;}.isArgHere of
            | nothing() -> treeTy
            | just(ind) ->
              case findProd(prod, top.silverContext) of
              | [(_, prodTy)] -> elemAtIndex(prodTy.argumentTypes, ind)
              | _ -> error("Production must exist 2 (" ++ prod ++ ")")
              end
            end
          | _ -> error("Should not access errCheckTy with other errors")
          end
        | _ -> treeTy
        end;
  local pcTheorem::Clearable =
        clearable(false, primaryComponent(rightAttr, treeTy, associatedProd), []);
  top.translation =
      [
       --Get structure assumption of correct form (treename = prod_<name> <children>)
       assertTactic(nameHint(equalityName), nothing(),
                    termMetaterm(
                       buildApplication(
                          nameTerm(typeToStructureEqName(treeTy), nothing()),
                          [nameTerm(associatedTree, nothing()),
                           structure.fromJust.2]),
                       emptyRestriction()))
      ] ++
       --Need to solve previous goal by case analysis if structure hyp is backward
      ( case findAssociated(structure.fromJust.fst, top.translatedState.hypList) of
        | nothing() -> error("This hypothesis must exist")
        | just(mtm) ->
          case decorate mtm with {silverContext = top.silverContext;} of
          | treeEqMetaterm(nameTerm(str, _), _) -> []
          | treeEqMetaterm(_, nameTerm(str, _)) ->
            [ backchainTactic(nothing(),
                 clearable(false, typeToStructureEq_Symm(treeTy), []), []) ]
          | _ ->
            error("This hypothesis must be \"<tree> = structure\" or \"structure = <tree>\"")
          end
        end
      ) ++
      [
       --Go from WPD nonterminal to full equation relation
       applyTactic(nameHint(eqHypName), nothing(), makeEqHypThm,
                   [hypApplyArg(wpdNtHyp.fromJust.1, [])], []),
       --Go from full equation relation to component equation relation
       applyTactic(nameHint(componentHypName), nothing(), pcTheorem,
                   [hypApplyArg(equalityName, []), hypApplyArg(eqHypName, [])], []),
       --Actual case analysis on component equation relation
       caseTactic(h, componentHypName, true),
       --Remove our extra assumptions (unnecessary, but nice)
       clearCommand([eqHypName, equalityName, componentHypName], false)
      ];

  top.shouldClean = true;
}


abstract production caseStructure
top::ProofCommand ::=
     h::HHint tree::String hyp::String otherTreeHyp::String keep::Boolean
{
  {-
    There is a question of whether this ought to be a tactic or a fake
    theorem.  Given that its result is to generate an indetermine
    number of conclusions (one for the root and one for each
    tree-typed child, I don't think a fake theorem is a good choice.
  -}
  top.pp = h.pp ++ "case_structure " ++ tree ++ " in " ++ hyp ++ ".  ";

  top.errors <-
      if indexOf("$", tree) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];
  top.errors <-
      if contains(tree, decorate top.currentState.state with
                        {silverContext = top.silverContext;}.gatheredTrees)
      then []
      else [errorMsg("Unknown tree " ++ tree)];
  top.errors <-
      if startsWith("$", hyp)
      then [errorMsg("Unknown hypothesis " ++ hyp)]
      else case hypBody of
           | nothing() -> [errorMsg("Unknown hypothesis " ++ hyp)]
           | just(mt) ->
             case decorate mt with
                  {silverContext = top.silverContext;} of
             | mt when mt.shouldHide ->
               [errorMsg("Unknown hypothesis " ++ hyp)]
             | treeEqMetaterm(nameTerm(tr1, _), nameTerm(tr2, _))
               when tr1 == tree || tr2 == tree -> []
             | treeEqMetaterm(_, _) ->
               [errorMsg("Hypothesis " ++ hyp ++ " is not a tree equality " ++
                         "of " ++ tree ++ " and another tree")]
             | _ ->
               [errorMsg("Hypothesis " ++ hyp ++ " is not an equality")]
             end
           end;
  local hypOkay::Boolean = --Don't check more unless this is true
        !startsWith("$", hyp) && hyp != "_" &&
        if hypBody.isJust
        then case decorate hypBody.fromJust with
                  {silverContext = top.silverContext;} of
             | treeEqMetaterm(nameTerm(tr1, _), nameTerm(tr2, _)) ->
               tr1 == tree || tr2 == tree
             | _ -> false
             end
        else false;
  top.errors <-
      if startsWith("$", otherTreeHyp)
      then [errorMsg("Unknown hypothesis " ++ otherTreeHyp)]
      else case otherTreeHypBody of
           | nothing() -> [errorMsg("Unknown hypothesis " ++ otherTreeHyp)]
           | just(mt) ->
             case decorate mt with {silverContext = top.silverContext;} of
             | mt when mt.shouldHide ->
               [errorMsg("Unknown hypothesis " ++ otherTreeHyp)]
             | treeEqMetaterm(nameTerm(tr, _), trm)
               when hypOkay && otherTree == tr && trm.isProdStructure ->
               []
             | treeEqMetaterm(trm, nameTerm(tr, _))
               when hypOkay && otherTree == tr && trm.isProdStructure ->
               []
             | treeEqMetaterm(nameTerm(tr, _), trm)
               when hypOkay && otherTree == tr ->
               [errorMsg(otherTreeHyp ++ " does not equate " ++ otherTree ++ " to a structure")]
             | treeEqMetaterm(trm, nameTerm(tr, _))
               when hypOkay && otherTree == tr ->
               [errorMsg(otherTreeHyp ++ " does not equate " ++ otherTree ++ " to a structure")]
             | treeEqMetaterm(_, _) when hypOkay ->
               [errorMsg("Hypothesis " ++ otherTreeHyp ++ " is not a tree " ++
                         "equality of " ++ tree ++ " another tree")]
             | _ ->
               [errorMsg("Hypothesis " ++ otherTreeHyp ++ " is not an equality")]
             end
           end;
  local hypsOkay::Boolean = --Don't check more unless this is true
        hypOkay && !startsWith("$", otherTreeHyp) && otherTreeHyp != "_" &&
        if otherTreeHypBody.isJust
        then case decorate otherTreeHypBody.fromJust with
                  {silverContext = top.silverContext;} of
             | treeEqMetaterm(nameTerm(tr, _), trm) when tree == tr ->
               trm.isProdStructure
             | treeEqMetaterm(trm, nameTerm(tr, _)) when tree == tr ->
               trm.isProdStructure
             | _ -> false
             end
        else false;
  top.errors <-
      if hypsOkay
      then case prodTy of
           | [] -> [errorMsg("Unknown production " ++ prod)]
           | [_] -> []
           | lst -> [errorMsg("Undetermined production " ++ prod ++
                              "; choices are " ++
                              implode(", ", map(fst, lst)))]
           end
      else [];

  --Index to make sure the names we use here are new
  local newIndex::String = toString(genInt());
  --Find the hypothesis, the other tree, and the structure for the other tree
  local hypBody::Maybe<Metaterm> =
        findAssociated(hyp, top.translatedState.hypList);
  local otherTree::String =
        case decorate hypBody.fromJust with
             {silverContext = top.silverContext;} of
        | treeEqMetaterm(nameTerm(tr1, _), nameTerm(tr2, _)) ->
          if tr1 == tree
          then tr2
          else tr1
        | _ -> error("Should not access otherTree with errors")
        end;
  local otherTreeHypBody::Maybe<Metaterm> =
        findAssociated(otherTreeHyp, top.translatedState.hypList);
  local structure::Term =
        case decorate findAssociated(otherTreeHyp,
                         top.currentState.state.hypList).fromJust with
             {silverContext = top.silverContext;} of
        | termMetaterm(
             applicationTerm(
                _,
                consTermList(
                   nameTerm(tr, _),
                   singleTermList(struct))),
             _)
          when tr == otherTree ->
          struct
        | termMetaterm(
             applicationTerm(
                _,
                consTermList(
                   struct,
                   singleTermList(nameTerm(tr, _)))),
             _)
          when tr == otherTree ->
          struct
        | other -> error("This must be treeEqMetaterm because of how it was found (just(" ++ other.pp ++ "))")
        end;
  structure.silverContext = top.silverContext;
  local wpdTreeHyp::Maybe<(String, Metaterm)> =
        find_WPD_nt_hyp(tree, top.translatedState.hypList, top.silverContext);
  local originalWpdTreeHyp::Maybe<Metaterm> =
        case wpdTreeHyp of
        | just((h, _)) ->
          findAssociated(h, top.currentState.state.hypList)
        | nothing() -> nothing()
        end;
  --Find the production, its type, its children, etc.
  local prod::String =
        case structure of
        | applicationTerm(nameTerm(str, _), _) -> str
        | nameTerm(str, _) -> str
        | _ -> error("This must be one of these because of error checking")
        end;
  local prodTy::[(String, Type)] =
        findProd(prodToName(prod), top.silverContext);
  local prodChildren::[Term] =
        case structure of
        | applicationTerm(_, args) -> args.argList
        | nameTerm(_, _) -> []
        | _ -> error("This must be one of these because of error checking")
        end;
  local buildNewChildren::([(Term, String, Term, Type)] ::= [Term] [Type] [String]) =
        \ children::[Term] types::[Type] usedNames::[String] ->
          case children, types of
          | [], [] -> []
          | c::ctl, ty::tytl ->
            if tyIsNonterminal(ty)
            then let newName::String = makeUniqueNameFromTy(ty, usedNames)
                 in
                   (nameTerm(newName, nothing()),
                    newName, c, ty)::buildNewChildren(ctl, tytl, newName::usedNames)
                  end
            else (c, "_", c, ty)::buildNewChildren(ctl, tytl, usedNames)
          | _, _ ->
            error("Must be the same length because children came from output")
          end;
      --(New child, new child name, original child, type of child)
  local newChildren::[(Term, String, Term, Type)] =
        buildNewChildren(prodChildren, head(prodTy).2.argumentTypes,
                         decorate top.translatedState with
                         {silverContext = top.silverContext;}.usedNames);
  --Generate commands to get the correct structures
  local eqName::String = "$Eq_" ++ newIndex;
  local tempName::String = "$Temp_" ++ newIndex;
  local correctDirectionName::String = "$CorrectDirection_" ++ newIndex;
  local componentName::String = "$Component_" ++ newIndex;
  local eqTheoremBody::Metaterm =
        foldl(\ rest::Metaterm p::(Term, String, Term, Type) ->
                if tyIsNonterminal(p.4)
                then andMetaterm(
                        rest,
                        termMetaterm(
                           buildApplication(
                              nameTerm(typeToStructureEqName(p.4), nothing()),
                              [p.1, p.3]),
                           emptyRestriction()))
                else rest,
              termMetaterm(
                 buildApplication(
                    nameTerm(typeToStructureEqName(head(prodTy).2.resultType),
                             nothing()),
                    [nameTerm(tree, nothing()),
                     buildApplication(nameTerm(prod, nothing()),
                        map(fst, newChildren))]),
                 emptyRestriction()), newChildren);
  local newBindings::[(String, Maybe<Type>)] =
        foldr(\ p::(Term, String, Term, Type) rest::[(String, Maybe<Type>)] ->
                if tyIsNonterminal(p.4)
                then (p.2, nothing())::rest
                else rest,
              [], newChildren);
  local eqCommands::[ProofCommand] =
        [
         assertTactic(
            if null(newBindings)
            then h
            else nameHint(eqName),
            nothing(),
            if null(newBindings)
            then eqTheoremBody
            else bindingMetaterm(existsBinder(), newBindings,
                                 eqTheoremBody)),
         --prove our assertion
         applyTactic(
            noHint(), nothing(),
            clearable(false, structureEqEqualTheorem(
                                head(prodTy).2.resultType), []),
            [hypApplyArg(otherTreeHyp, [])], [])
        ] ++
        ( case decorate hypBody.fromJust with
               {silverContext = top.silverContext;} of
          | treeEqMetaterm(nameTerm(tr1, _), nameTerm(tr2, _)) ->
            if tr1 == tree
            then [
                  assertTactic(
                     nameHint(correctDirectionName), just(length(newChildren) + 3),
                     termMetaterm(
                        buildApplication(
                           nameTerm(typeToStructureEqName(
                                       head(prodTy).2.resultType), nothing()),
                           [nameTerm(tr1, nothing()),
                            nameTerm(tr2, nothing())]),
                        emptyRestriction()))
                 ]
            else [
                  applyTactic(
                     nameHint(correctDirectionName), nothing(),
                     clearable(false, typeToStructureEq_Symm(
                                         head(prodTy).2.resultType), []),
                     [hypApplyArg(hyp, [])], [])
                 ]
          | _ -> error("Should not access eqCommands with errors")
          end
         ) ++
         [
          applyTactic(
             nameHint(componentName), nothing(),
             clearable(false, structureEqProdComponent(prod), []),
             [hypApplyArg(correctDirectionName, [])], []),
          caseTactic(noHint(), componentName, true),
          applyTactic(
             noHint(), nothing(),
             clearable(false, structureEqWPD(head(prodTy).2.resultType), []),
             [hypApplyArg(wpdTreeHyp.fromJust.1, [])], []),
          searchTactic()
        ] ++
        --clean it up by case analysis on what we just proved if NT children exist
        if null(newBindings)
        then []
        else [caseTactic(h, eqName, false)];
  --Get WPD of structure
  local wpdCompName::String = "$WPD_Comp_" ++ newIndex;
  local wpdCompCommands::[ProofCommand] =
        [
         applyTactic(
            nameHint(wpdCompName), nothing(),
            clearable(false, wpdPrimaryComponent(prod,
                                head(prodTy).2.resultType), []),
             --First argument comes from previous assertion---structure equality
            [hypApplyArg("_", []),
             hypApplyArg(wpdTreeHyp.fromJust.1, [])],
            [])
        ];
  --Get the form of the child list
  local clFormName::String = "$CL_Form_" ++ newIndex;
  local clFormBody::Metaterm =
        let built::([(String, Maybe<Type>)], Term) =
            foldr(\ p::(Term, String, Term, Type)
                    rest::([(String, Maybe<Type>)], Term) ->
                    if tyIsNonterminal(p.4)
                    then ((treeToNodeTreeName(p.2), nothing())::rest.1,
                          consTerm(nameTerm(treeToNodeTreeName(p.2),
                                            nothing()), rest.2))
                    else rest,
                  ([], nilTerm()), newChildren)
        in
          let innerBody::Metaterm =
             eqMetaterm(
                --find the child list for the tree
                case decorate originalWpdTreeHyp.fromJust with
                     {silverContext = top.silverContext;} of
                | termMetaterm(
                     applicationTerm(
                        wpdNT,
                        consTermList(tree,
                           singleTermList(
                              applicationTerm(ntrConstructor,
                                 consTermList(node,
                                 singleTermList(childList)))))),
                     _) ->
                  childList
                | _ -> error("Must have above form")
                end,
                built.2)
          in
            if null(built.1)
            then innerBody
            else bindingMetaterm(existsBinder(), built.1, innerBody)
          end
        end;
  local clCommands::[ProofCommand] =
        [
         assertTactic(nameHint(clFormName), nothing(), clFormBody),
         --Prove assertion
         caseTactic(noHint(), wpdCompName, false),
         searchTactic(),
         --Case analysis after proof to get correct forms
         caseTactic(noHint(), clFormName, false),
         caseTactic(noHint(), wpdCompName, false)
        ];
  --Turn the child node trees into appropriate forms
  local nodeStructName::String = "$NodeStruct_" ++ newIndex;
  local nodeStructCommands::[ProofCommand] =
        foldr(\ p::(Term, String, Term, Type) rest::[ProofCommand] ->
                if tyIsNonterminal(p.4)
                then assertTactic(
                        nameHint(nodeStructName), nothing(),
                        bindingMetaterm(
                           existsBinder(),
                           [(treeToNodeName(p.2), nothing()),
                            (treeToChildListName(p.2), nothing())],
                           eqMetaterm(
                              nameTerm(treeToNodeTreeName(p.2),
                                       nothing()),
                              buildApplication(
                                 nameTerm(nodeTreeConstructorName(p.4),
                                          nothing()),
                                 [nameTerm(treeToNodeName(p.2),
                                           nothing()),
                                  nameTerm(treeToChildListName(p.2),
                                           nothing())]))))::
                     backchainTactic(
                        nothing(),
                        clearable(false, wpdNodeTreeForm(p.4), []),
                        [])::
                     caseTactic(noHint(), nodeStructName, false)::
                     rest
                else rest,
              [], newChildren);
  --
  top.translation =
      eqCommands ++ wpdCompCommands ++ clCommands ++ nodeStructCommands;

  top.shouldClean = true;
}


abstract production treesEqual
top::ProofCommand ::= h::HHint hyp1::String hyp2::String
{
  top.pp = h.pp ++ "trees_equal " ++ hyp1 ++ " " ++ hyp2 ++ ".  ";

  top.errors <-
      case hyp1Find of
      | just(_) -> []
      | nothing() -> [errorMsg("Unknown hypothesis " ++ hyp1)]
      end;
  top.errors <-
      case hyp2Find of
      | just(_) -> []
      | nothing() -> [errorMsg("Unknown hypothesis " ++ hyp2)]
      end;
  top.errors <-
      case hyp1Find of
      | nothing() -> []
      | just(_) ->
        if hyp1Good
        then []
        else [errorMsg("Hypothesis " ++ hyp1 ++ " must be an " ++
                       "equality of a tree and a structure")]
      end;
  top.errors <-
      case hyp2Find of
      | nothing() -> []
      | just(_) ->
        if hyp2Good
        then []
        else [errorMsg("Hypothesis " ++ hyp2 ++ " must be an " ++
                       "equality of a tree and a structure")]
      end;
  top.errors <-
      if !(hyp1Good && hyp2Good)
      then []
      else if !tysEqual(treeTy, treeTy2)
      then [errorMsg("Trees have different types:  " ++
                     treeTy.pp ++ " and " ++ treeTy2.pp)]
      else if prod != prod2
      then [errorMsg("Trees are built by different productions " ++
                     "and cannot be equal:  " ++ prodToName(prod) ++
                     " and " ++ prodToName(prod2))]
      else [];
  --
  local hyp1Good::Boolean =
        if hyp1Find.isJust
        then case decorate hyp1Find.fromJust with
                  {silverContext = top.silverContext;} of
             | termMetaterm(
                  applicationTerm(_,
                     consTermList(nameTerm(treeName, _),
                     singleTermList(treeStructure))), _)
               when treeStructure.isProdStructure -> true
             | termMetaterm(
                  applicationTerm(_,
                     consTermList(treeStructure,
                     singleTermList(nameTerm(treeName, _)))), _)
               when treeStructure.isProdStructure -> true
             | _ -> false
             end
        else false;
  local hyp2Good::Boolean =
        if hyp2Find.isJust
        then case decorate hyp2Find.fromJust with
                  {silverContext = top.silverContext;} of
             | termMetaterm(
                  applicationTerm(_,
                     consTermList(nameTerm(treeName, _),
                     singleTermList(treeStructure))), _)
               when treeStructure.isProdStructure -> true
             | termMetaterm(
                  applicationTerm(_,
                     consTermList(treeStructure,
                     singleTermList(nameTerm(treeName, _)))), _)
               when treeStructure.isProdStructure -> true
             | _ -> false
             end
        else false;
  
  --
  local hyp1Find::Maybe<Metaterm> =
        findAssociated(hyp1, top.currentState.state.hypList);
  local hyp2Find::Maybe<Metaterm> =
        findAssociated(hyp2, top.currentState.state.hypList);
  --gather all at once since I'm doing tho same matching for all three
  --this is easier if I have to change the structure of the patterns
  local stuff1::(String, Term) =
        case decorate hyp1Find.fromJust with
             {silverContext = top.silverContext;} of
        | termMetaterm(
             applicationTerm(_,
                consTermList(nameTerm(treeName, _),
                singleTermList(treeStructure))), _)
          when treeStructure.isProdStructure ->
          (treeName, new(treeStructure))
        | termMetaterm(
             applicationTerm(_,
                consTermList(treeStructure,
                singleTermList(nameTerm(treeName, _)))), _)
          when treeStructure.isProdStructure ->
          (treeName, new(treeStructure))
        | _ -> error("Should not access this")
        end;
  local treeName1::String = stuff1.1;
  local treeStructure1::Term = stuff1.2;
  treeStructure1.silverContext = top.silverContext;
  local stuff2::(String, Term) =
        case decorate hyp2Find.fromJust with
             {silverContext = top.silverContext;} of
        | termMetaterm(
             applicationTerm(_,
                consTermList(nameTerm(treeName, _),
                singleTermList(treeStructure))), _)
          when treeStructure.isProdStructure ->
          (treeName, new(treeStructure))
        | termMetaterm(
             applicationTerm(_,
                consTermList(treeStructure,
                singleTermList(nameTerm(treeName, _)))), _)
          when treeStructure.isProdStructure ->
          (treeName, new(treeStructure))
        | _ -> error("Should not access this")
        end;
  local treeName2::String = stuff2.1;
  local treeStructure2::Term = stuff2.2;
  treeStructure2.silverContext = top.silverContext;
  local prod::String =
        case treeStructure1 of
        | applicationTerm(nameTerm(prod, _), _) -> prod
        | nameTerm(prod, _) -> prod
        | _ -> error("Impossible (prod)")
        end;
  local treeTy::Type =
        case findProd(prodToName(prod), top.silverContext) of
        | [(_, ty)] -> ty.resultType
        | _ -> error("Impossible (treeTy)")
        end;
  local prod2::String =
        case treeStructure2 of
        | applicationTerm(nameTerm(prod, _), _) -> prod
        | nameTerm(prod, _) -> prod
        | _ -> error("Impossible (prod2)")
        end;
  local treeTy2::Type =
        case findProd(prodToName(prod2), top.silverContext) of
        | [(_, ty)] -> ty.resultType
        | _ -> error("Impossible (treeTy)")
        end;
  local component::String =
        findProdComponent(prodToName(prod),
                          top.silverContext.knownWPDRelations);
  --
  local assertName::String = "$Assert_" ++ toString(genInt());
  local structEqName::String = typeToStructureEqName(treeTy);
  local structEqEqual::Clearable =
        clearable(false, structureEqEqualTheorem(treeTy), []);
  top.translation =
      [
       --set up what we want in the end
       assertTactic(h, nothing(),
          termMetaterm(
             buildApplication(
                nameTerm(structEqName, nothing()),
                [nameTerm(treeName1, nothing()),
                 nameTerm(treeName2, nothing())]),
             emptyRestriction())),
       --the way we're going to prove it
       assertTactic(nameHint(assertName), nothing(),
          impliesMetaterm(
             termMetaterm(
                buildApplication(
                   nameTerm(structEqName, nothing()),
                   [treeStructure1, treeStructure2]),
                emptyRestriction()),
             termMetaterm(
                buildApplication(
                   nameTerm(structEqName, nothing()),
                   [nameTerm(treeName1, nothing()),
                    nameTerm(treeName2, nothing())]),
                emptyRestriction()))),
       introsTactic([]),
       applyTactic(noHint(), nothing(), structEqEqual,
                   [hypApplyArg(hyp1, [])], []),
       applyTactic(noHint(), nothing(), structEqEqual,
                   [hypApplyArg(hyp2, [])], []),
       searchTactic(),
       --get the equality of structures as the goal
       backchainTactic(nothing(), clearable(false, assertName, []), []),
       clearCommand([assertName], false),
       --change to the component version
       backchainTactic(nothing(),
          clearable(false,
             structureEqExpansionTheorem(treeTy, component), []), [])
      ];

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

  local decState::ProofState = top.currentState.state;
  decState.silverContext = top.silverContext;
  m.silverContext = top.silverContext;
  m.boundVars = [];
  m.finalTys =
    [map(\ p::(String, Type) -> (p.1, just(p.2)),
         decState.treeTys)];
  m.knownNames = decState.usedNames;
  m.knownTrees = m.gatheredTrees ++ decState.gatheredTrees;
  m.knownDecoratedTrees =
    m.gatheredDecoratedTrees ++ decState.gatheredDecoratedTrees;
  m.knownTyParams = [];
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

  top.translation =
      [witnessTactic(
          map(\ e::EWitness ->
                decorate e with
                {knownTrees = top.currentState.state.gatheredTrees;
                 silverContext = top.silverContext;
                }.translation, ew))];

  top.errors <-
      foldr(\ e::EWitness rest::[Error] ->
              decorate e with
              {silverContext = top.silverContext;}.errors ++ rest,
            [], ew);

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

  top.translation =
      [witnessTactic(
          map(\ e::EWitness ->
                decorate e with
                {knownTrees = top.currentState.state.gatheredTrees;
                 silverContext = top.silverContext;
                }.translation, ew))];

  top.errors <-
      foldr(\ e::EWitness rest::[Error] ->
              decorate e with
              {silverContext = top.silverContext;}.errors ++ rest,
            [], ew);

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

  top.errors <-
      foldr(\ n::String rest::[Error] ->
              case findAssociated(n, top.currentState.state.hypList) of
              | just(mt) when !decorate mt with
                               {silverContext = top.silverContext;}.shouldHide -> rest
              | _ -> errorMsg("Unknown hypothesis " ++ n)::rest
              end,
            [], removes);
  --some things we can't eliminate---tree structure hypotheses
  top.errors <- [];

  top.translation = [clearCommand(removes, hasArrow)];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";

  top.errors <-
      if indexOf("$", original) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];
  top.errors <-
      if indexOf("$", renamed) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];

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

  --disallow this for now, since we need to know the shape of all terms
  top.translation = --[abbrevCommand(hyps, newText)];
      error("Translation not done in abbrev command");

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

  top.errors <-
      foldr(\ s::String rest::[Error] ->
              if indexOf("$", s) >= 0
              then errorMsg("Identifiers cannot contain \"$\"")::rest
              else rest,
            [], names);

  top.shouldClean = true;
}


abstract production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.pp = "unfold " ++ toString(steps) ++ if all then "(all).  " else ".  ";

  top.translation = [unfoldStepsTactic(steps, all)];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production unfoldIdentifierTactic
top::ProofCommand ::= id::String all::Boolean
{
  top.pp = "unfold " ++ id ++ if all then "(all).  " else ".  ";

  top.translation = error("Translation not done in unfoldIdentifierTactic yet");

  top.errors <-
      if indexOf("$", id) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];

  --no real change to proof state
  top.shouldClean = false;
}


abstract production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.pp = "unfold " ++ if all then "(all).  " else ".  ";

  top.translation = [unfoldTactic(all)];

  --no real change to proof state
  top.shouldClean = false;
}





nonterminal Clearable with
   pp,
   translation<Clearable>, errors, currentState, translatedState,
   name;

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

  top.name = hyp;

  local findName::[String] =
        case findAssociated(hyp, top.currentState.state.hypList) of
        | just(_) -> [hyp]
        | nothing() ->
          map(fst, findTheorem(hyp, top.currentState))
        end;

  top.translation =
      clearable(star, colonsToEncoded(head(findName)), instantiation);

  top.errors <-
      if indexOf("$", hyp) >= 0
      then [errorMsg("Names cannot include \"$\"")]
      else [];
  top.errors <-
      case findName of
      | [] -> [errorMsg("Could not find hypothesis or lemma " ++ hyp)]
      | [_] -> []
      | lst ->
        [errorMsg("Multiple choices for lemma " ++ hyp ++
                  "; options are " ++ implode(", ", lst))]
      end;
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
   translation<EWitness>, silverContext, knownTrees, errors;

abstract production termEWitness
top::EWitness ::= t::Term
{
  top.pp = t.pp;

  top.translation = termEWitness(t.translation);

  t.knownTyParams = [];
}


abstract production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.pp = name ++ " = " ++ t.pp;

  top.translation = nameEWitness(name, t.translation);

  top.errors <-
      if indexOf("$", name) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];

  t.knownTyParams = [];
}





nonterminal HHint with
   errors,
   pp;

abstract production nameHint
top::HHint ::= name::String
{
  top.pp = name ++ ": ";

  top.errors <-
      if indexOf("$", name) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];
}


abstract production noHint
top::HHint ::=
{
  top.pp = "";
}

