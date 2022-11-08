grammar interface_:toAbella:abstractSyntax;


attribute
   cleanUpCommands, numCleanUpCommands,
   nextStateIn, nextStateOut,
   treeTys
occurs on ProofState;


aspect production proofInProgress
top::ProofState ::=
   subgoalNum::[Integer] currGoal::CurrentGoal futureGoals::[Subgoal]
{
  --Clean up attribute accesses to be equal
  --(hyp name, tree name, attr name, type name, value of attr)
  local attrAccessHyps::[(String, String, String, String, Term)] =
        foldr(
          \ p::(String, Metaterm)
            rest::[(String, String, String, String, Term)] ->
            case p.1, decorate p.2 with {silverContext = top.silverContext;} of
            | hyp,
              termMetaterm(applicationTerm(nameTerm(access, _),
                             consTermList(nameTerm(treeName, _),
                             consTermList(nameTerm(treeNode, _),
                             singleTermList(val)))), _)
              when isAccessRelation(access) ->
              (hyp, treeName,
               accessRelationToAttr(access),
               accessRelationToType(access), new(val))::rest
            | _, _ -> rest
            end,
          [], currGoal.hypList);
  local sortedAttrAccessHyps::[(String, String, String, String, Term)] =
        sortBy(\ p1::(String, String, String, String, Term)
                 p2::(String, String, String, String, Term) ->
                 p1.3 < p2.3 || (p1.3 == p2.3 && p1.2 <= p2.2),
               attrAccessHyps);
  --group by tree name and attr
  local groupedAttrAccesses::[[(String, String, String, String, Term)]] =
        groupBy(\ p1::(String, String, String, String, Term)
                  p2::(String, String, String, String, Term) ->
                  p1.2 == p2.2 && p1.3 == p2.3,
                sortedAttrAccessHyps);
  --remove repeated accesses with same term
  local cleanedAttrAccessGroups::[[(String, String, String, String, Term)]] =
        map(\ l::[(String, String, String, String, Term)] ->
              nubBy(\ p1::(String, String, String, String, Term)
                      p2::(String, String, String, String, Term) ->
                      p1.5.pp == p2.5.pp, l), groupedAttrAccesses);
  local cleanedAttrAccesses::[[(String, String, String, String, Term)]] =
        filter(\ l::[(String, String, String, String, Term)] ->
                 length(l) > 1, cleanedAttrAccessGroups);
  --We can only do one clean up at a time, since each one might
  --   eliminate the goal based on impossibility
  --We can do the rest later, if we don't remove the goal
  local attrAccessCmd::String =
        case head(cleanedAttrAccesses) of
        | (hyp1, _, attr, ty, _)::(hyp2, _, _, _, _)::_ ->
          applyTactic(noHint(), nothing(),
                      clearable(false, accessUniqueThm(attr, ty), []),
                      [hypApplyArg(hyp2, []),
                       hypApplyArg(hyp1, [])], []).pp
        | _ -> error("Impossible after filtration")
        end;

  --Clear repeated accesses with same value, only leaving first one
  --Assume all accesses of same attribute have been equalized
  local repeatedAccessHypsToClear::[String] =
        flatMap(\ l::[(String, String, String, String, Term)] ->
           map(\ p::(String, String, String, String, Term) -> p.1,
               tail(l)),
           groupedAttrAccesses);
  local clearRepeatedAccessCmd::String =
        "clear " ++ implode(" ", repeatedAccessHypsToClear) ++ ".";

  --Clean up local attribute accesses to be equal
  --(hyp name, tree name, prod name, attr name, type name, value of attr)
  local localAccessHyps::[(String, String, String, String, String, Term)] =
        foldr(
          \ p::(String, Metaterm)
            rest::[(String, String, String, String, String, Term)] ->
            case p.1, decorate p.2 with {silverContext = top.silverContext;} of
            | hyp,
              termMetaterm(applicationTerm(nameTerm(access, _),
                             consTermList(nameTerm(treeName, _),
                             consTermList(nameTerm(treeNode, _),
                             singleTermList(val)))), _)
              when isLocalAccessRelation(access) ->
              (hyp, treeName,
               localAccessToProd(access),
               localAccessToAttr(access),
               localAccessToType(access).pp, new(val))::rest
            | _, _ -> rest
            end,
          [], currGoal.hypList);
  local sortedLocalAccessHyps::[(String, String, String, String, String, Term)] =
        sortBy(\ p1::(String, String, String, String, String, Term)
                 p2::(String, String, String, String, String, Term) ->
                 p1.4 < p2.4 || (p1.4 == p2.4 && p1.2 <= p2.2),
               localAccessHyps);
  local groupedLocalAccesses::[[(String, String, String, String, String, Term)]] =
        groupBy(\ p1::(String, String, String, String, String, Term)
                  p2::(String, String, String, String, String, Term) ->
                  p1.2 == p2.2 && p1.3 == p2.3 && p1.4 == p2.4,
                sortedLocalAccessHyps);
  local cleanedLocalAccessGroups::[[(String, String, String, String, String, Term)]] =
        map(\ l::[(String, String, String, String, String, Term)] ->
              nubBy(\ p1::(String, String, String, String, String, Term)
                      p2::(String, String, String, String, String, Term) ->
                    p1.6.pp == p2.6.pp, l), groupedLocalAccesses);
  local cleanedLocalAccesses::[[(String, String, String, String, String, Term)]] =
        filter(\ l::[(String, String, String, String, String, Term)] ->
                 length(l) > 1, cleanedLocalAccessGroups);
  --We can only do one clean up at a time, since each one might
  --   eliminate the goal based on impossibility
  --We can do the rest later, if we don't remove the goal
  local localAccessCmd::String =
        case head(cleanedLocalAccesses) of
        | (hyp1, _, prod, attr, ty, _)::(hyp2, _, _, _, _, _)::_ ->
          applyTactic(noHint(), nothing(),
                      clearable(false, localAccessUniqueThm(prod, attr, ty), []),
                      [hypApplyArg(hyp2, []),
                       hypApplyArg(hyp1, [])], []).pp
        | _ -> error("Impossible after filtration")
        end;

  --Clear repeated local accesses with same value, only leaving first one
  --Assume all local accesses of same attribute have been equalized
  local repeatedLocalAccessHypsToClear::[String] =
        flatMap(\ l::[(String, String, String, String, String, Term)] ->
           map(\ p::(String, String, String, String, String, Term) -> p.1,
               tail(l)),
           groupedLocalAccesses);
  local clearRepeatedLocalAccessCmd::String =
        "clear " ++ implode(" ", repeatedLocalAccessHypsToClear) ++ ".";

  --Clean up cases with impossible tree forms which come from equations
  --   for local attributes
  --We need to hide these cases to hide the encoding of the AG
  --(exists <Children>, <prod>(<Children'>) = <prod>(<Children>)) -> false
  local impossibleEqHyps::[String] =
        foldr(\ p::(String, Metaterm) rest::[String] ->
                case p.1, decorate p.2 with {silverContext = top.silverContext;} of
                --TODO need to handle non-tree children
                | hyp,
                  impliesMetaterm(
                     bindingMetaterm(
                        existsBinder(),
                        children,
                        eqMetaterm(
                           applicationTerm(nameTerm(prod1, _), args1),
                           applicationTerm(nameTerm(prod2, _), args2))),
                     falseMetaterm())
                  when isProd(prod1) && prod1 == prod2 ->
                  hyp::rest
                | hyp,
                  impliesMetaterm(
                     bindingMetaterm(
                        existsBinder(),
                        children,
                        eqMetaterm(
                           nameTerm(prod1, _),
                           nameTerm(prod2, _))),
                     falseMetaterm())
                  when isProd(prod1) && prod1 == prod2 -> hyp::rest
                | _, _ -> rest
                end,
              [], currGoal.hypList);
  local impossibleEqHypsCmd::[String] =
        let name::String = "$F_" ++ toString(genInt())
        in
          [name ++ ": assert false.",
          "backchain " ++ head(impossibleEqHyps) ++ ".",
          "case " ++ name ++ "."]
        end;

  --As soon as a tree shows up in our context, we want to get the WPD hyp
  --attr accesses of trees without WPD hyps, where defining tree does have WPD hyp
  --[(hyp, defining tree name, attr name, defined tree name, tree type name)]
  local treeAttrAccesses::[(String, String, String, String, String)] =
        foldr(\ p::(String, String, String, String, Term)
                rest::[(String, String, String, String, String)] ->
                case decorate p.5 with {silverContext = top.silverContext;} of
                | applicationTerm(nameTerm(attrEx, _),
                     singleTermList(
                        applicationTerm(nameTerm(pairC, _),
                           consTermList(nameTerm(treeName, _),
                           singleTermList(
                              applicationTerm(nameTerm(nodetreeC, _),
                                 consTermList(nameTerm(treeNode, _),
                                 singleTermList(childList))))))))
                  when attrEx == attributeExistsName &&
                       pairC == pairConstructorName &&
                       isNodeTreeConstructorName(nodetreeC) &&
                       !find_WPD_nt_hyp(treeName, currGoal.hypList,
                                        top.silverContext).isJust &&
                       find_WPD_nt_hyp(p.2, currGoal.hypList,
                                       top.silverContext).isJust ->
                  (p.1, p.2, p.3, treeName, p.4)::rest
                | _ -> rest
                end, [], attrAccessHyps);
  --
  local treeAttrAccessWpdCommands::[String] =
        map(\ p::(String, String, String, String, String) ->
              --hint for hypothesis name to avoid changing any proofs
              "$Wpd: apply " ++ accessIsThm(p.3, colonsToEncoded(p.5)) ++
                       " to _ " ++ p.1 ++ ".",
            treeAttrAccesses);

  --attr accesses of trees without WPD hyps, where defining tree does have WPD hyp
  --[(hyp, defining tree name, attr name, defined tree name,
  --  prod, tree type name)]
  local treeLocalAttrAccesses::[(String, String, String, String,
                                 String, String)] =
        foldr(\ p::(String, String, String, String, String, Term)
                rest::[(String, String, String, String, String, String)] ->
                case decorate p.6 with {silverContext = top.silverContext;} of
                | applicationTerm(nameTerm(attrEx, _),
                     singleTermList(
                        applicationTerm(nameTerm(pairC, _),
                           consTermList(nameTerm(treeName, _),
                           singleTermList(
                              applicationTerm(nameTerm(nodetreeC, _),
                                 consTermList(nameTerm(treeNode, _),
                                 singleTermList(childList))))))))
                  when attrEx == attributeExistsName &&
                       pairC == pairConstructorName &&
                       isNodeTreeConstructorName(nodetreeC) &&
                       !find_WPD_nt_hyp(treeName, currGoal.hypList,
                                        top.silverContext).isJust &&
                       find_WPD_nt_hyp(p.2, currGoal.hypList,
                                       top.silverContext).isJust ->
                  (p.1, p.2, p.4, treeName, p.3, p.5)::rest
                | _ -> []
                end, [], localAccessHyps);
  --
  local localAttrAccessWpdCommands::[String] =
        map(\ p::(String, String, String, String, String, String) ->
              --hint for hypothesis name to avoid changing any proofs
              "$Wpd: apply " ++ localAccessIsThm(p.3,
                                nameToProd(p.5),
                                colonsToEncoded(p.6)) ++
                 " to _ " ++ p.1 ++ ".",
            treeLocalAttrAccesses);

  top.cleanUpCommands =
      if !null(cleanedAttrAccesses)
      then [attrAccessCmd]
      else if !null(repeatedAccessHypsToClear)
      then [clearRepeatedAccessCmd]
      else if !null(cleanedLocalAccesses)
      then [localAccessCmd]
      else if !null(repeatedLocalAccessHypsToClear)
      then [clearRepeatedLocalAccessCmd]
      else if !null(impossibleEqHyps)
      then impossibleEqHypsCmd
      else if !null(treeAttrAccesses)
      then treeAttrAccessWpdCommands
      else if !null(treeLocalAttrAccesses)
      then localAttrAccessWpdCommands
      else [];
  top.numCleanUpCommands = length(top.cleanUpCommands);

  top.nextStateOut = top.nextStateIn;
  currGoal.knownDecoratedTrees = top.gatheredDecoratedTrees;
}


aspect production noProof
top::ProofState ::=
{
  top.cleanUpCommands = [];
  top.numCleanUpCommands = 0;

  top.nextStateOut = top.nextStateIn;
}


aspect production extensible_proofInProgress
top::ProofState ::=
     currentProofState::ProofState
     originalTheorems::[(String, Metaterm)]
     numProds::[(String, Integer)]
{
  --names for the split theorems
  local newThmNames::[String] =
        flatMap(\ p::(String, Integer) ->
           map(\ i::Integer -> "$" ++ colonsToEncoded(p.1) ++ "_$_" ++ toString(i),
               range(1, p.2 + 1)),
           numProds);
  local isDone::Boolean =
        case currentProofState of
        | proofInProgress(_, _, _) -> false
        | proofCompleted() -> true
        | proofAborted() -> true
        | noProof() ->
          error("Should not have extensible_proofInProgress of noProof")
        end;
  local shouldDeclare::Boolean =
        case currentProofState of
        | proofInProgress(_, _, _) -> false
        | proofCompleted() -> true
        | proofAborted() -> false
        | noProof() ->
          error("Should not have extensible_proofInProgress of noProof")
        end;
  top.cleanUpCommands =
      if isDone && shouldDeclare
      then --split, declare, and skip.
          [splitTheorem(
              extensible_theorem_name(colonsToEncoded(head(originalTheorems).1),
                 top.silverContext.currentGrammar),
              newThmNames).pp] ++
           foldr(\ p::(String, Metaterm) rest::[String] ->
                   theoremDeclaration(colonsToEncoded(p.1), [], p.2).pp::
                   skipTactic().pp::rest,
                 [], originalTheorems)
      else currentProofState.cleanUpCommands;
  top.numCleanUpCommands = length(top.cleanUpCommands);

  top.nextStateOut =
      if isDone
      then top.nextStateIn
      else extensible_proofInProgress(
              top.nextStateIn, originalTheorems, numProds);

  propagate silverContext;
}


abstract production obligation_proofInProgress
top::ProofState ::=
     currentProofState::ProofState
     originalTheorems::[(String, Metaterm)]
     numProds::[(String, Integer)]
{
  local isDone::Boolean =
        case currentProofState of
        | proofInProgress(_, _, _) -> false
        | proofCompleted() -> true
        | proofAborted() -> true
        | noProof() ->
          error("Should not have obligation_proofInProgress of noProof")
        end;
  local shouldDeclare::Boolean =
        case currentProofState of
        | proofInProgress(_, _, _) -> false
        | proofCompleted() -> true
        | proofAborted() -> false
        | noProof() ->
          error("Should not have obligation_proofInProgress of noProof")
        end;
  top.nextStateOut =
      if isDone
      then top.nextStateIn
      else obligation_proofInProgress(
              top.nextStateIn, originalTheorems, numProds);

  forwards to extensible_proofInProgress(currentProofState,
                 originalTheorems, numProds);
}



attribute
   knownDecoratedTrees,
   treeTys
occurs on CurrentGoal;

aspect production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{

}



attribute
   knownDecoratedTrees,
   treeTys
occurs on Context;

aspect production emptyContext
top::Context ::=
{
  
}


aspect production singleContext
top::Context ::= h::Hypothesis
{
  
}


aspect production branchContext
top::Context ::= c1::Context c2::Context
{
  
}



attribute
   knownDecoratedTrees,
   treeTys
occurs on Hypothesis;

aspect production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  
}

