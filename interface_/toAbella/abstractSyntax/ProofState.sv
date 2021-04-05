grammar interface_:toAbella:abstractSyntax;


attribute
   cleanUpCommands, numCleanUpCommands,
   nextStateIn, nextStateOut
occurs on ProofState;


aspect production proofInProgress
top::ProofState ::=
   subgoalNum::[Integer] currGoal::CurrentGoal futureGoals::[Subgoal]
{
  --(hyp name, tree name, attr name, type name, value of attr)
  local attrAccessHyps::[(String, String, String, String, Term)] =
        foldr(
          \ p::(String, Metaterm)
            rest::[(String, String, String, String, Term)] ->
            case p of
            | (hyp,
               termMetaterm(applicationTerm(nameTerm(access, _),
                              consTermList(nameTerm(treeNode, _),
                              singleTermList(val))), _))
              when isAccessRelation(access) ->
              (hyp, nodeToTreeName(treeNode),
               accessRelationToAttr(access),
               accessRelationToType(access), new(val))::rest
            | (_, _) -> rest
            end,
          [], currGoal.hypList);
  local sortedAttrAccessHyps::[(String, String, String, String, Term)] =
        sortBy(\ p1::(String, String, String, String, Term)
                 p2::(String, String, String, String, Term) ->
                 p1.3 < p2.3 || (p1.3 == p2.3 && p1.2 <= p2.2),
               attrAccessHyps);
  local groupedAttrAccesses::[[(String, String, String, String, Term)]] =
        groupBy(\ p1::(String, String, String, String, Term)
                  p2::(String, String, String, String, Term) ->
                  p1.2 == p2.2 && p1.3 == p2.3,
                sortedAttrAccessHyps);
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
                      [hypApplyArg(hyp1, []),
                       hypApplyArg(hyp2, [])], []).pp
        | _ -> error("Impossible after filtration")
        end;

  top.cleanUpCommands =
      if null(cleanedAttrAccesses)
      then ""
      else attrAccessCmd;
  top.numCleanUpCommands =
      if null(cleanedAttrAccesses)
      then 0
      else 1;

  top.nextStateOut = top.nextStateIn;
}


aspect production noProof
top::ProofState ::=
{
  top.cleanUpCommands = "";
  top.numCleanUpCommands = 0;

  top.nextStateOut = top.nextStateIn;
}


aspect production extensible_proofInProgress
top::ProofState ::=
     currentProofState::ProofState originalTheorem::Metaterm
     name::String numProds::Integer
{
  --names for the split theorems
  local newThmNames::[String] =
        map(\ i::Integer -> "$" ++ name ++ "_$_" ++ toString(i),
            range(1, numProds + 1));
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
           splitTheorem("$" ++ name, newThmNames).pp ++
           theoremDeclaration(name, [], originalTheorem).pp ++
           skipTactic().pp
      else currentProofState.cleanUpCommands;
  top.numCleanUpCommands =
      if isDone && shouldDeclare
      then 3
      else currentProofState.numCleanUpCommands;

  top.nextStateOut =
      if isDone
      then top.nextStateIn
      else extensible_proofInProgress(
              top.nextStateIn, originalTheorem, name, numProds);
}



--nonterminal CurrentGoal

aspect production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{

}



--nonterminal Context

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



--nonterminal Hypothesis

aspect production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  
}

