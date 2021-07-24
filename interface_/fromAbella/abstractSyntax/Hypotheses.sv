grammar interface_:fromAbella:abstractSyntax;



attribute
   translation<ProofState>,
   inProof, hypList
occurs on ProofState;

aspect production proofInProgress
top::ProofState ::= subgoalNum::[Integer] currGoal::CurrentGoal futureGoals::[Subgoal]
{
  top.translation = proofInProgress(subgoalNum, currGoal.translation,
                       map(\ a::Subgoal ->
                             decorate a with
                             {silverContext = top.silverContext;}.translation,
                           futureGoals));

  top.inProof = true;
  top.hypList = currGoal.hypList;
}


aspect production noProof
top::ProofState ::=
{
  top.translation = noProof();

  top.inProof = false;
  top.hypList = [];
}


aspect production proofCompleted
top::ProofState ::=
{
  top.translation = proofCompleted();

  top.inProof = false;
  top.hypList = [];
}


aspect production proofAborted
top::ProofState ::=
{
  top.translation = proofAborted();

  top.inProof = false;
  top.hypList = [];
}





attribute
   translation<Hypothesis>,
   hypList
occurs on Hypothesis;

aspect production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.translation =
      if body.shouldHide || startsWith("$", name)
      then hiddenHypothesis(name, body.translation)
      else metatermHyp(name, body.translation);

  top.hypList = [(name, new(body))];
}

{-Going to disallow this, at least for now.
abstract production abbreviatedHyp
top::Hypothesis ::= name::String body::String
{
  top.pp = name ++ " : " ++ body;

  top.translation = abbreviatedHyp(name, body);
}-}





attribute
   translation<Context>,
   hypList
occurs on Context;

aspect production emptyContext
top::Context ::=
{
  top.translation = emptyContext();

  top.hypList = [];
}


aspect production singleContext
top::Context ::= h::Hypothesis
{
  top.translation = singleContext(h.translation);

  top.hypList = h.hypList;
}


aspect production branchContext
top::Context ::= c1::Context c2::Context
{
  top.translation = branchContext(c1.translation, c2.translation);

  top.hypList = c1.hypList ++ c2.hypList;
}





attribute
   translation<CurrentGoal>,
   hypList
occurs on CurrentGoal;

aspect production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  local isHidden::(Boolean ::= String) =
        \ s::String ->
          contains(s, flatMap(\ p::(String, String, Term) ->
                                p.2::decorate p.3 with
                                     {silverContext = top.silverContext;}.usedNames,
                              ctx.gatheredDecoratedTrees));
  local cleanVars::[String] =
        foldr(\ s::String rest::[String] ->
                if isHidden(s)
                then rest
                else s::rest,
              [], vars);
  top.translation = currentGoal(cleanVars, ctx.translation, goal.translation);

  top.hypList = ctx.hypList;
}





attribute
   translation<Subgoal>
occurs on Subgoal;

aspect production subgoal
top::Subgoal ::= num::[Integer] goal::Metaterm
{
  top.translation = subgoal(num, goal.translation);
}


aspect production hiddenSubgoals
top::Subgoal ::= num::Integer
{
  top.translation = hiddenSubgoals(num);
}

