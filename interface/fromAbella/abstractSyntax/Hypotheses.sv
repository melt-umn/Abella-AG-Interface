grammar fromAbella:abstractSyntax;




nonterminal ProofState with
   pp,
   translation<ProofState>;

abstract production proofInProgress
top::ProofState ::= subgoalNum::[Integer] currGoal::CurrentGoal futureGoals::[Subgoal]
{
  local subgoalString::String =
        if !(length(subgoalNum) == 1 && head(subgoalNum) == 0) --subgoalNum != [0]
        then "Subgoal " ++ subgoalNumToString(subgoalNum) ++ ":\n"
        else "";
  local futureGoalsString::String =
        foldr(\ a::Subgoal b::String -> a.pp ++ "\n\n" ++ b,
              "", futureGoals);
  top.pp = subgoalString ++ "\n" ++ currGoal.pp ++ "\n" ++ futureGoalsString;

  top.translation = proofInProgress(subgoalNum, currGoal.translation,
                                    map(\ a::Subgoal -> a.translation, futureGoals));
}


abstract production noProof
top::ProofState ::=
{
  top.pp = "";

  top.translation = noProof();
}


abstract production proofCompleted
top::ProofState ::=
{
  top.pp = "Proof completed.";

  top.translation = proofCompleted();
}


abstract production proofAborted
top::ProofState ::=
{
  top.pp = "Proof ABORTED.";

  top.translation = proofAborted();
}





nonterminal Hypothesis with
   pp,
   translation<Hypothesis>;

abstract production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.pp = name ++ " : " ++ body.pp;

  top.translation = metatermHyp(name, body.translation);
}


abstract production abbreviatedHyp
top::Hypothesis ::= name::String body::String
{
  top.pp = name ++ " : " ++ body;

  top.translation = abbreviatedHyp(name, body);
}





--A context is the hypotheses available for proving the current goal
nonterminal Context with
   pp,
   translation<Context>;

abstract production emptyContext
top::Context ::=
{
  top.pp = "";

  top.translation = emptyContext();
}


abstract production singleContext
top::Context ::= h::Hypothesis
{
  top.pp = h.pp ++ "\n";

  top.translation = singleContext(h.translation);
}


abstract production branchContext
top::Context ::= c1::Context c2::Context
{
  top.pp = c1.pp ++ c2.pp;

  top.translation = branchContext(c1.translation, c2.translation);
}





nonterminal CurrentGoal with
   pp,
   translation<CurrentGoal>;

abstract production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  local varsString::String =
        if null(vars)
        then ""
        else "Variables: " ++ foldr1(\ x::String y::String -> x ++ " " ++ y, vars) ++ "\n";
  top.pp = varsString ++ ctx.pp ++ "============================\n " ++ goal.pp ++ "\n";

  top.translation = currentGoal(vars, ctx.translation, goal.translation);
}





--A subgoal is a goal to proven in the future, after the current goal
nonterminal Subgoal with
   pp,
   translation<Subgoal>;

abstract production subgoal
top::Subgoal ::= num::[Integer] goal::Metaterm
{
  top.pp = "Subgoal " ++ subgoalNumToString(num) ++ " is:\n " ++ goal.pp;

  top.translation = subgoal(num, goal.translation);
}


abstract production hiddenSubgoals
top::Subgoal ::= num::Integer
{
  top.pp = toString(num) ++ " other subgoal" ++ (if num == 1 then "s." else ".");

  top.translation = hiddenSubgoals(num);
}

