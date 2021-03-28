grammar interface_:common;

{-
  We put these in common rather than fromAbella because we need to
  have a ProofState in the undolist, which is passed to commands to
  determine how much should be undone.  We aren't touching the proof
  state, but we still need the type for typechecking.
-}

synthesized attribute hypList::[(String, Metaterm)];

nonterminal ProofState with pp, hypList;

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

  top.hypList = currGoal.hypList;
}


abstract production noProof
top::ProofState ::=
{
  top.pp = "";

  top.hypList = [];
}


{-
  We handle extensible theorems by proving one theorem which is the
  conjunction of the separate statements we want for the different
  productions.

  After that proof is finished, we want to split it into separate
  theorems with names of the form "$<name>_x" where "x" is a number
  1..numProds.  We also want to admit the original theorem under the
  original name so it can be used in further proofs.
-}
abstract production extensible_proofInProgress
top::ProofState ::= currentProofState::ProofState originalTheorem::Metaterm
                    name::String numProds::Integer
{
  --We could use this production to figure out what to label with * in the actual proof state
  --Have a translation attribute to label the things with * as needed

  forwards to currentProofState;
}



nonterminal CurrentGoal with pp, hypList;

abstract production currentGoal
top::CurrentGoal ::= vars::[String] ctx::Context goal::Metaterm
{
  local varsString::String =
        if null(vars)
        then ""
        else "Variables: " ++ foldr1(\ x::String y::String -> x ++ " " ++ y, vars) ++ "\n";
  top.pp = varsString ++ ctx.pp ++ "============================\n " ++ goal.pp ++ "\n";

  top.hypList = ctx.hypList;
}



--A context is the hypotheses available for proving the current goal
nonterminal Context with pp, hypList;

abstract production emptyContext
top::Context ::=
{
  top.pp = "";

  top.hypList = [];
}


abstract production singleContext
top::Context ::= h::Hypothesis
{
  --We don't want to put blank lines for hidden hypotheses
  top.pp = if h.pp == "" then "" else h.pp ++ "\n";

  top.hypList = h.hypList;
}


abstract production branchContext
top::Context ::= c1::Context c2::Context
{
  top.pp = c1.pp ++ c2.pp;

  top.hypList = c1.hypList ++ c2.hypList;
}



nonterminal Hypothesis with pp, hypList;

abstract production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.pp = name ++ " : " ++ body.pp;

  top.hypList = [(name, new(body))];
}



--A subgoal is a goal to proven in the future, after the current goal
nonterminal Subgoal with pp;

abstract production subgoal
top::Subgoal ::= num::[Integer] goal::Metaterm
{
  top.pp = "Subgoal " ++ subgoalNumToString(num) ++ " is:\n " ++ goal.pp;
}


abstract production hiddenSubgoals
top::Subgoal ::= num::Integer
{
  top.pp = toString(num) ++ " other subgoal" ++ (if num == 1 then "." else "s.");
}











function subgoalNumToString
String ::= subgoalNum::[Integer]
{
  return case subgoalNum of
         | [] -> error("Subgoal numbers should not be empty")
         | [x] -> toString(x)
         | h::t -> toString(h) ++ "." ++ subgoalNumToString(t)
         end;
}

