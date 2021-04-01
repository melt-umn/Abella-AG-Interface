grammar interface_:common;

{-
  We put these in common rather than fromAbella because we need to
  have a ProofState in the undolist, which is passed to commands to
  determine how much should be undone.  We aren't touching the proof
  state, but we still need the type for typechecking.
-}

synthesized attribute hypList::[(String, Metaterm)];
synthesized attribute currentSubgoal::[Integer];

nonterminal ProofState with pp, hypList, currentSubgoal;

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

  top.currentSubgoal = subgoalNum;
}


abstract production noProof
top::ProofState ::=
{
  top.pp = "";

  top.hypList = [];

  top.currentSubgoal = [];
}


abstract production proofCompleted
top::ProofState ::=
{
  top.pp = "Proof completed.";

  top.hypList = [];

  top.currentSubgoal = [];

  forwards to noProof();
}


abstract production proofAborted
top::ProofState ::=
{
  top.pp = "Proof ABORTED.";

  top.hypList = [];

  top.currentSubgoal = [];

  forwards to noProof();
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
  top.pp = forward.pp;
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


--s1 < s2
--true if some position (from left) in s1 is less than corresponding
--   in s2 or s1 runs out first
function subgoalLess
Boolean ::= s1::[Integer] s2::[Integer]
{
  return
     case s1, s2 of
     | h1::tl1, h2::tl2 ->
       if h1 < h2
       then true
       else if h1 == h2
            then subgoalLess(tl1, tl2)
            else false
     | [], _::_ -> true
     | _::_, [] -> false
     | [], [] -> false
     end;
}


--Comparing (possibly empty) subgoals to see if a goal was completed
function subgoalCompleted
Boolean ::= oldSubgoal::[Integer] newSubgoal::[Integer]
{
  --Catch a subgoal completing and going forward to another one
  local goalToNewGoal::Boolean =
        subgoalLess(oldSubgoal, newSubgoal) &&
        --need to check length to avoid catching e.g. [2] expanding to [2.1]
        ( length(oldSubgoal) == length(newSubgoal) ||
          length(oldSubgoal) > length(newSubgoal) );
  --Catch a subgoal completing and going back to the previous one
  local goalToPreviousGoal::Boolean =
        subgoalLess(newSubgoal, oldSubgoal);
  --Catch expanding [0]
  --Either finishing the whole proof or expanding to subgoals
  local isSubgoal0::Boolean =
        case oldSubgoal of
        | [0] -> true
        | _ -> false
        end;
  return
     ! null(oldSubgoal) &&
     ( goalToNewGoal ||
       goalToPreviousGoal ) &&
     ! isSubgoal0;
}

