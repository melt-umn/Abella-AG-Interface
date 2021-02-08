grammar interface_:fromAbella:abstractSyntax;




nonterminal ProofState with
   pp,
   translation<ProofState>,
   inProof;

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

  top.inProof = true;
}


abstract production noProof
top::ProofState ::=
{
  top.pp = "";

  top.translation = noProof();

  top.inProof = false;
}





nonterminal Hypothesis with
   pp,
   translation<Hypothesis>;

abstract production metatermHyp
top::Hypothesis ::= name::String body::Metaterm
{
  top.pp = name ++ " : " ++ body.pp;

  top.translation =
      if body.shouldHide
      then hiddenHypothesis(name, body)
      else metatermHyp(name, body.translation);
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
  --We don't want to put blank lines for hidden hypotheses
  top.pp = if h.pp == "" then "" else h.pp ++ "\n";

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

  {-
    We assume all attributes are for trees which are listed in the
    list of variables as well, and that all tree terms and nodes are
    included by pairs.
  -}
  local cleanVars::[String] =
        filter(\ x::String -> x != "", map(cleanVariable, vars));
  top.translation = currentGoal(cleanVars, ctx.translation, goal.translation);
}

function cleanVariable
String ::= name::String
{
  -- $<tree>_DOT_<attr>
  local is_attr_access::Boolean = indexOf("_DOT_", name) > 0;
  -- $<tree>_Tm
  local is_tm::Boolean = startsWith("$", name) && indexOf("_Tm", name) > 0;
  local tm_treename::String = substring(1, indexOf("_Tm", name), name);
  -- $<tree>_Node
  local is_node::Boolean = startsWith("$", name) && indexOf("_Node", name) > 0;

  return
     if is_attr_access
     then "" --the tree will be created from its term
     else if is_tm
          then tm_treename
          else if is_node
               then "" --the tree will be created from its term
               else name; --nothing special
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

