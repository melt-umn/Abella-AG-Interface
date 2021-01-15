grammar fromAbella:abstractSyntax;


function subgoalNumToString
String ::= subgoalNum::[Integer]
{
  return case subgoalNum of
         | [] -> error("Subgoal numbers should not be empty")
         | [x] -> toString(x)
         | h::t -> toString(h) ++ "." ++ subgoalNumToString(t)
         end;
}

