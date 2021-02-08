grammar interface_:toAbella:abstractSyntax;


nonterminal SearchWitness with pp;

abstract production trueSearchWitness
top::SearchWitness ::=
{
  top.pp = "true";
}


abstract production applySearchWitness
top::SearchWitness ::= name::String
{
  top.pp = "apply " ++ name;
}


abstract production leftSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = "left (" ++ sub.pp ++ ")";
}


abstract production rightSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = "right (" ++ sub.pp ++ ")";
}


abstract production splitSearchWitness
top::SearchWitness ::= l::SearchWitness r::SearchWitness
{
  top.pp = "split(" ++l.pp ++ ", " ++ r.pp ++ ")";
}


abstract production introsSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp =
     "intros [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.pp ++ ")";
}


abstract production forallSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp =
     "forall [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.pp ++ ")";
}


abstract production existsSearchWitness
top::SearchWitness ::= withs::[Pair<String Term>] sub::SearchWitness
{
  local buildWiths::(String ::= [Pair<String Term>]) =
     \ w::[Pair<String Term>] ->
       case w of
       | [] ->
         error("Should not reach here; existsSearchWitness production")
       | [pair(a, b)] -> a ++ " := " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " := " ++ b.pp ++ ", " ++ buildWiths(rest)
       end;
  local withsString::String =
     if null(withs)
     then ""
     else " with " ++ buildWiths(withs);
  top.pp = "exists [" ++ withsString ++ "] (" ++ sub.pp ++ ")";
}


abstract production unfoldSearchWitness
top::SearchWitness ::= name::String n::Integer swl::[SearchWitness]
{
  local swlString::String =
     if null(swl)
     then ""
     else foldr1(\a::String b::String -> a ++ ", " ++ b,
                 map(\x::SearchWitness -> x.pp, swl));
  top.pp = "unfold(" ++ name ++ ", " ++ toString(n) ++ swlString ++ ")";
}


abstract production starSearchWitness
top::SearchWitness ::=
{
  top.pp = "*";
}


abstract production eqSearchWitness
top::SearchWitness ::=
{
  top.pp = "=";
}

