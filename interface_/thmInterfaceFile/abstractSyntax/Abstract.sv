grammar interface_:thm_interface_file:abstractSyntax;


import interface_:common;
import interface_:toAbella:abstractSyntax;


nonterminal ParsedElement with pp, encode;

synthesized attribute encode::String;


abstract production extensibleMutualTheoremGroup
top::ParsedElement ::=
   --[(thm name, thm statement, induction tree)]
   thms::[(String, Metaterm, String)]
{
  top.pp =
      implode(",",
              map(\ p::(String, Metaterm, String) ->
                    p.1 ++ "&" ++ p.2.pp ++ "&" ++ p.3,
                  thms)) ++ ". ";

  top.encode = error("Not done yet");
}


--Non-extensible mutuals are written all in one
abstract production nonextensibleTheorem
top::ParsedElement ::= name::String stmt::Metaterm
{
  top.pp = name ++ "&" ++ stmt.pp ++ ". ";

  top.encode = theoremAndProof(name, [], stmt, [skipTactic()]).pp;
}


abstract production splitElement
top::ParsedElement ::= toSplit::String newNames::[String]
{
  top.pp =
      "$Spl " ++ toSplit ++ " " ++ implode(",", newNames) ++ ". ";

  top.encode = splitTheorem(toSplit, newNames).pp;
}





nonterminal DefElement with pp, encode;


abstract production defineElement
top::DefElement ::= defines::[(String, Type)]
                    --Some clauses don't have bodies, so Maybe
                    clauses::[(Metaterm, Maybe<Metaterm>)]
{
  top.pp =
      "$Def " ++
      implode(",", map(\ p::(String, Type) ->
                         p.1 ++ " : " ++ p.2.pp,
                       defines)) ++
      implode(";", map(\ p::(Metaterm, Maybe<Metaterm>) ->
                         case p.2 of
                         | nothing() ->
                           p.1.pp
                         | just(p2) ->
                           p.1.pp ++ "," ++ p2.pp
                         end, clauses)) ++ ". ";

  local defs::Defs =
        foldrLastElem(consDefs, singleDefs,
           map(\ p::(Metaterm, Maybe<Metaterm>) ->
                 case p of
                 | (m, nothing()) -> factDef(m)
                 | (m, just(b)) -> ruleDef(m, b)
                 end,
               clauses));
  top.encode = definitionDeclaration(defines, defs).pp;
}

