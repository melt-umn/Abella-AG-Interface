grammar interface_:thmInterfaceFile:abstractSyntax;


import interface_:common:abstractSyntax;
import interface_:toAbella:abstractSyntax;


nonterminal ThmElement with pp, encode, is_nonextensible;

--allows having a theorem declaration and its proof
synthesized attribute encode::[AnyCommand];
synthesized attribute is_nonextensible::Boolean;


abstract production extensibleMutualTheoremGroup
top::ThmElement ::=
   --[(thm name, thm statement, induction tree)]
   thms::[(String, Metaterm, String)]
{
  top.pp =
      implode(",",
              map(\ p::(String, Metaterm, String) ->
                    p.1 ++ "&" ++ p.2.pp ++ "&" ++ p.3,
                  thms)) ++ ". ";

  top.encode = error("Not done yet");
  top.is_nonextensible = false;
}


--Non-extensible mutuals are written all in one
abstract production nonextensibleTheorem
top::ThmElement ::= name::String stmt::Metaterm
{
  top.pp = name ++ "&" ++ stmt.pp ++ ". ";

  top.encode =
      [anyTopCommand(theoremDeclaration(name, [], stmt)),
       anyProofCommand(skipTactic())];
  top.is_nonextensible = true;
}


abstract production splitElement
top::ThmElement ::= toSplit::String newNames::[String]
{
  top.pp =
      "$Spl " ++ toSplit ++ " " ++ implode(",", newNames) ++ ". ";

  top.encode = [anyTopCommand(splitTheorem(toSplit, newNames))];
  top.is_nonextensible = true;
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
  top.encode = [anyTopCommand(definitionDeclaration(defines, defs))];
}

