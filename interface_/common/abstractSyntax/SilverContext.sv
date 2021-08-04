grammar interface_:common:abstractSyntax;


nonterminal SilverContext with
   pp,
   currentGrammar,
   knownAttrs, knownAttrOccurrences, knownProductions,
   knownWPDRelations, knownInheritedAttrs, knownLocalAttrs,
   knownFunctions;


synthesized attribute currentGrammar::String;

--(attr name, grammar name)
synthesized attribute knownAttrs::[(String, String)];
--[(attr, grammar, [(nonterminal, attr type)])]
synthesized attribute knownAttrOccurrences::[(String, String, [(Type, Type)])];
--any attr not in this list (and which is known) is synthesized
synthesized attribute knownInheritedAttrs::[(String, String)];
--local name and list of productions it occurs on, production grammar, and type there
synthesized attribute knownLocalAttrs::[(String, [(String, String, Type)])];

--(name, grammar, prod type)
synthesized attribute knownProductions::[(String, String, Type)];
synthesized attribute knownFunctions::[(String, String, Type)];

--The type here is just the nonterminal type---we can deduce the rest
--   of the WPD nonterminal relation's type from that.
--The [String] is the names of the productions in order---we can
--   deduce everything else we need from that, but the right order is
--   going to be helpful in composition.
synthesized attribute knownWPDRelations::[(String, Type, [String])];


abstract production silverContext
top::SilverContext ::=
   currentGrammar::String
   attrs::[(String, String)]
   attrOccurrences::[(String, String, [(Type, Type)])]
   prods::[(String, String, Type)]
   funs::[(String, String, Type)]
   wpdRelations::[(String, Type, [String])]
   inheritedAttrs::[(String, String)]
   localAttrs::[(String, [(String, String, Type)])]
{
  --for debugging purposes only
  top.pp =
      "Current Grammar:  " ++ currentGrammar ++ "\n" ++
      "Attrs:  [" ++ implode(", ", map(\ p::(String, String) -> "(" ++ p.1 ++ ", " ++ p.2 ++ ")", attrs)) ++ "]\n" ++
      "Occurrences:  [" ++ implode(";  ", map(\ p::(String, String, [(Type, Type)]) -> "{ " ++ p.1 ++ ", " ++ p.2 ++ ", [" ++ implode("; ", map(\ p::(Type, Type) -> "<" ++ p.1.pp ++ ", " ++ p.2.pp ++ ">", p.3)) ++ "] }", attrOccurrences)) ++ "]\n" ++
      "Prods:  [" ++ implode(";  ", map(\ p::(String, String, Type) -> "(" ++ p.1 ++ ", " ++ p.2 ++ ", " ++ p.3.pp ++ ")", prods)) ++ "]\n" ++
      "Funs:  [" ++ implode(";  ", map(\ p::(String, String, Type) -> "(" ++ p.1 ++ ", " ++ p.2 ++ ", " ++ p.3.pp ++ ")", funs)) ++ "]\n";

  top.currentGrammar = currentGrammar;
  top.knownAttrs = attrs;
  top.knownAttrOccurrences = attrOccurrences;
  top.knownProductions = prods;
  --Extra functions until we get silver:core working
  top.knownFunctions =
        [
         ("head", "silver:core",
                  arrowType(functorType(nameType("list"), nameType("A")),
                  arrowType(nameType("A"),
                            nameType("prop")))),
         ("null", "silver:core",
                  arrowType(functorType(nameType("list"), nameType("A")),
                  arrowType(nameType("bool"),
                            nameType("prop")))),
         ("tail", "silver:core",
                  arrowType(functorType(nameType("list"), nameType("A")),
                  arrowType(functorType(nameType("list"), nameType("A")),
                            nameType("prop")))),
         ("length", "silver:core",
                    arrowType(functorType(nameType("list"), nameType("A")),
                    arrowType(nameType("integer"),
                            nameType("prop")))),
         ("fst", "silver:core",
                  arrowType(functorType(functorType(nameType("$pair"),
                                          nameType("A")), nameType("B")),
                 arrowType(nameType("A"),
                           nameType("prop")))),
         ("snd", "silver:core",
                  arrowType(functorType(functorType(nameType("$pair"),
                                          nameType("A")), nameType("B")),
                 arrowType(nameType("A"),
                           nameType("prop"))))
        ] ++ funs;
  top.knownWPDRelations = wpdRelations;
  top.knownInheritedAttrs = inheritedAttrs;
  top.knownLocalAttrs = localAttrs;
}


function emptySilverContext
SilverContext ::=
{
  return silverContext("", [], [], [], [], [], [], []);
}


--find the full name and type of a production
function findProd
[(String, Type)] ::= prodName::String context::Decorated SilverContext
{
  return
    if isFullyQualifiedName(prodName)
    then let splitName::(String, String) =
             splitQualifiedName(prodName)
         in
         let found::[(String, Type)] =
             findAllAssociated(splitName.2, context.knownProductions)
         in
           case findAssociated(splitName.2, found) of
           | nothing() -> []
           | just(ty) -> [(prodName, ty)]
           end
         end end
    else map(\ p::(String, Type) -> (p.1 ++ ":" ++ prodName, p.2),
             findAllAssociated(prodName, context.knownProductions));
}


--find the full name and type of a function
function findFun
[(String, Type)] ::= funName::String context::Decorated SilverContext
{
  return
    if isFullyQualifiedName(funName)
    then let splitName::(String, String) =
             splitQualifiedName(funName)
         in
         let found::[(String, Type)] =
             findAllAssociated(splitName.2, context.knownFunctions)
         in
           case findAssociated(splitName.2, found) of
           | nothing() -> []
           | just(ty) -> [(funName, ty)]
           end
         end end
    else map(\ p::(String, Type) -> (p.1 ++ ":" ++ funName, p.2),
             findAllAssociated(funName, context.knownFunctions));
}


--find the full name and occurrences of an attribute
function findAttrOccurrences
[(String, [(Type, Type)])] ::= attrName::String context::Decorated SilverContext
{
  return
    if isFullyQualifiedName(attrName)
    then let splitName::(String, String) =
             splitQualifiedName(attrName)
         in
         let found::[(String, [(Type, Type)])] =
             findAllAssociated(splitName.2, context.knownAttrOccurrences)
         in
           case findAssociated(splitName.2, found) of
           | nothing() -> []
           | just(ty) -> [(attrName, ty)]
           end
         end end
    else map(\ p::(String, [(Type, Type)]) -> (p.1 ++ ":" ++ attrName, p.2),
             findAllAssociated(attrName, context.knownAttrOccurrences));
}


function isInheritedAttr
Boolean ::= attrName::String context::Decorated SilverContext
{
  return
    if isFullyQualifiedName(attrName)
    then let splitName::(String, String) =
             splitQualifiedName(attrName)
         in
           containsBy(\ p1::(String, String) p2::(String, String) ->
                        p1.1 == p2.1 && p1.2 == p2.2,
                      (splitName.2, splitName.1),
                      context.knownInheritedAttrs)
         end
    else contains(attrName, map(fst, context.knownInheritedAttrs));
}


function findAllAssociated
[a] ::= find::String lst::[(String, a)]
{
  return
     case lst of
     | [] -> []
     | (hd, data)::rest ->
       if hd == find
       then data::findAllAssociated(find, rest)
       else findAllAssociated(find, rest)
     end;
}

