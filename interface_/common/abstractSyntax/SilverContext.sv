grammar interface_:common:abstractSyntax;


nonterminal SilverContext with
   currentGrammar,
   knownAttrs, knownAttrOccurrences, knownProductions,
   knownWPDRelations, knownInheritedAttrs, knownLocalAttrs,
   knownFunctions;


synthesized attribute currentGrammar::String;

synthesized attribute knownAttrs::[String];
--[(attr, [(nonterminal, attr type)])]
synthesized attribute knownAttrOccurrences::[(String, [(Type, Type)])];
--any attr not in this list (and which is known) is synthesized
synthesized attribute knownInheritedAttrs::[String];
--local name and list of productions it occurs on and type there
synthesized attribute knownLocalAttrs::[(String, [(String, Type)])];

synthesized attribute knownProductions::[(String, Type)];
synthesized attribute knownFunctions::[(String, Type)];

--The type here is just the nonterminal type---we can deduce the rest
--   of the WPD nonterminal relation's type from that.
--The [String] is the names of the productions in order---we can
--   deduce everything else we need from that, but the right order is
--   going to be helpful in composition.
synthesized attribute knownWPDRelations::[(String, Type, [String])];


abstract production silverContext
top::SilverContext ::=
   currentGrammar::String
   attrs::[String]
   attrOccurrences::[(String, [(Type, Type)])]
   prods::[(String, Type)]
   funs::[(String, Type)]
   wpdRelations::[(String, Type, [String])]
   inheritedAttrs::[String]
   localAttrs::[(String, [(String, Type)])]
{
  top.currentGrammar = currentGrammar;
  top.knownAttrs = attrs;
  top.knownAttrOccurrences = attrOccurrences;
  top.knownProductions = prods;
  --Extra functions until we get silver:core working
  top.knownFunctions =
        [
         ("head", arrowType(functorType(nameType("list"), nameType("A")),
                  arrowType(nameType("A"),
                            nameType("prop")))),
         ("null", arrowType(functorType(nameType("list"), nameType("A")),
                  arrowType(nameType("bool"),
                            nameType("prop")))),
         ("tail", arrowType(functorType(nameType("list"), nameType("A")),
                  arrowType(functorType(nameType("list"), nameType("A")),
                            nameType("prop")))),
         ("length", arrowType(functorType(nameType("list"), nameType("A")),
                    arrowType(nameType("integer"),
                            nameType("prop")))),
         ("fst", arrowType(functorType(functorType(nameType("$pair"),
                                          nameType("A")), nameType("B")),
                 arrowType(nameType("A"),
                           nameType("prop")))),
         ("snd", arrowType(functorType(functorType(nameType("$pair"),
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

