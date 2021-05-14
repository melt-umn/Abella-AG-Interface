grammar abella_compilation;


function generateNonterminalTypes
String ::= nonterminals::[String]
{
  return
     case nonterminals of
     | [] -> ""
     | nt::rest ->
       "Kind " ++ nameToNonterminal(nt) ++ "   type.\n" ++
       generateNonterminalTypes(rest)
     end;
}


function generateProductions
String ::= prods::[(String, Type)]
{
  return
     case prods of
     | [] -> ""
     | (prod, ty)::rest ->
       "Type " ++ nameToProd(prod) ++ "   " ++ ty.pp ++ ".\n" ++
       generateProductions(rest)
     end;
}


function generateNodeTypes
String ::= nonterminals::[String]
{
  return
     case nonterminals of
     | [] -> ""
     | nt::rest ->
       "Kind " ++ nameToNodeType(nt) ++ "   type.\n" ++
       generateNodeTypes(rest)
     end;
}


function generateNodeTreeConstructors
String ::= nonterminals::[String]
{
  return
     case nonterminals of
     | [] -> ""
     | nt::rest ->
       "Type " ++ nodeTreeConstructorName(nameToNonterminalType(nt)) ++
       "   " ++ nameToNodeType(nt) ++
       " -> list $node_tree -> $node_tree.\n" ++
       generateNodeTreeConstructors(rest)
     end;
}


function generateAccessRelations
String ::= attrOccurrences::[(String, [String])] attrs::[(String, Type)]
{
  return
     case attrOccurrences of
     | [] -> ""
     | (attr, nts)::rest
       when findAssociated(attr, attrs) matches just(attrTy) ->
       foldr(\ nt::String rest::String ->
               "Type " ++ accessRelationName(nameToNonterminalType(nt), attr) ++
               "   " ++ nameToNonterminal(nt) ++ " -> " ++
               nameToNodeType(nt) ++ " -> " ++
               functorType(nameType(attrValTypeName), attrTy).pp ++
               " -> prop.\n" ++ rest,
             generateAccessRelations(rest, attrs), nts)
     | _ -> error("Impossible for a well-typed grammar")
     end;
}


function generateLocalAccessRelations
String ::= localAttrs::[(String, [(String, Type)])] prods::[(String, Type)]
{
  return
     case localAttrs of
     | [] -> ""
     | (attr, [])::rest ->
       generateLocalAccessRelations(rest, prods)
     | (attr, (prod, attrTy)::tl)::rest
       when findAssociated(prod, prods) matches just(prodTy) ->
       "Type " ++ localAccessRelationName(prodTy.resultType, attr, prod) ++
       "   " ++ prodTy.resultType.pp ++ " -> " ++
       typeToNodeType(prodTy.resultType) ++ " -> " ++
       functorType(nameType(attrValTypeName), attrTy).pp ++
       " -> prop.\n" ++
       generateLocalAccessRelations((attr, tl)::rest, prods)
     | _ -> error("Impossible for a well-typed grammar")
     end;
}


function generateInheritedInformation
String ::= inheritedAttrs::[String]
{
  return
     case inheritedAttrs of
     | [] -> ""
     | attr::rest ->
       "Type $" ++ attr ++ "$_is_inherited   prop.\n" ++
       generateInheritedInformation(rest)
     end;
}


function generateStructureEqFull
String ::= nonterminals::[String]
{
  return
     case nonterminals of
     | [] -> ""
     | nt::rest ->
       let ntName::String = nameToNonterminal(nt) in
           "Type " ++ typeToStructureEqName(nameType(ntName)) ++
           "   " ++ ntName ++ " -> " ++ ntName ++ " -> prop.\n" ++
           generateStructureEqFull(rest)
       end
     end;
}


function generateStructureEqComponent
String ::= prods::[(String, Type)] component::String
{
  --Need to sort before grouping to get all prods of type grouped together
  local sorted::[(String, Type)] =
        sortBy(\ p1::(String, Type) p2::(String, Type) ->
                 p1.2.headTypeName <= p2.2.headTypeName,
               prods);
  local grouped::[[(String, Type)]] =
        groupBy(\ p1::(String, Type) p2::(String, Type) ->
                  tysEqual(p1.2.resultType, p2.2.resultType), sorted);
  return
     implode(".\n",
        map(\ g::[(String, Type)] ->
              generateStructureEqComponentGroup(g, component),
            grouped)) ++ ".\n";
}
function generateStructureEqComponentGroup
String ::= group::[(String, Type)] component::String
{
  local nt::Type =
        case group of
        | [] -> error("Impossible if called after grouping")
        | (_, prodTy)::_ -> prodTy.resultType
        end;
  return
     "Define " ++ typeToStructureEqName(nt) ++ "__" ++ component ++
     " : " ++ nt.pp ++ " -> " ++ nt.pp ++ " -> prop by\n" ++
     implode(";\n",
         map(\ p::(String, Type) ->
               generateStructureEqComponentBodies(p.1, p.2,
                  nt, component), group));
}
function generateStructureEqComponentBodies
String ::= prod::String prodTy::Type nt::Type component::String
{
  local children::[(String, String, Type)] =
        foldr(\ t::Type rest::([(String, String, Type)], [String]) ->
                let n1::String =
                    makeUniqueNameFromTy(t, rest.2) in
                let n2::String =
                    makeUniqueNameFromTy(t, n1::rest.2) in
                  if tyIsNonterminal(t)
                  then ((n1, n2, t)::rest.1, n1::n2::rest.2)
                  else ((n1, n1, t)::rest.1, n1::rest.2)
                end end,
              ([], []), prodTy.argumentTypes).1;
  local clauseHead::String =
        typeToStructureEqName(nt) ++ "__" ++ component ++ " " ++
        "(" ++ nameToProd(prod) ++ " " ++
            implode(" ", map(\ p::(String, String, Type) ->
                               p.1, children)) ++ ") " ++
        "(" ++ nameToProd(prod) ++ " " ++
            implode(" ", map(\ p::(String, String, Type) ->
                               p.2, children)) ++ ")";
  local clauseBody::String =
        foldr(\ p::(String, String, Type) rest::String ->
                if tyIsNonterminal(p.3)
                then typeToStructureEqName(p.3) ++
                     " " ++ p.1 ++ " " ++ p.2 ++
                     --Only include an and if rest isn't empty
                     if rest == ""
                     then ""
                     else " /\\\n     " ++ rest
                else rest,
              "", children);
  return
     if clauseBody == ""
     then "  " ++ clauseHead
     else "  " ++ clauseHead ++ " :=\n     " ++ clauseBody;
}


function generateContents
String ::= nonterminals::[String] attrs::[(String, Type)]
           --(attribute name, [nonterminal name])
           attrOccurrences::[(String, [String])]
           inheritedAttrs::[String]
           --(local name, [(production name, attr type)])
           localAttrs::[(String, [(String, Type)])]
           prods::[(String, Type)]
           componentName::String
{
  return
     generateNonterminalTypes(nonterminals) ++ "\n" ++
     generateProductions(prods) ++ "\n\n" ++
     generateNodeTypes(nonterminals) ++ "\n\n" ++
     "Kind $node_tree   type.\n\n" ++
     generateNodeTreeConstructors(nonterminals) ++ "\n\n" ++
     generateAccessRelations(attrOccurrences, attrs) ++ "\n" ++
     generateLocalAccessRelations(localAttrs, prods) ++ "\n\n" ++
     generateInheritedInformation(inheritedAttrs) ++ "\n\n" ++
     generateStructureEqFull(nonterminals) ++ "\n" ++
     generateStructureEqComponent(prods, componentName) ++ "\n";
}



function main
IOVal<Integer> ::= largs::[String] ioin::IO
{
  local nonterminals::[String] = ["A", "B", "C"];
  local attrs::[(String, Type)] =
        [ ( "env",
            functorType(nameType("list"),
               functorType(
                  functorType(nameType("$pair"),
                     functorType(nameType("list"),
                                 nameType("$char"))),
                  nameType("integer"))) ),
          ( "intVal", nameType("integer") ),
          ( "boolVal", nameType("bool") ),
          ( "env_out",
            functorType(nameType("list"),
               functorType(
                  functorType(nameType("$pair"),
                     functorType(nameType("list"),
                                 nameType("$char"))),
                  nameType("integer"))) ) ];
  local attrOccurrences::[(String, [String])] =
        [ ( "env", ["A", "B", "C"] ),
          ( "intVal", ["A"] ),
          ( "boolVal", ["B"] ),
          ( "env_out", ["C"] ) ];
  local inheritedAttrs::[String] = ["env"];
  local localAttrs::[(String, [(String, Type)])] =
        [ ( "subWhile",
            [ ( "while",
                functorType(
                   functorType(nameType("$pair"),
                      nameType("nt_C")),
                   nameType("$node_tree")) ) ] ) ];
  local prods::[(String, Type)] =
         [ ( "plus",
             arrowType(nameType("nt_A"),
             arrowType(nameType("nt_A"),
                       nameType("nt_A"))) ),
           ( "num",
             arrowType(nameType("integer"),
                       nameType("nt_A")) ),
           ( "name",
             arrowType(functorType(nameType("list"),
                                   nameType("$char")),
                       nameType("nt_A")) ),
           ( "greater",
             arrowType(nameType("nt_A"),
             arrowType(nameType("nt_A"),
                       nameType("nt_B"))) ),
           ( "equal",
             arrowType(nameType("nt_A"),
             arrowType(nameType("nt_A"),
                       nameType("nt_B"))) ),
           ( "and",
             arrowType(nameType("nt_B"),
             arrowType(nameType("nt_B"),
                       nameType("nt_B"))) ),
           ( "or",
             arrowType(nameType("nt_B"),
             arrowType(nameType("nt_B"),
                       nameType("nt_B"))) ),
           ( "bTrue",
             nameType("nt_B") ),
           ( "bFalse",
             nameType("nt_B") ),
           ( "noop",
             nameType("nt_C") ),
           ( "seq",
             arrowType(nameType("nt_C"),
             arrowType(nameType("nt_C"),
                       nameType("nt_C"))) ),
           ( "assign",
             arrowType(functorType(nameType("list"),
                                   nameType("$char")),
             arrowType(nameType("nt_A"),
                       nameType("nt_C"))) ),
           ( "ifThenElse",
             arrowType(nameType("nt_B"),
             arrowType(nameType("nt_C"),
             arrowType(nameType("nt_C"),
                       nameType("nt_C")))) ),
           ( "while",
             arrowType(nameType("nt_B"),
             arrowType(nameType("nt_C"),
                       nameType("nt_C"))) ) ];
  local componentName::String = "host";
  local contents::String =
        generateContents(
           nonterminals, attrs, attrOccurrences, inheritedAttrs,
           localAttrs, prods, componentName);
  local out::IO = print(contents, ioin);
  return ioval(out, 0);
}

