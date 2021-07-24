grammar interface_:toAbella:abstractSyntax;



--Build a term for an expanded node tree (ntr_treeTy Node ChildList)
function buildNodeTree
Term ::= nodeName::String childListName::String treeTy::Type
{
  return
     buildApplication(
        nameTerm(nodeTreeConstructorName(treeTy), nothing()),
        [ nameTerm(nodeName, nothing()),
          nameTerm(childListName, nothing()) ]);
}



function ordinalToCharConstructor
String ::= ord::Integer
{
  return "$c_" ++ toString(ord);
}




function integerToIntegerTerm
Term ::= i::Integer
{
  return if i >= 0
         then buildApplication(nameTerm("$posInt", nothing()),
                               [integerToNatTerm(i)])
         else buildApplication(nameTerm("$negSuccInt", nothing()),
                               [integerToNatTerm((i * -1) - 1)]);
}

function integerToNatTerm
Term ::= i::Integer
{
  return if i == 0
         then nameTerm(natZeroName, nothing())
         else buildApplication(nameTerm(natSuccName, nothing()),
                               [integerToNatTerm(i-1)]);
}




{-
  The NewPremise nonterminal is for new premises that we are going to
  add to the theorem we are defining based on how we translate
  something else in the theorem.

  Why don't we just generate the metaterm we want to add directly?  I
  think there are two reasons:
  1. I think this makes it easier to filter out any duplicates.  For
     example, if we access t.a twice, we will generate a new premise
     for the attribute access twice.  However, we only want to put
     this in once, so we can filter them out by testing equality on
     these.
  2. If I change the translation, I can change it here, rather than
     tracking it down elsewhere in the code base.
-}

nonterminal NewPremise with
   translation<Metaterm>,
   currentNames, boundVarsHere, addPremiseHere,
   eqTest<NewPremise>, isEq,
   newBindingNames, removeBindingNames,
   gatheredDecoratedTrees, knownNames;

--This is so we can figure out if this new premise should be added in
--   one place or elsewhere, based on the names that are bound
inherited attribute currentNames::[String];
inherited attribute boundVarsHere::[Pair<String Maybe<[Type]>>];
synthesized attribute addPremiseHere::Boolean;

--Our new premises come with some new names which need to be bound when the premise is added
synthesized attribute newBindingNames::[Pair<String Maybe<Type>>];
--These new names will replace some old names
synthesized attribute removeBindingNames::[String];


abstract production wpdNewPremise
top::NewPremise ::= tree::String
{
  local wpdRel::Term = nameTerm(wpdTypeName(ty), nothing());
  local treeStructure::Term = nameTerm(tree, nothing());
  local nodeName::String =
        makeUniqueNameFromBase(treeToNodeName(tree), top.knownNames);
  local treeNode::Term = nameTerm(nodeName, nothing());
  local childListName::String =
        makeUniqueNameFromBase(treeToChildListName(tree), top.knownNames);
  local treeChildList::Term = nameTerm(childListName, nothing());
  local nodeTree::Term =
        buildApplication(nameTerm(nodeTreeConstructorName(ty), nothing()),
                         [treeNode, treeChildList]);
  top.translation =
     case findty of
     | just(just([_])) ->
       -- <wpdRel> <treeStructure> <treeNode>
       termMetaterm(
          buildApplication(wpdRel, [treeStructure, nodeTree]),
          emptyRestriction())
     | just(just(_)) -> trueMetaterm() --no type, so can't actually translate this
     | _ -> trueMetaterm() --error case, but I think it is caught elsewhere
     end;

  top.gatheredDecoratedTrees := [(tree, nodeName, new(treeChildList))];

  local findty::Maybe<Maybe<[Type]>> = findAssociated(tree, top.boundVarsHere);
  local ty::Type =
        case findty of
        | just(just([ty])) -> ty
        | _ -> error("Shouldn't access local ty if local findty is " ++
                     "the wrong shape (wpdNewPremise)")
        end;

  top.addPremiseHere = containsBy(\ x::String y::String -> x == y, tree, top.currentNames);

  top.isEq =
     case top.eqTest of
     | wpdNewPremise(t) -> t == tree
     | _ -> false
     end;

  --We don't want to add these names if we can't find a type for them.
  top.newBindingNames =
     case findty of
     | just(just([_])) -> [(tree, just(ty)),
                           (nodeName, nothing()),
                           (childListName, nothing())]
     | _ -> []
     end;
  top.removeBindingNames =
     case findty of
     | just(just([_])) -> [tree]
     | _ -> []
     end;
}






function extensible_theorem_name
String ::= name::String
{
  return "$Extensible_Theorem_" ++ name;
}



{-
  This builds the metaterm for an extensible theorem based on the
  original theorem statement and the productions it works on.

  thms:  [(original (translated) metaterms for the mutual theorems,
           name of the tree on which we are doing induction,
           type of the tree on which we are doing induction,
           production order for the type of tree on which we are doing induction)]
  usedNames:  Names which were used in the original theorem statement,
              which we can't use when generating children
  allProds:  All the productions we know
  localAttrs:  All the local attributes we know
-}
function buildExtensibleTheoremBody
Metaterm ::= thms::[(Metaterm, String, Type, [String])]
             usedNames::[String] allProds::[(String, Type)]
             localAttrs::[(String, [(String, Type)])]
             silverContext::Decorated SilverContext
{
  return buildAllTheoremBodies(thms, thms, usedNames, allProds,
                               localAttrs, silverContext);
}

--We need to know all the theorems to make IH's for the body, so we
--   have the list we are walking through and the full, original list
function buildAllTheoremBodies
Metaterm ::= walkThroughThms::[(Metaterm, String, Type, [String])]
             allThms::[(Metaterm, String, Type, [String])]
             usedNames::[String] allProds::[(String, Type)]
             localAttrs::[(String, [(String, Type)])]
             silverContext::Decorated SilverContext
{
  local thm::(Metaterm, String, Type, [String]) = head(walkThroughThms);
  local body::Metaterm =
        case decorate thm.1 with {silverContext = silverContext;} of
        | bindingMetaterm(_, _, body) -> body
        | _ -> error("Can't have anything but binding metaterm to start")
        end;
  body.silverContext = silverContext;
  local thisThm::Metaterm =
        case findAssociated(thm.2, body.gatheredDecoratedTrees) of
        | just((nodeName, tm)) ->
          case decorate tm with {silverContext = silverContext;} of
          | nameTerm(childList, _) ->
            buildProdBodies(thm.4, thm.1, thm.2, nodeName, childList, thm.3,
                            allThms, usedNames, allProds, localAttrs, silverContext)
          | _ -> error("Tree must be bound at root")
          end
        | _ -> error("Tree must be bound at root")
        end;

  return
     case walkThroughThms of
     | [] -> error("Should not be called with an empty list of thms")
     | [hd] -> thisThm
     | hd::tl ->
       andMetaterm(thisThm,
          buildAllTheoremBodies(tl, allThms, usedNames,
                                allProds, localAttrs, silverContext))
     end;
}



--Walk through the list of productions and fill them in, and adding in
--their inductive hypotheses and premises for the current case
function buildProdBodies
Metaterm ::= prods::[String] original::Metaterm
             treeName::String treeNode::String treeCL::String treeTy::Type
             allThms::[(Metaterm, String, Type, [String])]
             usedNames::[String] allProds::[(String, Type)]
             localAttrs::[(String, [(String, Type)])]
             silverContext::Decorated SilverContext
{
  original.silverContext = silverContext;
  local prodName::String = head(prods);
  --The productions referenced in WPD relations had better exist
  local prodTy::Type = findAssociated(prodName, allProds).fromJust;
  local children::[(Type, String, String, String)] =
        buildChildNames(prodTy.argumentTypes, usedNames);
  local newTree::Term =
        buildApplication(
           nameTerm(nameToProd(prodName), nothing()),
           map(\ p::(Type, String, String, String) ->
                 nameTerm(p.2, nothing()), children));
  local newChildList::Term =
        foldr(\ p::(Type, String, String, String) rest::Term ->
                if tyIsNonterminal(p.1)
                then consTerm(
                        buildNodeTree(p.3, p.4, p.1),
                        rest)
                else rest,
              nilTerm(), children);
  local newNodeTree::Term =
        buildApplication(
           nameTerm(nodeTreeConstructorName(treeTy), nothing()),
           [nameTerm(treeNode, nothing()), newChildList]);
  local originalBinder::Binder =
        case original of
        | bindingMetaterm(binder, bindings, body) -> binder
        | _ -> error("Should not have anything but a binding to start")
        end;
  local originalBindings::[(String, Maybe<Type>)] =
        case original of
        | bindingMetaterm(binder, bindings, body) -> bindings
        | _ -> error("Should not have anything but a binding to start")
        end;
  local newBindings::[(String, Maybe<Type>)] =
        flatMap(\ p::(Type, String, String, String) ->
                  if tyIsNonterminal(p.1)
                  then [(p.2, just(p.1)),
                        (p.3, nothing()),
                        (p.4, nothing())]
                  else [(p.2, just(p.1))], children) ++
          removeBy(\ p1::(String, Maybe<Type>) p2::(String, Maybe<Type>) ->
                     p1.1 == p2.1,
                   (treeCL, nothing()), originalBindings);
  local originalBody::Metaterm =
        case original of
        | bindingMetaterm(binder, bindings, body) -> body
        | _ -> error("Should not have anything but a binding to start")
        end;
  --Remove original WPD assumption
  local copyOriginalBody::Metaterm = originalBody;
  copyOriginalBody.removeWPDTree = treeName;
  copyOriginalBody.silverContext = silverContext;
  local noWPD::Metaterm = copyOriginalBody.removedWPD;
  --Replace the original tree and child list
   --noWPD.replaceName = treeToStructureName(treeName);
   --noWPD.replaceTerm = newTree;
  local replaceTree::Metaterm = noWPD; --.replaced;
  replaceTree.replaceName = treeCL;
  replaceTree.replaceTerm = newChildList;
  replaceTree.silverContext = silverContext;
  local replaceTreeNode::Metaterm = replaceTree.replaced;
  --
  local thisCase::[Metaterm] =
          --Show user the structure
        [ termMetaterm(
             buildApplication(
                nameTerm(typeToStructureEqName(prodTy.resultType), nothing()),
                [nameTerm(treeName, nothing()),
                 newTree]),
             emptyRestriction()),
          --WPD nonterminal relation for root
          --Add back after removal to get just the name, not the structure, in it
          termMetaterm(
             buildApplication(nameTerm(wpdTypeName(treeTy), nothing()),
                              [nameTerm(treeName, nothing()),
                               newNodeTree]),
             emptyRestriction()),
          --WPD node relation for root
          termMetaterm(
             buildApplication(nameTerm(wpdNodeTypeName(treeTy), nothing()),
                              [newTree, newNodeTree]),
             emptyRestriction()) ] ++
          --WPD nonterminal relations/is relations for children
          foldr(\ p::(Type, String, String, String) rest::[Metaterm] ->
                  if tyIsNonterminal(p.1)
                  then termMetaterm(
                          buildApplication(
                             nameTerm(wpdTypeName(p.1), nothing()),
                             [nameTerm(p.2, nothing()),
                              buildNodeTree(p.3, p.4, p.1)]),
                          emptyRestriction())::rest
                  else case p.1.isRelation of
                       | right(isRel) ->
                         termMetaterm(
                            buildApplication(isRel,
                                             [nameTerm(p.2, nothing())]),
                            emptyRestriction())::rest
                       | left(err) ->
                         error("Could not generate is relation:\n" ++ err)
                       end,
                [], children);
  --fake IHs remove WPD nonterminal relation, and replace original tree with child tree
  local prodLocalAttrs::[(String, Type)] =
        findProdLocalAttrs(prodName, localAttrs);
  local fakeIHs::[Metaterm] =
        buildFakeIHs(allThms, children, prodName, prodTy.resultType,
                     nameTerm(treeNode, nothing()),
                     prodLocalAttrs,
                     usedNames ++
                     flatMap(\ p::(Type, String, String, String) ->
                               [p.2, p.3, p.4], children),
                     silverContext);
  local currentStep::Metaterm =
        bindingMetaterm(originalBinder, newBindings,
           foldr(\ m::Metaterm rest::Metaterm ->
                   impliesMetaterm(m, rest),
                 replaceTreeNode, fakeIHs ++ thisCase));
  return
     case prods of
     | [] -> error("Should not call buildProdBodies with an empty list")
     | [_] -> currentStep
     | _::t ->
       andMetaterm(currentStep,
          buildProdBodies(t, original, treeName, treeNode, treeCL, treeTy,
                          allThms, usedNames, allProds, localAttrs, silverContext))
     end;
}

function buildFakeIHs
[Metaterm] ::= thms::[(Metaterm, String, Type, [String])]
               children::[(Type, String, String, String)] prod::String
               rootTy::Type rootNode::Term
               --local name, local type
               relevantLocalAttrs::[(String, Type)]
               usedNames::[String]
               silverContext::Decorated SilverContext
{
  local first::(Metaterm, String, Type, [String]) = head(thms);
  local treeTy::Type = first.3;
  local treeName::String = first.2;
  local treeNode::String =
        case findAssociated(first.2, originalBody.gatheredDecoratedTrees) of
        | just((nodeName, tm)) ->
          case decorate tm with {silverContext = silverContext;} of
          | nameTerm(childList, _) -> nodeName
          | _ -> error("Tree must be bound at root")
          end
        | _ -> error("Tree must be bound at root")
        end;
  local treeCL::String =
        case findAssociated(first.2, originalBody.gatheredDecoratedTrees) of
        | just((nodeName, tm)) ->
          case decorate tm with {silverContext = silverContext;} of
          | nameTerm(childList, _) -> childList
          | _ -> error("Tree must be bound at root")
          end
        | _ -> error("Tree must be bound at root")
        end;
  local original::Metaterm = first.1;
  original.silverContext = silverContext;
  local originalBinder::Binder =
        case original of
        | bindingMetaterm(binder, bindings, body) -> binder
        | _ -> error("Should not have anything but a binding to start")
        end;
  local originalBindings::[(String, Maybe<Type>)] =
        case original of
        | bindingMetaterm(binder, bindings, body) -> bindings
        | _ -> error("Should not have anything but a binding to start")
        end;
  local originalBody::Metaterm =
        case original of
        | bindingMetaterm(binder, bindings, body) -> body
        | _ -> error("Should not have anything but a binding to start")
        end;
  originalBody.removeWPDTree = treeName;
  originalBody.silverContext = silverContext;
  local removedWPD::Metaterm = originalBody.removedWPD;
  local removedBindings::[(String, Maybe<Type>)] =
        removeAllBy(\ p1::(String, Maybe<Type>) p2::(String, Maybe<Type>) ->
                      p1.fst == p2.fst,
                    [(treeName, nothing()),
                     (treeNode, nothing()),
                     (treeCL, nothing())],
                    originalBindings);
  --Hypotheses for the children of the production
  local firstIHs::[Metaterm] =
        foldr(\ p::(Type, String, String, String) rest::[Metaterm] ->
                if tysEqual(p.1, treeTy)
                then if null(removedBindings)
                     then --replace tree, tree node, and tree child list
                          decorate
                             (decorate
                                (decorate removedWPD with
                                    {replaceName = treeCL;
                                     replaceTerm = nameTerm(p.4, nothing());
                                     silverContext = silverContext;}.replaced)
                              with {replaceName = treeNode;
                                    replaceTerm = nameTerm(p.3, nothing());
                                     silverContext = silverContext;}.replaced)
                          with {replaceName = treeName;
                                replaceTerm = nameTerm(p.2, nothing());
                                silverContext = silverContext;}.replaced::rest
                     else bindingMetaterm(
                             originalBinder,
                             removedBindings,
                                --replace tree, tree node, and tree child list
                                decorate
                                   (decorate
                                      (decorate removedWPD with
                                          {replaceName = treeCL;
                                           replaceTerm = nameTerm(p.4, nothing());
                                           silverContext = silverContext;}.replaced)
                                    with {replaceName = treeNode;
                                          replaceTerm = nameTerm(p.3, nothing());
                                          silverContext = silverContext;}.replaced)
                                with {replaceName = treeName;
                                      replaceTerm = nameTerm(p.2, nothing());
                                      silverContext = silverContext;}.replaced)::rest
                else rest,
              [], children);
  --Hypotheses for the local attributes which occur on the given production
  local localIHs::[Metaterm] =
        foldr(\ p::(String, Type) rest::[Metaterm] ->
                if tysEqual(p.2, treeTy)
                then let newName::String =
                         makeUniqueNameFromBase(capitalizeString(p.1), usedNames) in
                     let newNodeName::String =
                         makeUniqueNameFromBase(treeToNodeName(newName), usedNames) in
                     let newCLName::String =
                         makeUniqueNameFromBase(treeToChildListName(newName), usedNames) in
                     bindingMetaterm(
                        originalBinder,
                        removedBindings ++
                           [(newName, nothing()),
                            (newNodeName, nothing()),
                            (newCLName, nothing())],
                        --Add accessing the local with a value as a premise
                        impliesMetaterm(
                           termMetaterm(
                              buildApplication(
                                 nameTerm(
                                    localAccessRelationName(rootTy, p.1, prod),
                                    nothing()),
                                 [nameTerm(treeName, nothing()),
                                  rootNode,
                                  buildApplication(
                                     nameTerm(attributeExistsName, nothing()),
                                     [buildApplication(
                                         nameTerm(pairConstructorName, nothing()),
                                         [nameTerm(newName, nothing()),
                                          buildApplication(
                                             nameTerm(nodeTreeConstructorName(p.2), nothing()),
                                             [nameTerm(newNodeName, nothing()),
                                              nameTerm(newCLName, nothing())])
                                         ])
                                     ])
                                 ]),
                              emptyRestriction()),
                           --replace tree, tree node, and tree child list
                           decorate
                              (decorate
                                 (decorate removedWPD with
                                     {replaceName = treeCL;
                                      replaceTerm = nameTerm(newCLName,
                                                             nothing());
                                      silverContext = silverContext;}.replaced)
                               with {replaceName = treeNode;
                                     replaceTerm = nameTerm(newNodeName,
                                                            nothing());
                                     silverContext = silverContext;}.replaced)
                           with {replaceName = treeName;
                                 replaceTerm = nameTerm(newName,
                                                        nothing());
                                 silverContext = silverContext;}.replaced))::rest
                     end end end
                else rest,
              [], relevantLocalAttrs);

  return
     case thms of
     | [] -> []
     | hd::tl ->
       firstIHs ++ localIHs ++
       buildFakeIHs(tl, children, prod, rootTy, rootNode,
                    relevantLocalAttrs, usedNames, silverContext)
     end;
}


--Build names for each element of tys which do not occur in usedNames
--Produces a name, a node name, and a child list name, whether needed or not
function buildChildNames
[(Type, String, String, String)] ::= tys::[Type] usedNames::[String]
{
  local uniqueName::String = makeUniqueNameFromTy(head(tys), usedNames);
  return
     case tys of
     | [] -> []
     | h::t ->
       let name::String = makeUniqueNameFromTy(head(tys), usedNames) in
       let nodeName::String =
           makeUniqueNameFromBase(treeToNodeName(name), usedNames) in
       let childListName::String =
           makeUniqueNameFromBase(treeToChildListName(name), usedNames) in
           (h, name, nodeName, childListName)::
           buildChildNames(t, name::nodeName::childListName::usedNames)
       end end end
     end;
}


--Make a name that isn't in usedNames, based on the type
function makeUniqueNameFromTy
String ::= ty::Type usedNames::[String]
{
  local base::String =
        if tyIsNonterminal(ty)
        then substring(3, 4, ty.headTypeName.fromJust)
        else case ty.headTypeName of
             | nothing() -> "A"
             | just("integer") -> "N"
             | just(str) ->
               if isAlpha(substring(0, 1, str))
               then --capitalize the first character
                    charsToString([head(stringToChars(substring(0, 1, str))) - 32])
               else substring(0, 1, str)
             end;
  return
     if contains(base, usedNames)
     then makeUniqueName(base, 1, usedNames)
     else base;
}


--Make anem that isn't in usedNames, starting with the given base
function makeUniqueNameFromBase
String ::= base::String usedNames::[String]
{
  return
     if contains(base, usedNames)
     then makeUniqueName(base, 1, usedNames)
     else base;
}


--Make a name starting with base that isn't in usedNames
function makeUniqueName
String ::= base::String index::Integer usedNames::[String]
{
  return
     if contains(base ++ toString(index), usedNames)
     then makeUniqueName(base, index + 1, usedNames)
     else base ++ toString(index);
}

