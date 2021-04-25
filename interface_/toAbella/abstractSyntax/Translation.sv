grammar interface_:toAbella:abstractSyntax;


{-
  When we're translating things, we're going to end up needing the
  names of some constants that will be defined in Abella.  We will
  have those as globals here.
-}

global attributeExistsName::String = "$attr_ex";
global attributeNotExistsName::String = "$attr_no";

global nodeTreeName::String = "$node_tree";
global nodeTreeType::Type = nameType(nodeTreeName);

global natSuccName::String = "$succ";
global natZeroName::String = "$zero";

global integerAdditionName::String = "$plus_integer";
global integerSubtractionName::String = "$minus_integer";
global integerMultiplicationName::String = "$multiply_integer";
global integerDivisionName::String = "$divide_integer";
global integerModulusName::String = "$modulus_integer";
global integerNegateName::String = "$negate_integer";
global integerLessName::String = "$less_integer";
global integerLessEqName::String = "$lesseq_integer";
global integerGreaterName::String = "$greater_integer";
global integerGreaterEqName::String = "$greatereq_integer";

global stringType::Type =
       functorType(nameType("list"), nameType("$char"));

global appendName::String = "$append";

global pairConstructorName::String = "$pair_c";

global orName::String = "$or_bool";
global andName::String = "$and_bool";
global notName::String = "$not_bool";
global trueName::String = "$btrue";
global falseName::String = "$bfalse";



--Build a term for an expanded node tree (ntr_treeTy Node ChildList)
function buildNodeTree
Term ::= name::String treeTy::Type
{
  return
     buildApplication(
        nameTerm(nodeTreeConstructorName(treeTy), nothing()),
        [ nameTerm(treeToNodeName(name), nothing()),
          nameTerm(treeToChildListName(name), nothing()) ]);
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
   newBindingNames, removeBindingNames;

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
  local treeStructure::Term = nameTerm(treeToStructureName(tree), nothing());
  local treeNode::Term = nameTerm(treeToNodeName(tree), nothing());
  local treeChildList::Term = nameTerm(treeToChildListName(tree), nothing());
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
     | just(just([_])) -> [(treeToStructureName(tree), just(ty)),
                           (treeToNodeName(tree), nothing()),
                           (treeToChildListName(tree), nothing())]
     | _ -> []
     end;
  top.removeBindingNames =
     case findty of
     | just(just([_])) -> [tree]
     | _ -> []
     end;
}







{-
  This builds the metaterm for an extensible theorem based on the
  original theorem statement and the productions it works on.

  original:  The original (translated) metaterm
  treeName:  The name of the tree on which we are doing induction
  treeTy:  The type of the tree treename
  wpdRel:  The WPD nonterminal relation on which we are really doing
           induction (type it is for and production order)
  usedNames:  Names which were used in the original theorem statement,
              which we can't use when generating children
-}
function buildExtensibleTheoremBody
Metaterm ::= thms::[(Metaterm, String, Type, [String])]
             usedNames::[String] allProds::[(String, Type)]
{
  return buildAllTheoremBodies(thms, thms, usedNames, allProds);
}

--We need to know all the theorems to make IH's for the body, so we
--   have the list we are walking through and the full, original list
function buildAllTheoremBodies
Metaterm ::= walkThroughThms::[(Metaterm, String, Type, [String])]
             allThms::[(Metaterm, String, Type, [String])]
             usedNames::[String] allProds::[(String, Type)]
{
  local thm::(Metaterm, String, Type, [String]) = head(walkThroughThms);
  local thisThm::Metaterm =
        buildProdBodies(thm.4, thm.1, thm.2, thm.3, allThms, usedNames, allProds);

  return
     case walkThroughThms of
     | [] -> error("Should not be called with an empty list of thms")
     | [hd] -> thisThm
     | hd::tl ->
       andMetaterm(thisThm,
          buildAllTheoremBodies(tl, allThms, usedNames, allProds))
     end;
}



--Walk through the list of productions and fill them in, and adding in
--their inductive hypotheses and premises for the current case
function buildProdBodies
Metaterm ::= prods::[String] original::Metaterm treeName::String
             treeTy::Type allThms::[(Metaterm, String, Type, [String])]
             usedNames::[String] allProds::[(String, Type)]
{
  local prodName::String = head(prods);
  --The productions referenced in WPD relations had better exist
  local prodTy::Type = findAssociated(prodName, allProds).fromJust;
  local children::[(Type, String)] = buildChildNames(prodTy.argumentTypes, usedNames);
  local newTree::Term =
        buildApplication(
           nameTerm(nameToProd(prodName), nothing()),
           map(\ p::(Type, String) ->
                 nameTerm( if tyIsNonterminal(p.fst)
                           then treeToStructureName(p.snd)
                           else p.snd, nothing()), children));
  local newChildList::Term =
        foldr(\ p::(Type, String) rest::Term ->
                if tyIsNonterminal(p.fst)
                then consTerm(
                        buildNodeTree(p.snd, p.fst),
                        rest)
                else rest,
              nilTerm(), children);
  local newNodeTree::Term =
        buildApplication(
           nameTerm(nodeTreeConstructorName(treeTy), nothing()),
           [nameTerm(treeToNodeName(treeName), nothing()), newChildList]);
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
        flatMap(\ p::(Type, String) ->
                  if tyIsNonterminal(p.fst)
                  then [(treeToStructureName(p.snd), just(p.fst)),
                        (treeToNodeName(p.snd), nothing()),
                        (treeToChildListName(p.snd), nothing())]
                  else [(p.snd, just(p.fst))], children) ++
          removeBy(\ p1::(String, Maybe<Type>) p2::(String, Maybe<Type>) ->
                     p1.fst == p2.fst,
                   (treeToChildListName(treeName), nothing()), originalBindings);
  local originalBody::Metaterm =
        case original of
        | bindingMetaterm(binder, bindings, body) -> body
        | _ -> error("Should not have anything but a binding to start")
        end;
  --Remove original WPD assumption
  local copyOriginalBody::Metaterm = originalBody;
  copyOriginalBody.removeWPDTree = treeName;
  local noWPD::Metaterm = copyOriginalBody.removedWPD;
  --Replace the original tree and child list
   --noWPD.replaceName = treeToStructureName(treeName);
   --noWPD.replaceTerm = newTree;
  local replaceTree::Metaterm = noWPD; --.replaced;
  replaceTree.replaceName = treeToChildListName(treeName);
  replaceTree.replaceTerm = newChildList;
  local replaceTreeNode::Metaterm = replaceTree.replaced;
  --
  local thisCase::[Metaterm] =
          --Show user the structure
        [ termMetaterm(
             buildApplication(
                nameTerm(typeToStructureEqName(prodTy.resultType), nothing()),
                [nameTerm(treeToStructureName(treeName), nothing()),
                 newTree]),
             emptyRestriction()),
          --WPD nonterminal relation for root
          --Add back after removal to get just the name, not the structure, in it
          termMetaterm(
             buildApplication(nameTerm(wpdTypeName(treeTy), nothing()),
                              [nameTerm(treeToStructureName(treeName), nothing()),
                               newNodeTree]),
             emptyRestriction()),
          --WPD node relation for root
          termMetaterm(
             buildApplication(nameTerm(wpdNodeTypeName(treeTy), nothing()),
                              [newTree, newNodeTree]),
             emptyRestriction()) ] ++
          --WPD nonterminal relations/is relations for children
          foldr(\ p::(Type, String) rest::[Metaterm] ->
                  if tyIsNonterminal(p.fst)
                  then termMetaterm(
                          buildApplication(
                             nameTerm(wpdTypeName(p.fst), nothing()),
                             [nameTerm(treeToStructureName(p.snd), nothing()),
                              buildNodeTree(p.snd, p.fst)]),
                          emptyRestriction())::rest
                  else case p.fst.isRelation of
                       | right(isRel) ->
                         termMetaterm(
                            buildApplication(isRel,
                                             [nameTerm(p.snd, nothing())]),
                            emptyRestriction())::rest
                       | left(err) ->
                         error("Could not generate is relation:\n" ++ err)
                       end,
                [], children);
  --fake IHs remove WPD nonterminal relation, and replace original tree with child tree
  local fakeIHs::[Metaterm] =
        buildFakeIHs(allThms, children);
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
          buildProdBodies(t, original, treeName, treeTy, allThms, usedNames, allProds))
     end;
}

function buildFakeIHs
[Metaterm] ::= thms::[(Metaterm, String, Type, [String])]
               children::[(Type, String)]
{
  local first::(Metaterm, String, Type, [String]) = head(thms);
  local treeTy::Type = first.3;
  local treeName::String = first.2;
  local original::Metaterm = first.1;
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
  local removedWPD::Metaterm = originalBody.removedWPD;
  local removedBindings::[(String, Maybe<Type>)] =
        removeAllBy(\ p1::(String, Maybe<Type>) p2::(String, Maybe<Type>) ->
                      p1.fst == p2.fst,
                    [(treeToStructureName(treeName), nothing()),
                     (treeToNodeName(treeName), nothing()),
                     (treeToChildListName(treeName), nothing())],
                    originalBindings);
  local firstIHs::[Metaterm] =
        foldr(\ p::(Type, String) rest::[Metaterm] ->
                if tysEqual(p.fst, treeTy)
                then if null(removedBindings)
                     then --replace tree, tree node, and tree child list
                          decorate
                             (decorate
                                (decorate removedWPD with
                                    {replaceName = treeToChildListName(treeName);
                                     replaceTerm = nameTerm(treeToChildListName(p.snd),
                                                            nothing());}.replaced)
                              with {replaceName = treeToNodeName(treeName);
                                    replaceTerm = nameTerm(treeToNodeName(p.snd),
                                                           nothing());}.replaced)
                          with {replaceName = treeToStructureName(treeName);
                                replaceTerm = nameTerm(treeToStructureName(p.snd),
                                                       nothing());}.replaced::rest
                     else bindingMetaterm(
                             originalBinder,
                             removedBindings,
                                --replace tree, tree node, and tree child list
                                decorate
                                   (decorate
                                      (decorate removedWPD with
                                          {replaceName = treeToChildListName(treeName);
                                           replaceTerm = nameTerm(treeToChildListName(p.snd),
                                                                  nothing());}.replaced)
                                    with {replaceName = treeToNodeName(treeName);
                                          replaceTerm = nameTerm(treeToNodeName(p.snd),
                                                                 nothing());}.replaced)
                                with {replaceName = treeToStructureName(treeName);
                                      replaceTerm = nameTerm(treeToStructureName(p.snd),
                                                             nothing());}.replaced)::rest
                else rest,
              [], children);

  return
     case thms of
     | [] -> []
     | hd::tl -> firstIHs ++ buildFakeIHs(tl, children)
     end;
}


--Build names for each element of tys which do not occur in usedNames
function buildChildNames
[(Type, String)] ::= tys::[Type] usedNames::[String]
{
  local uniqueName::String = makeUniqueNameFromTy(head(tys), usedNames);
  return
     case tys of
     | [] -> []
     | h::t -> (h, makeUniqueNameFromTy(head(tys), usedNames))::
               buildChildNames(t, uniqueName::usedNames)
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


--Make a name starting with base that isn't in usedNames
function makeUniqueName
String ::= base::String index::Integer usedNames::[String]
{
  return
     if contains(base ++ toString(index), usedNames)
     then makeUniqueName(base, index + 1, usedNames)
     else base ++ toString(index);
}

