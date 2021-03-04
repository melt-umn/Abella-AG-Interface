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

global appendName::String = "$append";

global orName::String = "$or_bool";
global andName::String = "$and_bool";
global notName::String = "$not_bool";
global trueName::String = "$btrue";
global falseName::String = "$bfalse";




{-
  When we're translating things, we're going to end up taking some of
  the names we find and change them.  To keep this consistent, we can
  use functions to do this.
-}

function treeToStructureName
String ::= treeName::String
{
  return "$" ++ treeName ++ "_Tm";
}

function treeToNodeName
String ::= treeName::String
{
  return "$" ++ treeName ++ "_Node";
}

function accessToAccessName
String ::= treeName::String attrName::String
{
  return "$" ++ treeName ++ "_DOT_" ++ attrName;
}

function accessRelationName
String ::= treeTy::Type attrName::String
{
  return "$access__" ++ attrName ++ "__" ++ treeTy.pp;
}

function wpdTypeName
String ::= treeTy::Type
{
  return "$wpd_" ++ treeTy.pp;
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

abstract production attrAccessNewPremise
top::NewPremise ::= tree::String attr::String
{
  local treeNode::Term = nameTerm(treeToNodeName(tree), nothing());
  local valueName::Term = nameTerm(accessToAccessName(tree, attr), nothing());
  local accessRel::Term = nameTerm(accessRelationName(ty, attr), nothing());
  top.translation =
     case findty of
     | just(just([_])) ->
       -- <accessRel> <treeNode> (<attributeExistsName> <valueName>)
       termMetaterm(
          buildApplication(accessRel, [treeNode, valueName]),
          emptyRestriction())
     | just(just(_)) -> trueMetaterm() --no type, so can't actually translate this
     | _ -> trueMetaterm() --error case, but I think it is caught elsewhere
     end;

  local findty::Maybe<Maybe<[Type]>> = findAssociated(tree, top.boundVarsHere);
  local ty::Type =
        case findty of
        | just(just([ty])) -> ty
        | _ -> error("Shouldn't access local ty if local findty is " ++
                     "the wrong shape (attrAccessNewPremise)")
        end;

  top.addPremiseHere = containsBy(\ x::String y::String -> x == y, tree, top.currentNames);

  top.isEq =
     case top.eqTest of
     | attrAccessNewPremise(t, a) -> t == tree && a == attr
     | _ -> false
     end;

  --We don't want to add the name if we can't find a type for it.
  top.newBindingNames =
     case findty of
     | just(just(_)) -> [pair(accessToAccessName(tree, attr), nothing())]
     | _ -> []
     end;
  top.removeBindingNames = [];
}


abstract production wpdNewPremise
top::NewPremise ::= tree::String
{
  local wpdRel::Term = nameTerm(wpdTypeName(ty), nothing());
  local treeStructure::Term = nameTerm(treeToStructureName(tree), nothing());
  local treeNode::Term = nameTerm(treeToNodeName(tree), nothing());
  top.translation =
     case findty of
     | just(just([_])) ->
       -- <wpdRel> <treeStructure> <treeNode>
       termMetaterm(
          buildApplication(wpdRel, [treeStructure, treeNode]),
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
     | just(just([_])) -> [pair(treeToStructureName(tree), just(ty)),
                           pair(treeToNodeName(tree), just(nodeTreeType))]
     | _ -> []
     end;
  top.removeBindingNames =
     case findty of
     | just(just([_])) -> [tree]
     | _ -> []
     end;
}

