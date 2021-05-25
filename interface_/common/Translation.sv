grammar interface_:common;

{-
  This file provides some common functions for name translation and
  checking, such as translating between Abella and user-facing names
  and checking if names have these forms.
-}


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



--Decorated Trees
function treeToNodeName
String ::= treeName::String
{
  return "$Node_" ++ treeName;
}

function treeToChildListName
String ::= treeName::String
{
  return "$ChildList_" ++ treeName;
}

function treeToNodeTreeName
String ::= treeName::String
{
  return "$Ntr_" ++ treeName;
}

function nodeTreeConstructorName
String ::= treeTy::Type
{
  return "$ntr_" ++ treeTy.pp;
}
function isNodeTreeConstructorName
Boolean ::= s::String
{
  return startsWith("$ntr_", s);
}


--Attribute Access
function accessToAccessName
String ::= treeName::String attrName::String
{
  return "$" ++ treeName ++ "_DOT_" ++ attrName;
}
function accessRelationName
String ::= treeTy::Type attrName::String
{
  return "$access_$_" ++ attrName ++ "_$_" ++ treeTy.pp;
}
function isAccessRelation
Boolean ::= str::String
{
  return startsWith("$access_$_", str);
}
function accessRelationToAttr
String ::= str::String
{
  local firstSplit::Integer = indexOf("_$_", str);
  local lastSplit::Integer = lastIndexOf("_$_", str);
  return substring(firstSplit + 3, lastSplit, str);
}
function accessRelationToType
String ::= str::String
{
  local lastSplit::Integer = lastIndexOf("_$_", str);
  return substring(lastSplit + 3, length(str), str);
}


--Access Theorems
function accessUniqueThm
String ::= attr::String ty::String
{
  return "$access_$_" ++ attr ++ "_$_" ++ ty ++ "__unique";
}
function accessIsThm
String ::= attr::String ty::String
{
  return "$access_$_" ++ attr ++ "_$_" ++ ty ++ "__is";
}


--Local Attributes
function isLocalAccessRelation
Boolean ::= s::String
{
  return startsWith("$local_access_$_", s);
}
function localAccessRelationName
String ::= treeTy::Type attrName::String prodName::String
{
  --$local_access_$_<prod>_$_<name>_$_<type>
  return "$local_access_$_" ++ nameToProd(prodName) ++ "_$_" ++
         attrName ++ "_$_" ++ treeTy.pp;
}
function localAccessToProd
String ::= s::String
{
  --$local_access_$_<prod>_$_<name>_$_<type>
  local tailStr::String = substring(16, length(s), s);
  return prodToName(substring(0, indexOf("_$_", tailStr), tailStr));
}
function localAccessToAttr
String ::= s::String
{
  --$local_access_$_<prod>_$_<name>_$_<type>
  local tailStr::String = substring(16, length(s), s);
  local midStr::String = substring(0, lastIndexOf("_$_", tailStr), tailStr);
  return substring(indexOf("_$_", midStr) + 3, length(midStr), midStr);
}
function localAccessToType
Type ::= s::String
{
  --$local_access_$_<prod>_$_<name>_$_<type>
  return nameType(substring(lastIndexOf("_$_", s) + 3, length(s), s));
}
function wpdNt_to_LocalAttrEq
String ::= prod::String attr::String ty::Type
{
  --$wpd__to__<prod>_local_<attr>__<ty>
  return "$wpd__to__" ++ prod ++ "_local_" ++ attr ++ "__" ++ ty.pp;
}
function localAccessUniqueThm
String ::= prod::String attr::String ty::String
{
  --$local_access_$_<$prod_prod>_$_<attr>_$_<ty>__unique
  return "$local_access_$_$prod_" ++ prod ++ "_$_" ++ attr ++ "_$_" ++ ty ++ "__unique";
}


--WPD Nonterminal
function wpdTypeName
String ::= treeTy::Type
{
  return "$wpd_" ++ treeTy.pp;
}
function isWpdTypeName
Boolean ::= rel::String
{
  return startsWith("$wpd_", rel) && !startsWith("$wpd_node_", rel);
}
function wpdNt_type
Type ::= rel::String
{
  --$wpd_<type name>
  return nameType(substring(5, length(rel), rel));
}
function wpdPrimaryComponent
String ::= prod::String builtTy::Type
{
  return "$wpd_" ++ builtTy.pp ++ "__" ++ prod;
}
function wpdComponentRelToComponentName
String ::= rel::String
{
  --$wpd_<type name>__<component>
  local index::Integer = lastIndexOf("__", rel);
  return substring(index + 2, length(rel), rel);
}

function wpdNodeTreeForm
String ::= ty::Type
{
  return "$wpd_" ++ ty.pp ++ "__ntr_" ++ ty.pp;
}


--WPD Node
function wpdNodeTypeName
String ::= treeTy::Type
{
  return "$wpd_node_" ++ treeTy.pp;
}
function isWPD_NodeRelName
Boolean ::= str::String
{
  return startsWith("$wpd_node_", str);
}
function wpdNode_type
Type ::= str::String
{
  --$wpd_node_<type name>
  return nameType(substring(10, length(str), str));
}


--Attribute Equations
function wpdNode_to_AttrEq
String ::= attr::String ty::Type
{
  return "$wpd_node__to__" ++ attr ++ "__" ++ ty.pp;
}
function wpdNt_to_AttrEq
String ::= attr::String ty::Type
{
  return "$wpd__to__" ++ attr ++ "__" ++ ty.pp;
}
function primaryComponent
String ::= attr::String ty::Type prod::String
{
  return "$" ++ attr ++ "__" ++ ty.pp ++ "__" ++ prod;
}


--Structure Equality
function typeToStructureEqName
String ::= ty::Type
{
  return "$structure_eq__" ++ ty.pp;
}
function isStructureEqName
Boolean ::= rel::String
{
  return startsWith("$structure_eq__", rel);
}
function structureEqToType
Type ::= s::String
{
  return nameType(substring(15, length(s), s));
}
function structureEqWPD
String ::= ty::Type
{
  return "$structure_eq__" ++ ty.pp ++ "__wpd";
}
function structureEqEqualTheorem
String ::= ty::Type
{
  return "$structure_eq__" ++ ty.pp ++ "__equal";
}
function typeToStructureEq_Symm
String ::= ty::Type
{
  return "$structure_eq__" ++ ty.pp ++ "__symm";
}
function structureEqProdComponent
String ::= prod::String
{
  return "$structure_eq__" ++ prod;
}
function structureEqExpansionTheorem
String ::= ty::Type component::String
{
  return "$structure_eq__" ++ ty.pp ++ "__" ++ component ++ "__expand";
}


--Productions
function isProd
Boolean ::= name::String
{
  return startsWith("$prod_", name);
}
function prodToName
String ::= prod::String
{
  --$prod_<name>
  return substring(6, length(prod), prod);
}
function nameToProd
String ::= s::String
{
  return "$prod_" ++ s;
}


--Functions
function isFun
Boolean ::= name::String
{
  return startsWith("$fun__", name);
}
function funToName
String ::= fun::String
{
  --$fun__<name>
  return substring(6, length(fun), fun);
}
function nameToFun
String ::= s::String
{
  return "$fun__" ++ s;
}

