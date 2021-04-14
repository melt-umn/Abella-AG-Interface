grammar interface_:common;

{-
  This file provides some common functions for name translation and
  checking, such as translating between Abella and user-facing names
  and checking if names have these forms.
-}

--Decorated Trees
function treeToStructureName
String ::= treeName::String
{
  return "$Tm_" ++ treeName;
}
function isTreeStructureName
Boolean ::= str::String
{
  return startsWith("$Tm_", str);
}
function structureToTreeName
String ::= treeStructure::String
{
  return substring(4, length(treeStructure), treeStructure);
}

function treeToNodeName
String ::= treeName::String
{
  return "$Node_" ++ treeName;
}
function isTreeNodeName
Boolean ::= str::String
{
  return startsWith("$Node_", str);
}
function nodeToTreeName
String ::= treeName::String
{
  return substring(6, length(treeName), treeName);
}

function treeToChildListName
String ::= treeName::String
{
  return "$ChildList_" ++ treeName;
}
function isChildListName
Boolean ::= str::String
{
  return startsWith("$ChildList_", str);
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

--Productions
function isProd
Boolean ::= name::String
{
  return startsWith("prod_", name);
}

