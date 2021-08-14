grammar interface_:common:abstractSyntax;

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



--Nonterminals
function nameToNonterminalName
String ::= ntName::String
{
  return "$nt_" ++ colonsToEncoded(ntName);
}

function nameToColonNonterminalName
String ::= ntName::String
{
  return "$nt_" ++ encodedToColons(ntName);
}

function nameIsNonterminal
Boolean ::= name::String
{
  return startsWith("$nt_", name);
}

function nonterminalNameToName
String ::= ntName::String
{
  return encodedToColons(substring(4, length(ntName), ntName));
}


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
  return "$ntr_" ++ colonsToEncoded(treeTy.pp);
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
  return "$" ++ treeName ++ "_DOT_" ++ colonsToEncoded(attrName);
}
function accessRelationName
String ::= treeTy::Type attrName::String
{
  return "$access_$_" ++ colonsToEncoded(attrName) ++ "_$_" ++ colonsToEncoded(treeTy.pp);
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
  return encodedToColons(substring(firstSplit + 3, lastSplit, str));
}
function accessRelationToType
String ::= str::String
{
  local lastSplit::Integer = lastIndexOf("_$_", str);
  return encodedToColons(substring(lastSplit + 3, length(str), str));
}


--Access Theorems
function accessUniqueThm
String ::= attr::String ty::String
{
  return "$access_$_" ++ colonsToEncoded(attr) ++ "_$_" ++ colonsToEncoded(ty) ++ "__unique";
}
function accessIsThm
String ::= attr::String ty::String
{
  return "$access_$_" ++ colonsToEncoded(attr) ++ "_$_" ++ colonsToEncoded(ty) ++ "__is";
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
         attrName ++ "_$_" ++ colonsToEncoded(treeTy.pp);
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
  return nameType(encodedToColons(substring(lastIndexOf("_$_", s) + 3, length(s), s)));
}
function wpdNt_to_LocalAttrEq
String ::= prod::String attr::String ty::Type
{
  --$wpd__to__<prod>_local_<attr>__<ty>
  return "$wpd__to__" ++ colonsToEncoded(prod) ++ "_local_" ++ attr ++ "__" ++ colonsToEncoded(ty.pp);
}
function localAccessUniqueThm
String ::= prod::String attr::String ty::String
{
  --$local_access_$_<$prod_prod>_$_<attr>_$_<ty>__unique
  return "$local_access_$_$prod_" ++ colonsToEncoded(prod) ++ "_$_" ++ attr ++ "_$_" ++ colonsToEncoded(ty) ++ "__unique";
}


--WPD Nonterminal
function wpdTypeName
String ::= treeTy::Type
{
  return "$wpd_" ++ colonsToEncoded(treeTy.pp);
}
function isWpdTypeName
Boolean ::= rel::String
{
  return startsWith("$wpd_", rel) && !startsWith("$wpd_node_", rel);
}
function wpdToTypeName
String ::= wpd::String
{
  local component::Integer = lastIndexOf("__", wpd);
  return
     if component < 0
     then nonterminalNameToName(substring(5, length(wpd), wpd))
     else nonterminalNameToName(substring(5, component, wpd));
}
function wpdNt_type
Type ::= rel::String
{
  --$wpd_<type name>
  return nameType(encodedToColons(substring(5, length(rel), rel)));
}
function wpdPrimaryComponent
String ::= prod::String builtTy::Type
{
  return "$wpd_" ++ colonsToEncoded(builtTy.pp) ++ "__" ++ colonsToEncoded(prod);
}
function wpdComponentRelToComponentName
String ::= rel::String
{
  --$wpd_<type name>__<component>
  local index::Integer = lastIndexOf("__", rel);
  return encodedToColons(substring(index + 2, length(rel), rel));
}

function wpdNodeTreeForm
String ::= ty::Type
{
  return "$wpd_" ++ colonsToEncoded(ty.pp) ++ "__ntr_" ++ colonsToEncoded(ty.pp);
}


--WPD Node
function wpdNodeTypeName
String ::= treeTy::Type
{
  return "$wpd_node_" ++ colonsToEncoded(treeTy.pp);
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
  return nameType(encodedToColons(substring(10, length(str), str)));
}


--Attribute Equations
function wpdNode_to_AttrEq
String ::= attr::String ty::Type
{
  return "$wpd_node__to__" ++ colonsToEncoded(attr) ++ "__" ++ colonsToEncoded(ty.pp);
}
function wpdNt_to_AttrEq
String ::= attr::String ty::Type
{
  return "$wpd__to__" ++ colonsToEncoded(attr) ++ "__" ++ colonsToEncoded(ty.pp);
}
function primaryComponent
String ::= attr::String ty::Type prod::String
{
  return "$" ++ colonsToEncoded(attr) ++ "__" ++ colonsToEncoded(ty.pp) ++ "__" ++ colonsToEncoded(prod);
}


--Structure Equality
function typeToStructureEqName
String ::= ty::Type
{
  return "$structure_eq__" ++ colonsToEncoded(ty.pp);
}
function isStructureEqName
Boolean ::= rel::String
{
  return startsWith("$structure_eq__", rel);
}
function structureEqToType
Type ::= s::String
{
  return nameType(encodedToColons(substring(15, length(s), s)));
}
function structureEqWPD
String ::= ty::Type
{
  return "$structure_eq__" ++ colonsToEncoded(ty.pp) ++ "__wpd";
}
function structureEqEqualTheorem
String ::= ty::Type
{
  return "$structure_eq__" ++ colonsToEncoded(ty.pp) ++ "__equal";
}
function typeToStructureEq_Symm
String ::= ty::Type
{
  return "$structure_eq__" ++ colonsToEncoded(ty.pp) ++ "__symm";
}
function structureEqProdComponent
String ::= prod::String
{
  return "$structure_eq__" ++ colonsToEncoded(prod);
}
function structureEqExpansionTheorem
String ::= ty::Type component::String
{
  return "$structure_eq__" ++ colonsToEncoded(ty.pp) ++ "__" ++ colonsToEncoded(component) ++ "__expand";
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
  return encodedToColons(substring(6, length(prod), prod));
}
function nameToProd
String ::= s::String
{
  return "$prod_" ++ colonsToEncoded(s);
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
  return encodedToColons(substring(6, length(fun), fun));
}
function nameToFun
String ::= s::String
{
  return "$fun__" ++ colonsToEncoded(s);
}


--Qualified Names
{-
  We need to encode qualified names with something other than a colon,
  since colons are not allowed in Abella names.  We do this by
  replacing colons with $*$.  This works because we ban dollar signs
  in names otherwise.
-}
function encodedToColons
String ::= s::String
{
  return substitute("$*$", ":", s);
}
function colonsToEncoded
String ::= s::String
{
  return substitute(":", "$*$", s);
}
--Get the grammar and the short name for something
function splitQualifiedName
(String, String) ::= s::String
{
  local ind::Integer = lastIndexOf(":", s);
  return
     if ind < 0
     then error("Not a qualified name to split (" ++ s ++ ")")
     else (substring(0, ind, s), substring(ind + 1, length(s), s));
}
function splitEncodedName
(String, String) ::= s::String
{
  local ind::Integer = lastIndexOf("$*$", s);
  return
     if ind < 0
     then error("Not an encoded name to split (" ++ s ++ ")")
     else (substring(0, ind, s), substring(ind + 3, length(s), s));
}
function isFullyQualifiedName
Boolean ::= s::String
{
  return indexOf(":", s) >= 0;
}

