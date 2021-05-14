grammar abella_compilation;


global attrValTypeName::String = "$attrVal";
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
function nameToNonterminal
String ::= name::String
{
  return "nt_" ++ name;
}
function nameToNonterminalType
Type ::= name::String
{
  return nameType(nameToNonterminal(name));
}

function nameToNodeType
String ::= name::String
{
  return "node_" ++ name;
}
function typeToNodeType
String ::= ty::Type
{
  --drop "nt_" from beginning
  return nameToNodeType(substring(3, length(ty.pp), ty.pp));
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


function nodeTreeConstructorName
String ::= treeTy::Type
{
  return "$ntr_" ++ treeTy.pp;
}


--Attribute Access
function accessRelationName
String ::= treeTy::Type attrName::String
{
  return "$access_$_" ++ attrName ++ "_$_" ++ treeTy.pp;
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
function localAccessRelationName
String ::= treeTy::Type attrName::String prodName::String
{
  --$local_access_$_<prod>_$_<name>_$_<type>
  return "$local_access_$_" ++ nameToProd(prodName) ++ "_$_" ++
         attrName ++ "_$_" ++ treeTy.pp;
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
function nameToProd
String ::= s::String
{
  return "$prod_" ++ s;
}


--Functions
function nameToFun
String ::= s::String
{
  return "$fun__" ++ s;
}

