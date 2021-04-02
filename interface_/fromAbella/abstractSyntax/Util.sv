grammar interface_:fromAbella:abstractSyntax;


function cleanVariable
String ::= name::String
{
  -- $<tree>_DOT_<attr>
  local is_attr_access::Boolean = indexOf("_DOT_", name) > 0;
  -- $<tree>_Tm
  local is_tm::Boolean = varIsTreeStructure(name);
  local tm_treename::String = treeStructureToVar(name);
  -- $<tree>_Node
  local is_node::Boolean = startsWith("$", name) && indexOf("_Node", name) > 0;
  -- $<tree>_ChildList
  local is_childlist::Boolean = startsWith("$", name) && indexOf("_ChildList", name) > 0;

  return
     if is_attr_access
     then "" --the tree will be created from its term
     else if is_tm
          then tm_treename
          else if is_node
               then "" --the tree will be created from its term
               else if is_childlist
                    then "" --the tree will be created from its term
                    else name; --nothing special
}


function varIsTreeStructure
Boolean ::= name::String
{
  return startsWith("$", name) && endsWith("_Tm", name);
}

function treeStructureToVar
String ::= structureName::String
{
  --$<name>_Tm
  return substring(1, length(structureName) - 3, structureName);
}


function varIsTreeNode
Boolean ::= name::String
{
  return startsWith("$", name) && endsWith("_Node", name);
}
function treeNodeToVar
String ::= nodeName::String
{
  --$<name>_Node
  return substring(1, length(nodeName) - 5, nodeName);
}


function nameIsAccessRelation
Boolean ::= name::String
{
  return startsWith("$access_$_", name);
}

function accessRelationToAttr
String ::= accessRel::String
{
  -- $access_$_<attr>_$<ty>
  local frontRemoved::String = substring(10, length(accessRel), accessRel);
  local loc__::Integer = indexOf("_$_", frontRemoved);
  return substring(0, loc__, frontRemoved);
}

