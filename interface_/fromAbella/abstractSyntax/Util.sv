grammar interface_:fromAbella:abstractSyntax;


function cleanVariable
String ::= name::String
{
  -- $<tree>_DOT_<attr>
  local is_attr_access::Boolean = indexOf("_DOT_", name) > 0;
  -- $<tree>_Tm
  local is_tm::Boolean = isTreeStructureName(name);
  local tm_treename::String = structureToTreeName(name);
  -- $<tree>_Node
  local is_node::Boolean = isTreeNodeName(name);
  -- $<tree>_ChildList
  local is_childlist::Boolean = isChildListName(name);

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

