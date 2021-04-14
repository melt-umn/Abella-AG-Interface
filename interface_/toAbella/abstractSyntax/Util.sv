grammar interface_:toAbella:abstractSyntax;

{-
  Find the value associated with a key, either in a single list or in
  a nested list of scopes.
-}
function findAssociated
Maybe<a> ::= key::String container::[Pair<String a>]
{
  return case container of
         | [] -> nothing()
         | pair(a, b)::tl -> if key == a
                             then just(b)
                             else findAssociated(key, tl)
         end;
}

function findAssociatedScopes
Maybe<a> ::= key::String scopes::[[Pair<String a>]]
{
  return case scopes of
         | [] -> nothing()
         | scope::rest ->
           case findAssociated(key, scope) of
           | just(x) -> just(x)
           | nothing() -> findAssociatedScopes(key, rest)
           end
         end;
}




{-
  Replace the value associated with a key with the new value, either
  in a single list or in a nested list of scopes.
  - The scopes version assumes the key is contained in some scope.
-}
function replaceAssociated
Maybe<[Pair<String a>]> ::= key::String newVal::a container::[Pair<String a>]
{
  return case container of
         | [] -> nothing()
         | pair(a, b)::tl ->
           if key == a
           then just(pair(a, newVal)::tl)
           else case replaceAssociated(key, newVal, tl) of
                | just(newtl) -> just(pair(a, b)::newtl)
                | nothing() -> nothing()
                end
         end;
}

function replaceAssociatedScopes
[[Pair<String a>]] ::= key::String newVal::a scopes::[[Pair<String a>]]
{
  return case scopes of
         | [] -> [] --error for an unknown name
         | currentScope::rest ->
           case replaceAssociated(key, newVal, currentScope) of
           | just(newScope) -> newScope::rest
           | nothing() -> currentScope::replaceAssociatedScopes(key, newVal, rest)
           end
         end;
}





function tysEqual
Boolean ::= ty1::Type ty2::Type
{
  ty1.eqTest = ty2;
  ty2.eqTest = ty1;
  return ty1.isEq && ty2.isEq;
}

function termsEqual
Boolean ::= tm1::Term tm2::Term
{
  tm1.eqTest = tm2;
  tm2.eqTest = tm1;
  return tm1.isEq && tm2.isEq;
}



--Check whether a type is nominally a nonterminal
--Does not check if that nonterminal type exists
function tyIsNonterminal
Boolean ::= ty::Type
{
  return
     case ty of
     | nameType(s) -> startsWith("nt_", s)
     | _ -> false
     end;
}





function splitList
Pair<[a] [b]> ::= l::[Pair<a b>]
{
  return case l of
         | [] -> pair([], [])
         | pair(a, b)::rest ->
           case splitList(rest) of
           | pair(la, lb) -> pair(a::la, b::lb)
           end
         end;
}

function elemAtIndex
a ::= l::[a] i::Integer
{
  return
     case l of
     | [] -> error("Index too deep")
     | h::t ->
       if i == 0
       then h
       else elemAtIndex(t, i - 1)
     end;
}




function buildApplication
Term ::= fun::Term args::[Term]
{
  --I'll make this handle degenerate "applications" as well
  return if null(args)
         then fun
         else applicationTerm(fun, buildApplicationArgs(args));
}

function buildApplicationArgs
TermList ::= args::[Term]
{
  return
     case args of
     | [] ->
       error("Should not call buildApplicationArgs with an empty list")
     | [x] -> singleTermList(x)
     | h::t -> consTermList(h, buildApplicationArgs(t))
     end;
}





--Find the metaterm which is the body of a hypothesis
function get_arg_hyp_metaterm
Maybe<Metaterm> ::= arg::ApplyArg hyps::[(String, Metaterm)]
{
  return
     case arg of
     | hypApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     | starApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     end;
}




--Find the WPD nonterminal relation for a given treename, if it exists
function find_WPD_nt_hyp
Maybe<(String, Metaterm)> ::= treename::String hyps::[(String, Metaterm)]
{
  local structure::Term =
        case find_structure_hyp(treename, hyps) of
        | just((_, s)) -> s
        | nothing() -> nameTerm(treename, nothing())
        end;
  return find_WPD_nt_help(structure, treename, hyps);
}


function find_WPD_nt_help
Maybe<(String, Metaterm)> ::= tree::Term treename::String hyps::[(String, Metaterm)]
{
  return
     case hyps of
     | [] -> nothing()
       --(hyp, wpd_<ty> tr (ntr_<ty> treeNode childList))
     | (hyp, termMetaterm(applicationTerm(nameTerm(str, x),
                consTermList(tr,
                singleTermList(
                   applicationTerm(nameTerm(ntr, ntrty),
                      consTermList(
                         nameTerm(treeNode, treeNodeTy),
                      singleTermList(childList)))))),
                _))::_
       when isWpdTypeName(str) && termsEqual(tree, tr) &&
            nodeToTreeName(treeNode) == treename ->
       just((hyp,
          termMetaterm(applicationTerm(nameTerm(str, x),
                consTermList(tr,
                singleTermList(
                   applicationTerm(nameTerm(ntr, ntrty),
                      consTermList(
                         nameTerm(treeNode, treeNodeTy),
                      singleTermList(childList)))))),
                emptyRestriction())))
       --(hyp, wpd_<ty> tr (ntr_<ty> treeNode childList)) where tr is a tree name
     | (hyp, termMetaterm(applicationTerm(nameTerm(str, x),
                consTermList(nameTerm(tr, trty),
                singleTermList(
                   applicationTerm(nameTerm(ntr, ntrty),
                      consTermList(
                         nameTerm(treeNode, treeNodeTy),
                      singleTermList(childList)))))),
                _))::_
       when isWpdTypeName(str) && tr == treename &&
            nodeToTreeName(treeNode) == treename ->
       just((hyp,
          termMetaterm(applicationTerm(nameTerm(str, x),
                consTermList(nameTerm(tr, trty),
                singleTermList(
                   applicationTerm(nameTerm(ntr, ntrty),
                      consTermList(
                         nameTerm(treeNode, treeNodeTy),
                      singleTermList(childList)))))),
                emptyRestriction())))
     | (hyp, mt)::tl -> find_WPD_nt_help(tree, treename, tl)
     end;
}


--find a hypthesis of the form "<treename> = ___" or "___ = <treename>"
function find_structure_hyp
Maybe<(String, Term)> ::= treename::String hyps::[(String, Metaterm)]
{
  return
     case hyps of
     | [] -> nothing()
     | (hyp, eqMetaterm(nameTerm(str, _), structure))::_
       when str == treename && structure.isProdStructure ->
       just((hyp, new(structure)))
     | (hyp, eqMetaterm(structure, nameTerm(str, _)))::_
       when str == treename && structure.isProdStructure ->
       just((hyp, new(structure)))
     | (hyp, mt)::tl -> find_structure_hyp(treename, tl)
     end;
}


--Find the tree which is the parent of the given tree and the term it is in
function find_parent_tree
Maybe<(String, Term)> ::= treename::String hyps::[(String, Metaterm)]
{
  return
     case hyps of
     | [] -> nothing()
     | (hyp, eqMetaterm(nameTerm(str, _), structure))::_
       when contains(treename, structure.usedNames) ->
       just((str, new(structure)))
     | _::tl -> find_parent_tree(treename, tl)
     end;
}

