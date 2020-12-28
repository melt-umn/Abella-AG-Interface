grammar toAbella:abstractSyntax;

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
         | [] ->
           error("Should not call replaceAssociatedScopes with " ++
                 "scopes which do not contain the replacement key")
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
  return ty1.isEq;
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

