grammar interface_:common:abstractSyntax;




nonterminal Metaterm with
   pp, isAtomic, shouldHide,
   gatheredTrees, knownTrees, gatheredDecoratedTrees,
   usedNames,
   silverContext;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;
  top.isAtomic = true;
  top.shouldHide = t.shouldHide;
}

abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = (if t1.isAtomic
            then t1.pp
            else "(" ++ t1.pp ++ ")") ++ " -> " ++ t2.pp;
  top.isAtomic = false;
  top.shouldHide = false;
}

abstract production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp =
    ( if t1.isAtomic
      then t1.pp
      else "(" ++ t1.pp ++ ")" ) ++ " \\/ " ++
    ( if t2.isAtomic
      then t2.pp
      else "(" ++ t2.pp ++ ")" );
  top.isAtomic = false;
  top.shouldHide = false;
}

abstract production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp =
    ( if t1.isAtomic
      then t1.pp
      else "(" ++ t1.pp ++ ")" ) ++ " /\\ " ++
    ( if t2.isAtomic
      then t2.pp
      else "(" ++ t2.pp ++ ")" );
  top.isAtomic = false;
  top.shouldHide = false;
}

abstract production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::[Pair<String Maybe<Type>>] body::Metaterm
{
  local bindings::[String] =
        map(\ p::Pair<String Maybe<Type>> ->
              case p of
              | (name, just(ty)) -> "(" ++ name ++ " : " ++ ty.pp ++ ")"
              | (name, nothing()) -> name
              end,
            nameBindings);
  local bindingsString::String =
     if null(bindings)
     then error("Empty bindings not allowed; production bindingsMetaterm (" ++ body.pp ++ ")")
     else foldr1(\ a::String b::String -> a ++ " " ++ b, bindings);
  top.pp = b.pp ++ " " ++ bindingsString ++ ", " ++ body.pp;
  top.isAtomic = false;
  top.shouldHide = false;

  --Want ALL names which occur, even if only in bindings
  top.usedNames := map(fst, nameBindings) ++ body.usedNames;

  top.gatheredTrees :=
      foldr(\ s::String rest::[String] ->
              if containsAssociated(s, nameBindings)
              then rest
              else s::rest,
            [], body.gatheredTrees);

  top.gatheredDecoratedTrees :=
      foldr(\ p::(String, String, Term)
              rest::[(String, String, Term)] ->
              if containsAssociated(p.1, nameBindings)
              then rest
              else p::rest,
            [], body.gatheredDecoratedTrees);

  body.knownTrees =
       body.gatheredTrees ++
       foldr(\ s::String rest::[String] ->
               if containsAssociated(s, nameBindings)
               then rest
               else s::rest,
             [],  top.knownTrees);
}




nonterminal Restriction with pp;

abstract production emptyRestriction
top::Restriction ::=
{
  top.pp = "";
}

abstract production starRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "*");
}

abstract production atRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "@");
}

abstract production plusRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "+");
}

abstract production hashRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "#");
}




nonterminal Binder with pp;

abstract production forallBinder
top::Binder ::=
{
  top.pp = "forall";
}

abstract production existsBinder
top::Binder ::=
{
  top.pp = "exists";
}

abstract production nablaBinder
top::Binder::=
{
  top.pp = "nabla";
}




nonterminal Term with
   pp, isAtomic, shouldHide,
   gatheredTrees, knownTrees, gatheredDecoratedTrees,
   usedNames,
   silverContext;

--Easy equality check
attribute compareTo, isEqual occurs on
   Term, TermList, ParenthesizedArgs, ListContents, PairContents, Type;
propagate compareTo, isEqual on
   Term, TermList, ParenthesizedArgs, ListContents, PairContents, Type;

abstract production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp =
    ( if f.isAtomic
      then f.pp
      else "(" ++ f.pp ++ ")" ) ++ " " ++ args.pp;
  top.isAtomic = false;
  top.shouldHide =
      case f of
      | nameTerm(name, _) ->
        startsWith("$wpd_", name)
      | _ -> false
      end;

  top.gatheredTrees :=
      f.gatheredTrees ++
      case f, args of
      | nameTerm(wpdNT, _), consTermList(nameTerm(tree, _), _)
        when isWpdTypeName(wpdNT) ->
        [tree]
      --accessing decorated trees as attributes
      | nameTerm(access, _),
        consTermList(onTree,
           consTermList(onTreeNode,
           singleTermList(
              applicationTerm(
                 nameTerm(attrEx, _),
                 singleTermList(
                    applicationTerm(
                       nameTerm(pairMaker, _),
                       consTermList(nameTerm(treeName, _),
                          singleTermList(
                             applicationTerm(nameTerm(ntr, _),
                                consTermList(nameTerm(nodeName, _),
                                singleTermList(childList)))))))))))
        when attrEx == attributeExistsName &&
             pairMaker == pairConstructorName &&
             isNodeTreeConstructorName(ntr) ->
        [treeName]
      | _, _ -> []
      end;

  top.gatheredDecoratedTrees :=
      f.gatheredDecoratedTrees ++
      case f, args of
      | nameTerm(wpdNT, _),
        consTermList(nameTerm(tree, _),
           singleTermList(
              applicationTerm(
                 nameTerm(ntr, _),
                 consTermList(nameTerm(node, _),
                    singleTermList(children)))))
        when isWpdTypeName(wpdNT) ->
        [(tree, node, new(children))]
      --accessing decorated trees as attributes
      | nameTerm(access, _),
        consTermList(onTree,
           consTermList(onTreeNode,
           singleTermList(
              applicationTerm(
                 nameTerm(attrEx, _),
                 singleTermList(
                    applicationTerm(
                       nameTerm(pairMaker, _),
                       consTermList(nameTerm(treeName, _),
                          singleTermList(
                             applicationTerm(nameTerm(ntr, _),
                                consTermList(nameTerm(nodeName, _),
                                singleTermList(childList)))))))))))
        when attrEx == attributeExistsName &&
             pairMaker == pairConstructorName &&
             isNodeTreeConstructorName(ntr) ->
        [(treeName, nodeName, new(childList))]
      | _, _ -> []
      end;
}

abstract production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.pp =
      case ty of
      | just(t) -> "(" ++ name ++ " : " ++ t.pp ++ ")"
      | nothing() -> name
      end;
  top.isAtomic = true;
  top.shouldHide = false;

  top.usedNames := [name];
}

abstract production consTerm
top::Term ::= t1::Term t2::Term
{
  top.pp =
    ( if t1.isAtomic
      then t1.pp
      else "(" ++ t1.pp ++ ")" ) ++ "::" ++
    ( if t2.isAtomic
      then t2.pp
      else "(" ++ t2.pp ++ ")" );
  top.isAtomic = false;
  top.shouldHide = false;
}

abstract production nilTerm
top::Term ::=
{
  top.pp = "nil";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.pp =
      case ty of
      | just(t) -> "(_ : " ++ t.pp ++ ")"
      | nothing() -> "_"
      end;

  top.isAtomic = true;
  top.shouldHide = false;
}




nonterminal TermList with
   pp, argList,
   knownTrees,
   usedNames,
   silverContext;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = if t.isAtomic then t.pp else "(" ++ t.pp ++ ")";

  top.argList = [t];
}

abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = (if t.isAtomic then t.pp else "(" ++ t.pp ++ ")") ++ " " ++ rest.pp;

  top.argList = t::rest.argList;
}

abstract production emptyTermList
top::TermList ::=
{
  top.pp = "";

  top.argList = [];
}

