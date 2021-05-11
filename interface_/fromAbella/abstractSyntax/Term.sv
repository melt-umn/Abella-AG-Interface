grammar interface_:fromAbella:abstractSyntax;


attribute
   translation<Metaterm>
occurs on Metaterm;

aspect production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.translation =
      case t.translation of
      | left(tm) -> termMetaterm(tm, r)
      | right(mtm) -> mtm
      end;
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.translation = trueMetaterm();
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.translation = falseMetaterm();
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.translation =
      case t1.translation, t2.translation of
      | left(tm1), left(tm2) -> eqMetaterm(tm1, tm2)
      | _, _ -> error("Should not have metaterm translations in eqMetaterm")
      end;
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation =
      if t1.shouldHide
      then t2.translation
      else impliesMetaterm(t1.translation, t2.translation);
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = orMetaterm(t1.translation, t2.translation);
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = andMetaterm(t1.translation, t2.translation);
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::[(String, Maybe<Type>)] body::Metaterm
{
  local isHidden::(Boolean ::= String) =
        \ s::String ->
          contains(s, flatMap(\ p::(String, String, Term) -> p.2::p.3.usedNames,
                              body.gatheredDecoratedTrees));
  local cleanedNames::[(String, Maybe<Type>)] =
        foldr(\ p::(String, Maybe<Type>) rest::[(String, Maybe<Type>)] ->
                if isHidden(p.1)
                then rest
                else p::rest,
              [], nameBindings);
  top.translation = bindingMetaterm(b, cleanedNames, body.translation);
}





attribute
   --Either because some applied relations need to become metaterms
   translation<Either<Term Metaterm>>
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.translation =
     case f, args.translation of
     --Integer Operations
     | nameTerm("$plus_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(plusMetaterm(arg1, arg2, arg3))
     | nameTerm("$minus_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(minusMetaterm(arg1, arg2, arg3))
     | nameTerm("$multiply_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(multiplyMetaterm(arg1, arg2, arg3))
     | nameTerm("$divide_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(divideMetaterm(arg1, arg2, arg3))
     | nameTerm("$modulus_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(modulusMetaterm(arg1, arg2, arg3))
     | nameTerm("$less_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(lessMetaterm(arg1, arg2, arg3))
     | nameTerm("$lessEq_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(lessEqMetaterm(arg1, arg2, arg3))
     | nameTerm("$greater_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(greaterMetaterm(arg1, arg2, arg3))
     | nameTerm("$greaterEq_integer", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(greaterEqMetaterm(arg1, arg2, arg3))
     | nameTerm("$negate_integer", _),
       consTermList(arg1, singleTermList(arg2)) ->
       right(negateMetaterm(arg1, arg2))
     --Append
     | nameTerm("$append", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(appendMetaterm(arg1, arg2, arg3))
     --Boolean Operations
     | nameTerm("$or_bool", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(orBoolMetaterm(arg1, arg2, arg3))
     | nameTerm("$and_bool", _),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       right(andBoolMetaterm(arg1, arg2, arg3))
     | nameTerm("$not_bool", _),
       consTermList(arg1, singleTermList(arg2)) ->
       right(notBoolMetaterm(arg1, arg2))
     --Attribute Access
     | nameTerm(str, _),
       consTermList(nameTerm(treeName, _),
       consTermList(nameTerm(treeNodeName, _),
                    singleTermList(applicationTerm(nameTerm("$attr_ex", _),
                                                   singleTermList(val)))))
       when isAccessRelation(str) ->
       right(attrAccessMetaterm(treeName, accessRelationToAttr(str), val))
     | nameTerm(str, _),
       consTermList(nameTerm(treeName, _),
       consTermList(nameTerm(treeNodeName, _),
                    singleTermList(nameTerm("$attr_no", _))))
       when isAccessRelation(str) ->
       right(attrAccessEmptyMetaterm(treeName, accessRelationToAttr(str)))
     --Local Attribute Access
     | nameTerm(str, _),
       consTermList(nameTerm(treeName, _),
       consTermList(nameTerm(treeNodeName, _),
                    singleTermList(applicationTerm(nameTerm("$attr_ex", _),
                                                   singleTermList(val)))))
       when isLocalAccessRelation(str) ->
       case val of
       | pairTerm(
            addPairContents(nameTerm(tree, _),
            singlePairContents(applicationTerm(nameTerm(ntr, _), _))))
         when isNodeTreeConstructorName(ntr) ->
         right(localAttrAccessMetaterm(treeName,
                  localAccessToAttr(str), nameTerm(tree, nothing())))
       | _ ->
         right(localAttrAccessMetaterm(treeName,
                  localAccessToAttr(str), val))
       end
     | nameTerm(str, _),
       consTermList(nameTerm(treeName, _),
       consTermList(nameTerm(treeNodeName, _),
                    singleTermList(nameTerm("$attr_no", _))))
       when isLocalAccessRelation(str) ->
       right(localAttrAccessEmptyMetaterm(treeName, localAccessToAttr(str)))
     --Structural Equality
     | nameTerm(str, _), consTermList(t1, singleTermList(t2))
       when isStructureEqName(str) ->
       right(eqMetaterm(t1, t2))
     --Function Application
     | nameTerm(str, _), args when isFun(str) ->
       right(funMetaterm(funToName(str),
                foldr(addParenthesizedArgs(_, _),
                      emptyParenthesizedArgs(),
                      take(length(args.argList) - 1, args.argList)),
                last(args.argList)))
     --Production Application
     | nameTerm(str, _), args when isProd(str) ->
       left(prodTerm(prodToName(str),
               foldr(addParenthesizedArgs(_, _),
                     emptyParenthesizedArgs(), args.argList)))
     --Integer Constants
     | nameTerm("$posInt", _), singleTermList(intTerm(i)) ->
       left(intTerm(i))
     | nameTerm("$negSuccInt", _), singleTermList(intTerm(i)) ->
       left(intTerm(-i - 1))
     | nameTerm("$succ", _), singleTermList(intTerm(i)) ->
       left(intTerm(i + 1))
     --Pairs
     | nameTerm("$pair_c", _), consTermList(arg1, singleTermList(arg2)) ->
       left(pairTerm(addPairContents(arg1, singlePairContents(arg2))))
     --Nothing Special
     | ftm, atm -> left(applicationTerm(ftm, atm))
     end;
}


aspect production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.translation =
     left(case name of
          --Booleans
          | "$btrue" -> trueTerm()
          | "$bfalse" -> falseTerm()
          --Integers
          | "$zero" -> intTerm(0)
          --Productions
          | str when isProd(str) ->
            prodTerm(prodToName(str), emptyParenthesizedArgs())
          --Characters
          | str when startsWith("$c_", str) ->
            charTerm(charsToString([toInteger(
                        substring(3, length(name), name))]))
          --Other
          | _ ->
            nameTerm(name, ty)
          end);
  local findDot::Integer = indexOf("_DOT_", name);
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.translation =
      left(case t1.translation, t2.translation of
           | left(charTerm(char)), left(stringTerm(contents)) ->
             stringTerm(char ++ contents)
           --we need this because we are using lists for strings, and don't know
           --which we are looking at until we add a character to the beginning
           | left(charTerm(char)), left(listTerm(emptyListContents())) ->
             stringTerm(char)
           | left(tm1), left(listTerm(contents)) ->
             listTerm(addListContents(tm1, contents))
           | left(tm1), left(tm2) -> consTerm(tm1, tm2)
           | _, _ -> error("Should not have metaterm translations in consTerm")
           end);
}


aspect production nilTerm
top::Term ::=
{
  top.translation = left(listTerm(emptyListContents()));
}


aspect production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.translation = error("Should not translate underscoreTerm");
}





attribute
   translation<TermList>
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.translation =
      case t.translation of
      | left(tm) -> singleTermList(tm)
      | right(_) -> error("Should not have a metaterm translation in singleTermList")
      end;
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.translation =
      case t.translation of
      | left(tm) -> consTermList(tm, rest.translation)
      | right(_) -> error("Should not have a metaterm translation in consTermList")
      end;
}


aspect production emptyTermList
top::TermList ::=
{
  top.translation = error("Should not have an emptyTermList here");
}

