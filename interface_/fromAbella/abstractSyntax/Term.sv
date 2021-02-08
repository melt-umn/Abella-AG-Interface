grammar interface_:fromAbella:abstractSyntax;


attribute
   pp, isAtomic,
   translation<Metaterm>, shouldHide
occurs on Metaterm;

aspect production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;
  top.isAtomic = true;

  top.translation =
      case t.translation of
      | left(tm) -> termMetaterm(tm, r)
      | right(mtm) -> mtm
      end;
  top.shouldHide = t.shouldHide;
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
  top.isAtomic = true;

  top.translation = trueMetaterm();
  top.shouldHide = false;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
  top.isAtomic = true;

  top.translation = falseMetaterm();
  top.shouldHide = false;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
  top.isAtomic = true;

  top.translation =
      case t1.translation, t2.translation of
      | left(tm1), left(tm2) -> eqMetaterm(tm1, tm2)
      | _, _ -> error("Should not have metaterm translations in eqMetaterm")
      end;
  top.shouldHide = false;
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = (if t1.isAtomic
            then t1.pp
            else "(" ++ t1.pp ++ ")") ++ " -> " ++ t2.pp;
  top.isAtomic = false;

  top.translation = impliesMetaterm(t1.translation, t2.translation);
  top.shouldHide = false;
}


aspect production orMetaterm
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

  top.translation = orMetaterm(t1.translation, t2.translation);
  top.shouldHide = false;
}


aspect production andMetaterm
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

  top.translation = andMetaterm(t1.translation, t2.translation);
  top.shouldHide = false;
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder nameBindings::[Pair<String Maybe<Type>>] body::Metaterm
{
  local bindings::[String] = map(fst, nameBindings);
  local bindingsString::String =
     if null(bindings)
     then error("Empty bindings not allowed; production bindingsMetaterm")
     else foldr1(\ a::String b::String -> a ++ " " ++ b, bindings);
  top.pp = b.pp ++ " " ++ bindingsString ++ ", " ++ body.pp;
  top.isAtomic = false;

  top.translation = bindingMetaterm(b, nameBindings, body.translation);
  top.shouldHide = false;
}





attribute pp occurs on Restriction;

aspect production emptyRestriction
top::Restriction ::=
{
  top.pp = "";
}


aspect production starRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "*");
}


aspect production atRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "@");
}


aspect production plusRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "+");
}


aspect production hashRestriction
top::Restriction ::= n::Integer
{
  top.pp = " " ++ replicate(n, "#");
}





attribute pp occurs on Binder;

aspect production forallBinder
top::Binder ::=
{
  top.pp = "forall";
}


aspect production existsBinder
top::Binder ::=
{
  top.pp = "exists";
}


aspect production nablaBinder
top::Binder::=
{
  top.pp = "nabla";
}





attribute
   pp, isAtomic,
   --Either because some applied relations need to become metaterms
   translation<Either<Term Metaterm>>, shouldHide
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp =
    ( if f.isAtomic
      then f.pp
      else "(" ++ f.pp ++ ")" ) ++ " " ++ args.pp;
  top.isAtomic = false;

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
     --Integer Constants
     | nameTerm("$posInt", _), singleTermList(intTerm(i)) ->
       left(intTerm(i))
     | nameTerm("$negSuccInt", _), singleTermList(intTerm(i)) ->
       left(intTerm(-i - 1))
     | nameTerm("$succ", _), singleTermList(intTerm(i)) ->
       left(intTerm(i + 1))
     --Nothing Special
     | ftm, atm -> left(applicationTerm(ftm, atm))
     end;
  top.shouldHide =
      case f of
      | nameTerm(name, _) ->
        startsWith("$wpd_", name) ||
        startsWith("$access_", name)
      | _ -> false
      end;
}


aspect production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.pp = name;
  top.isAtomic = true;

  top.translation =
     left(case name of
          --Booleans
          | "$btrue" -> trueTerm()
          | "$bfalse" -> falseTerm()
          --Integers
          | "$zero" -> intTerm(0)
          --Other
          | _ ->
            if findDot > 0
            --Value of Attribute Access:  $<tree>_DOT_<attr>
            then attrAccessTerm(substring(1, findDot, name),
                                substring(findDot + 5, length(name), name))
            else if startsWith("$c_", name)
                 --Character for string
                 then charTerm(charsToString([toInteger(substring(3, 5, name))]))
                 --Nothing Special
                 else nameTerm(name, ty)
          end);
  local findDot::Integer = indexOf("_DOT_", name);
  top.shouldHide = false;
}


aspect production consTerm
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
  top.shouldHide = false;
}


aspect production nilTerm
top::Term ::=
{
  top.pp = "nil";
  top.isAtomic = true;

  top.translation = left(listTerm(emptyListContents()));
  top.shouldHide = false;
}





attribute
   pp,
   translation<TermList>
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.pp = if t.isAtomic then t.pp else "(" ++ t.pp ++ ")";

  top.translation =
      case t.translation of
      | left(tm) -> singleTermList(tm)
      | right(_) -> error("Should not have a metaterm translation in singleTermList")
      end;
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = (if t.isAtomic then t.pp else "(" ++ t.pp ++ ")") ++ " " ++ rest.pp;

  top.translation =
      case t.translation of
      | left(tm) -> consTermList(tm, rest.translation)
      | right(_) -> error("Should not have a metaterm translation in consTermList")
      end;
}

