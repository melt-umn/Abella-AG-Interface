grammar fromAbella:abstractSyntax;


nonterminal Metaterm with
   pp, isAtomic,
   translation<Metaterm>, shouldHide;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;
  top.isAtomic = true;

  top.translation = termMetaterm(t.translation, r);
  top.shouldHide = t.shouldHide;
}


abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
  top.isAtomic = true;

  top.translation = trueMetaterm();
  top.shouldHide = false;
}


abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
  top.isAtomic = true;

  top.translation = falseMetaterm();
  top.shouldHide = false;
}


abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
  top.isAtomic = true;

  top.translation = eqMetaterm(t1.translation, t2.translation);
  top.shouldHide = false;
}


abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = (if t1.isAtomic
            then t1.pp
            else "(" ++ t1.pp ++ ")") ++ " -> " ++ t2.pp;
  top.isAtomic = false;

  top.translation = impliesMetaterm(t1.translation, t2.translation);
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

  top.translation = orMetaterm(t1.translation, t2.translation);
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

  top.translation = andMetaterm(t1.translation, t2.translation);
  top.shouldHide = false;
}


abstract production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[String] body::Metaterm
{
  local bindingsString::String =
     if null(bindings)
     then error("Empty bindings not allowed; production bindingsMetaterm")
     else foldr1(\ a::String b::String -> a ++ " " ++ b, bindings);
  top.pp = b.pp ++ " " ++ bindingsString ++ ", " ++ body.pp;
  top.isAtomic = false;

  top.translation = bindingMetaterm(b, bindings, body.translation);
  top.shouldHide = false;
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
   pp, isAtomic,
   translation<Term>, shouldHide;

abstract production applicationTerm
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
     | nameTerm("$plus_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerAddition(arg1, arg2, arg3)
     | nameTerm("$minus_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerSubtraction(arg1, arg2, arg3)
     | nameTerm("$multiply_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerMultiplication(arg1, arg2, arg3)
     | nameTerm("$divide_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerDivision(arg1, arg2, arg3)
     | nameTerm("$modulus_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerModulus(arg1, arg2, arg3)
     | nameTerm("$less_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerLess(arg1, arg2, arg3)
     | nameTerm("$lessEq_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerLessEq(arg1, arg2, arg3)
     | nameTerm("$greater_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerGreater(arg1, arg2, arg3)
     | nameTerm("$greaterEq_integer"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       integerGreaterEq(arg1, arg2, arg3)
     | nameTerm("$negate_integer"),
       consTermList(arg1, singleTermList(arg2)) ->
       integerNegate(arg1, arg2)
     --Append
     | nameTerm("$append"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       appendTerm(arg1, arg2, arg3)
     --Boolean Operations
     | nameTerm("$or_bool"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       boolOr(arg1, arg2, arg3)
     | nameTerm("$and_bool"),
       consTermList(arg1, consTermList(arg2, singleTermList(arg3))) ->
       boolAnd(arg1, arg2, arg3)
     | nameTerm("$not_bool"),
       consTermList(arg1, singleTermList(arg2)) ->
       boolNot(arg1, arg2)
     --Integer Constants
     | nameTerm("$posInt"), singleTermList(integerTerm(i)) ->
       integerTerm(i)
     | nameTerm("$negSuccInt"), singleTermList(integerTerm(i)) ->
       integerTerm(-i - 1)
     | nameTerm("$succ"), singleTermList(integerTerm(i)) ->
       integerTerm(i + 1)
     --Nothing Special
     | _, _ -> applicationTerm(f.translation, args.translation)
     end;
  top.shouldHide =
      case f of
      | nameTerm(name) ->
        startsWith("$wpd_", name) ||
        startsWith("$access_", name)
      | _ -> false
      end;
}


abstract production nameTerm
top::Term ::= name::String
{
  top.pp = name;
  top.isAtomic = true;

  top.translation =
     case name of
     --Booleans
     | "$btrue" -> trueTerm()
     | "$bfalse" -> falseTerm()
     --Integers
     | "$zero" -> integerTerm(0)
     --Other Nothing Special
     | _ ->
       if findDot > 0
       --Value of Attribute Access:  $<tree>_DOT_<attr>
       then attrAccess(substring(1, findDot, name),
                       substring(findDot + 5, length(name), name))
       --Nothing Special
       else nameTerm(name)
     end;
  local findDot::Integer = indexOf("_DOT_", name);
  top.shouldHide = false;
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

  top.translation =
      case t2.translation of
      | listTerm(contents) ->
        listTerm(addListContents(t1.translation, contents))
      | _ -> consTerm(t1.translation, t2.translation)
      end;
  top.shouldHide = false;
}


abstract production nilTerm
top::Term ::=
{
  top.pp = "nil";
  top.isAtomic = true;

  top.translation = listTerm(emptyListContents());
  top.shouldHide = false;
}





nonterminal TermList with
   pp,
   translation<TermList>;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = if t.isAtomic then t.pp else "(" ++ t.pp ++ ")";

  top.translation = singleTermList(t.translation);
}


abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = (if t.isAtomic then t.pp else "(" ++ t.pp ++ ")") ++ " " ++ rest.pp;

  top.translation = consTermList(t.translation, rest.translation);
}

