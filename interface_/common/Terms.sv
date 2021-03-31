grammar interface_:common;




nonterminal Metaterm with pp, isAtomic;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;
  top.isAtomic = true;
}

abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
  top.isAtomic = true;
}

abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
  top.isAtomic = true;
}

abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
  top.isAtomic = true;
}

abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = (if t1.isAtomic
            then t1.pp
            else "(" ++ t1.pp ++ ")") ++ " -> " ++ t2.pp;
  top.isAtomic = false;
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
     then error("Empty bindings not allowed; production bindingsMetaterm")
     else foldr1(\ a::String b::String -> a ++ " " ++ b, bindings);
  top.pp = b.pp ++ " " ++ bindingsString ++ ", " ++ body.pp;
  top.isAtomic = false;
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




nonterminal Term with pp, isAtomic;

abstract production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp =
    ( if f.isAtomic
      then f.pp
      else "(" ++ f.pp ++ ")" ) ++ " " ++ args.pp;
  top.isAtomic = false;
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
}

abstract production nilTerm
top::Term ::=
{
  top.pp = "nil";
  top.isAtomic = true;
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
}




nonterminal TermList with pp;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = if t.isAtomic then t.pp else "(" ++ t.pp ++ ")";
}

abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = (if t.isAtomic then t.pp else "(" ++ t.pp ++ ")") ++ " " ++ rest.pp;
}

