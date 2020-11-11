grammar toAbella:abstractSyntax;


nonterminal Metaterm with pp;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;
}


abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
}


abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
}


abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
}


abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") -> " ++ t2.pp;
}


abstract production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") \\/ (" ++ t2.pp ++ ")";
}


abstract production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") /\\ (" ++ t2.pp ++ ")";
}


abstract production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[Pair<String Maybe<Type>>] body::Metaterm
{
  local bindingsString::String =
     if null(bindings)
     then error("Empty bindings not allowed; production bindingsMetaterm")
     else foldr1(\ a::String b::String -> a ++ " " ++ b,
                 map(\p::Pair<String Maybe<Type>> ->
                     case p of
                     | pair(a, just(ty)) -> "(" ++ a ++ " : " ++ ty.pp ++ ")"
                     | pair(a, nothing()) -> a
                     end, bindings));
  top.pp = b.pp ++ " " ++ bindingsString ++ ", " ++ body.pp;
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
  top.pp = replicate(n, "*");
}


abstract production atRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "@");
}


abstract production plusRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "+");
}


abstract production hashRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "#");
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





nonterminal Term with pp;

abstract production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp = "(" ++ f.pp ++ ") " ++ args.pp;
}


abstract production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.pp = case ty of
           | just(t) -> "(" ++ name ++ " : " ++ t.pp ++ ")"
           | nothing() -> name
           end;
}


abstract production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.pp = case ty of
           | just(t) -> "(_ : " ++ t.pp ++ ")"
           | nothing() -> "_"
           end;
}





nonterminal TermList with pp;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = "(" ++ t.pp ++ ")";
}


abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = "(" ++ t.pp ++ ") " ++ rest.pp;
}

