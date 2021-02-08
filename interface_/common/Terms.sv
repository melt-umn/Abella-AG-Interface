grammar interface_:common;


nonterminal Metaterm;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{ }

abstract production trueMetaterm
top::Metaterm ::=
{ }

abstract production falseMetaterm
top::Metaterm ::=
{ }

abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{ }

abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{ }

abstract production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{ }

abstract production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{ }

abstract production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[Pair<String Maybe<Type>>] body::Metaterm
{ }


nonterminal Restriction;

abstract production emptyRestriction
top::Restriction ::=
{ }

abstract production starRestriction
top::Restriction ::= n::Integer
{ }

abstract production atRestriction
top::Restriction ::= n::Integer
{ }

abstract production plusRestriction
top::Restriction ::= n::Integer
{ }

abstract production hashRestriction
top::Restriction ::= n::Integer
{ }


nonterminal Binder;

abstract production forallBinder
top::Binder ::=
{ }

abstract production existsBinder
top::Binder ::=
{ }

abstract production nablaBinder
top::Binder::=
{ }


nonterminal Term;

abstract production applicationTerm
top::Term ::= f::Term args::TermList
{ }

abstract production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{ }

abstract production consTerm
top::Term ::= t1::Term t2::Term
{ }

abstract production nilTerm
top::Term ::=
{ }

abstract production underscoreTerm
top::Term ::= ty::Maybe<Type>
{ }


nonterminal TermList;

abstract production singleTermList
top::TermList ::= t::Term
{ }

abstract production consTermList
top::TermList ::= t::Term rest::TermList
{ }

