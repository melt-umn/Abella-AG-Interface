grammar interface_:common;


nonterminal Type;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{ }

abstract production nameType
top::Type ::= name::String
{ }

abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{ }

abstract production underscoreType
top::Type ::=
{ }

