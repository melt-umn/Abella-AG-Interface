grammar interface_:common:abstractSyntax;


nonterminal Type with pp, isAtomic, silverContext;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = (if ty1.isAtomic then ty1.pp else "(" ++ ty1.pp ++ ")") ++ " -> " ++ ty2.pp;
  top.isAtomic = false;

  propagate silverContext;
}

abstract production nameType
top::Type ::= name::String
{
  top.pp = name;
  top.isAtomic = true;

  propagate silverContext;
}

abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = functorTy.pp ++ " " ++ if argTy.isAtomic then argTy.pp else "(" ++ argTy.pp ++ ")";
  top.isAtomic = false;

  propagate silverContext;
}

abstract production underscoreType
top::Type ::=
{
  top.pp = "_";
  top.isAtomic = true;

  propagate silverContext;
}

