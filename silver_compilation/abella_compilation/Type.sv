grammar abella_compilation;


nonterminal Type with pp, isAtomic, resultType, headTypeName, argumentTypes;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = (if ty1.isAtomic then ty1.pp else "(" ++ ty1.pp ++ ")") ++ " -> " ++ ty2.pp;
  top.isAtomic = false;

  top.resultType = ty2.resultType;
  top.headTypeName = ty2.headTypeName;
  top.argumentTypes = ty1::ty2.argumentTypes;
}

abstract production nameType
top::Type ::= name::String
{
  top.pp = name;
  top.isAtomic = true;

  top.resultType = top;
  top.headTypeName = just(name);
  top.argumentTypes = [];
}

abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = functorTy.pp ++ " " ++ if argTy.isAtomic then argTy.pp else "(" ++ argTy.pp ++ ")";
  top.isAtomic = false;

  top.resultType = top;
  top.headTypeName = functorTy.headTypeName;
  top.argumentTypes = [];
}



function tysEqual
Boolean ::= ty1::Type ty2::Type
{
  return
     case ty1, ty2 of
     | arrowType(t11, t12), arrowType(t21, t22) ->
       tysEqual(t11, t21) && tysEqual(t12, t22)
     | nameType(n1), nameType(n2) -> n1 == n2
     | functorType(f1, a1), functorType(f2, a2) ->
       tysEqual(f1, f2) && tysEqual(a1, a2)
     | _, _ -> false
     end;
}


function tyIsNonterminal
Boolean ::= ty::Type
{
  return
     case ty of
     | nameType(name) when startsWith("nt_", name) -> true
     | _ -> false
     end;
}

