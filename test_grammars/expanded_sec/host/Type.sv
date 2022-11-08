grammar expanded_sec:host;

nonterminal Type with
   isIntTy, isBoolTy, isRecTy, recTyFields,
   compareTy, isTyEqual;

--Because we can't encode pattern matching, write attributes
synthesized attribute isIntTy::Boolean;
synthesized attribute isBoolTy::Boolean;
synthesized attribute isRecTy::Boolean;
synthesized attribute recTyFields::[(String, Type)];
--Comparing two types
inherited attribute compareTy::Type;
synthesized attribute isTyEqual::Boolean;

abstract production intTy
top::Type ::=
{
  top.isIntTy = true;
  top.isBoolTy = false;
  top.isRecTy = false;
  top.recTyFields = error("Not a record type");

  local comp::Type = top.compareTy;
  top.isTyEqual = comp.isIntTy;
}


abstract production boolTy
top::Type ::=
{
  top.isIntTy = false;
  top.isBoolTy = true;
  top.isRecTy = false;
  top.recTyFields = error("Not a record type");

  local comp::Type = top.compareTy;
  top.isTyEqual = comp.isBoolTy;
}


abstract production recTy
top::Type ::= contents::[(String, Type)]
{
  top.isIntTy = false;
  top.isBoolTy = false;
  top.isRecTy = true;
  top.recTyFields = contents;

  local comp::Type = top.compareTy;
  top.isTyEqual =
      comp.isRecTy &&
      fieldsContained(contents, comp.recTyFields) &&
      fieldsContained(comp.recTyFields, contents);
}



function fieldsContained
Boolean ::= fields::[(String, Type)] contained::[(String, Type)]
{
  return if null(fields)
         then true
         else if member(head(fields).1, contained)
         then tysEq(head(fields).2,
                    lookupTy(head(fields).1, contained)) &&
              fieldsContained(tail(fields), contained)
         else false;
}

function tysEq
Boolean ::= ty1::Type ty2::Type
{
  ty1.compareTy = ty2;
  return ty1.isTyEqual;
}

function member
Boolean ::= v::String ctx::[(String, Type)]
{
  return if null(ctx)
         then false
         else head(ctx).1 == v || member(v, tail(ctx));
}




function lookupTy
Type ::= v::String tys::[(String, Type)]
{
  return if null(tys)
         then error("Not found")
         else if head(tys).1 == v
              then head(tys).2
              else lookupTy(v, tail(tys));
}
