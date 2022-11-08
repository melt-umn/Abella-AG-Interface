grammar expanded_sec:host;

nonterminal C with tyCtx, tyCtx_out;

abstract production noop
top::C ::=
{
  top.tyCtx_out = top.tyCtx;
}


abstract production seq
top::C ::= c1::C c2::C
{
  c1.tyCtx = top.tyCtx;
  c2.tyCtx = c1.tyCtx_out;
  top.tyCtx_out = c2.tyCtx_out;
}


abstract production declare
top::C ::= v::String ty::Type e::Expr
{
  e.tyCtx = top.tyCtx;
  ty.compareTy = e.ty;
  top.tyCtx_out =
      if ty.isTyEqual
      then pair(v, ty)::top.tyCtx
      else error("Mismatched types");
}


abstract production assign
top::C ::= v::String e::Expr
{
  e.tyCtx = top.tyCtx;
  local vty::Type = lookupTy(v, top.tyCtx);
  vty.compareTy = e.ty;
  top.tyCtx_out =
      if vty.isTyEqual
      then top.tyCtx
      else error("Mismatched types");
}


abstract production ifThenElse
top::C ::= cond::Expr th::C el::C
{
  cond.tyCtx = top.tyCtx;
  th.tyCtx = top.tyCtx;
  el.tyCtx = top.tyCtx;
  local condTy::Type = cond.ty;
  top.tyCtx_out =
      if condTy.isBoolTy &&
         fieldsContained(th.tyCtx_out, el.tyCtx_out) &&
         fieldsContained(el.tyCtx_out, th.tyCtx_out)
      then top.tyCtx
      else error("Not typable");
}


abstract production while
top::C ::= cond::Expr body::C
{
  cond.tyCtx = top.tyCtx;
  body.tyCtx = top.tyCtx;
  local condTy::Type = cond.ty;
  top.tyCtx_out =
      if condTy.isBoolTy &&
         fieldsContained(top.tyCtx, body.tyCtx_out) &&
         fieldsContained(body.tyCtx_out, top.tyCtx)
      then top.tyCtx
      else error("Not typable");
}


abstract production recUpdate
top::C ::= rec::String fields::RecFields e::Expr
{
  e.tyCtx = top.tyCtx;
  local lookedUp::Type = lookupTy(rec, top.tyCtx);
  fields.incomingFields = lookedUp.recTyFields;
  top.tyCtx_out = top.tyCtx;
}





nonterminal RecFields with incomingFields, ty;
inherited attribute incomingFields::[(String, Type)];

abstract production oneField
top::RecFields ::= field::String
{
  top.ty = lookupTy(field, top.incomingFields);
}


abstract production addField
top::RecFields ::= field::String rest::RecFields
{
  local lookedUp::Type = lookupTy(field, top.incomingFields);
  rest.incomingFields = lookedUp.recTyFields;
  top.ty = rest.ty;
}
