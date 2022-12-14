grammar expanded_sec:host;

nonterminal C with
   tyCtx, tyCtx_out, funTyCtx, wellTyped,
   evalCtx, evalCtx_out, funEvalCtx, printedOutput;

abstract production noop
top::C ::=
{
  top.tyCtx_out = top.tyCtx;

  top.wellTyped = true;
  --
  top.evalCtx_out = top.evalCtx;
  top.printedOutput = [];
}


abstract production seq
top::C ::= c1::C c2::C
{
  c1.tyCtx = top.tyCtx;
  c2.tyCtx = c1.tyCtx_out;
  top.tyCtx_out = c2.tyCtx_out;

  top.wellTyped = c1.wellTyped && c2.wellTyped;

  c1.funTyCtx = top.funTyCtx;
  c2.funTyCtx = top.funTyCtx;
  --
  c1.evalCtx = top.evalCtx;
  c2.evalCtx = c1.evalCtx_out;
  top.evalCtx_out = c2.evalCtx_out;

  c1.funEvalCtx = top.funEvalCtx;
  c2.funEvalCtx = top.funEvalCtx;

  top.printedOutput = c1.printedOutput ++ c2.printedOutput;
}


abstract production declare
top::C ::= v::String ty::Type e::Expr
{
  e.tyCtx = top.tyCtx;
  ty.compareTy = e.ty;
  top.tyCtx_out = pair(v, ty)::top.tyCtx;

  top.wellTyped = ty.isTyEqual;

  e.funTyCtx = top.funTyCtx;
  --
  e.evalCtx = top.evalCtx;
  e.funEvalCtx = top.funEvalCtx;
  top.evalCtx_out = (v, e.value)::top.evalCtx;
  top.printedOutput = e.printedOutput;
}


abstract production assign
top::C ::= v::String e::Expr
{
  e.tyCtx = top.tyCtx;
  local vty::Type = lookupTy(v, top.tyCtx);
  vty.compareTy = e.ty;
  top.tyCtx_out = top.tyCtx;

  top.wellTyped = vty.isTyEqual;

  e.funTyCtx = top.funTyCtx;
  --
  e.evalCtx = top.evalCtx;
  e.funEvalCtx = top.funEvalCtx;
  top.evalCtx_out = (v, e.value)::top.evalCtx;
  top.printedOutput = e.printedOutput;
}


abstract production ifThenElse
top::C ::= cond::Expr th::C el::C
{
  cond.tyCtx = top.tyCtx;
  th.tyCtx = top.tyCtx;
  el.tyCtx = top.tyCtx;
  top.tyCtx_out =top.tyCtx;

  local condTy::Type = cond.ty;
  top.wellTyped = condTy.isBoolTy && th.wellTyped && el.wellTyped;

  cond.funTyCtx = top.funTyCtx;
  th.funTyCtx = top.funTyCtx;
  el.funTyCtx = top.funTyCtx;
  --
  cond.evalCtx = top.evalCtx;
  th.evalCtx = top.evalCtx;
  el.evalCtx = top.evalCtx;

  cond.funEvalCtx = top.funEvalCtx;
  th.funEvalCtx = top.funEvalCtx;
  el.funEvalCtx = top.funEvalCtx;

  top.evalCtx_out =
      if cond.value.isTrueVal
      then th.evalCtx_out
      else if cond.value.isFalseVal
           then el.evalCtx_out
           else error("Bad condition value");
  top.printedOutput =
      cond.printedOutput ++
      if cond.value.isTrueVal
      then th.printedOutput
      else if cond.value.isFalseVal
           then el.printedOutput
           else error("Bad condition value");
}


abstract production while
top::C ::= cond::Expr body::C
{
  cond.tyCtx = top.tyCtx;
  body.tyCtx = top.tyCtx;
  top.tyCtx_out = top.tyCtx;

  local condTy::Type = cond.ty;
  top.wellTyped = condTy.isBoolTy && body.wellTyped;

  cond.funTyCtx = top.funTyCtx;
  body.funTyCtx = top.funTyCtx;
  --
  local subWhile::C = while(cond, body);

  cond.evalCtx = top.evalCtx;
  body.evalCtx = top.evalCtx;
  subWhile.evalCtx = body.evalCtx_out;

  cond.funEvalCtx = top.funEvalCtx;
  body.funEvalCtx = top.funEvalCtx;
  subWhile.funEvalCtx = top.funEvalCtx;

  top.evalCtx_out =
      if cond.value.isTrueVal
      then subWhile.evalCtx_out
      else if cond.value.isFalseVal
           then top.evalCtx
           else error("Bad condition value");
  top.printedOutput =
      cond.printedOutput ++
      if cond.value.isTrueVal
      then body.printedOutput ++ subWhile.printedOutput
      else if cond.value.isFalseVal
           then []
           else error("Bad condition value");
}


abstract production recUpdate
top::C ::= rec::String fields::RecFields e::Expr
{
  e.tyCtx = top.tyCtx;
  local lookedUp::Type = lookupTy(rec, top.tyCtx);
  fields.incomingFields = lookedUp.recTyFields;
  top.tyCtx_out = top.tyCtx;

  top.wellTyped = tysEq(e.ty, fields.ty);

  e.funTyCtx = top.funTyCtx;
  --
  e.evalCtx = top.evalCtx;
  e.funEvalCtx = top.funEvalCtx;
  local findRec::Value = lookupVal(rec, top.evalCtx);
  fields.evalRecFields = findRec.recValFields;
  fields.newVal = e.value;
  top.evalCtx_out = (rec, fields.value)::top.evalCtx;
  top.printedOutput = e.printedOutput;
}


abstract production printVal
top::C ::= e::Expr
{
  e.tyCtx = top.tyCtx;
  top.tyCtx_out = top.tyCtx;

  --just check that e.ty has a value, really
  local eTy::Type = e.ty;
  top.wellTyped = eTy.isIntTy || !eTy.isIntTy;

  e.funTyCtx = top.funTyCtx;
  --
  e.evalCtx = top.evalCtx;
  e.funEvalCtx = top.funEvalCtx;
  top.evalCtx_out = top.evalCtx;
  top.printedOutput = e.printedOutput ++ [e.value];
}





nonterminal RecFields with
   incomingFields, ty, evalRecFields, newVal, value;
inherited attribute incomingFields::[(String, Type)];
--
inherited attribute evalRecFields::[(String, Value)];
inherited attribute newVal::Value;

abstract production oneField
top::RecFields ::= field::String
{
  top.ty = lookupTy(field, top.incomingFields);
  --
  top.value = recVal((field, top.newVal)::top.evalRecFields);
}


abstract production addField
top::RecFields ::= field::String rest::RecFields
{
  local lookedUp::Type = lookupTy(field, top.incomingFields);
  rest.incomingFields = lookedUp.recTyFields;
  top.ty = rest.ty;
  --
  local lookupField::Value = lookupVal(field, top.evalRecFields);
  rest.evalRecFields = lookupField.recValFields;
  rest.newVal = top.newVal;
  top.value = recVal((field, rest.value)::top.evalRecFields);
}
