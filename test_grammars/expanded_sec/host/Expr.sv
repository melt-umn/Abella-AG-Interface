grammar expanded_sec:host;

nonterminal Expr with vars, tyCtx, ty, evalCtx, value;

abstract production num
top::Expr ::= i::Integer
{
  top.vars = [];

  top.ty = intTy();

  top.value = intVal(i);
}


abstract production plus
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;

  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isIntTy && ty2.isIntTy
           then intTy()
           else error("plus type error");

  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;
  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = intVal(v1.intValNum + v2.intValNum);
}


abstract production name
top::Expr ::= v::String
{
  top.vars = [v];

  top.ty = lookupTy(v, top.tyCtx);

  top.value = lookupVal(v, top.evalCtx);
}


abstract production greater
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;

  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isIntTy && ty2.isIntTy
           then boolTy()
           else error("greater type error");

  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;
  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = if v1.intValNum > v2.intValNum
              then trueVal()
              else falseVal();
}


abstract production eqCheck
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;

  local ty::Type = e1.ty;
  ty.compareTy = e2.ty;
  top.ty = if ty.isTyEqual
           then boolTy()
           else error("eqCheck eval error");
}


abstract production and
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;

  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isBoolTy && ty2.isBoolTy
           then boolTy()
           else error("and type error");

  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;
  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = if v1.isFalseVal
              then falseVal()
              else if v2.isTrueVal
                   then trueVal()
                   else if v2.isFalseVal
                        then falseVal()
                        else error("and eval error");
}


abstract production or
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;

  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isBoolTy && ty2.isBoolTy
           then boolTy()
           else error("or type error");

  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;
  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = if v1.isTrueVal
              then trueVal()
              else if v2.isTrueVal
                   then trueVal()
                   else if v2.isFalseVal
                        then falseVal()
                        else error("or eval error");
}


abstract production etrue
top::Expr ::=
{
  top.vars = [];

  top.ty = boolTy();

  top.value = trueVal();
}


abstract production efalse
top::Expr ::=
{
  top.vars = [];

  top.ty = boolTy();

  top.value = falseVal();
}


abstract production recBuild
top::Expr ::= contents::RecFieldExprs
{
  top.vars = contents.vars;

  contents.tyCtx = top.tyCtx;
  top.ty = recTy(contents.tyCtx_out);

  contents.evalCtx = top.evalCtx;
  top.value = recVal(contents.evalCtx_out);
}


abstract production recFieldAccess
top::Expr ::= rec::Expr field::String
{
  top.vars = rec.vars;

  rec.tyCtx = top.tyCtx;
  local rty::Type = rec.ty;
  top.ty = lookupTy(field, rty.recTyFields);

  rec.evalCtx = top.evalCtx;
  local rval::Value = rec.value;
  top.value = lookupVal(field, rval.recValFields);
}





nonterminal RecFieldExprs with
   vars, tyCtx, tyCtx_out, evalCtx, evalCtx_out;

abstract production endRecFieldExprs
top::RecFieldExprs ::=
{
  top.vars = [];

  top.tyCtx_out = [];

  top.evalCtx_out = [];
}


abstract production addRecFieldExprs
top::RecFieldExprs ::= field::String e::Expr rest::RecFieldExprs
{
  top.vars = e.vars ++ rest.vars;

  e.tyCtx = top.tyCtx;
  rest.tyCtx = top.tyCtx;
  top.tyCtx_out = (field, e.ty)::rest.tyCtx_out;

  e.evalCtx = top.evalCtx;
  rest.evalCtx = top.evalCtx;
  top.evalCtx_out = (field, e.value)::rest.evalCtx_out;
}