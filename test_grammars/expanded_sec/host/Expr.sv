grammar expanded_sec:host;

nonterminal Expr with
   vars,
   tyCtx, funTyCtx, ty,
   evalCtx, funEvalCtx, value, printedOutput;

abstract production num
top::Expr ::= i::Integer
{
  top.vars = [];
  --
  top.ty = intTy();
  --
  top.value = intVal(i);
  top.printedOutput = [];
}


abstract production plus
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;
  --
  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  e1.funTyCtx = top.funTyCtx;
  e2.funTyCtx = top.funTyCtx;
  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isIntTy && ty2.isIntTy
           then intTy()
           else error("plus type error");
  --
  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;

  e1.funEvalCtx = top.funEvalCtx;
  e2.funEvalCtx = top.funEvalCtx;

  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = intVal(v1.intValNum + v2.intValNum);

  top.printedOutput = e1.printedOutput ++ e2.printedOutput;
}


abstract production name
top::Expr ::= v::String
{
  top.vars = [v];
  --
  top.ty = lookupTy(v, top.tyCtx);
  --
  top.value = lookupVal(v, top.evalCtx);
  top.printedOutput = [];
}


abstract production greater
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;
  --
  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  e1.funTyCtx = top.funTyCtx;
  e2.funTyCtx = top.funTyCtx;
  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isIntTy && ty2.isIntTy
           then boolTy()
           else error("greater type error");
  --
  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;

  e1.funEvalCtx = top.funEvalCtx;
  e2.funEvalCtx = top.funEvalCtx;

  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = if v1.intValNum > v2.intValNum
              then trueVal()
              else falseVal();

  top.printedOutput = e1.printedOutput ++ e2.printedOutput;
}


abstract production eqCheck
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;
  --
  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  e1.funTyCtx = top.funTyCtx;
  e2.funTyCtx = top.funTyCtx;
  local ty::Type = e1.ty;
  ty.compareTy = e2.ty;
  top.ty = if ty.isTyEqual
           then boolTy()
           else error("eqCheck eval error");
  --
  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;

  e1.funEvalCtx = top.funEvalCtx;
  e2.funEvalCtx = top.funEvalCtx;

  top.value = error("Not done");

  top.printedOutput = e1.printedOutput ++ e2.printedOutput;
}


abstract production and
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;
  --
  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;
  e1.funTyCtx = top.funTyCtx;
  e2.funTyCtx = top.funTyCtx;
  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isBoolTy && ty2.isBoolTy
           then boolTy()
           else error("and type error");
  --
  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;

  e1.funEvalCtx = top.funEvalCtx;
  e2.funEvalCtx = top.funEvalCtx;

  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = if v1.isFalseVal
              then falseVal()
              else if v2.isTrueVal
                   then trueVal()
                   else if v2.isFalseVal
                        then falseVal()
                        else error("and eval error");

  top.printedOutput =
      e1.printedOutput ++
      if v1.isFalseVal
      then []
      else e2.printedOutput;
}


abstract production or
top::Expr ::= e1::Expr e2::Expr
{
  top.vars = e1.vars ++ e2.vars;
  --
  e1.tyCtx = top.tyCtx;
  e2.tyCtx = top.tyCtx;

  e1.funTyCtx = top.funTyCtx;
  e2.funTyCtx = top.funTyCtx;

  local ty1::Type = e1.ty;
  local ty2::Type = e2.ty;
  top.ty = if ty1.isBoolTy && ty2.isBoolTy
           then boolTy()
           else error("or type error");
  --
  e1.evalCtx = top.evalCtx;
  e2.evalCtx = top.evalCtx;

  e1.funEvalCtx = top.funEvalCtx;
  e2.funEvalCtx = top.funEvalCtx;

  local v1::Value = e1.value;
  local v2::Value = e2.value;
  top.value = if v1.isTrueVal
              then trueVal()
              else if v2.isTrueVal
                   then trueVal()
                   else if v2.isFalseVal
                        then falseVal()
                        else error("or eval error");

  top.printedOutput =
      e1.printedOutput ++
      if v1.isTrueVal
      then []
      else e2.printedOutput;
}


abstract production etrue
top::Expr ::=
{
  top.vars = [];
  --
  top.ty = boolTy();
  --
  top.value = trueVal();
  top.printedOutput = [];
}


abstract production efalse
top::Expr ::=
{
  top.vars = [];
  --
  top.ty = boolTy();
  --
  top.value = falseVal();
  top.printedOutput = [];
}


abstract production call
top::Expr ::= funName::String args::Args
{
  top.vars = args.vars;
  --
  args.tyCtx = top.tyCtx;
  args.funTyCtx = top.funTyCtx;
  local funInfo::(Type, Params) = lookupFunTy(funName, top.funTyCtx);
  local p::Params = funInfo.2;
  top.ty = if compareTys(args.tys, p.tys)
           then funInfo.1
           else error("Mismatched argument types");
  --
  args.evalCtx = top.evalCtx;
  args.funEvalCtx = top.funEvalCtx;

  local evalFunInfo::(String, [String], C) =
        lookupFunEval(funName, top.funEvalCtx);
  local funBody::C = evalFunInfo.3;
  funBody.evalCtx = buildEvalCtx(evalFunInfo.2, args.vals);
  funBody.funEvalCtx = top.funEvalCtx;

  top.value = lookupVal(evalFunInfo.1, funBody.evalCtx_out);

  top.printedOutput = args.printedOutput ++ funBody.printedOutput;
}


abstract production recBuild
top::Expr ::= contents::RecFieldExprs
{
  top.vars = contents.vars;
  --
  contents.tyCtx = top.tyCtx;
  contents.funTyCtx = top.funTyCtx;
  top.ty = recTy(contents.tyCtx_out);
  --
  contents.evalCtx = top.evalCtx;
  contents.funEvalCtx = top.funEvalCtx;
  top.value = recVal(contents.evalCtx_out);
  top.printedOutput = contents.printedOutput;
}


abstract production recFieldAccess
top::Expr ::= rec::Expr field::String
{
  top.vars = rec.vars;
  --
  rec.tyCtx = top.tyCtx;
  rec.funTyCtx = top.funTyCtx;
  local rty::Type = rec.ty;
  top.ty = lookupTy(field, rty.recTyFields);
  --
  rec.evalCtx = top.evalCtx;
  rec.funEvalCtx = top.funEvalCtx;
  local rval::Value = rec.value;
  top.value = lookupVal(field, rval.recValFields);
  top.printedOutput = rec.printedOutput;
}





nonterminal RecFieldExprs with
   vars,
   tyCtx, funTyCtx, tyCtx_out,
   evalCtx, funEvalCtx, evalCtx_out, printedOutput;

abstract production endRecFieldExprs
top::RecFieldExprs ::=
{
  top.vars = [];
  --
  top.tyCtx_out = [];
  --
  top.evalCtx_out = [];
  top.printedOutput = [];
}


abstract production addRecFieldExprs
top::RecFieldExprs ::= field::String e::Expr rest::RecFieldExprs
{
  top.vars = e.vars ++ rest.vars;
  --
  e.tyCtx = top.tyCtx;
  rest.tyCtx = top.tyCtx;

  e.funTyCtx = top.funTyCtx;
  rest.funTyCtx = top.funTyCtx;

  top.tyCtx_out = (field, e.ty)::rest.tyCtx_out;
  --
  e.evalCtx = top.evalCtx;
  rest.evalCtx = top.evalCtx;

  e.funEvalCtx = top.funEvalCtx;
  rest.funEvalCtx = top.funEvalCtx;

  top.evalCtx_out = (field, e.value)::rest.evalCtx_out;
  top.printedOutput = e.printedOutput ++ rest.printedOutput;
}





nonterminal Args with
   vars,
   tyCtx, funTyCtx, tys,
   evalCtx, funEvalCtx, vals, printedOutput;

abstract production endArgs
top::Args ::=
{
  top.vars = [];
  --
  top.tys = [];
  --
  top.vals = [];
  top.printedOutput = [];
}


abstract production addArgs
top::Args ::= e::Expr rest::Args
{
  top.vars = e.vars ++ rest.vars;
  --
  e.tyCtx = top.tyCtx;
  rest.tyCtx = top.tyCtx;

  e.funTyCtx = top.funTyCtx;
  rest.funTyCtx = top.funTyCtx;

  top.tys = e.ty::rest.tys;
  --
  e.evalCtx = top.evalCtx;
  rest.evalCtx = top.evalCtx;

  e.funEvalCtx = top.funEvalCtx;
  rest.funEvalCtx = top.funEvalCtx;

  top.vals = e.value::rest.vals;
  top.printedOutput = e.printedOutput ++ rest.printedOutput;
}