grammar expanded_sec:security;

attribute secCtx, funSecCtx, pc, level occurs on Expr;

aspect production num
top::Expr ::= i::Integer
{
  top.level = public();
}


aspect production plus
top::Expr ::= e1::Expr e2::Expr
{
  e1.secCtx = top.secCtx;
  e2.secCtx = top.secCtx;

  e1.funSecCtx = top.funSecCtx;
  e2.funSecCtx = top.funSecCtx;

  e1.pc = top.pc;
  e2.pc = top.pc;

  top.level = secmax(e1.level, e2.level);
}


aspect production name
top::Expr ::= v::String
{
  top.level = lookupSec(v, top.secCtx);
}


aspect production greater
top::Expr ::= e1::Expr e2::Expr
{
  e1.secCtx = top.secCtx;
  e2.secCtx = top.secCtx;

  e1.funSecCtx = top.funSecCtx;
  e2.funSecCtx = top.funSecCtx;

  e1.pc = top.pc;
  e2.pc = top.pc;

  top.level = secmax(e1.level, e2.level);
}


aspect production eqCheck
top::Expr ::= e1::Expr e2::Expr
{
  e1.secCtx = top.secCtx;
  e2.secCtx = top.secCtx;

  e1.funSecCtx = top.funSecCtx;
  e2.funSecCtx = top.funSecCtx;

  e1.pc = top.pc;
  e2.pc = top.pc;

  top.level = secmax(e1.level, e2.level);
}


aspect production and
top::Expr ::= e1::Expr e2::Expr
{
  e1.secCtx = top.secCtx;
  e2.secCtx = top.secCtx;

  e1.funSecCtx = top.funSecCtx;
  e2.funSecCtx = top.funSecCtx;

  e1.pc = top.pc;
  e2.pc = top.pc;

  top.level = secmax(e1.level, e2.level);
}


aspect production or
top::Expr ::= e1::Expr e2::Expr
{
  e1.secCtx = top.secCtx;
  e2.secCtx = top.secCtx;

  e1.funSecCtx = top.funSecCtx;
  e2.funSecCtx = top.funSecCtx;

  e1.pc = top.pc;
  e2.pc = top.pc;

  top.level = secmax(e1.level, e2.level);
}


aspect production etrue
top::Expr ::=
{
  top.level = public();
}


aspect production efalse
top::Expr ::=
{
  top.level = public();
}


aspect production call
top::Expr ::= funName::String args::Args
{
  args.secCtx = top.secCtx;
  args.funSecCtx = top.funSecCtx;
  args.pc = top.pc;

  local funSec::(SecurityLevel, SecurityLevel, [SecurityLevel]) =
        lookupFunSec(funName, top.funSecCtx);
  local funStart::SecurityLevel = funSec.1;
  local pc::SecurityLevel = top.pc;
  top.level =
      if ((pc.isPublic && funStart.isPublic) || funStart.isPrivate) &&
         secureArgCombination(args.levels, funSec.3)
      then funSec.2
      else error("Invalid security combination");
}


aspect production recBuild
top::Expr ::= contents::RecFieldExprs
{
  contents.secCtx = top.secCtx;
  contents.funSecCtx = top.funSecCtx;
  contents.pc = top.pc;
  top.level = contents.level;
}


aspect production recFieldAccess
top::Expr ::= rec::Expr field::String
{
  rec.secCtx = top.secCtx;
  rec.funSecCtx = top.funSecCtx;
  rec.pc = top.pc;
  top.level = rec.level;
}





attribute secCtx, funSecCtx, pc, level occurs on RecFieldExprs;

aspect production endRecFieldExprs
top::RecFieldExprs ::=
{
  top.level = public();
}


aspect production addRecFieldExprs
top::RecFieldExprs ::= field::String e::Expr rest::RecFieldExprs
{
  e.secCtx = top.secCtx;
  rest.secCtx = top.secCtx;

  e.funSecCtx = top.funSecCtx;
  rest.funSecCtx = top.funSecCtx;

  e.pc = top.pc;
  rest.pc = top.pc;

  top.level = secmax(e.level, rest.level);
}





attribute secCtx, funSecCtx, pc, levels occurs on Args;

aspect production endArgs
top::Args ::=
{
  top.levels = [];
}


aspect production addArgs
top::Args ::= e::Expr rest::Args
{
  e.secCtx = top.secCtx;
  rest.secCtx = top.secCtx;

  e.funSecCtx = top.funSecCtx;
  rest.funSecCtx = top.funSecCtx;

  e.pc = top.pc;
  rest.pc = top.pc;

  top.levels = e.level::rest.levels;
}
