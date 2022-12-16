grammar expanded_sec:security;

attribute secCtx, pc, funSecCtx, secCtx_out, isSecure;

aspect production noop
top::C ::=
{
  top.secCtx_out = top.secCtx;
  top.isSecure = true;
}


aspect production seq
top::C ::= c1::C c2::C
{
  c1.pc = top.pc;
  c2.pc = top.pc;

  c1.funSecCtx = top.funSecCtx;
  c2.funSecCtx = top.funSecCtx;

  c1.secCtx = top.secCtx;
  c2.secCtx = c1.secCtx_out;
  top.secCtx_out = c2.secCtx_out;

  top.isSecure = c1.isSecure && c2.isSecure;
}


aspect production declare
top::C ::= v::String ty::Type e::Expr
{
  e.pc = top.pc;
  e.secCtx = top.secCtx;
  e.funSecCtx = top.funSecCtx;

  top.secCtx_out = (v, public())::top.secCtx;
  local el::SecurityLevel = e.level;
  top.isSecure = el.isPublic;
}


abstract production declareSec
top::C ::= v::String ty::Type s::SecurityLevel e::Expr
{
  e.pc = top.pc;
  e.secCtx = top.secCtx;
  e.funSecCtx = top.funSecCtx;

  top.secCtx_out = (v, s)::top.secCtx;
  top.isSecure = seclesseq(e.level, s);
  --
  forwards to declare(v, ty, e);
}


aspect production assign
top::C ::= v::String e::Expr
{
  e.pc = top.pc;
  e.secCtx = top.secCtx;
  e.funSecCtx = top.funSecCtx;

  top.secCtx_out = top.secCtx;
  local vlev::SecurityLevel = lookupSec(v, top.secCtx);
  top.isSecure = seclesseq(e.level, vlev);
}


aspect production ifThenElse
top::C ::= cond::Expr th::C el::C
{
  cond.secCtx = top.secCtx;
  th.secCtx = top.secCtx;
  el.secCtx = top.secCtx;

  cond.funSecCtx = top.funSecCtx;
  th.funSecCtx = top.funSecCtx;
  el.funSecCtx = top.funSecCtx;

  cond.pc = top.pc;
  th.pc = secmax(cond.level, top.pc);
  el.pc = secmax(cond.level, top.pc);

  top.secCtx_out = top.secCtx;
  top.isSecure = th.isSecure && el.isSecure;
}


aspect production while
top::C ::= cond::Expr body::C
{

}


aspect production recUpdate
top::C ::= rec::String fields::RecFields e::Expr
{

}


aspect production printVal
top::C ::= e::Expr
{

}





aspect production oneField
top::RecFields ::= field::String
{

}


aspect production addField
top::RecFields ::= field::String rest::RecFields
{

}
