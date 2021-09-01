grammar imp:security;


imports imp:host;


inherited attribute secCtx::[(String, Integer)] occurs on A, B, C;
synthesized attribute secLevel::Integer occurs on A, B;
inherited attribute programCounter::Integer occurs on C;
synthesized attribute isSecure::Boolean occurs on C;


aspect production plus
top::A ::= a1::A a2::A
{
  a1.secCtx = top.secCtx;
  a2.secCtx = top.secCtx;
  top.secLevel = max(a1.secLevel, a2.secLevel);
}


aspect production num
top::A ::= i::Integer
{
  top.secLevel = 0;
}


aspect production name
top::A ::= s::String
{
  top.secLevel = imp:host:lookup(s, top.secCtx);
}




aspect production greater
top::B ::= a1::A a2::A
{
  a1.secCtx = top.secCtx;
  a2.secCtx = top.secCtx;
  top.secLevel = max(a1.secLevel, a2.secLevel);
}


aspect production equal
top::B ::= a1::A a2::A
{
  a1.secCtx = top.secCtx;
  a2.secCtx = top.secCtx;
  top.secLevel = max(a1.secLevel, a2.secLevel);
}


aspect production and
top::B ::= b1::B b2::B
{
  b1.secCtx = top.secCtx;
  b2.secCtx = top.secCtx;
  top.secLevel = max(b1.secLevel, b2.secLevel);
}


aspect production or
top::B ::= b1::B b2::B
{
  b1.secCtx = top.secCtx;
  b2.secCtx = top.secCtx;
  top.secLevel = max(b1.secLevel, b2.secLevel);
}


aspect production bTrue
top::B ::=
{
  top.secLevel = 0;
}


aspect production bFalse
top::B ::=
{
  top.secLevel = 0;
}




aspect production noop
top::C ::=
{
  top.isSecure = true;
}


aspect production seq
top::C ::= c1::C c2::C
{
  c1.secCtx = top.secCtx;
  c2.secCtx = top.secCtx;
  c1.programCounter = top.programCounter;
  c2.programCounter = top.programCounter;
  top.isSecure = c1.isSecure && c2.isSecure;
}


aspect production assign
top::C ::= name::String val::A
{
  val.secCtx = top.secCtx;
  top.isSecure = imp:host:lookup(name, top.secCtx) >= val.secLevel;
}


aspect production ifThenElse
top::C ::= cond::B th::C el::C
{
  cond.secCtx = top.secCtx;
  th.secCtx = top.secCtx;
  el.secCtx = top.secCtx;
  th.programCounter = max(cond.secLevel, top.programCounter);
  el.programCounter = max(cond.secLevel, top.programCounter);
  top.isSecure = th.isSecure && el.isSecure;
}


aspect production while
top::C ::= cond::B body::C
{
  cond.secCtx = top.secCtx;
  body.secCtx = top.secCtx;
  body.programCounter = max(cond.secLevel, top.programCounter);
  top.isSecure = body.isSecure;
}



function max
Integer ::= i1::Integer i2::Integer
{
  return if i1 > i2 then i1 else i2;
}

