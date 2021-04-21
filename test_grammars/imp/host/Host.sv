grammar imp:host;


inherited attribute env::[(String, Integer)];
synthesized attribute intVal::Integer;
synthesized attribute boolVal::Boolean;
synthesized attribute env_out::[(String, Integer)];


nonterminal A with env, intVal;

abstract production plus
top::A ::= a1::A a2::A
{
  a1.env = top.env;
  a2.env = top.env;
  top.intVal = a1.intVal + a2.intVal;
}


abstract production num
top::A ::= i::Integer
{
  top.intVal = i;
}


abstract production name
top::A ::= s::String
{
  top.intVal = lookup(s, top.env);
}




nonterminal B with env, boolVal;

abstract production greater
top::B ::= a1::A a2::A
{
  a1.env = top.env;
  a2.env = top.env;
  top.boolVal = a1.intVal > a2.intVal;
}


abstract production equal
top::B ::= a1::A a2::A
{
  a1.env = top.env;
  a2.env = top.env;
  top.boolVal = a1.intVal == a2.intVal;
}


abstract production and
top::B ::= b1::B b2::B
{
  b1.env = top.env;
  b2.env = top.env;
  top.boolVal = b1.boolVal && b2.boolVal;
}


abstract production or
top::B ::= b1::B b2::B
{
  b1.env = top.env;
  b2.env = top.env;
  top.boolVal = b1.boolVal && b2.boolVal;
}


abstract production bTrue
top::B ::=
{
  top.boolVal = true;
}


abstract production bFalse
top::B ::=
{
  top.boolVal = false;
}




nonterminal C with env, env_out;

abstract production noop
top::C ::=
{
  top.env_out = top.env;
}


abstract production seq
top::C ::= c1::C c2::C
{
  c1.env = top.env;
  c2.env = c1.env_out;
  top.env_out = c2.env_out;
}


abstract production assign
top::C ::= name::String val::A
{
  val.env = top.env;
  top.env_out = (name, val.intVal)::top.env;
}


abstract production ifThenElse
top::C ::= cond::B th::C el::C
{
  cond.env = top.env;
  th.env = top.env;
  el.env = top.env;
  top.env_out =
      if cond.boolVal
      then th.env_out
      else el.env_out;
}


abstract production while
top::C ::= cond::B body::C
{
  cond.env = top.env;
  body.env = top.env;
  local subWhile::C =
        if cond.boolVal
        then while(cond, body)
        else error("Should not access subWhile");
  subWhile.env = body.env_out;
  top.env_out =
      if cond.boolVal
      then subWhile.env_out
      else top.env;
}




function lookup
Integer ::= name::String env::[(String, Integer)]
{
  --written with if-then-else because pattern matching is a mess
  return
     if head(env).1 == name
     then head(env).2
     else lookup(name, tail(env));
}

