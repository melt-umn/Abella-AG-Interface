grammar imp:host;


inherited attribute env::[(String, Integer)];
synthesized attribute value<a>::a;
synthesized attribute env_out::[(String, Integer)];


nonterminal A with env, value<Integer>;

abstract production plus
top::A ::= a1::A a2::A
{
  a1.env = top.env;
  a2.env = top.env;
  top.value = a1.value + a2.value;
}


abstract production num
top::A ::= i::Integer
{
  top.value = i;
}


abstract production name
top::A ::= s::String
{
  top.value = lookup(s, top.env);
}




nonterminal B with env, value<Boolean>;

abstract production greater
top::B ::= a1::A a2::A
{
  a1.env = top.env;
  a2.env = top.env;
  top.value = a1.value > a2.value;
}


abstract production equal
top::B ::= a1::A a2::A
{
  a1.env = top.env;
  a2.env = top.env;
  top.value = a1.value == a2.value;
}


abstract production and
top::B ::= b1::B b2::B
{
  b1.env = top.env;
  b2.env = top.env;
  top.value = b1.value && b2.value;
}


abstract production or
top::B ::= b1::B b2::B
{
  b1.env = top.env;
  b2.env = top.env;
  top.value = b1.value || b2.value;
}


abstract production bTrue
top::B ::=
{
  top.value = true;
}


abstract production bFalse
top::B ::=
{
  top.value = false;
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
  top.env_out = (name, val.value)::top.env;
}


abstract production ifThenElse
top::C ::= cond::B th::C el::C
{
  cond.env = top.env;
  th.env = top.env;
  el.env = top.env;
  top.env_out =
      if cond.value
      then th.env_out
      else el.env_out;
}


abstract production while
top::C ::= cond::B body::C
{
  cond.env = top.env;
  body.env = top.env;
  local subWhile::C =
        if cond.value
        then while(cond, body)
        else error("Should not access subWhile");
  subWhile.env = body.env_out;
  top.env_out =
      if cond.value
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

--Just to test the encoding
function impossible
Integer ::= name::String
{
  return error("Impossible");
}