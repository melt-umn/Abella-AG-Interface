grammar calculator;


inherited attribute env::[(String, Integer)];
synthesized attribute value::Integer;

inherited attribute knownNames::[String];
synthesized attribute valExists::Boolean;

nonterminal Expr with env, value, knownNames, valExists;


abstract production intConst
top::Expr ::= i::Integer
{
  top.value = i;

  top.valExists = true;
}


abstract production plus
top::Expr ::= e1::Expr e2::Expr
{
  e1.env = top.env;
  e2.env = top.env;
  top.value = e1.value + e2.value;

  e1.knownNames = top.knownNames;
  e2.knownNames = top.knownNames;
  top.valExists = e1.valExists && e2.valExists;
}


abstract production minus
top::Expr ::= e1::Expr e2::Expr
{
  e1.env = top.env;
  e2.env = top.env;
  top.value = e1.value - e2.value;

  e1.knownNames = top.knownNames;
  e2.knownNames = top.knownNames;
  top.valExists = e1.valExists && e2.valExists;
}


abstract production mult
top::Expr ::= e1::Expr e2::Expr
{
  e1.env = top.env;
  e2.env = top.env;
  top.value = e1.value * e2.value;

  e1.knownNames = top.knownNames;
  e2.knownNames = top.knownNames;
  top.valExists = e1.valExists && e2.valExists;
}


{-abstract production div
top::Expr ::= e1::Expr e2::Expr
{
  e1.env = top.env;
  e2.env = top.env;
  top.value = e1.value / e2.value;
}-}


abstract production letBind
top::Expr ::= n::String e::Expr body::Expr
{
  e.env = top.env;
  body.env = [(n, e.value)] ++ top.env;
  top.value = body.value;

  e.knownNames = top.knownNames;
  body.knownNames = [n] ++ top.knownNames;
  top.valExists = e.valExists && body.valExists;
}


abstract production name
top::Expr ::= n::String
{
  top.value = lookup(top.env, n);

  top.valExists = contains(n, top.knownNames);
}




function lookup
Integer ::= env::[(String, Integer)] n::String
{
  return if fst(head(env)) == n
         then snd(head(env))
         else lookup(tail(env), n);
}

function contains
Boolean ::= n::String l::[String]
{
  return if null(l)
         then false
         else head(l) == n || contains(n, tail(l));
}




nonterminal Root with value, valExists;


abstract production root
top::Root ::= e::Expr
{
  e.env = [];
  top.value = e.value;

  e.knownNames = [];
  top.valExists = e.valExists;
}

