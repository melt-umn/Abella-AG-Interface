grammar expanded_sec:host;

nonterminal Value with
   intValNum, isTrueVal, isFalseVal, recValFields;

synthesized attribute intValNum::Integer;
synthesized attribute isTrueVal::Boolean;
synthesized attribute isFalseVal::Boolean;
synthesized attribute recValFields::[(String, Value)];

abstract production intVal
top::Value ::= i::Integer
{
  top.intValNum = i;
  top.isTrueVal = error("Not a Boolean value");
  top.isFalseVal = error("Not a Boolean value");
  top.recValFields = error("Not a record value");
}


abstract production trueVal
top::Value ::=
{
  top.intValNum = error("Not an integer value");
  top.isTrueVal = true;
  top.isFalseVal = false;
  top.recValFields = error("Not a record value");
}


abstract production falseVal
top::Value ::=
{
  top.intValNum = error("Not an integer value");
  top.isTrueVal = false;
  top.isFalseVal = true;
  top.recValFields = error("Not a record value");
}


abstract production recVal
top::Value ::= contents::[(String, Value)]
{
  top.intValNum = error("Not an integer value");
  top.isTrueVal = error("Not a Boolean value");
  top.isFalseVal = error("Not a Boolean value");
  top.recValFields = contents;
}




function lookupVal
Value ::= v::String vals::[(String, Value)]
{
  return if null(vals)
         then error("Not found")
         else if head(vals).1 == v
              then head(vals).2
              else lookupVal(v, tail(vals));
}
