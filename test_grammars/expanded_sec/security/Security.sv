grammar expanded_sec:security;


nonterminal SecurityLevel with isPublic, isPrivate;

synthesized attribute isPublic::Boolean;
synthesized attribute isPrivate::Boolean;

abstract production public
top::SecurityLevel ::=
{
  top.isPublic = true;
  top.isPrivate = false;
}


abstract production private
top::SecurityLevel ::=
{
  top.isPublic = false;
  top.isPrivate = true;
}



function secmax
SecurityLevel ::= s1::SecurityLevel s2::SecurityLevel
{
  return if s1.isPublic && s2.isPublic
         then public()
         else private();
}



function lookupSec
SecurityLevel ::= name::String ctx::[(String, SecurityLevel)]
{
  return if head(ctx).1 == name
         then head(ctx).2
         else lookupSec(name, tail(ctx));
}
