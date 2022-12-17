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

function seclesseq
Boolean ::= s1::SecurityLevel s2::SecurityLevel
{
  return s1.isPublic || (s1.isPrivate && s2.isPrivate);
}

--Check args are valid to give
--Public can go into private but private can't go into public
function secureArgCombination
Boolean ::= given::[SecurityLevel] expected::[SecurityLevel]
{
  return if null(given)
         then true
         else if seclesseq(head(given), head(expected))
              then secureArgCombination(tail(given), tail(expected))
              else false;
}



function lookupSec
SecurityLevel ::= name::String ctx::[(String, SecurityLevel)]
{
  return if head(ctx).1 == name
         then head(ctx).2
         else lookupSec(name, tail(ctx));
}

function lookupFunSec
(SecurityLevel, SecurityLevel, [SecurityLevel]) ::=
   name::String
   ctx::[(String, SecurityLevel, SecurityLevel, [SecurityLevel])]
{
  return if head(ctx).1 == name
         then (head(ctx).2, head(ctx).3, head(ctx).4)
         else lookupFunSec(name, tail(ctx));
}
