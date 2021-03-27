grammar interface_:fromAbella:abstractSyntax;

{-
  This file contains the terms which only show up in the translated
  output.  These are to make the output look nicer and hide the
  details of what we do in the encoding.

  Some of these are actually Metaterms, but we are translating a Term,
  so we can't handle it like that.
-}


{-
  INTEGER OPERATIONS
-}

aspect production plusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an plusMetaterm");
  top.shouldHide = false;
}


aspect production minusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an minusMetaterm");
  top.shouldHide = false;
}


aspect production multiplyMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an multiplyMetaterm");
  top.shouldHide = false;
}


aspect production divideMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an divideMetaterm");
  top.shouldHide = false;
}


aspect production modulusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an modulusMetaterm");
  top.shouldHide = false;
}


aspect production lessMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an lessMetaterm");
  top.shouldHide = false;
}


aspect production lessEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an lessEqMetaterm");
  top.shouldHide = false;
}


aspect production greaterMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an greaterMetaterm");
  top.shouldHide = false;
}


aspect production greaterEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an greaterEqMetaterm");
  top.shouldHide = false;
}


aspect production negateMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.translation = error("Should never be translating an negateMetaterm");
  top.shouldHide = false;
}




{-
  APPEND
-}

aspect production appendMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an appendMetaterm");
  top.shouldHide = false;
}




{-
  BOOLEAN OPERATIONS
-}

aspect production orBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating a orBoolMetaterm");
  top.shouldHide = false;
}


aspect production andBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating a andBoolMetaterm");
  top.shouldHide = false;
}


aspect production notBoolMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.translation = error("Should never be translating a notBoolMetaterm");
  top.shouldHide = false;
}




{-
  ATTRIBUTE ACCESS
-}

aspect production attrAccessMetaterm
top::Metaterm ::= tree::String attr::String val::Term
{
  top.translation = error("Should never be translating an attrAccessMetaterm");
  top.shouldHide = false;
}


aspect production attrAccessEmptyMetaterm
top::Metaterm ::= tree::String attr::String
{
  top.translation = error("Should enver be translating an attrAccessEmptyMetaterm");
  top.shouldHide = false;
}




{-
  BOOLEAN CONSTANTS
-}

aspect production trueTerm
top::Term ::=
{
  top.translation = error("Should never be translatiing a trueTerm");
  top.shouldHide = false;
}


aspect production falseTerm
top::Term ::=
{
  top.translation = error("Should never be translatiing a falseTerm");
  top.shouldHide = false;
}




{-
  INTEGER CONSTANTS
-}

--We're going to use this for nats to facilitate translation,
--since the user should never have bare nats there anyway
aspect production intTerm
top::Term ::= i::Integer
{
  top.translation = error("Should never be translating an intTerm");
  top.shouldHide = false;
}




{-
  LIST SYNTAX
-}

aspect production listTerm
top::Term ::= contents::ListContents
{
  top.translation = error("Should never be translating a listTerm");
  top.shouldHide = false;
}




{-
  PAIR SYNTAX
-}

aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.translation = error("Should never be translating a pairTerm");
  top.shouldHide = false;
}




{-
  STRING CONSTANTS
-}

aspect production stringTerm
top::Term ::= contents::String
{
  top.translation = error("Should never be translating a stringTerm");
  top.shouldHide = false;
}


--This is just for getting strings vs. lists of strings correct
aspect production charTerm
top::Term ::= char::String
{
  top.translation = error("Should never be translating a charTerm");
  top.shouldHide = false;
}




{-
  HIDDEN HYPOTHESES
-}

abstract production hiddenHypothesis
top::Hypothesis ::= name::String body::Metaterm
{
  top.pp = "";

  top.translation = error("Should never be translating a hiddenHypothesis");

  top.hypList = [(name, new(body))];

  forwards to metatermHyp(name, body);
}

