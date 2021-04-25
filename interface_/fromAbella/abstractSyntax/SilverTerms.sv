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
}


aspect production minusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an minusMetaterm");
}


aspect production multiplyMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an multiplyMetaterm");
}


aspect production divideMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an divideMetaterm");
}


aspect production modulusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an modulusMetaterm");
}


aspect production lessMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an lessMetaterm");
}


aspect production lessEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an lessEqMetaterm");
}


aspect production greaterMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an greaterMetaterm");
}


aspect production greaterEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an greaterEqMetaterm");
}


aspect production negateMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.translation = error("Should never be translating an negateMetaterm");
}




{-
  APPEND
-}

aspect production appendMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating an appendMetaterm");
}




{-
  BOOLEAN OPERATIONS
-}

aspect production orBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating a orBoolMetaterm");
}


aspect production andBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.translation = error("Should never be translating a andBoolMetaterm");
}


aspect production notBoolMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.translation = error("Should never be translating a notBoolMetaterm");
}




{-
  FUNCTION SYNTAX
-}

aspect production funMetaterm
top::Metaterm ::= funName::String args::ParenthesizedArgs result::Term
{
  top.translation = error("Should never be translating a funMetaterm");
}




{-
  ATTRIBUTE ACCESS
-}

aspect production attrAccessMetaterm
top::Metaterm ::= tree::String attr::String val::Term
{
  top.translation = error("Should never be translating an attrAccessMetaterm");
}


aspect production attrAccessEmptyMetaterm
top::Metaterm ::= tree::String attr::String
{
  top.translation = error("Should never be translating an attrAccessEmptyMetaterm");
}


aspect production localAttrAccessMetaterm
top::Metaterm ::= tree::String attr::String val::Term
{
  top.translation = error("Should never be translating a localAttrAccessMetaterm");
}

aspect production localAttrAccessEmptyMetaterm
top::Metaterm ::= tree::String attr::String
{
  top.translation = error("Should never be translating a localAttrAccessEmptyMetaterm");
}




{-
  BOOLEAN CONSTANTS
-}

aspect production trueTerm
top::Term ::=
{
  top.translation = error("Should never be translatiing a trueTerm");
}


aspect production falseTerm
top::Term ::=
{
  top.translation = error("Should never be translatiing a falseTerm");
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
}




{-
  LIST SYNTAX
-}

aspect production listTerm
top::Term ::= contents::ListContents
{
  top.translation = error("Should never be translating a listTerm");
}




{-
  PAIR SYNTAX
-}

aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.translation = error("Should never be translating a pairTerm");
}




{-
  PRODUCTION SYNTAX
-}

aspect production prodTerm
top::Term ::= prodName::String args::ParenthesizedArgs
{
  top.translation = error("Should never be translating a prodTerm");
}




{-
  STRING CONSTANTS
-}

aspect production stringTerm
top::Term ::= contents::String
{
  top.translation = error("Should never be translating a stringTerm");
}


--This is just for getting strings vs. lists of strings correct
aspect production charTerm
top::Term ::= char::String
{
  top.translation = error("Should never be translating a charTerm");
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

