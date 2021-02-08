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
  top.pp = arg1.pp ++ " + " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an plusMetaterm");
  top.shouldHide = false;
}


aspect production minusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " - " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an minusMetaterm");
  top.shouldHide = false;
}


aspect production multiplyMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " * " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an multiplyMetaterm");
  top.shouldHide = false;
}


aspect production divideMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " / " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an divideMetaterm");
  top.shouldHide = false;
}


aspect production modulusMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " mod " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an modulusMetaterm");
  top.shouldHide = false;
}


aspect production lessMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " < " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an lessMetaterm");
  top.shouldHide = false;
}


aspect production lessEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " <= " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an lessEqMetaterm");
  top.shouldHide = false;
}


aspect production greaterMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " > " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an greaterMetaterm");
  top.shouldHide = false;
}


aspect production greaterEqMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " >= " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an greaterEqMetaterm");
  top.shouldHide = false;
}


aspect production negateMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.pp = "- " ++ arg.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an negateMetaterm");
  top.shouldHide = false;
}




{-
  APPEND
-}

aspect production appendMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg2.pp ++ " ++ " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an appendMetaterm");
  top.shouldHide = false;
}




{-
  BOOLEAN OPERATIONS
-}

aspect production orBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg2.pp ++ " || " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a orBoolMetaterm");
  top.shouldHide = false;
}


aspect production andBoolMetaterm
top::Metaterm ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg2.pp ++ " && " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a andBoolMetaterm");
  top.shouldHide = false;
}


aspect production notBoolMetaterm
top::Metaterm ::= arg::Term result::Term
{
  top.pp = "! " ++ arg.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a notBoolMetaterm");
  top.shouldHide = false;
}




{-
  BOOLEAN CONSTANTS
-}

aspect production trueTerm
top::Term ::=
{
  top.pp = "true";
  top.isAtomic = true;

  top.translation = error("Should never be translatiing a trueTerm");
  top.shouldHide = false;
}


aspect production falseTerm
top::Term ::=
{
  top.pp = "false";
  top.isAtomic = true;

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
  top.pp = toString(i);
  top.isAtomic = true;

  top.translation = error("Should never be translating an intTerm");
  top.shouldHide = false;
}




{-
  LIST CONSTANTS
-}

aspect production listTerm
top::Term ::= contents::ListContents
{
  top.pp = "[" ++ contents.pp ++ "]";
  top.isAtomic = true;

  top.translation = error("Should never be translating a listTerm");
  top.shouldHide = false;
}



attribute pp occurs on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.pp = "";
}


aspect production addListContents
top::ListContents ::= t::Term rest::ListContents
{
  top.pp = t.pp ++ (if rest.pp == "" then "" else ", " ++ rest.pp);
}




{-
  STRING CONSTANTS
-}

aspect production stringTerm
top::Term ::= contents::String
{
  top.pp = "\"" ++ contents ++ "\"";
  top.isAtomic = true;

  top.translation = error("Should never be translating a stringTerm");
  top.shouldHide = false;
}


--This is just for getting strings vs. lists of strings correct
abstract production charTerm
top::Term ::= char::String
{
  top.pp = "\"" ++ char ++ "\"";
  top.isAtomic = true;

  top.translation = error("Should never be translating a charTerm");
  top.shouldHide = false;
}




{-
  ATTRIBUTE ACCESS
-}

aspect production attrAccessTerm
top::Term ::= treename::String attr::String
{
  top.pp = treename ++ "." ++ attr;
  top.isAtomic = true;

  top.translation = error("Should not be translating attrAccessTerm");
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
}

