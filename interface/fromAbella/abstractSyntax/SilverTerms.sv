grammar fromAbella:abstractSyntax;

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

abstract production integerAddition
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " + " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerAddition");
  top.shouldHide = false;
}


abstract production integerSubtraction
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " - " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerSubtraction");
  top.shouldHide = false;
}


abstract production integerMultiplication
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " * " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerMultiplication");
  top.shouldHide = false;
}


abstract production integerDivision
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " / " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerDivision");
  top.shouldHide = false;
}


abstract production integerModulus
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " mod " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerModulus");
  top.shouldHide = false;
}


abstract production integerLess
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " < " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerLess");
  top.shouldHide = false;
}


abstract production integerLessEq
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " <= " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerLessEq");
  top.shouldHide = false;
}


abstract production integerGreater
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " > " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerGreater");
  top.shouldHide = false;
}


abstract production integerGreaterEq
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " >= " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerGreaterEq");
  top.shouldHide = false;
}


abstract production integerNegate
top::Term ::= arg::Term result::Term
{
  top.pp = "- " ++ arg.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerNegate");
  top.shouldHide = false;
}




{-
  APPEND
-}

abstract production appendTerm
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg2.pp ++ " ++ " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an append");
  top.shouldHide = false;
}




{-
  BOOLEAN OPERATIONS
-}

abstract production boolOr
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg2.pp ++ " || " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a boolOr");
  top.shouldHide = false;
}


abstract production boolAnd
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg2.pp ++ " && " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a boolAnd");
  top.shouldHide = false;
}


abstract production boolNot
top::Term ::= arg::Term result::Term
{
  top.pp = "! " ++ arg.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a boolNot");
  top.shouldHide = false;
}




{-
  BOOLEAN CONSTANTS
-}

abstract production trueTerm
top::Term ::=
{
  top.pp = "true";
  top.isAtomic = true;

  top.translation = error("Should never be translatiing a trueTerm");
  top.shouldHide = false;
}


abstract production falseTerm
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
abstract production integerTerm
top::Term ::= i::Integer
{
  top.pp = toString(i);
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerTerm");
  top.shouldHide = false;
}




{-
  LIST CONSTANTS
-}

abstract production listTerm
top::Term ::= contents::ListContents
{
  top.pp = "[" ++ contents.pp ++ "]";
  top.isAtomic = true;

  top.translation = error("Should never be translating a listTerm");
  top.shouldHide = false;
}



nonterminal ListContents with
   pp;

abstract production emptyListContents
top::ListContents ::=
{
  top.pp = "";
}


abstract production addListContents
top::ListContents ::= t::Term rest::ListContents
{
  top.pp = t.pp ++ (if rest.pp == "" then "" else ", " ++ rest.pp);
}




{-
  ATTRIBUTE ACCESS
-}

abstract production attrAccess
top::Term ::= treename::String attr::String
{
  top.pp = treename ++ "." ++ attr;
  top.isAtomic = true;

  top.translation = error("Should not be translating attrAccess");
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

