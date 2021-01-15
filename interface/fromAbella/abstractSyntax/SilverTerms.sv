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
}


abstract production integerSubtraction
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " - " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerSubtraction");
}


abstract production integerMultiplication
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " * " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerMultiplication");
}


abstract production integerDivision
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " / " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerDivision");
}


abstract production integerModulus
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " mod " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerModulus");
}


abstract production integerLess
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " < " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerLess");
}


abstract production integerLessEq
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " <= " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerLessEq");
}


abstract production integerGreater
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " > " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerGreater");
}


abstract production integerGreaterEq
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg1.pp ++ " >= " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerGreaterEq");
}


abstract production integerNegate
top::Term ::= arg::Term result::Term
{
  top.pp = "- " ++ arg.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating an integerNegate");
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
}


abstract production boolAnd
top::Term ::= arg1::Term arg2::Term result::Term
{
  top.pp = arg2.pp ++ " && " ++ arg2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a boolAnd");
}


abstract production boolNot
top::Term ::= arg::Term result::Term
{
  top.pp = "! " ++ arg.pp ++ " = " ++ result.pp;
  top.isAtomic = true;

  top.translation = error("Should never be translating a boolNot");
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
}


abstract production falseTerm
top::Term ::=
{
  top.pp = "false";
  top.isAtomic = true;

  top.translation = error("Should never be translatiing a falseTerm");
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
}




{-
  LISTS CONSTANTS
-}

abstract production listTerm
top::Term ::= contents::ListContents
{
  top.pp = "[" ++ contents.pp ++ "]";
  top.isAtomic = true;

  top.translation = error("Should never be translating a listTerm");
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

