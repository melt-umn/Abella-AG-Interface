grammar interface_:common;


--METATERMS
{-
  Why don't we just put these operations in Term?  Then we could use
  something like `3+4` directly in the next addition.  That sounds
  wonderful, but it doesn't really fit the Abella style, and thus it
  would be really difficult to work with.  We would not have a good
  way to use properties of the arithmetic operations, which are
  theorems which need to be applied.

  The translation of the numeric operations will need to be dependent
  on typing once we add floats.
-}
abstract production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " + " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " - " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " * " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " / " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " mod " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "- " ++ t.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production lessMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " < " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " <= " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " > " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " >= " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " ++ " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " || " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " && " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}

abstract production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "! " ++ t.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
}



--TERMS
abstract production attrAccessTerm
top::Term ::= treename::String attr::String
{
  top.pp = treename ++ "." ++ attr;
  top.isAtomic = true;
}

abstract production intTerm
top::Term ::= i::Integer
{
  top.pp = toString(i);
  top.isAtomic = true;
}

abstract production stringTerm
top::Term ::= contents::String
{
  top.pp = "\"" ++ contents ++ "\"";
  top.isAtomic = true;
}

abstract production trueTerm
top::Term ::=
{
  top.pp = "true";
  top.isAtomic = true;
}

abstract production falseTerm
top::Term ::=
{
  top.pp = "false";
  top.isAtomic = true;
}

abstract production listTerm
top::Term ::= contents::ListContents
{
  top.pp = "[" ++ contents.pp ++ "]";
  top.isAtomic = true;
}

abstract production pairTerm
top::Term ::= contents::PairContents
{
  top.pp = "(" ++ contents.pp ++ ")";
  top.isAtomic = true;
}

abstract production charTerm
top::Term ::= char::String
{
  top.pp = "\"" ++ char ++ "\"";
  top.isAtomic = true;
}




nonterminal ListContents with pp;

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




nonterminal PairContents with pp;

abstract production singlePairContents
top::PairContents ::= t::Term
{
  top.pp = t.pp;
}

abstract production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.pp = t.pp ++ ", " ++ rest.pp;
}

