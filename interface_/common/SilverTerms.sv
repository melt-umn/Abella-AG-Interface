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
{ }

abstract production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production negateMetaterm
top::Metaterm ::= t::Term result::Term
{ }

abstract production lessMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{ }

abstract production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{ }



--TERMS
abstract production attrAccessTerm
top::Term ::= treename::String attr::String
{ }

abstract production intTerm
top::Term ::= i::Integer
{ }

abstract production stringTerm
top::Term ::= contents::String
{ }

abstract production trueTerm
top::Term ::=
{ }

abstract production falseTerm
top::Term ::=
{ }

abstract production listTerm
top::Term ::= contents::ListContents
{ }


nonterminal ListContents;

abstract production emptyListContents
top::ListContents ::=
{ }

abstract production addListContents
top::ListContents ::= t::Term rest::ListContents
{ }

