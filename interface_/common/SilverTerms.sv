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
  top.shouldHide = false;
}

abstract production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " - " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " * " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " / " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " mod " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "- " ++ t.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production lessMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " < " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " <= " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " > " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " >= " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " ++ " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " || " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.pp = t1.pp ++ " && " ++ t2.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.pp = "! " ++ t.pp ++ " = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production funMetaterm
top::Metaterm ::= funName::String args::ParenthesizedArgs result::Term
{
  top.pp = funName ++ "(" ++ args.pp ++ ") = " ++ result.pp;
  top.isAtomic = true;
  top.shouldHide = false;
}

{-
  We were going to handle attribute access implicitly, with t.a being
  a Term and inserting an access Metaterm earlier in the theorem.
  However, that is difficult to handle when an attribute occurs only
  in the head.  Should we assume the attribute has a value (insert the
  access assumption earlier), or should we have to prove it has a
  value?  If it is the latter, how do we do that implicitly and still
  interact well?  Therefore we make the values of attributes be
  explicitly bound by using this instead.
-}
abstract production attrAccessMetaterm
top::Metaterm ::= tree::String attr::String val::Term
{
  top.pp = tree ++ "." ++ attr ++ " = " ++ val.pp;
  top.isAtomic = true;
  top.shouldHide = false;

  top.usedNames := [tree];
  top.gatheredTrees <- [tree];
}

abstract production attrAccessEmptyMetaterm
top::Metaterm ::= tree::String attr::String
{
  top.pp = tree ++ "." ++ attr ++ " = <no value>";
  top.isAtomic = true;
  top.shouldHide = false;

  top.usedNames := [tree];
  top.gatheredTrees <- [tree];
}


abstract production localAttrAccessMetaterm
top::Metaterm ::= tree::String attr::String val::Term
{
  top.pp = "local " ++ tree ++ "." ++ attr ++ " = " ++ val.pp;
  top.isAtomic = true;
  top.shouldHide = false;

  top.usedNames := [tree];
  top.gatheredTrees <- [tree];
}

abstract production localAttrAccessEmptyMetaterm
top::Metaterm ::= tree::String attr::String
{
  top.pp = "local " ++ tree ++ "." ++ attr ++ " = <no value>";
  top.isAtomic = true;
  top.shouldHide = false;

  top.usedNames := [tree];
  top.gatheredTrees <- [tree];
}



--TERMS
abstract production intTerm
top::Term ::= i::Integer
{
  top.pp = toString(i);
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production stringTerm
top::Term ::= contents::String
{
  top.pp = "\"" ++ contents ++ "\"";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production trueTerm
top::Term ::=
{
  top.pp = "true";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production falseTerm
top::Term ::=
{
  top.pp = "false";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production listTerm
top::Term ::= contents::ListContents
{
  top.pp = "[" ++ contents.pp ++ "]";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production pairTerm
top::Term ::= contents::PairContents
{
  top.pp = "(" ++ contents.pp ++ ")";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production charTerm
top::Term ::= char::String
{
  top.pp = "\"" ++ char ++ "\"";
  top.isAtomic = true;
  top.shouldHide = false;
}

abstract production prodTerm
top::Term ::= prodName::String args::ParenthesizedArgs
{
  top.pp = prodName ++ "(" ++ args.pp ++ ")";
  top.isAtomic = true;
  top.shouldHide = false;
}




nonterminal ParenthesizedArgs with pp, argList, knownTrees, knownDecoratedTrees, usedNames;

abstract production emptyParenthesizedArgs
top::ParenthesizedArgs ::=
{
  top.pp = "";
  top.argList = [];
}

abstract production addParenthesizedArgs
top::ParenthesizedArgs ::= t::Term rest::ParenthesizedArgs
{
  top.pp = t.pp ++ (if rest.pp == "" then "" else ", " ++ rest.pp);
  top.argList = t::rest.argList;
}




nonterminal ListContents with pp, argList, knownTrees, knownDecoratedTrees, usedNames;

abstract production emptyListContents
top::ListContents ::=
{
  top.pp = "";
  top.argList = [];
}

abstract production addListContents
top::ListContents ::= t::Term rest::ListContents
{
  top.pp = t.pp ++ (if rest.pp == "" then "" else ", " ++ rest.pp);
  top.argList = t::rest.argList;
}




nonterminal PairContents with pp, argList, knownTrees, knownDecoratedTrees, usedNames;

abstract production singlePairContents
top::PairContents ::= t::Term
{
  top.pp = t.pp;
  top.argList = [t];
}

abstract production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.pp = t.pp ++ ", " ++ rest.pp;
  top.argList = t::rest.argList;
}

