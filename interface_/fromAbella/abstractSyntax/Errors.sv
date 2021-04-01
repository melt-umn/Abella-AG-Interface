grammar interface_:fromAbella:abstractSyntax;





nonterminal WarningMessage with
   pp,
   translation<WarningMessage>;

abstract production stratificationWarning
top::WarningMessage ::= name::String
{
  top.pp = "Definition might not be stratified\n (\"" ++ name ++ "\" occurs to the left of ->)";

  top.translation = stratificationWarning(name);
}


abstract production defeatStratification
top::WarningMessage ::= name::String
{
  top.pp = "Definition can be used to defeat stratification\n" ++
           " (higher-order argument \"" ++ name ++ "\" occurs to the left of ->)";

  top.translation = defeatStratification(name);
}


abstract production overridingLemma
top::WarningMessage ::= name::String
{
  top.pp = "overriding existing lemma named \"" ++ name ++ "\"";

  top.translation = overridingLemma(name);
}





nonterminal ProcessingErrorMessage with
   pp,
   translation<ProcessingErrorMessage>;

abstract production undeterminedVarType
top::ProcessingErrorMessage ::=
{
  top.pp = "Types of variables are not fully determined";

  top.translation = undeterminedVarType();
}


abstract production searchFailure
top::ProcessingErrorMessage ::=
{
  top.pp = "Search failed";

  top.translation = searchFailure();
}


abstract production unknownHypLemma
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Could not find hypothesis or lemma " ++ name;

  top.translation = unknownHypLemma(name);
}


abstract production unknownConstant
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown constant: " ++ name;

  top.translation = unknownConstant(name);
}


abstract production importedUnknownTy
top::ProcessingErrorMessage ::= names::[String]
{
  local namesString::String = implode(", ", names);
  top.pp = "Imported file makes reference to unknown types: " ++ namesString;

  top.translation = importedUnknownTy(names);
}


abstract production invalidFormula
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Invalid formula: " ++ formula.pp ++
           "\nCannot use size restrictions (*, @, #, or +)";

  top.translation = invalidFormula(formula.translation);
}


abstract production unboundedTyVars
top::ProcessingErrorMessage ::=
{
  top.pp = "Some type variables in the theorem is not bounded";

  top.translation = unboundedTyVars();
}


abstract production alreadyDefined
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Predicate or constant " ++ name ++ " already exists";

  top.translation = alreadyDefined(name);
}


abstract production invalidCapDefName
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Invalid defined predicate name \"" ++ name ++
           "\".\n Defined predicates may not begin with a capital letter.";

  top.translation = invalidCapDefName(name);
}


abstract production invalidCapConstName
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Constants may not begin with a capital letter: " ++ name;

  top.translation = invalidCapConstName(name);
}


abstract production strayClause
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Found stray clause for " ++ name;

  top.translation = strayClause(name);
}


abstract production invalidHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Invalid head in definition: " ++ formula.pp;

  top.translation = invalidHead(formula.translation);
}


abstract production nonatomicHead
top::ProcessingErrorMessage ::= formula::Metaterm
{
  top.pp = "Definitional clause head not atomic:\n" ++ formula.pp;

  top.translation = nonatomicHead(formula.translation);
}


abstract production caseUndefinedAtom
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot perform case-analysis on undefined atom";

  top.translation = caseUndefinedAtom();
}


abstract production unknownHypVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown hypothesis or variable " ++ name;

  top.translation = unknownHypVar(name);
}


abstract production unknownTheorem
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Could not find theorem named \"" ++ name ++ "\"";

  top.translation = unknownTheorem(name);
}


abstract production unknownVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown variable " ++ name;

  top.translation = unknownVar(name);
}


abstract production inductPredJudg
top::ProcessingErrorMessage ::=
{
  top.pp = "Can only induct on predicates and judgments";

  top.translation = inductPredJudg();
}


abstract production inductUndefined
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Cannot induct on " ++ name ++ " since it has not been defined";

  top.translation = inductUndefined(name);
}


abstract production tooManyInductions
top::ProcessingErrorMessage ::= expected::Integer got::Integer
{
  top.pp = "Expecting " ++ toString(expected) ++
           " induction arguments but got " ++ toString(got);

  top.translation = tooManyInductions(expected, got);
}


abstract production needlessSplit
top::ProcessingErrorMessage ::=
{
  top.pp = "Needless use of split";

  top.translation = needlessSplit();
}


abstract production cannotSplit
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot split this type of theorem";

  top.translation = cannotSplit();
}


abstract production nameExistingHyp
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to an existing hypothesis";

  top.translation = nameExistingHyp(name);
}


abstract production nameExistingLemma
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to a lemma";

  top.translation = nameExistingLemma(name);
}


abstract production nameExistingVar
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "\"" ++ name ++ "\" already refers to an existing variable";

  top.translation = nameExistingVar(name);
}


abstract production unknownVarHypLabel
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown variable or hypothesis label \"" ++ name ++ "\"";

  top.translation = unknownVarHypLabel(name);
}


abstract production cannotGoBack
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot go that far back!";

  top.translation = cannotGoBack();
}


abstract production matchingUnificationFailure
top::ProcessingErrorMessage ::= argnum::Integer const1::String const2::String
{
  top.pp = "While matching argument #" ++ toString(argnum) ++
           ":\nUnification failure (constant clash between " ++
           const1 ++ " and " ++ const2 ++ ")";

  top.translation = matchingUnificationFailure(argnum, const1, const2);
}


abstract production unificationFailure
top::ProcessingErrorMessage ::=
{
  top.pp = "Unification failure";

  top.translation = unificationFailure();
}


abstract production tyConstrInconsistentKinds
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Type constructor " ++ name ++ " has inconsistent kind declarations";

  top.translation = tyConstrInconsistentKinds(name);
}


abstract production tyNoCaps
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Types may not begin with a capital letter: " ++ name;

  top.translation = tyNoCaps(name);
}


abstract production unknownTyConstr
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown type constructor: " ++ name;

  top.translation = unknownTyConstr(name);
}


abstract production wrongArgNumber
top::ProcessingErrorMessage ::= name::String expected::Integer given::Integer
{
  top.pp = name ++ " expects " ++ toString(expected) ++ " arguments but has " ++ toString(given);

  top.translation = wrongArgNumber(name, expected, given);
}


abstract production noQuantifyProp
top::ProcessingErrorMessage ::=
{
  top.pp = "Cannot quantify over type prop";

  top.translation = noQuantifyProp();
}


abstract production unknownSettingKey
top::ProcessingErrorMessage ::= name::String
{
  top.pp = "Unknown key '" ++ name ++ "'";

  top.translation = unknownSettingKey(name);
}


abstract production unknownSettingsValueExpectInt
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++ "\"; expected non-negative integer";

  top.translation = unknownSettingsValueExpectInt(val, key);
}


abstract production unknownSettingsValueExpectOnOff
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++ "\"; expected 'on' or 'off'";

  top.translation = unknownSettingsValueExpectOnOff(val, key);
}


abstract production unknownSettingsValueExpectMany
top::ProcessingErrorMessage ::= val::String key::String
{
  top.pp = "Unknown value '" ++ val ++ "' for key \"" ++ key ++ "\"; expected 'on', 'off', non-negative integer, or depth specification";

  top.translation = unknownSettingsValueExpectMany(val, key);
}


abstract production applyWrongArgsNumber
top::ProcessingErrorMessage ::= expected::Integer got::Integer
{
  top.pp = "Not enough arguments to apply\n(Expected " ++ toString(expected) ++ " but got " ++ toString(got) ++ ")";

  top.translation = applyWrongArgsNumber(expected, got);
}


abstract production logicVariableToplevel
top::ProcessingErrorMessage ::=
{
  top.pp = "Found logic variable at toplevel";

  top.translation = logicVariableToplevel();
}


abstract production appliedStructure
top::ProcessingErrorMessage ::=
{
  top.pp =
      "Structure of applied term must be a substructure of the following.\n" ++
      "forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C";

  top.translation = appliedStructure();
}





nonterminal TypingErrorMessage with
   pp,
   translation<TypingErrorMessage>;

abstract production badTypeUsage
top::TypingErrorMessage ::= hasType::Type usedType::Type
{
  top.pp = "Expression has type " ++ hasType.pp ++ " but is used here with type " ++ usedType.pp ++ ".";

  top.translation = badTypeUsage(hasType.translation, usedType.translation);
}


abstract production tooManyArguments
top::TypingErrorMessage ::=
{
  top.pp = "Expression is applied to too many arguments";

  top.translation = tooManyArguments();
}





attribute
   translation<Type>
occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.translation = arrowType(ty1.translation, ty2.translation);
}


aspect production nameType
top::Type ::= name::String
{
  top.translation = nameType(name);
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.translation = functorType(functorTy.translation, argTy.translation);
}


aspect production underscoreType
top::Type ::=
{
  top.translation = underscoreType();
}

