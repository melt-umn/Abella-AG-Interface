grammar interface_:fromAbella:concreteSyntax;



closed nonterminal FullDisplay_c with ast<FullDisplay>;
closed nonterminal TheoremList_c with ast<TheoremList>;

concrete productions top::FullDisplay_c
| ei::ExtraInformation_c ps::ProofState_c
  { top.ast = fullDisplay(ei.ast, ps.ast); }
| tl::TheoremList_c
  { top.ast = showDisplay(tl.ast); }

concrete productions top::TheoremList_c
| 'Theorem' name::Id_t ':' body::Metaterm_c '.'
  { top.ast = theoremListAdd(name.lexeme, body.ast, theoremListEmpty()); }
| 'Theorem' name::Id_t ':' body::Metaterm_c '.' rest::TheoremList_c
  { top.ast = theoremListAdd(name.lexeme, body.ast, rest.ast); }





closed nonterminal ExtraInformation_c with ast<ExtraInformation>;

concrete productions top::ExtraInformation_c
|
  { top.ast = emptyInformation(); }
| 'Importing from' module::QString_t '.'
  { top.ast = importInformation(stripQuotes(module.lexeme)); }
| 'Syntax error.'
  { top.ast = syntaxErrorInformation(); }
| 'Error:' msg::ProcessingErrorMessage_c
  { top.ast = processingError(msg.ast); }
| 'Warning:' msg::WarningMessage_c
  { top.ast = warningInformation(msg.ast); }
| 'Typing error.' msg::TypingErrorMessage_c
  { top.ast = typingError(msg.ast); }
| 'Ignoring import:' file::FilePath_t 'has already been imported.'
  { top.ast = alreadyImported(file.lexeme); }
--I think this is the only one which can have two messages together
| 'Importing from' module::QString_t '.'
  'Error:' msg::ProcessingErrorMessage_c
  { top.ast = importError(stripQuotes(module.lexeme), msg.ast); }





closed nonterminal ProofState_c with ast<ProofState>;

concrete productions top::ProofState_c
|
  { top.ast = noProof(); }
| cs::CurrentSubgoal_c cg::CurrentGoal_c rest::MoreSubgoals_c
  { top.ast = proofInProgress(cs.ast, cg.ast, rest.ast); }
| cs::CurrentSubgoal_c cg::CurrentGoal_c num::Number_t 'other subgoals.'
  { top.ast = proofInProgress(cs.ast, cg.ast, [hiddenSubgoals(toInteger(num.lexeme))]); }
| cs::CurrentSubgoal_c cg::CurrentGoal_c num::Number_t 'other subgoal.'
  { top.ast = proofInProgress(cs.ast, cg.ast, [hiddenSubgoals(toInteger(num.lexeme))]); }
| 'Proof completed.'
  { top.ast = proofCompleted(); }
| 'Proof ABORTED.'
  { top.ast = proofAborted(); }





closed nonterminal CurrentGoal_c with ast<CurrentGoal>;
closed nonterminal ExistantVars_c with ast<[String]>;

concrete productions top::CurrentGoal_c
| hyps::HypothesisList_c gl::GoalLine_t goal::Metaterm_c
  { top.ast = currentGoal([], hyps.ast, goal.ast); }
| 'Variables' ':' vars::ExistantVars_c hyps::HypothesisList_c gl::GoalLine_t goal::Metaterm_c
  { top.ast = currentGoal(vars.ast, hyps.ast, goal.ast); }


concrete productions top::ExistantVars_c
| name::Id_t
  { top.ast = [name.lexeme]; }
| name::Id_t rest::ExistantVars_c
  { top.ast = name.lexeme::rest.ast; }





closed nonterminal CurrentSubgoal_c with ast<[Integer]>;
closed nonterminal MoreSubgoals_c with ast<[Subgoal]>; --after the current goal
closed nonterminal SubgoalNum_c with ast<[Integer]>;


--Current subgoal may or may not be labeled
concrete productions top::CurrentSubgoal_c
|
  --when we have no subgoal listed, it is the zeroeth goal, before any splitting
  { top.ast = [0]; }
| 'Subgoal' num::SubgoalNum_c ':'
  { top.ast = num.ast; }


concrete productions top::MoreSubgoals_c
|
  { top.ast = []; }
| 'Subgoal' 'is' ':' g::Metaterm_c
  { top.ast = [subgoal([1], g.ast)]; }
| 'Subgoal' num::SubgoalNum_c 'is' ':' g::Metaterm_c rest::MoreSubgoals_c
  { top.ast = [subgoal(num.ast, g.ast)] ++ rest.ast; }
{-| num::Number_t 'other subgoals.'
  { top.ast = [hiddenSubgoals(toInteger(num.lexeme))]; }
| num::Number_t 'other subgoal.'
  { top.ast = [hiddenSubgoals(toInteger(num.lexeme))]; }-}


concrete productions top::SubgoalNum_c
| n::Number_t
  { top.ast = [toInteger(n.lexeme)]; }
| n::Number_t '.' rest::SubgoalNum_c
  { top.ast = [toInteger(n.lexeme)] ++ rest.ast; }





closed nonterminal Hypothesis_c with ast<Context>; --we aren't going to group
closed nonterminal HypNameList_c with ast<[String]>;
closed nonterminal HypothesisList_c with ast<Context>;


concrete productions top::Hypothesis_c
--I'm not sure we can get grouped ones without abbreviation, but it doesn't hurt
| hyps::HypNameList_c body::Metaterm_c
  {
    top.ast = foldr(\ a::String b::Context ->
                      branchContext(singleContext(metatermHyp(a, body.ast)), b),
                    emptyContext(), hyps.ast);
  }
--EVERYTHING is turning into abbreviated hypotheses if I include this
--For when we have some abbreviated hypotheses (if we allow that)
{-| hyps::HypNameList_c abbrev::Abbreviated_t
  {
    top.ast = foldr(\ a::String b::Context ->
                      branchContext(singleContext(abbreviatedHyp(a, abbrev.lexeme)), b),
                    emptyContext(), hyps.ast);
  }-}


concrete productions top::HypNameList_c
| name::IdColon_t
  --we need to remove the <space colon space> from IdColon_t
  { top.ast = [substring(0, length(name.lexeme) - 3, name.lexeme)]; }
| name::IdComma_t rest::HypNameList_c
  --we need to remove the comma from IdComma_t
  { top.ast = [substring(0, length(name.lexeme) - 1, name.lexeme)] ++ rest.ast; }


concrete productions top::HypothesisList_c
|
  { top.ast = emptyContext(); }
| h::Hypothesis_c rest::HypothesisList_c
  { top.ast = branchContext(h.ast, rest.ast); }





closed nonterminal ProcessingErrorMessage_c with ast<ProcessingErrorMessage>;
closed nonterminal TypingErrorMessage_c with ast<TypingErrorMessage>;
closed nonterminal WarningMessage_c with ast<WarningMessage>;

concrete productions top::WarningMessage_c
| 'Definition might not be stratified' '(' name::QString_t 'occurs to the left of ->)'
  { top.ast = stratificationWarning(stripQuotes(name.lexeme)); }
| 'Definition can be used to defeat stratification' '(higher-order argument' name::QString_t 'occurs to the left of ->)'
  { top.ast = defeatStratification(stripQuotes(name.lexeme)); }
| 'overriding existing lemma named' name::QString_t
  { top.ast = overridingLemma(stripQuotes(name.lexeme)); }


concrete productions top::ProcessingErrorMessage_c
| 'Types of variables are not fully determined'
  { top.ast = undeterminedVarType(); }
| 'Search failed'
  { top.ast = searchFailure(); }
| 'Could not find hypothesis or lemma' name::ErrorId_t
  { top.ast = unknownHypLemma(name.lexeme); }
| 'Unknown constant:' name::ErrorId_t
  { top.ast = unknownConstant(name.lexeme); }
| 'Imported file makes reference to unknown types:' names::IdList_c
  { top.ast = importedUnknownTy(names.ast); }
| 'Invalid formula:' form::Metaterm_c 'Cannot use size restrictions (*, @, #, or +)'
  { top.ast = invalidFormula(form.ast); }
| 'Some type variables in the theorem is not bounded'
  { top.ast = unboundedTyVars(); }
| 'Predicate or constant' name::ErrorId_t 'already exists'
  { top.ast = alreadyDefined(name.lexeme); }
| 'Invalid defined predicate name' name::QString_t '.' 'Defined predicates may not begin with a capital letter.'
  { top.ast = invalidCapDefName(stripQuotes(name.lexeme)); }
| 'Constants may not begin with a capital letter:' name::ErrorId_t
  { top.ast = invalidCapConstName(name.lexeme); }
| 'Found stray clause for' name::ErrorId_t
  { top.ast = strayClause(name.lexeme); }
| 'Invalid head in definition:' formula::Metaterm_c
  { top.ast = invalidHead(formula.ast); }
| 'Definitional clause head not atomic:' hd::Metaterm_c
  { top.ast = nonatomicHead(hd.ast); }
| 'Cannot perform case-analysis on undefined atom'
  { top.ast = caseUndefinedAtom(); }
| 'Unknown hypothesis or variable' hyp::ErrorId_t
  { top.ast = unknownHypVar(hyp.lexeme); }
| 'Could not find theorem named' name::QString_t
  { top.ast = unknownTheorem(stripQuotes(name.lexeme)); }
| 'Unknown variable' name::ErrorId_t
  { top.ast = unknownVar(name.lexeme); }
| 'Can only induct on predicates and judgments'
  { top.ast = inductPredJudg(); }
| 'Cannot induct on' name::ErrorId_t 'since it has not been defined'
  { top.ast = inductUndefined(name.lexeme); }
| 'Expecting' expected::Number_t 'induction arguments but got' got::Number_t
  { top.ast = tooManyInductions(toInteger(expected.lexeme), toInteger(got.lexeme)); }
| 'Needless use of split'
  { top.ast = needlessSplit(); }
| 'Cannot split this type of theorem'
  { top.ast = cannotSplit(); }
| name::QString_t 'already refers to an existing hypothesis'
  { top.ast = nameExistingHyp(stripQuotes(name.lexeme)); }
| name::QString_t 'already refers to a lemma'
  { top.ast = nameExistingLemma(stripQuotes(name.lexeme)); }
| name::QString_t 'already refers to an existing variable'
  { top.ast = nameExistingVar(stripQuotes(name.lexeme)); }
| 'Unknown variable or hypothesis label' name::QString_t
  { top.ast = unknownVarHypLabel(stripQuotes(name.lexeme)); }
| 'Cannot go that far back!'
  { top.ast = cannotGoBack(); }
| 'While matching argument #' argnum::Number_t ':' 'Unification failure (constant clash between' name1::ErrorId_t 'and' name2::ErrorId_t ')'
  { top.ast = matchingUnificationFailureConstants(toInteger(argnum.lexeme), name1.lexeme, name2.lexeme); }
| 'While matching argument #' argnum::Number_t ':' 'Unification failure'
  { top.ast = matchingUnificationFailure(toInteger(argnum.lexeme)); }
| 'Unification failure'
  { top.ast = unificationFailure(); }
| 'Type constructor' name::ErrorId_t 'has inconsistent kind declarations'
  { top.ast = tyConstrInconsistentKinds(name.lexeme); }
| 'Types may not begin with a capital letter:' name::ErrorId_t
  { top.ast = tyNoCaps(name.lexeme); }
| 'Unknown type constructor:' name::ErrorId_t
  { top.ast = unknownTyConstr(name.lexeme); }
| name::Id_t 'expects' expected::Number_t 'arguments but has' given::Number_t
  { top.ast = wrongArgNumber(name.lexeme, toInteger(expected.lexeme), toInteger(given.lexeme)); }
| 'Cannot quantify over type prop'
  { top.ast = noQuantifyProp(); }
| 'Unknown key' name::SingleQString_t
  { top.ast = unknownSettingKey(stripQuotes(name.lexeme)); }
| 'Unknown value' val::SingleQString_t 'for key' key::QString_t ';' 'expected non-negative integer'
  { top.ast = unknownSettingsValueExpectInt(stripQuotes(val.lexeme), stripQuotes(key.lexeme)); }
| 'Unknown value' val::SingleQString_t 'for key' key::QString_t ';' x::ExpectOnOff_t
  { top.ast = unknownSettingsValueExpectOnOff(stripQuotes(val.lexeme), stripQuotes(key.lexeme)); }
| 'Unknown value' val::SingleQString_t 'for key' key::QString_t ';' x::ExpectMany_t
  { top.ast = unknownSettingsValueExpectMany(stripQuotes(val.lexeme), stripQuotes(key.lexeme)); }
| 'Not enough arguments to apply' '(' 'Expected' exp::Number_t 'but got' got::Number_t ')'
  { top.ast = applyWrongArgsNumber(toInteger(exp.lexeme), toInteger(got.lexeme)); }
| 'Too many arguments to apply' '(' 'Expected' exp::Number_t 'but got' got::Number_t ')'
  { top.ast = applyWrongArgsNumber(toInteger(exp.lexeme), toInteger(got.lexeme)); }
| 'Found logic variable at toplevel'
  { top.ast = logicVariableToplevel(); }
| 'Structure of applied term must be a substructure of the following.'
  'forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C'
  { top.ast = appliedStructure(); }


concrete productions top::TypingErrorMessage_c
| 'Expression has type' ty1::Ty_c 'but is used here with type' ty2::Ty_c '.'
  { top.ast = badTypeUsage(ty1.ast, ty2.ast); }
| 'Expression is applied to too many arguments'
  { top.ast = tooManyArguments(); }





closed nonterminal IdList_c with ast<[String]>;

concrete productions top::IdList_c
| name::Id_t
  { top.ast = [name.lexeme]; }
| name::Id_t ',' rest::IdList_c
  { top.ast = name.lexeme::rest.ast; }






--I'm stripping quotes a lot
function stripQuotes
String ::= n::String
{
  return substring(1, length(n) - 1, n);
}

