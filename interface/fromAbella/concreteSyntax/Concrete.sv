grammar fromAbella:concreteSyntax;

{-
  Some of this is very similar to the the toAbella concrete syntax;
  namely, we use the same metaterms and terms.  However, we are going
  from the full Abella syntax to the restricted syntax for our
  interface, so we need to have the full range of identifiers for
  Abella (allowing starting with a dollar sign).  Therefore, we need
  to have a different identifier string and everything that grows from
  that, which is every nonterminal.
-}


synthesized attribute ast<a>::a;

--a count of how many levels of a restriction
synthesized attribute count::Integer;





nonterminal FullDisplay_c with ast<FullDisplay>;

concrete productions top::FullDisplay_c
| ei::ExtraInformation_c ps::ProofState_c
{ top.ast = fullDisplay(ei.ast, ps.ast); }
| ei::ExtraInformation_c 'Proof completed.'
  { top.ast = displayProofCompleted(ei.ast); }
| ei::ExtraInformation_c 'Proof ABORTED.'
  { top.ast = displayProofAborted(ei.ast); }
| 'Theorem' name::Id_t ':' body::Metaterm_c
  { top.ast = showDisplay(name.lexeme, body.ast); }





nonterminal ExtraInformation_c with ast<ExtraInformation>;

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





nonterminal ProofState_c with ast<ProofState>;

concrete productions top::ProofState_c
|
  { top.ast = noProof(); }
| cs::CurrentSubgoal_c cg::CurrentGoal_c rest::MoreSubgoals_c
  { top.ast = proofInProgress(cs.ast, cg.ast, rest.ast); }





nonterminal CurrentGoal_c with ast<CurrentGoal>;
nonterminal ExistantVars_c with ast<[String]>;

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





nonterminal CurrentSubgoal_c with ast<[Integer]>;
nonterminal MoreSubgoals_c with ast<[Subgoal]>; --after the current goal
nonterminal SubgoalNum_c with ast<[Integer]>;


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
| 'Subgoal' num::SubgoalNum_c 'is' ':' g::Metaterm_c rest::MoreSubgoals_c
  { top.ast = [subgoal(num.ast, g.ast)] ++ rest.ast; }
| num::Number_t 'other subgoals.'
  { top.ast = [hiddenSubgoals(toInteger(num.lexeme))]; }
| num::Number_t 'other subgoal.'
  { top.ast = [hiddenSubgoals(toInteger(num.lexeme))]; }


concrete productions top::SubgoalNum_c
| n::Number_t
  { top.ast = [toInteger(n.lexeme)]; }
| n::Number_t '.' rest::SubgoalNum_c
  { top.ast = [toInteger(n.lexeme)] ++ rest.ast; }





nonterminal Hypothesis_c with ast<Context>; --we aren't going to group
nonterminal HypNameList_c with ast<[String]>;
nonterminal HypothesisList_c with ast<Context>;


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
  --we need to remove the space and colon from IdColon_t
  { top.ast = [substring(0, length(name.lexeme) - 2, name.lexeme)]; }
| name::IdComma_t rest::HypNameList_c
  --we need to remove the comma from IdComma_t
  { top.ast = [substring(0, length(name.lexeme) - 1, name.lexeme)] ++ rest.ast; }


concrete productions top::HypothesisList_c
|
  { top.ast = emptyContext(); }
| h::Hypothesis_c rest::HypothesisList_c
  { top.ast = branchContext(h.ast, rest.ast); }





nonterminal Metaterm_c with ast<Metaterm>;
nonterminal SubMetaterm_c with ast<Metaterm>;


{-concrete productions top::Metaterm_c
| 'true'
{ }
| 'false'
{ }
| t1::Term_c '=' t2::Term_c
{ }
| b::Binder_c bl::BindingList_c ',' m::Metaterm_c
{ }
| m1::Metaterm_c '->' m2::Metaterm_c
{ }
| m1::Metaterm_c '\/' m2::Metaterm_c
{ }
| m1::Metaterm_c '/\' m2::Metaterm_c
{ }
| '(' m::Metaterm_c ')'
{ }
| t::Term_c r::Restriction_c
{ }-}
{-
  The original grammar rules, translated from the OCaml Yacc grammar,
  are above.  That grammar had an ambiguity where `(Term)` could not
  be parsed:
  - It could be a Term followed by an empty Restriction inside
    Metaterm_c parentheses.
  - It could be a Term in Exp parentheses, which is then a Term
    followed by an empty Restriction as a Metaterm_c.
  These end up being equal treatments.  The refactoring below
  eliminates the first possibility, since any Term in Metaterm_c
  parentheses must be followed by a non-empty restriction set.  This
  makes the grammar unambiguous, but still able to parse the same
  strings.
-}
concrete productions top::Metaterm_c
| t::Term_c
  {-This lets us overload `true` and `false` for use as metaterms and
    Silver Booleans.  If it is simply "true" or "false" where a
    metaterm is needed, that is the Abella metaterm; otherwise, it
    must be the Silver Boolean.-}
  { top.ast = termMetaterm(t.ast, emptyRestriction()); }
| s::SubMetaterm_c
  { top.ast = s.ast; }


concrete productions top::SubMetaterm_c
| 'true'
  { top.ast = trueMetaterm(); }
| 'false'
  { top.ast = falseMetaterm(); }
| t1::Term_c '=' t2::Term_c
  { top.ast = eqMetaterm(t1.ast, t2.ast); }
| b::Binder_c bl::BindingList_c ',' m::Metaterm_c
  { top.ast = bindingMetaterm(b.ast, bl.ast, m.ast); }
| m1::Metaterm_c '->' m2::Metaterm_c
  { top.ast = impliesMetaterm(m1.ast, m2.ast); }
| m1::Metaterm_c '\/' m2::Metaterm_c
  { top.ast = orMetaterm(m1.ast, m2.ast); }
| m1::Metaterm_c '/\' m2::Metaterm_c
  { top.ast = andMetaterm(m1.ast, m2.ast); }
| '(' m::SubMetaterm_c ')'
  { top.ast = m.ast; }
| t::Term_c s::Stars_c
  { top.ast = termMetaterm(t.ast, s.ast); }
| t::Term_c p::Pluses_c
  { top.ast = termMetaterm(t.ast, p.ast); }
| t::Term_c a::Ats_c
  { top.ast = termMetaterm(t.ast, a.ast); }
| t::Term_c h::Hashes_c
  { top.ast = termMetaterm(t.ast, h.ast); }





nonterminal Term_c with ast<Term>;
nonterminal Exp_c with ast<Term>;
nonterminal ExpList_c with ast<TermList>;
nonterminal PAId_c with ast<Term>;


concrete productions top::Term_c
| e::Exp_c el::ExpList_c
  { top.ast = applicationTerm(e.ast, el.ast); }
| e::Exp_c
  { top.ast = e.ast; }
| t1::Term_c '::' t2::Term_c
  { top.ast = consTerm(t1.ast, t2.ast); }
| 'nil'
  { top.ast = nilTerm(); }


concrete productions top::Exp_c
| '(' t::Term_c ')'
  { top.ast = t.ast; }
| p::PAId_c
  { top.ast = p.ast; }


concrete productions top::ExpList_c
| e::Exp_c el::ExpList_c
  { top.ast = consTermList(e.ast, el.ast); }
| e::Exp_c
  { top.ast = singleTermList(e.ast); }


concrete productions top::PAId_c
| l::Id_t
  { top.ast = nameTerm(l.lexeme); }





nonterminal Binder_c with ast<Binder>;
nonterminal BindingList_c with ast<[String]>;
nonterminal BindingOne_c with ast<[String]>;


concrete productions top::Binder_c
| 'forall'
  { top.ast = forallBinder(); }
| 'exists'
  { top.ast = existsBinder(); }
| 'nabla'
  { top.ast = nablaBinder(); }


concrete productions top::BindingList_c
| b::BindingOne_c
  { top.ast = b.ast; }
| b::BindingOne_c rest::BindingList_c
  { top.ast = b.ast ++ rest.ast; }


concrete productions top::BindingOne_c
| i::Id_t
  { top.ast = [i.lexeme]; }





nonterminal Stars_c with ast<Restriction>, count;
nonterminal Ats_c with ast<Restriction>, count;
nonterminal Pluses_c with ast<Restriction>, count;
nonterminal Hashes_c with ast<Restriction>, count;


concrete productions top::Stars_c
| '*' rest::Stars_c
  {
    top.count = rest.count + 1;
    top.ast = starRestriction(top.count);
  }
| '*'
  {
    top.count = 1;
    top.ast = starRestriction(1);
  }


concrete productions top::Ats_c
| '@' rest::Ats_c
  {
    top.count = rest.count + 1;
    top.ast = atRestriction(top.count);
  }
| '@'
  {
    top.count = 1;
    top.ast = atRestriction(top.count);
  }


concrete productions top::Pluses_c
| '+' rest::Pluses_c
  {
    top.count = rest.count + 1;
    top.ast = plusRestriction(top.count);
  }
| '+'
  {
    top.count = 1;
    top.ast = plusRestriction(top.count);
  }


concrete productions top::Hashes_c
| '#' rest::Hashes_c
  {
    top.count = rest.count + 1;
    top.ast = hashRestriction(top.count);
  }
| '#'
  {
    top.count = 1;
    top.ast = hashRestriction(top.count);
  }





nonterminal ProcessingErrorMessage_c with ast<ProcessingErrorMessage>;
nonterminal TypingErrorMessage_c with ast<TypingErrorMessage>;
nonterminal WarningMessage_c with ast<WarningMessage>;

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
  { top.ast = matchingUnificationFailure(toInteger(argnum.lexeme), name1.lexeme, name2.lexeme); }
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


concrete productions top::TypingErrorMessage_c
| 'Expression has type' ty1::Ty_c 'but is used here with type' ty2::Ty_c '.'
  { top.ast = badTypeUsage(ty1.ast, ty2.ast); }
| 'Expression is applied to too many arguments'
  { top.ast = tooManyArguments(); }





nonterminal IdList_c with ast<[String]>;

concrete productions top::IdList_c
| name::Id_t
  { top.ast = [name.lexeme]; }
| name::Id_t ',' rest::IdList_c
  { top.ast = name.lexeme::rest.ast; }





nonterminal PTy_c with ast<Type>;
nonterminal ATy_c with ast<Type>;
nonterminal Ty_c with ast<Type>;

concrete productions top::PTy_c
| i::Id_t
  { top.ast = nameType(i.lexeme); }
| '(' t::Ty_c ')'
  { top.ast = t.ast; }


concrete productions top::ATy_c
| i::Id_t
  { top.ast = nameType(i.lexeme); }
| a::ATy_c p::PTy_c
  { top.ast = functorType(a.ast, p.ast); }


concrete productions top::Ty_c
| a::ATy_c
  { top.ast = a.ast; }
| t1::Ty_c '->' t2::Ty_c
  { top.ast = arrowType(t1.ast, t2.ast); }
| '(' t::Ty_c ')'
  { top.ast = t.ast; }






--I'm stripping quotes a lot
function stripQuotes
String ::= n::String
{
  return substring(1, length(n) - 1, n);
}

