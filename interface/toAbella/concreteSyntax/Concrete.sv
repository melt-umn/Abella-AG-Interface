grammar toAbella:concreteSyntax;


synthesized attribute ast<a>::a;

--a count of how many levels of a restriction
synthesized attribute count::Integer;



--split an AttrAccess_t into the tree name and attr name
function split_AttrAccess_t
Pair<String String> ::= a::AttrAccess_t
{
  local lexeme::String = a.lexeme;
  local dotLoc::Integer = indexOf(".", a.lexeme);
  return pair(substring(0, dotLoc, lexeme),
              substring(dotLoc + 1, length(lexeme), lexeme));
}





nonterminal Command_c with ast<ProofCommand>;
nonterminal PureCommand_c with ast<ProofCommand>;
nonterminal TopCommand_c with ast<TopCommand>;
nonterminal CommonCommand_c with ast<NoOpCommand>;
nonterminal PureTopCommand_c with ast<TopCommand>;


{-This appears to be useless, but it might end up being useful in
  ProofGeneral, so I'll hold onto it in a comment.

nonterminal AnyCommand_c;
concrete productions top::AnyCommand_c
| c::PureTopCommand_c
{ }
| c::PureCommand_c
{ }
| c::CommonCommand_c
{ }
-}


concrete productions top::Command_c
| p::PureCommand_c
  { top.ast = p.ast; }
| c::CommonCommand_c
  { top.ast = proofNoOpCommand(c.ast); }


concrete productions top::PureCommand_c
| h::HHint_c 'induction' 'on' nl::NumList_c '.'
  { top.ast = inductionTactic(h.ast, nl.ast); }
| h::HHint_c 'coinduction' '.'
  { top.ast = coinductionTactic(h.ast); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c 'to' a::ApplyArgs_c '.'
  { top.ast = applyTactic(h.ast, md.ast, c.ast, a.ast, []); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c 'to' a::ApplyArgs_c 'with' w::Withs_c '.'
  { top.ast = applyTactic(h.ast, md.ast, c.ast, a.ast, w.ast); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c 'with' w::Withs_c '.'
  { top.ast = applyTactic(h.ast, md.ast, c.ast, [], w.ast); }
| h::HHint_c 'apply' md::MaybeDepth_c c::Clearable_c '.'
  { top.ast = applyTactic(h.ast, md.ast, c.ast, [], []); }
| 'backchain' md::MaybeDepth_c c::Clearable_c '.'
  { top.ast = backchainTactic(md.ast, c.ast, []); }
| 'backchain' md::MaybeDepth_c c::Clearable_c 'with' w::Withs_c '.'
  { top.ast = backchainTactic(md.ast, c.ast, w.ast); }
| h::HHint_c 'case' hy::Hyp_c '.'
  { top.ast = caseTactic(h.ast, hy.ast, false); }
| h::HHint_c 'case' hy::Hyp_c '(' 'keep' ')' '.'
  { top.ast = caseTactic(h.ast, hy.ast, true); }
| h::HHint_c 'case' a::AttrAccess_t '.'
  { local treeName::String = case split_AttrAccess_t(a) of | pair(trn, _) -> trn end;
    local attrName::String = case split_AttrAccess_t(a) of | pair(_, atn) -> atn end;
    top.ast = caseAttrAccess(h.ast, treeName, attrName); }
| h::HHint_c 'assert' md::MaybeDepth_c m::Metaterm_c '.'
  { top.ast = assertTactic(h.ast, md.ast, m.ast); }
| 'exists' ew::EWitnesses_c '.'
  { top.ast = existsTactic(ew.ast); }
| 'witness' ew::EWitnesses_c '.'
  { top.ast = witnessTactic(ew.ast); }
| 'search' '.'
  { top.ast = searchTactic(); }
| 'search' n::Number_t '.'
  { top.ast = searchDepthTactic(toInt(n.lexeme)); }
| 'search' 'with' sw::SearchWitness_c '.'
  { top.ast = searchWitnessTactic(sw.ast); }
| 'async' '.'
  { top.ast = asyncTactic(); }
| 'split' '.'
  { top.ast = splitTactic(); }
| 'split*' '.'
  { top.ast = splitStarTactic(); }
| 'left' '.'
  { top.ast = leftTactic(); }
| 'right' '.'
  { top.ast = rightTactic(); }
| 'intros' '.'
  { top.ast = introsTactic([]); }
| 'intros' names::HypList_c '.'
  { top.ast = introsTactic(names.ast); }
| 'skip' '.'
  { top.ast = skipTactic(); }
| 'abort' '.'
  { top.ast = abortCommand(); }
| 'undo' '.'
  { top.ast = undoCommand(); }
| 'unfold' cs::ClauseSel_c ss::SolSel_c '.'
  { top.ast = cs.ast(ss.ast); }
| 'clear' hl::HypList_c '.'
  { top.ast = clearCommand(hl.ast, false); }
| 'clear' '->' hl::HypList_c '.'
  { top.ast = clearCommand(hl.ast, true); }
| 'abbrev' hl::HypList_c q::QString_t '.'
  { top.ast = abbrevCommand(hl.ast, substring(1, length(q.lexeme) - 1, q.lexeme)); }
| 'unabbrev' hl::HypList_c '.'
  { top.ast = unabbrevCommand(hl.ast); }
| 'rename' original::Id_t 'to' newname::Id_t '.'
  { top.ast = renameTactic(original.lexeme, newname.lexeme); }
| 'permute' p::Perm_c '.'
  { top.ast = permuteTactic(p.ast, nothing()); }
| 'permute' p::Perm_c h::Hyp_c '.'
  { top.ast = permuteTactic(p.ast, just(h.ast)); }


concrete productions top::TopCommand_c
| p::PureTopCommand_c
  { top.ast = p.ast; }
| c::CommonCommand_c
  { top.ast = topNoOpCommand(c.ast); }


concrete productions top::PureTopCommand_c
| 'Theorem' name::Id_t params::TheoremTyparams_c ':' body::Metaterm_c '.'
  { top.ast = theoremDeclaration(name.lexeme, params.ast, body.ast); }
| 'Define' x::IdTys_c 'by' o::OptSemi_t d::Defs_c '.'
  { top.ast = definitionDeclaration(x.ast, d.ast); }
| 'CoDefine' x::IdTys_c 'by' o::OptSemi_t d::Defs_c '.'
  { top.ast = codefinitionDeclaration(x.ast, d.ast); }
| 'Query' m::Metaterm_c '.'
  { top.ast = queryCommand(m.ast); }
| 'Import' q::QString_t '.'
  { top.ast = importCommand(q.lexeme, []); }
| 'Import' q::QString_t 'with' iw::ImportWiths_c '.'
  { top.ast = importCommand(q.lexeme, iw.ast); }
| 'Kind' il::IdList_c k::Knd_c '.'
  { top.ast = kindDeclaration(il.ast, k.ast); }
| 'Type' il::IdList_c t::Ty_c '.'
  { top.ast = typeDeclaration(il.ast, t.ast); }
| 'Close' al::ATyList_c '.'
  { top.ast = closeCommand(al.ast); }
| 'Split' name::Id_t '.'
  { top.ast = splitTheorem(name.lexeme, []); }
| 'Split' name::Id_t 'as' il::IdList_c '.'
  { top.ast = splitTheorem(name.lexeme, il.ast); }


concrete productions top::CommonCommand_c
| 'Set' opt::Id_t value::Id_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t value::Number_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t value::QString_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Show' name::Id_t '.'
  { top.ast = showCommand(name.lexeme); }
| 'Quit' '.'
  { top.ast = quitCommand(); }
| '#back' '.'
  { top.ast = backCommand(); }
| '#reset' '.'
  { top.ast = resetCommand(); }





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
| a::AttrAccess_t
  { local dotLoc::Integer = indexOf(".", a.lexeme);
    top.ast =
       attrAccessTerm(substring(0, dotLoc, a.lexeme),
                      substring(dotLoc + 1, length(a.lexeme), a.lexeme)); }


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
  { top.ast = nameTerm(l.lexeme, nothing()); }
| '(' l::Id_t ':' t::Ty_c ')'
  { top.ast = nameTerm(l.lexeme, just(t.ast)); }
| '_'
  { top.ast = underscoreTerm(nothing()); }
| '(' '_' ':' t::Ty_c ')'
  { top.ast = underscoreTerm(just(t.ast)); }





nonterminal Knd_c with ast<Kind>;
nonterminal PTy_c with ast<Type>;
nonterminal ATy_c with ast<Type>;
nonterminal Ty_c with ast<Type>;
nonterminal UTy_c with ast<Type>;
nonterminal UTyList_c with ast<[Type]>;
nonterminal ATyList_c with ast<[Type]>;


concrete productions top::Knd_c
| 'type'
  { top.ast = typeKind(); }
| 'type' '->' k::Knd_c
  { top.ast = arrowKind(k.ast); }


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


concrete productions top::UTy_c
| t::Ty_c
  { top.ast = t.ast; }
| '_'
  { top.ast = underscoreType(); }


concrete productions top::UTyList_c
| u::UTy_c
  { top.ast = [u.ast]; }
| u::UTy_c ',' rest::UTyList_c
  { top.ast = u.ast::rest.ast; }


concrete productions top::ATyList_c
| a::ATy_c
  { top.ast = [a.ast]; }
| a::ATy_c ',' rest::ATyList_c
  { top.ast = a.ast::rest.ast; }





nonterminal Binder_c with ast<Binder>;
nonterminal BindingList_c with ast<[Pair<String Maybe<Type>>]>;
nonterminal BindingOne_c with ast<[Pair<String Maybe<Type>>]>;
nonterminal BindingVars_c with ast<[String]>;
nonterminal ExistsBinds_c with ast<[Pair<String Term>]>;


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
  { top.ast = [pair(i.lexeme, nothing())]; }
| '(' bv::BindingVars_c ':' t::Ty_c ')'
  { top.ast = map(\x::String -> pair(x, just(t.ast)), bv.ast); }


concrete productions top::BindingVars_c
| i::Id_t
  { top.ast = [i.lexeme]; }
| i::Id_t rest::BindingVars_c
  { top.ast = [i.lexeme]; }


concrete productions top::ExistsBinds_c
|
  { top.ast = []; }
| w::Withs_c
  { top.ast = w.ast; }





nonterminal Restriction_c with ast<Restriction>;
nonterminal Stars_c with ast<Restriction>, count;
nonterminal Ats_c with ast<Restriction>, count;
nonterminal Pluses_c with ast<Restriction>, count;
nonterminal Hashes_c with ast<Restriction>, count;


concrete productions top::Restriction_c
|
  { top.ast = emptyRestriction(); }
| s::Stars_c
  { top.ast = s.ast; }
| p::Pluses_c
  { top.ast = p.ast; }
| a::Ats_c
  { top.ast = a.ast; }
| h::Hashes_c
  { top.ast = h.ast; }


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





nonterminal Defs_c with ast<Defs>;
nonterminal Def_c with ast<Def>;


concrete productions top::Defs_c
| d::Def_c ';' rest::Defs_c
  { top.ast = consDefs(d.ast, rest.ast); }
| d::Def_c
  { top.ast = singleDefs(d.ast); }


concrete productions top::Def_c
| m::Metaterm_c
  { top.ast = factDef(m.ast); }
| h::Metaterm_c ':=' b::Metaterm_c
  { top.ast = ruleDef(h.ast, b.ast); }





nonterminal Perm_c with ast<[String]>;
nonterminal PermIds_c with ast<[String]>;


concrete productions top::Perm_c
| '(' p::PermIds_c ')'
  { top.ast = p.ast; }


concrete productions top::PermIds_c
| i::Id_t rest::PermIds_c
  { top.ast = i.lexeme::rest.ast; }
| i::Id_t
  { top.ast = [i.lexeme]; }





nonterminal SearchWitness_c with ast<SearchWitness>;
nonterminal SearchWitnessList_c with ast<[SearchWitness]>;


concrete productions top::SearchWitness_c
| 'true'
  { top.ast = trueSearchWitness(); }
| 'apply' i::Id_t
  { top.ast = applySearchWitness(i.lexeme); }
| 'left' sw::SearchWitness_c
  { top.ast = leftSearchWitness(sw.ast); }
| 'right' sw::SearchWitness_c
  { top.ast = rightSearchWitness(sw.ast); }
| 'split' '(' sw1::SearchWitness_c ',' sw2::SearchWitness_c ')'
  { top.ast = splitSearchWitness(sw1.ast, sw2.ast); }
| 'intros' '[' il::IdList_c ']' sw::SearchWitness_c
  { top.ast = introsSearchWitness(il.ast, sw.ast); }
| 'forall' '[' il::IdList_c ']' sw::SearchWitness_c
  { top.ast = forallSearchWitness(il.ast, sw.ast); }
| 'exists' '[' eb::ExistsBinds_c ']' sw::SearchWitness_c
  { top.ast = existsSearchWitness(eb.ast, sw.ast); }
| 'unfold' '(' i::Id_t ',' n::Number_t swl::SearchWitnessList_c ')'
  { top.ast = unfoldSearchWitness(i.lexeme, toInt(n.lexeme), swl.ast); }
| '*'
  { top.ast = starSearchWitness(); }
| '='
  { top.ast = eqSearchWitness(); }
| '(' sw::SearchWitness_c ')'
  { top.ast = sw.ast; }


concrete productions top::SearchWitnessList_c
|
  { top.ast = []; }
| ',' sw::SearchWitness_c swl::SearchWitnessList_c
  { top.ast = sw.ast::swl.ast; }





nonterminal EWitnesses_c with ast<[EWitness]>;
nonterminal EWitness_c with ast<EWitness>;


concrete productions top::EWitnesses_c
| ew::EWitness_c ',' rest::EWitnesses_c
  { top.ast = ew.ast::rest.ast; }
| ew::EWitness_c
  { top.ast = [ew.ast]; }


concrete productions top::EWitness_c
| name::Id_t '=' t::Term_c
  { top.ast = nameEWitness(name.lexeme, t.ast); }
| t::Term_c
  { top.ast = termEWitness(t.ast); }





nonterminal ApplyArgs_c with ast<[ApplyArg]>;
nonterminal ApplyArg_c with ast<ApplyArg>;


concrete productions top::ApplyArgs_c
| a::ApplyArg_c rest::ApplyArgs_c
  { top.ast = a.ast::rest.ast; }
| a::ApplyArg_c
  { top.ast = [a.ast]; }


concrete productions top::ApplyArg_c
| h::Hyp_c m::MaybeInst_c
  { top.ast = hypApplyArg(h.ast, m.ast); }
| '*' i::Id_t m::MaybeInst_c
  { top.ast = starApplyArg(i.lexeme, m.ast); }





nonterminal IdList_c with ast<[String]>;
nonterminal IdTy_c with ast<Pair<String Type>>;
nonterminal IdTys_c with ast<[Pair<String Type>]>;
nonterminal HHint_c with ast<HHint>;
nonterminal Clearable_c with ast<Clearable>;
nonterminal Withs_c with ast<[Pair<String Term>]>;


concrete productions top::IdList_c
| l::Id_t
  { top.ast = [l.lexeme]; }
| l::Id_t ',' rest::IdList_c
  { top.ast = l.lexeme::rest.ast; }


concrete productions top::IdTy_c
| i::Id_t ':' t::Ty_c
  { top.ast = pair(i.lexeme, t.ast); }


concrete productions top::IdTys_c
| i::IdTy_c ',' rest::IdTys_c
  { top.ast = i.ast::rest.ast;}
| i::IdTy_c
  { top.ast = [i.ast]; }


concrete productions top::HHint_c
| name::Id_t ':'
  { top.ast = nameHint(name.lexeme); }
|
  { top.ast = noHint(); }


concrete productions top::Clearable_c
| h::Hyp_c m::MaybeInst_c
  { top.ast = clearable(false, h.ast, m.ast); }
| '*' h::Hyp_c m::MaybeInst_c
  { top.ast = clearable(true, h.ast, m.ast); }


concrete productions top::Withs_c
| i::Id_t '=' t::Term_c ',' rest::Withs_c
  { top.ast = pair(i.lexeme, t.ast)::rest.ast; }
| i::Id_t '=' t::Term_c
  { top.ast = [pair(i.lexeme, t.ast)]; }





nonterminal Hyp_c with ast<String>;
nonterminal HypList_c with ast<[String]>;


concrete productions top::Hyp_c
| name::Id_t
  { top.ast = name.lexeme; }
| '_'
  { top.ast = "_"; }


concrete productions top::HypList_c
| h::Hyp_c l::HypList_c
  { top.ast = h.ast::l.ast; }
| h::Hyp_c
  { top.ast = [h.ast]; }





nonterminal MaybeInst_c with ast<[Type]>;
nonterminal MaybeDepth_c with ast<Maybe<Integer>>;


concrete productions top::MaybeInst_c
|
  { top.ast = []; }
| '[' u::UTyList_c ']'
  { top.ast = u.ast; }


concrete productions top::MaybeDepth_c
| n::Number_t
  { top.ast = just(toInt(n.lexeme)); }
|
  { top.ast = nothing(); }





nonterminal NumList_c with ast<[Integer]>;


concrete productions top::NumList_c
| n::Number_t rest::NumList_c
  { top.ast = toInt(n.lexeme)::rest.ast; }
| n::Number_t
  { top.ast = [toInt(n.lexeme)]; }





nonterminal ClauseSel_c with ast<(ProofCommand ::= Boolean)>;
nonterminal SolSel_c with ast<Boolean>;


concrete productions top::ClauseSel_c
|
  { top.ast = unfoldTactic(_); }
| n::Number_t
  { top.ast = unfoldStepsTactic(toInt(n.lexeme), _); }
| si::Id_t
  { top.ast = unfoldIdentifierTactic(si.lexeme, _); }


concrete productions top::SolSel_c
|
  { top.ast = false; }
| '(' 'all' ')'
  { top.ast = true; }





nonterminal TheoremTyparams_c with ast<[String]>;


concrete productions top::TheoremTyparams_c
|
  { top.ast = []; }
| '[' il::IdList_c ']'
  { top.ast = il.ast; }





nonterminal ImportWiths_c with ast <[Pair<String String>]>;


concrete productions top::ImportWiths_c
| i1::Id_t ':=' i2::Id_t
{ top.ast = [pair(i1.lexeme, i2.lexeme)]; }
| i1::Id_t ':=' i2::Id_t ',' rest::ImportWiths_c
{ top.ast = pair(i1.lexeme, i2.lexeme)::rest.ast; }

