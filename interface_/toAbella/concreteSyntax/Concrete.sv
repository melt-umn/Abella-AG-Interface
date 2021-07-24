grammar interface_:toAbella:concreteSyntax;






closed nonterminal GrammarDecl_c with ast<String>;

concrete productions top::GrammarDecl_c
| 'Grammar' q::Qname_t '.'
  { top.ast = q.lexeme; }






closed nonterminal FullFile_c with ast<(String, ListOfCommands)>;
closed nonterminal ListOfCommands_c with ast<ListOfCommands>;

concrete productions top::FullFile_c
| g::GrammarDecl_c contents::ListOfCommands_c
  { top.ast = (g.ast, contents.ast); }

concrete productions top::ListOfCommands_c
|
  { top.ast = emptyListOfCommands(); }
| a::AnyCommand_c rest::ListOfCommands_c
  { top.ast = addListOfCommands(a.ast, rest.ast); }





closed nonterminal PureCommand_c with ast<ProofCommand>;
closed nonterminal CommonCommand_c with ast<NoOpCommand>;
closed nonterminal PureTopCommand_c with ast<AnyCommand>; --to handle common parsing errors gracefully
closed nonterminal AnyCommand_c with ast<AnyCommand>;
closed nonterminal TheoremStmts_c with ast<Either<String [(String, Metaterm, String)]>>;
closed nonterminal QnameList_c with ast<[String]>;

concrete productions top::AnyCommand_c
| c::PureTopCommand_c
  { top.ast = c.ast; }
| c::PureCommand_c
  { top.ast = anyProofCommand(c.ast); }
| c::CommonCommand_c
  { top.ast = anyNoOpCommand(c.ast); }

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
| h::HHint_c 'case_local' a::AttrAccess_t '.'
  { local treeName::String = case split_AttrAccess_t(a) of | pair(trn, _) -> trn end;
    local attrName::String = case split_AttrAccess_t(a) of | pair(_, atn) -> atn end;
    top.ast = caseLocalAttr(h.ast, treeName, attrName); }
| h::HHint_c 'case_structure' tree::Id_t 'in' hy::Hyp_c 'with' hy2::Hyp_c '.'
  { top.ast = caseStructure(h.ast, tree.lexeme, hy.ast, hy2.ast, false); }
| h::HHint_c 'case_structure' tree::Id_t 'in' hy::Hyp_c 'with' hy2::Hyp_c '(' 'keep' ')' '.'
  { top.ast = caseStructure(h.ast, tree.lexeme, hy.ast, hy2.ast, true); }
--| h::HHint_c 'assert' md::MaybeDepth_c m::Metaterm_c '.'
--  { top.ast = assertTactic(h.ast, md.ast, m.ast); }
{-The above is the original rule.  Once I added Silver things, this
  became an ambiguity.  By moving the option here (in the following
  two rules) rather than the MaybeDepth_c nonterminal, we remove the
  ambiguity.-}
--| h::HHint_c 'assert' d::Depth_c m::Metaterm_c '.'
--  { top.ast = assertTactic(h.ast, just(d.ast), m.ast); }
| h::HHint_c 'trees_equal' hyp1::Hyp_c hyp2::Hyp_c '.'
  { top.ast = treesEqual(h.ast, hyp1.ast, hyp2.ast); }
| h::HHint_c 'assert' m::Metaterm_c '.'
  { top.ast = assertTactic(h.ast, nothing(), m.ast); }
| 'exists' ew::EWitnesses_c '.'
  { top.ast = existsTactic(ew.ast); }
| 'witness' ew::EWitnesses_c '.'
  { top.ast = witnessTactic(ew.ast); }
| 'search' '.'
  { top.ast = searchTactic(); }
| 'search' n::Number_t '.'
  { top.ast = searchDepthTactic(toInteger(n.lexeme)); }
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
  { top.ast = abbrevCommand(hl.ast, removeQuotes(q.lexeme)); }
| 'unabbrev' hl::HypList_c '.'
  { top.ast = unabbrevCommand(hl.ast); }
| 'rename' original::Id_t 'to' newname::Id_t '.'
  { top.ast = renameTactic(original.lexeme, newname.lexeme); }
| 'permute' p::Perm_c '.'
  { top.ast = permuteTactic(p.ast, nothing()); }
| 'permute' p::Perm_c h::Hyp_c '.'
  { top.ast = permuteTactic(p.ast, just(h.ast)); }

concrete productions top::PureTopCommand_c
| 'Theorem' name::Id_t params::TheoremTyparams_c ':' body::Metaterm_c '.'
  { top.ast = anyTopCommand(theoremDeclaration(name.lexeme, params.ast, body.ast)); }
| 'Define' x::IdTys_c 'by' o::OptSemi_t d::Defs_c '.'
  { top.ast = anyTopCommand(definitionDeclaration(x.ast, d.ast)); }
| 'CoDefine' x::IdTys_c 'by' o::OptSemi_t d::Defs_c '.'
  { top.ast = anyTopCommand(codefinitionDeclaration(x.ast, d.ast)); }
| 'Query' m::Metaterm_c '.'
  { top.ast = anyTopCommand(queryCommand(m.ast)); }
| 'Kind' il::IdList_c k::Knd_c '.'
  { top.ast = anyTopCommand(kindDeclaration(il.ast, k.ast)); }
| 'Type' il::IdList_c t::Ty_c '.'
  { top.ast = anyTopCommand(typeDeclaration(il.ast, t.ast)); }
| 'Close' al::ATyList_c '.'
  { top.ast = anyTopCommand(closeCommand(al.ast)); }
| 'Split' name::Id_t '.'
  { top.ast = anyTopCommand(splitTheorem(name.lexeme, [])); }
| 'Split' name::Id_t 'as' il::IdList_c '.'
  { top.ast = anyTopCommand(splitTheorem(name.lexeme, il.ast)); }
--New for Silver
| 'Extensible_Theorem' thms::TheoremStmts_c '.'
  { top.ast =
        case thms.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(lst) -> anyTopCommand(extensibleTheoremDeclaration(1, lst))
        end; }
| 'Extensible_Theorem' '[' depth::Number_t ']' thms::TheoremStmts_c '.'
  { top.ast =
        case thms.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(lst) ->
          anyTopCommand(extensibleTheoremDeclaration(toInteger(depth.lexeme), lst))
        end; }
| 'Prove' thms::QnameList_c '.'
  { top.ast = error("Not done yet"); }
| 'Extensible_Theorem' newthms::TheoremStmts_c 'with' oldthms::QnameList_c '.'
  { top.ast =
        case newthms.ast of
        | left(msg) -> anyParseFailure(msg)
        | right(lst) -> error("Not done yet")
        end; }


concrete productions top::TheoremStmts_c
| name::Id_t ':' body::Metaterm_c 'on' tree::Id_t
  { top.ast = right([(toString(name.lexeme), body.ast, toString(tree.lexeme))]); }
| name::Id_t ':' body::Metaterm_c 'on' tree::Id_t ',' rest::TheoremStmts_c
  { top.ast =
        case rest.ast of
        | left(msg) -> left(msg)
        | right(lst) ->
          right((toString(name.lexeme), body.ast, toString(tree.lexeme))::lst)
        end; }
  --These are to get errors which are more helpful, because I forget
  --   the trees a lot and can't figure out why it doesn't work.
| name::Id_t ':' body::Metaterm_c
  { top.ast =
        left("Must include tree on which to do induction for theorem " ++
             toString(name.lexeme)); }
| name::Id_t ':' body::Metaterm_c ',' rest::TheoremStmts_c
  { top.ast =       
        left("Must include tree on which to do induction for theorem " ++
              toString(name.lexeme) ++ "\n" ++
             case rest.ast of
             | left(msg) -> msg
             | right(_) -> ""
             end); }


concrete productions top::QnameList_c
| q::Qname_t
  { top.ast = [q.lexeme]; }
| q::Qname_t ',' rest::QnameList_c
  { top.ast = q.lexeme::rest.ast; }


concrete productions top::CommonCommand_c
| 'Set' opt::Id_t value::Id_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t value::Number_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t value::QString_t '.'
  { top.ast = setCommand(opt.lexeme, value.lexeme); }
| 'Set' opt::Id_t 'on' '.'
  { top.ast = setCommand(opt.lexeme, "on"); }
| 'Show' name::Id_t '.'
  { top.ast = showCommand(name.lexeme); }
| 'Quit' '.'
  { top.ast = quitCommand(); }
| b::Backs_c
  { top.ast = backCommand(b.ast); }
| '#reset' '.'
  { top.ast = resetCommand(); }
| 'Show $$current.'
  { top.ast = showCurrentCommand(); }


closed nonterminal Backs_c with ast<Integer>;

concrete productions top::Backs_c
| b::Backs_t
  { top.ast = countOctothorpeOccurrences(b.lexeme); }

function countOctothorpeOccurrences
Integer ::= str::String
{
  local index::Integer = indexOf("#", str);
  local rest::String = substring(index + 1, length(str), str);
  return
     if index > -1
     then 1 + countOctothorpeOccurrences(rest)
     else 0;
}





concrete productions top::Exp_c
--This doesn't work with fromAbella, so we put it here instead
| i::Number_t
  { top.ast = intTerm(toInteger(i.lexeme)); }





closed nonterminal Knd_c with ast<Kind>;
closed nonterminal UTy_c with ast<Type>;
closed nonterminal UTyList_c with ast<[Type]>;
closed nonterminal ATyList_c with ast<[Type]>;


concrete productions top::Knd_c
| 'type'
  { top.ast = typeKind(); }
| 'type' '->' k::Knd_c
  { top.ast = arrowKind(k.ast); }


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





closed nonterminal Defs_c with ast<Defs>;
closed nonterminal Def_c with ast<Def>;


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





closed nonterminal Perm_c with ast<[String]>;
closed nonterminal PermIds_c with ast<[String]>;


concrete productions top::Perm_c
| '(' p::PermIds_c ')'
  { top.ast = p.ast; }


concrete productions top::PermIds_c
| i::Id_t rest::PermIds_c
  { top.ast = i.lexeme::rest.ast; }
| i::Id_t
  { top.ast = [i.lexeme]; }





closed nonterminal SearchWitness_c with ast<SearchWitness>;
closed nonterminal SearchWitnessList_c with ast<[SearchWitness]>;


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
  { top.ast = unfoldSearchWitness(i.lexeme, toInteger(n.lexeme), swl.ast); }
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





closed nonterminal EWitnesses_c with ast<[EWitness]>;
closed nonterminal EWitness_c with ast<EWitness>;


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





closed nonterminal ApplyArgs_c with ast<[ApplyArg]>;
closed nonterminal ApplyArg_c with ast<ApplyArg>;


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





closed nonterminal ExistsBinds_c with ast<[Pair<String Term>]>;


concrete productions top::ExistsBinds_c
|
  { top.ast = []; }
| w::Withs_c
  { top.ast = w.ast; }





closed nonterminal IdList_c with ast<[String]>;
closed nonterminal IdTy_c with ast<Pair<String Type>>;
closed nonterminal IdTys_c with ast<[Pair<String Type>]>;
closed nonterminal HHint_c with ast<HHint>;
closed nonterminal Clearable_c with ast<Clearable>;
closed nonterminal Withs_c with ast<[Pair<String Term>]>;


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





closed nonterminal Hyp_c with ast<String>;
closed nonterminal HypList_c with ast<[String]>;


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





closed nonterminal MaybeInst_c with ast<[Type]>;
closed nonterminal MaybeDepth_c with ast<Maybe<Integer>>;


concrete productions top::MaybeInst_c
|
  { top.ast = []; }
| '[' u::UTyList_c ']'
  { top.ast = u.ast; }


concrete productions top::MaybeDepth_c
| d::Depth_c
  { top.ast = just(d.ast); }
|
  { top.ast = nothing(); }

--this is solely a helper to fix a parsing error with MaybeDepth
closed nonterminal Depth_c with ast<Integer>;
concrete productions top::Depth_c
| n::Number_t
  { top.ast = toInteger(n.lexeme); }





closed nonterminal NumList_c with ast<[Integer]>;


concrete productions top::NumList_c
| n::Number_t rest::NumList_c
  { top.ast = toInteger(n.lexeme)::rest.ast; }
| n::Number_t
  { top.ast = [toInteger(n.lexeme)]; }





closed nonterminal ClauseSel_c with ast<(ProofCommand ::= Boolean)>;
closed nonterminal SolSel_c with ast<Boolean>;


concrete productions top::ClauseSel_c
|
  { top.ast = unfoldTactic(_); }
| n::Number_t
  { top.ast = unfoldStepsTactic(toInteger(n.lexeme), _); }
| si::Id_t
  { top.ast = unfoldIdentifierTactic(si.lexeme, _); }


concrete productions top::SolSel_c
|
  { top.ast = false; }
| '(' 'all' ')'
  { top.ast = true; }





closed nonterminal TheoremTyparams_c with ast<[String]>;


concrete productions top::TheoremTyparams_c
|
  { top.ast = []; }
| '[' il::IdList_c ']'
  { top.ast = il.ast; }





function removeQuotes
String ::= qstring::String
{
  return substring(1, length(qstring) - 1, qstring);
}

