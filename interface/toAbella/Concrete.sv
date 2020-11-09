grammar toAbella;


--some of these might become terminals/get wrapped into the definitions
--we'll see when I get through the whole grammar in which I am interested
nonterminal Hyp;
nonterminal Knd;
nonterminal AId; --Annotated ID
nonterminal PAId; --Parenthesized Annotated ID
nonterminal ContextedTerm;
nonterminal FocusedTerm;
nonterminal Context;
nonterminal Term;
nonterminal Exp;
nonterminal ExpList;
nonterminal IdList;
nonterminal PTy;
nonterminal ATy;
nonterminal Ty;
nonterminal Defs;
nonterminal Def;
nonterminal Perm;
nonterminal PermIds;
nonterminal AnyCommand;
nonterminal Command;
nonterminal Clearable;
nonterminal MaybeInst;
nonterminal UTy;
nonterminal UTyList;
nonterminal ATyList;
nonterminal ApplyArgs;
nonterminal ApplyArg;
nonterminal MaybeDepth;
nonterminal PureCommand;
nonterminal HHint;
nonterminal HypList;
nonterminal NumList;
nonterminal EWitnesses;
nonterminal EWitness;
nonterminal Withs;
nonterminal ClauseSel;
nonterminal SolSel;
nonterminal Metaterm;
nonterminal Objseq;
nonterminal Binder;
nonterminal BindingList;
nonterminal BindingOne;
nonterminal BindingVars;
nonterminal Restriction;
nonterminal Stars;
nonterminal Ats;
nonterminal Pluses;
nonterminal Hashes;
nonterminal IdTy;
nonterminal IdTys;
nonterminal TopCommand;
nonterminal TheoremTyparams;
nonterminal PureTopCommand;
nonterminal ImportWiths;
nonterminal CommonCommand;
nonterminal OptSemi;
nonterminal SearchWitness;
nonterminal SearchWitnessList;
nonterminal ExistsBinds;


concrete productions top::Hyp
| name::Id_t
{ }
| '_'
{ }


concrete productions top::Knd
| 'Type'
{ }
| 'Type' '->' k::Knd
{ }


concrete productions top::AId
| l::Id_t
{ }
| l::Id_t ':' t::Ty
{ }


concrete productions top::PAId
| l::Id_t
{ }
| '(' l::Id_t ':' t::Ty ')'
{ }
| '_'
{ }
| '(' '_' ':' t::Ty ')'
{ }


concrete productions top::Term
| e::Exp el::ExpList
{ }
| e::Exp
{ }


concrete productions top::Exp
| '(' t::Term ')'
{ }
| p::PAId
{ }


concrete productions top::ExpList
| e::Exp el::ExpList
{ }
| e::Exp
{ }
| a::AId '\' t::Term
{ }


concrete productions top::IdList
| l::Id_t
{ }
| l::Id_t ',' rest::IdList
{ }


concrete productions top::PTy
| i::Id_t
{ }
| '(' t::Ty ')'
{ }


concrete productions top::ATy
| i::Id_t
{ }
| a::ATy p::PTy
{ }


concrete productions top::Ty
| a::ATy
{ }
| t1::Ty '->' t2::Ty
{ }
| '(' t::Ty ')'
{ }


concrete productions top::Defs
| d::Def ';' rest::Defs
{ }
| d::Def
{ }


concrete productions top::Def
| m::Metaterm
{ }
| h::Metaterm ':=' b::Metaterm
{ }


concrete productions top::Perm
| '(' p::PermIds ')'
{ }


concrete productions top::PermIds
| i::Id_t rest::PermIds
{ }
| i::Id_t
{ }


{-This appears to be useless, but it might end up benig useful in
  ProofGeneral, so I'll hold onto it in a comment.
concrete productions top::AnyCommand
| c::PureTopCommand
{ }
| c::PureCommand
{ }
| c::CommonCommand
{ }
-}


concrete productions top::Command
| p::PureCommand
{ }
| c::CommonCommand
{ }


concrete productions top::Clearable
| h::Hyp m::MaybeInst
{ }
| '*' h::Hyp m::MaybeInst
{ }


concrete productions top::MaybeInst
|
{ }
| '[' u::UTyList ']'
{ }


concrete productions top::UTy
| t::Ty
{ }
| '_'
{ }


concrete productions top::UTyList
| u::UTy
{ }
| u::UTy ',' rest::UTyList
{ }


concrete productions top::ATyList
| a::ATy
{ }
| a::ATy ',' rest::ATyList
{ }


concrete productions top::ApplyArgs
| a::ApplyArg rest::ApplyArgs
{ }
| a::ApplyArg
{ }


concrete productions top::ApplyArg
| h::Hyp m::MaybeInst
{ }
| '*' i::Id_t m::MaybeInst
{ }


concrete productions top::MaybeDepth
| n::Number_t
{ }
|
{ }


concrete productions top::PureCommand
| h::HHint 'induction' 'on' nl::NumList '.'
{ }
| h::HHint 'coinduction' '.'
{ }
| h::HHint 'apply' md::MaybeDepth c::Clearable 'to' a::ApplyArgs '.'
{ }
| h::HHint 'apply' md::MaybeDepth c::Clearable 'to' a::ApplyArgs 'with' w::Withs '.'
{ }
| h::HHint 'apply' md::MaybeDepth c::Clearable 'with' w::Withs '.'
{ }
| h::HHint 'apply' md::MaybeDepth c::Clearable '.'
{ }
| 'backchain' md::MaybeDepth c::Clearable '.'
{ }
| 'backchain' md::MaybeDepth c::Clearable 'with' w::Withs '.'
{ }
| h::HHint 'case' hy::Hyp '.'
{ }
| h::HHint 'case' hy::Hyp '(' 'keep' ')' '.'
{ }
| h::HHint 'assert' md::MaybeDepth m::Metaterm '.'
{ }
| 'exists' ew::EWitnesses '.'
{ }
| 'witness' ew::EWitnesses '.'
{ }
| 'search' '.'
{ }
| 'search' n::Number_t '.'
{ }
| 'search' 'with' sw::SearchWitness '.'
{ }
| 'async' '.'
{ }
| 'split' '.'
{ }
| 'split*' '.'
{ }
| 'left' '.'
{ }
| 'right' '.'
{ }
| 'intros' '.'
{ }
| 'intros' names::HypList '.'
{ }
| 'skip' '.'
{ }
| 'abort' '.'
{ }
| 'undo' '.'
{ }
| 'unfold' cs::ClauseSel ss::SolSel '.'
{ }
| 'clear' hl::HypList '.'
{ }
| 'clear' '->' hl::HypList '.'
{ }
| 'abbrev' hl::HypList q::QString_t '.'
{ }
| 'unabbrev' hl::HypList '.'
{ }
| 'rename' original::Id_t 'to' newname::Id_t '.'
{ }
| 'permute' p::Perm '.'
{ }
| 'permute' p::Perm h::Hyp '.'
{ }


concrete productions top::HHint
| name::Id_t ':'
{ }
|
{ }


concrete productions top::HypList
| h::Hyp l::HypList
{ }
| h::Hyp
{ }


concrete productions top::NumList
| n::Number_t rest::NumList
{ }
| n::Number_t
{ }


concrete productions top::EWitnesses
| ew::EWitness ',' rest::EWitnesses
{ }
| ew::EWitness
{ }


concrete productions top::EWitness
| name::Id_t '=' t::Term
{ }
| t::Term
{ }


concrete productions top::Withs
| i::Id_t '=' t::Term ',' rest::Withs
{ }
| i::Id_t '=' t::Term
{ }


concrete productions top::ClauseSel
|
{ }
| n::Number_t
{ }
| si::Id_t
{ }


concrete productions top::SolSel
|
{ }
| '(' 'all' ')'
{ }


{-concrete productions top::Metaterm
| 'true'
{ }
| 'false'
{ }
| t1::Term '=' t2::Term
{ }
| b::Binder bl::BindingList ',' m::Metaterm
{ }
| m1::Metaterm '->' m2::Metaterm
{ }
| m1::Metaterm '\/' m2::Metaterm
{ }
| m1::Metaterm '/\' m2::Metaterm
{ }
| '(' m::Metaterm ')'
{ }
| t::Term r::Restriction
{ }-}
{-
  The original grammar rules, translated from the OCaml Yacc grammar,
  are above.  That grammar had an ambiguity where `(Term)` could not
  be parsed:
  - It could be a Term followed by an empty Restriction inside
    Metaterm parentheses.
  - It could be a Term in Exp parentheses, which is then a Term
    followed by an empty Restriction as a Metaterm.
  These end up being equal treatments.  The refactoring below
  eliminates the first possibility, since any Term in Metaterm
  parentheses must be followed by a non-empty restriction set.  This
  makes the grammar unambiguous, but still able to parse the same
  strings.
-}
concrete productions top::Metaterm
| t::Term
{ }
| s::SubMetaterm
{ }
nonterminal SubMetaterm;
concrete productions top::SubMetaterm
| 'true'
{ }
| 'false'
{ }
| t1::Term '=' t2::Term
{ }
| b::Binder bl::BindingList ',' m::Metaterm
{ }
| m1::Metaterm '->' m2::Metaterm
{ }
| m1::Metaterm '\/' m2::Metaterm
{ }
| m1::Metaterm '/\' m2::Metaterm
{ }
| '(' m::SubMetaterm ')'
{ }
| t::Term s::Stars
{ }
| t::Term p::Pluses
{ }
| t::Term a::Ats
{ }
| t::Term h::Hashes
{ }


concrete productions top::Binder
| 'forall'
{ }
| 'exists'
{ }
| 'nabla'
{ }


concrete productions top::BindingList
| b::BindingOne
{ }
| b::BindingOne rest::BindingList
{ }


concrete productions top::BindingOne
| i::Id_t
{ }
| '(' bv::BindingVars ':' t::Ty ')'
{ }


concrete productions top::BindingVars
| i::Id_t
{ }
| i::Id_t rest::BindingVars
{ }


concrete productions top::Restriction
|
{ }
| s::Stars
{ }
| p::Pluses
{ }
| a::Ats
{ }
| h::Hashes
{ }


concrete productions top::Stars
| '*' rest::Stars
{ }
| '*'
{ }


concrete productions top::Ats
| '@' rest::Ats
{ }
| '@'
{ }


concrete productions top::Pluses
| '+' rest::Pluses
{ }
| '+'
{ }


concrete productions top::Hashes
| '#' rest::Hashes
{ }
| '#'
{ }


concrete productions top::IdTy
| i::Id_t ':' t::Ty
{ }


concrete productions top::IdTys
| i::IdTy ',' rest::IdTys
{ }
| i::IdTy
{ }


concrete productions top::TopCommand
| p::PureTopCommand
{ }
| c::CommonCommand
{ }


concrete productions top::TheoremTyparams
|
{ }
| '[' il::IdList ']'
{ }


concrete productions top::PureTopCommand
| 'Theorem' name::Id_t params::TheoremTyparams ':' body::Metaterm '.'
{ }
| 'Define' x::IdTys 'by' o::OptSemi d::Defs '.'
{ }
| 'CoDefine' x::IdTys 'by' o::OptSemi d::Defs '.'
{ }
| 'Query' m::Metaterm '.'
{ }
| 'Import' q::QString_t '.'
{ }
| 'Import' q::QString_t 'with' iw::ImportWiths '.'
{ }
| 'Specification' q::QString_t '.'
{ }
| 'Kind' il::IdList k::Knd '.'
{ }
| 'Type' il::IdList t::Ty '.'
{ }
| 'Close' al::ATyList '.'
{ }
| 'Split' name::Id_t '.'
{ }
| 'Split' name::Id_t 'as' il::IdList '.'
{ }


concrete productions top::ImportWiths
| i1::Id_t ':=' i2::Id_t
{ }
| i1::Id_t ':=' a2::Id_t ',' rest::ImportWiths
{ }


concrete productions top::CommonCommand
| 'Set' option::Id_t value::Id_t '.'
{ }
| 'Set' option::Id_t value::Number_t '.'
{ }
| 'Set' option::Id_t value::QString_t '.'
{ }
| 'Show' name::Id_t '.'
{ }
| 'Quit' '.'
{ }
| '#back' '.'
{ }
| '#reset' '.'
{ }


concrete productions top::OptSemi
|
{ }
| ';'
{ }


concrete productions top::SearchWitness
| 'true'
{ }
| 'apply' i::Id_t
{ }
| 'left' sw::SearchWitness
{ }
| 'right' sw::SearchWitness
{ }
| 'split' '(' sw1::SearchWitness ',' sw2::SearchWitness ')'
{ }
| 'intros' '[' il::IdList ']' sw::SearchWitness
{ }
| 'forall' '[' il::IdList ']' sw::SearchWitness
{ }
| 'exists' '[' eb::ExistsBinds ']' sw::SearchWitness
{ }
| 'unfold' '(' i::Id_t ',' n::Number_t swl::SearchWitnessList ')'
{ }
| '*'
{ }
| '='
{ }
| '(' sw::SearchWitness ')'
{ }


concrete productions top::SearchWitnessList
|
{ }
| ',' sw::SearchWitness swl::SearchWitnessList
{ }


concrete productions top::ExistsBinds
|
{ }
| w::Withs
{ }

