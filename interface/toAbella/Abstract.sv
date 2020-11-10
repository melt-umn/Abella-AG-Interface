grammar toAbella;


synthesized attribute pp::String;


--things you can do outside of proofs
nonterminal TopCommand with
   --pp should always end with a newline
   pp;

abstract production theoremDeclaration
top::TopCommand ::= name::String params::[String] body::Metaterm
{
  local buildParams::(String ::= [String]) =
     \ p::[String] ->
       case p of
       | [] ->
         error("Should not reach here; theoremDeclaration production")
       | [a] -> a
       | a::rest ->
         a ++ ", " ++ buildParams(rest)
       end;
  local paramsString::String =
     if null(params)
     then ""
     else " [" ++ buildParams(params) ++ "] ";
  top.pp =
      "Theorem " ++ name ++ " " ++ paramsString ++
      " : " ++ body.pp ++ ".\n";
}


abstract production definitionDeclaration
top::TopCommand ::= preds::[Pair<String Type>] defs::Defs
{
  local buildPreds::(String ::= [Pair<String Type>]) =
     \ w::[Pair<String Type>] ->
       case w of
       | [] ->
         error("Should not reach here; definitionDeclaration production")
       | [pair(a, b)] -> a ++ " : " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " := " ++ b.pp ++ ", " ++ buildPreds(rest)
       end;
  local predsString::String =
     if null(preds)
     then error("Definition should not be empty; definitionDeclaration")
     else buildPreds(preds);
  top.pp = "Define " ++ predsString ++ " by " ++ defs.pp ++ ".";
}


abstract production codefinitionDeclaration
top::TopCommand ::= preds::[Pair<String Type>] defs::Defs
{
  local buildPreds::(String ::= [Pair<String Type>]) =
     \ w::[Pair<String Type>] ->
       case w of
       | [] ->
         error("Should not reach here; codefinitionDeclaration production")
       | [pair(a, b)] -> a ++ " : " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " := " ++ b.pp ++ ", " ++ buildPreds(rest)
       end;
  local predsString::String =
     if null(preds)
     then error("CoDefinition should not be empty; codefinitionDeclaration")
     else buildPreds(preds);
  top.pp = "CoDefine " ++ predsString ++ " by " ++ defs.pp ++ ".";
}


abstract production importCommand
top::TopCommand ::= importFile::String withs::[Pair<String String>]
{
  local buildWiths::(String ::= [Pair<String String>]) =
     \ w::[Pair<String String>] ->
       case w of
       | [] ->
         error("Should not reach here; importCommand production")
       | [pair(a, b)] -> a ++ " := " ++ b
       | pair(a,b)::rest ->
         a ++ " := " ++ b ++ ", " ++ buildWiths(rest)
       end;
  local withString::String =
     if null(withs)
     then ""
     else " with " ++ buildWiths(withs);
  top.pp = "Import " ++ importFile ++ withString ++ ".\n";
}


abstract production queryCommand
top::TopCommand ::= m::Metaterm
{
  top.pp = "Query " ++ m.pp ++ ".\n";
}


abstract production splitTheorem
top::TopCommand ::= theoremName::String newTheoremNames::[String]
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; splitTheorem production")
       | [a] -> a
       | a::rest -> a ++ ", " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(newTheoremNames)
     then ""
     else " as " ++ buildNames(newTheoremNames);
  top.pp = "Split " ++ theoremName ++ namesString ++ ".\n";
}


--I'm not sure we need new kinds and types, but I'll put it in
abstract production kindDeclaration
top::TopCommand ::= names::[String] k::Kind
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; splitTheorem production")
       | [a] -> a
       | a::rest -> a ++ ", " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(names)
     then ""
     else " as " ++ buildNames(names);
  top.pp = "Kind " ++ namesString ++ "   " ++ k.pp ++ ".\n";
}


abstract production typeDeclaration
top::TopCommand ::= names::[String] ty::Type
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; splitTheorem production")
       | [a] -> a
       | a::rest -> a ++ ", " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(names)
     then ""
     else " as " ++ buildNames(names);
  top.pp = "Type " ++ namesString ++ "   " ++ ty.pp ++ ".\n";
}


abstract production closeCommand
top::TopCommand ::= tys::[Type]
{
  local buildTypes::(String ::= [Type]) =
     \ n::[Type] ->
       case n of
       | [] ->
         error("Should not reach here; closeCommand production")
       | [a] -> a.pp
       | a::rest -> a.pp ++ ", " ++ buildTypes(rest)
       end;
  local typesString::String =
     if null(tys)
     then error("Close commands should not be devoid of tyes")
     else buildTypes(tys);
  top.pp = "Close " ++ typesString ++ ".\n";
}


abstract production topNoOpCommand
top::TopCommand ::= n::NoOpCommand
{
  top.pp = n.pp;
}





--things you can do inside of proofs
nonterminal ProofCommand with
   --pp should end with two spaces
   pp;

abstract production inductionTactic
top::ProofCommand ::= h::HHint nl::[Integer]
{
  local buildInts::(String ::= [Integer]) =
     \ nl::[Integer] ->
       case nl of
       | [] -> error("Empty list of induction premises in inductionTactic")
       | [n] -> toString(n)
       | n::rest -> toString(n) ++ " " ++ buildInts(rest)
       end;
  top.pp = h.pp ++ "induction " ++ buildInts(nl) ++ ".  ";
}


abstract production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.pp = h.pp ++ "coinduction.  ";
}


abstract production introsTactic
top::ProofCommand ::= names::[String]
{
  local buildNames::(String ::= [String]) =
     \ n::[String] ->
       case n of
       | [] ->
         error("Should not reach here; introsTactic production")
       | [a] -> a
       | a::rest -> a ++ ", " ++ buildNames(rest)
       end;
  local namesString::String =
     if null(names)
     then ""
     else " " ++ buildNames(names);
  top.pp = "intros" ++ namesString ++ ".  ";
}


abstract production applyTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> theorem::Clearable args::[ApplyArg] withs::[Pair<String Term>]
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local buildArgs::(String ::= [ApplyArg]) =
    \ al::[ApplyArg] ->
      case al of
      | [] -> error("Should not reach here; applyTactic production")
      | [a] -> a.pp
      | a::rest -> a.pp ++ " " ++ buildArgs(rest)
      end;
  local argsString::String =
     if null(args)
     then ""
     else "to " ++ buildArgs(args);
  local buildWiths::(String ::= [Pair<String Term>]) =
    \ wl::[Pair<String Term>] ->
      case wl of
      | [] -> error("Should not reach here; applyTactic production")
      | [pair(a, b)] -> a ++ " = " ++ b.pp
      | pair(a, b)::rest -> a ++ " = " ++ b.pp ++ ", " ++ buildWiths(rest)
      end;
  local withsString::String =
     if null(withs)
     then ""
     else "with " ++ buildWiths(withs);
  top.pp = h.pp ++ "apply " ++ depthString ++ theorem.pp ++ argsString ++ withsString ++ ".  ";
}


abstract production backchainTactic
top::ProofCommand ::= depth::Maybe<Integer> theorem::Clearable withs::[Pair<String Term>]
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  local buildWiths::(String ::= [Pair<String Term>]) =
    \ wl::[Pair<String Term>] ->
      case wl of
      | [] -> error("Should not reach here; backchainTactic production")
      | [pair(a, b)] -> a ++ " = " ++ b.pp
      | pair(a, b)::rest -> a ++ " = " ++ b.pp ++ ", " ++ buildWiths(rest)
      end;
  local withsString::String =
     if null(withs)
     then ""
     else "with " ++ buildWiths(withs);
  top.pp = "backchain " ++ depthString ++ theorem.pp ++ withsString ++ ".  ";
}


abstract production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.pp = h.pp ++ "case " ++ hyp ++ if keep then "(keep).  " else ".  ";
}


abstract production assertTactic
top::ProofCommand ::= h::HHint depth::Maybe<Integer> m::Metaterm
{
  local depthString::String =
     case depth of
     | just(d) -> toString(d) ++ " "
     | nothing() -> ""
     end;
  top.pp = h.pp ++ "assert " ++ depthString ++ m.pp ++ ".  ";
}


abstract production existsTactic
top::ProofCommand ::= ew::[EWitness]
{
  local buildWitnesses::(String ::= [EWitness]) =
   \ ew::[EWitness] ->
     case ew of
     | [] ->
       error("Cannot have an empty list in existsTactic")
     | [e] -> e.pp
     | e::rest -> e.pp ++ ", " ++ buildWitnesses(rest)
     end;
  top.pp = "exists " ++ buildWitnesses(ew) ++ ".  ";
}


abstract production witnessTactic
top::ProofCommand ::= ew::[EWitness]
{
  local buildWitnesses::(String ::= [EWitness]) =
   \ ew::[EWitness] ->
     case ew of
     | [] ->
       error("Cannot have an empty list in existsTactic")
     | [e] -> e.pp
     | e::rest -> e.pp ++ ", " ++ buildWitnesses(rest)
     end;
  top.pp = "witness " ++ buildWitnesses(ew) ++ ".  ";
}


abstract production searchTactic
top::ProofCommand ::=
{
  top.pp = "search.  ";
}


abstract production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.pp = "search " ++ toString(n) ++ ".  ";
}


abstract production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.pp = "search with " ++ sw.pp ++ ".  ";
}


abstract production asyncTactic
top::ProofCommand ::=
{
  top.pp = "async.  ";
}


abstract production splitTactic
top::ProofCommand ::=
{
  top.pp = "split.  ";
}


abstract production splitStarTactic
top::ProofCommand ::=
{
  top.pp = "split*.  ";
}


abstract production leftTactic
top::ProofCommand ::=
{
  top.pp = "left.  ";
}


abstract production rightTactic
top::ProofCommand ::=
{
  top.pp = "right.  ";
}


abstract production skipTactic
top::ProofCommand ::=
{
  top.pp = "skip.  ";
}


abstract production abortCommand
top::ProofCommand ::=
{
  top.pp = "abort.  ";
}


abstract production undoCommand
top::ProofCommand ::=
{
  top.pp = "undo.  ";
}


--I have no idea what the arrow does, but there are clears with and without it
abstract production clearCommand
top::ProofCommand ::= removes::[String] hasArrow::Boolean
{
  local buildHyps::(String ::= [String]) =
   \ hl::[String] ->
     case hl of
     | [] ->
       error("Cannot have an empty list in clearCommand")
     | [h] -> h
     | h::rest -> h ++ " " ++ buildHyps(rest)
     end;
  top.pp = "clear " ++ (if hasArrow then "-> " else "") ++ buildHyps(removes) ++ ".  ";
}


abstract production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";
}


--this assumes newText does NOT include the quotation marks
abstract production abbrevCommand
top::ProofCommand ::= hyps::[String] newText::String
{
  local buildHyps::(String ::= [String]) =
   \ hl::[String] ->
     case hl of
     | [] ->
       error("Cannot have an empty list in abbrevCommand")
     | [h] -> h
     | h::rest -> h ++ " " ++ buildHyps(rest)
     end;
  top.pp = "abbrev " ++ buildHyps(hyps) ++ " \"" ++ newText ++ "\".  ";
}


abstract production unabbrevCommand
top::ProofCommand ::= hyps::[String]
{
  local buildHyps::(String ::= [String]) =
   \ hl::[String] ->
     case hl of
     | [] ->
       error("Cannot have an empty list in abbrevCommand")
     | [h] -> h
     | h::rest -> h ++ " " ++ buildHyps(rest)
     end;
  top.pp = "unabbrev " ++ buildHyps(hyps) ++ "\".  ";
}


abstract production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  local hypString::String = case hyp of | just(h) -> " " ++ h | nothing() -> "" end;
  top.pp = "permute " ++ foldr1(\a::String b::String -> a ++ " " ++ b, names) ++ hypString ++ ".  ";
}


abstract production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.pp = "unfold " ++ toString(steps) ++ if all then "(all).  " else ".  ";
}


abstract production unfoldIdentifierTactic
top::ProofCommand ::= id::String all::Boolean
{
  top.pp = "unfold " ++ id ++ if all then "(all).  " else ".  ";
}


abstract production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.pp = "unfold " ++ if all then "(all).  " else ".  ";
}


abstract production proofNoOpCommand
top::ProofCommand ::= n::NoOpCommand
{
  top.pp = n.pp;
}





--things that aren't connected to the logic, like setting options
nonterminal NoOpCommand with
   --pp should always end with a newline
   pp;

--because we only intend to pass these through to Abella, we don't
--   need to actually know anything about the option or its value
--   other than its text
abstract production setCommand
top::NoOpCommand ::= opt::String val::String
{
  top.pp = "Set " ++ opt ++ " " ++ val ++ ".\n";
}


abstract production showCommand
top::NoOpCommand ::= theoremName::String
{
  top.pp = "Show " ++ theoremName ++ ".\n";
}


abstract production quitCommand
top::NoOpCommand ::=
{
  top.pp = "Quit.\n";
}


abstract production backCommand
top::NoOpCommand ::=
{
  top.pp = "#back.\n";
}


abstract production resetCommand
top::NoOpCommand ::=
{
  top.pp = "#reset.\n";
}






nonterminal HHint with pp;

abstract production nameHint
top::HHint ::= name::String
{
  top.pp = name ++ ": ";
}


abstract production noHint
top::HHint ::=
{
  top.pp = "";
}









nonterminal Metaterm with pp;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;
}


abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";
}


abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";
}


abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;
}


abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") -> " ++ t2.pp;
}


abstract production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") \\/ (" ++ t2.pp ++ ")";
}


abstract production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") /\\ (" ++ t2.pp ++ ")";
}


abstract production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[Pair<String Maybe<Type>>] body::Metaterm
{
  local bindingsString::String =
     if null(bindings)
     then error("Empty bindings not allowed; production bindingsMetaterm")
     else foldr1(\ a::String b::String -> a ++ " " ++ b,
                 map(\p::Pair<String Maybe<Type>> ->
                     case p of
                     | pair(a, just(ty)) -> "(" ++ a ++ " : " ++ ty.pp ++ ")"
                     | pair(a, nothing()) -> a
                     end, bindings));
  top.pp = b.pp ++ " " ++ bindingsString ++ ", " ++ body.pp;
}



nonterminal Restriction with pp;

abstract production emptyRestriction
top::Restriction ::=
{
  top.pp = "";
}


abstract production starRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "*");
}


abstract production atRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "@");
}


abstract production plusRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "+");
}


abstract production hashRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "#");
}




nonterminal Binder with pp;

abstract production forallBinder
top::Binder ::=
{
  top.pp = "forall";
}


abstract production existsBinder
top::Binder ::=
{
  top.pp = "exists";
}


abstract production nablaBinder
top::Binder::=
{
  top.pp = "nabla";
}





nonterminal Term with pp;

abstract production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp = "(" ++ f.pp ++ ") " ++ args.pp;
}


abstract production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.pp = case ty of
           | just(t) -> "(" ++ name ++ " : " ++ t.pp ++ ")"
           | nothing() -> name
           end;
}


abstract production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.pp = case ty of
           | just(t) -> "(_ : " ++ t.pp ++ ")"
           | nothing() -> "_"
           end;
}



nonterminal TermList with pp;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = "(" ++ t.pp ++ ")";
}


abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = "(" ++ t.pp ++ ") " ++ rest.pp;
}







nonterminal Clearable with pp;

--I don't know what the star is, but some have it
abstract production clearable
top::Clearable ::= star::Boolean hyp::String instantiation::[Type]
{
  local instString::String =
     if null(instantiation)
     then ""
     else "[" ++ foldr1(\a::String b::String -> a ++ ", " ++ b,
                        map((.pp), instantiation)) ++ "]";
  top.pp = (if star then "*" else "") ++ hyp ++ instString;
}



nonterminal ApplyArg with pp;

abstract production hypApplyArg
top::ApplyArg ::= hyp::String instantiation::[Type]
{
  local instString::String =
     if null(instantiation)
     then ""
     else "[" ++ foldr1(\a::String b::String -> a ++ ", " ++ b,
                        map((.pp), instantiation)) ++ "]";
  top.pp = hyp ++ instString;
}

abstract production starApplyArg
top::ApplyArg ::= name::String instantiation::[Type]
{
  local instString::String =
     if null(instantiation)
     then ""
     else "[" ++ foldr1(\a::String b::String -> a ++ ", " ++ b,
                        map((.pp), instantiation)) ++ "]";
  top.pp = "*" ++ name ++ instString;
}







nonterminal SearchWitness with pp;

abstract production trueSearchWitness
top::SearchWitness ::=
{
  top.pp = "true";
}


abstract production applySearchWitness
top::SearchWitness ::= name::String
{
  top.pp = "apply " ++ name;
}


abstract production leftSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = "left (" ++ sub.pp ++ ")";
}


abstract production rightSearchWitness
top::SearchWitness ::= sub::SearchWitness
{
  top.pp = "right (" ++ sub.pp ++ ")";
}


abstract production splitSearchWitness
top::SearchWitness ::= l::SearchWitness r::SearchWitness
{
  top.pp = "split(" ++l.pp ++ ", " ++ r.pp ++ ")";
}


abstract production introsSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp =
     "intros [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.pp ++ ")";
}


abstract production forallSearchWitness
top::SearchWitness ::= names::[String] sub::SearchWitness
{
  top.pp =
     "forall [" ++ foldr1(\a::String b::String -> a ++ ", " ++ b, names) ++
     "] (" ++ sub.pp ++ ")";
}


abstract production existsSearchWitness
top::SearchWitness ::= withs::[Pair<String Term>] sub::SearchWitness
{
  local buildWiths::(String ::= [Pair<String Term>]) =
     \ w::[Pair<String Term>] ->
       case w of
       | [] ->
         error("Should not reach here; existsSearchWitness production")
       | [pair(a, b)] -> a ++ " := " ++ b.pp
       | pair(a,b)::rest ->
         a ++ " := " ++ b.pp ++ ", " ++ buildWiths(rest)
       end;
  local withsString::String =
     if null(withs)
     then ""
     else " with " ++ buildWiths(withs);
  top.pp = "exists [" ++ withsString ++ "] (" ++ sub.pp ++ ")";
}


abstract production unfoldSearchWitness
top::SearchWitness ::= name::String n::Integer swl::[SearchWitness]
{
  local swlString::String =
     if null(swl)
     then ""
     else foldr1(\a::String b::String -> a ++ ", " ++ b,
                 map(\x::SearchWitness -> x.pp, swl));
  top.pp = "unfold(" ++ name ++ ", " ++ toString(n) ++ swlString ++ ")";
}


abstract production starSearchWitness
top::SearchWitness ::=
{
  top.pp = "*";
}


abstract production eqSearchWitness
top::SearchWitness ::=
{
  top.pp = "=";
}







nonterminal EWitness with pp;

abstract production termEWitness
top::EWitness ::= t::Term
{
  top.pp = t.pp;
}


abstract production nameEWitness
top::EWitness ::= name::String t::Term
{
  top.pp = name ++ " = " ++ t.pp;
}






nonterminal Kind with pp;

abstract production typeKind
top::Kind ::=
{
  top.pp = "type";
}


abstract production arrowKind
top::Kind ::= k::Kind
{
  top.pp = "type -> " ++ k.pp;
}



nonterminal Type with pp;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = "(" ++ ty1.pp ++ ") -> " ++ ty2.pp;
}


abstract production nameType
top::Type ::= name::String
{
  top.pp = name;
}


abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = functorTy.pp ++ " (" ++ argTy.pp ++ ")";
}


abstract production underscoreType
top::Type ::=
{
  top.pp = "_";
}



nonterminal Defs with pp;

abstract production singleDefs
top::Defs ::= d::Def
{
  top.pp = d.pp;
}


abstract production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.pp = d.pp ++ "; " ++ rest.pp;
}



nonterminal Def with pp;

abstract production factDef
top::Def ::= clausehead::Metaterm
{
  top.pp = clausehead.pp;
}


abstract production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.pp = clausehead.pp ++ " := " ++ body.pp;
}


