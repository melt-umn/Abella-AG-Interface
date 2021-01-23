grammar toAbella:abstractSyntax;


--things you can do inside of proofs

nonterminal ProofCommand with
   pp, --pp should end with two spaces
   translation<[ProofCommand]>, attrOccurrences,
   isQuit;



aspect default production
top::ProofCommand ::=
{
  --the only quits are no-op commands
  top.isQuit = false;
}



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

  top.translation = error("Translation not done in inductionTactic yet");
}


abstract production coinductionTactic
top::ProofCommand ::= h::HHint
{
  top.pp = h.pp ++ "coinduction.  ";

  top.translation = [coinductionTactic(h)];
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

  {-
    Need to keep track of introduced names for turning them into structures/nodes.
    e.g. forall (t : nt_Tree), ...
         We might introduce it as tree, in which case we want $tree_Structure and $tree_Node
  -}
  top.translation = error("Translation not done in introsTactic yet");
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

  top.translation = error("Translation not done in applyTactic yet");
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

  top.translation = error("Translation not done in backchainTactic yet");
}


abstract production caseTactic
top::ProofCommand ::= h::HHint hyp::String keep::Boolean
{
  top.pp = h.pp ++ "case " ++ hyp ++ if keep then "(keep).  " else ".  ";

  top.translation = error("Translation not done in caseTactic yet");
}


abstract production caseAttrAccess
top::ProofCommand ::= h::HHint tree::String attr::String
{
  top.pp = h.pp ++ "case " ++ tree ++ "." ++ attr ++ ".  ";

  top.translation = error("Translation not done in caseAttrAccess yet");
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

  top.translation = error("Translation not done in assertTactic yet");
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

  top.translation = error("Translation not done in existsTactic yet");
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

  top.translation = error("Translation not done in witnessTactic yet");
}


abstract production searchTactic
top::ProofCommand ::=
{
  top.pp = "search.  ";

  top.translation = [searchTactic()];
}


abstract production searchDepthTactic
top::ProofCommand ::= n::Integer
{
  top.pp = "search " ++ toString(n) ++ ".  ";

  top.translation = [searchDepthTactic(n)];
}


abstract production searchWitnessTactic
top::ProofCommand ::= sw::SearchWitness
{
  top.pp = "search with " ++ sw.pp ++ ".  ";

  top.translation = error("Translation not done in searchWitnessTactic yet");
}


abstract production asyncTactic
top::ProofCommand ::=
{
  top.pp = "async.  ";
  top.translation = [asyncTactic()];
}


abstract production splitTactic
top::ProofCommand ::=
{
  top.pp = "split.  ";

  top.translation = [splitTactic()];
}


abstract production splitStarTactic
top::ProofCommand ::=
{
  top.pp = "split*.  ";

  top.translation = [splitStarTactic()];
}


abstract production leftTactic
top::ProofCommand ::=
{
  top.pp = "left.  ";

  top.translation = [leftTactic()];
}


abstract production rightTactic
top::ProofCommand ::=
{
  top.pp = "right.  ";

  top.translation = [rightTactic()];
}


abstract production skipTactic
top::ProofCommand ::=
{
  top.pp = "skip.  ";

  top.translation = [skipTactic()];
}


abstract production abortCommand
top::ProofCommand ::=
{
  top.pp = "abort.  ";

  top.translation = [abortCommand()];
}


abstract production undoCommand
top::ProofCommand ::=
{
  top.pp = "undo.  ";

  {-
    The number of undos we really need to generate depends on our last
    command the user entered.  If that turned into multiple commands,
    we should undo them all.
  -}
  top.translation = error("Translation not done in undoTactic yet");
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

  top.translation = [clearCommand(removes, hasArrow)];
}


abstract production renameTactic
top::ProofCommand ::= original::String renamed::String
{
  top.pp = "rename " ++ original ++ " to " ++ renamed ++ ".  ";

  {-
    Depending on what they want you to rename, you might have to
    rename a couple of things which map together (renaming a tree
    needs to rename its structure and nodes)
  -}
  top.translation = error("Translation not done in renameTactic yet");
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

  top.translation = [abbrevCommand(hyps, newText)];
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

  top.translation = [unabbrevCommand(hyps)];
}


abstract production permuteTactic
top::ProofCommand ::= names::[String] hyp::Maybe<String>
{
  local hypString::String = case hyp of | just(h) -> " " ++ h | nothing() -> "" end;
  top.pp = "permute " ++ foldr1(\a::String b::String -> a ++ " " ++ b, names) ++ hypString ++ ".  ";

  top.translation = [permuteTactic(names, hyp)];
}


abstract production unfoldStepsTactic
top::ProofCommand ::= steps::Integer all::Boolean
{
  top.pp = "unfold " ++ toString(steps) ++ if all then "(all).  " else ".  ";

  top.translation = error("Translation not done in unfoldStepsTactic yet");
}


abstract production unfoldIdentifierTactic
top::ProofCommand ::= id::String all::Boolean
{
  top.pp = "unfold " ++ id ++ if all then "(all).  " else ".  ";

  top.translation = error("Translation not done in unfoldIdentifierTactic yet");
}


abstract production unfoldTactic
top::ProofCommand ::= all::Boolean
{
  top.pp = "unfold " ++ if all then "(all).  " else ".  ";

  top.translation = error("Translation not done in unfoldTactic yet");
}


abstract production proofNoOpCommand
top::ProofCommand ::= n::NoOpCommand
{
  top.pp = n.pp;

  top.translation = [proofNoOpCommand(n.translation)];

  top.isQuit = n.isQuit;
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

