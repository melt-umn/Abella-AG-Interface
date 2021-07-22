grammar interface_:common:abstractSyntax;


synthesized attribute pp::String;

--This tells us whether something is essentially atomic for pretty printing purposes
synthesized attribute isAtomic::Boolean;


--The arguments in a TermList, but in an actual list
synthesized attribute argList::[Term];


--Whether a premise should be hidden
--We include this here because we need it in both toAbella and fromAbella
synthesized attribute shouldHide::Boolean;


--The goal we are currently trying to prove, if there is one
synthesized attribute goal::Maybe<Metaterm>;


--Names of trees used in a proof state
monoid attribute gatheredTrees::[String] with [], ++;
propagate gatheredTrees on
   Metaterm, Term, ProofState, Context, Hypothesis, CurrentGoal
   excluding bindingMetaterm, applicationTerm;
--Names which are known to be trees of any type
autocopy attribute knownTrees::[String];


--(Name of tree, name of node, child list)
monoid attribute gatheredDecoratedTrees::[(String, String, Term)] with [], ++;
propagate gatheredDecoratedTrees on
   Metaterm, Term, ProofState, Context, Hypothesis, CurrentGoal
   excluding bindingMetaterm, applicationTerm;



--Names which occur anywhere in a term or metaterm, including uses and bindings
--(May include unbound names or names which are bound but used nowhere)
monoid attribute usedNames::[String] with [], ++;
propagate usedNames on
   Metaterm, Term, TermList, ParenthesizedArgs, ListContents, PairContents,
      Hypothesis, Context, CurrentGoal, ProofState
   excluding bindingMetaterm, nameTerm, attrAccessMetaterm, attrAccessEmptyMetaterm, localAttrAccessMetaterm, localAttrAccessEmptyMetaterm;



--
inherited attribute currentState::ProverState occurs on Metaterm, Term;

