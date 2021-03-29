grammar interface_:toAbella:abstractSyntax;


imports interface_:common;


{-
  How are we going to do translation?  We're going to build an actual
  structured tree, then use pp to get the text to send to Abella.
-}
synthesized attribute translation<a>::a;
flowtype translation {attrOccurrences, boundVars} on Metaterm;

--new premises we are adding to the current theorem being defined
monoid attribute newPremises::[NewPremise] with [], ++;
propagate newPremises on
   Metaterm, Term, TermList, ListContents, PairContents
   excluding bindingMetaterm, attrAccessMetaterm, attrAccessEmptyMetaterm;


monoid attribute errors::[Error] with [], ++;
propagate errors on
   Metaterm, Term, TermList, ListContents, PairContents,
   ProofCommand, TopCommand, NoOpCommand;

--Whether a command is something to be sent to Abella, or handled internally
synthesized attribute sendCommand::Boolean;

--Our own output, to show the user in the case we shouldn't send to Abella
synthesized attribute ownOutput::String;

--Number of commands sent, or nothing() if it is the import problem
synthesized attribute numCommandsSent::Maybe<Integer>;



--State list before the command
inherited attribute stateListIn::[(Integer, ProverState)];
--State list after the command
synthesized attribute stateListOut::[(Integer, ProverState)];

--The new proof state read back from Abella
inherited attribute newProofState::ProofState;
--If Abella gave an error on the translation of this command
inherited attribute wasError::Boolean;



{-
  To determine what access relation to use for an attribute on a
  particular tree, we need to know what the type of the tree is.  We
  can determine this by passing down the variables we have type
  information for and their possible types.  Everything in the list
  for a name is a possible type.  A name with nothing() has no
  information about the type of the variable, and thus its type may be
  anything.

  We do the bound variables by scopes so we can get rid of new
  bindings that might override others.  For example, in the
  nonsensical theorem
     forall a, a = 3 -> (forall a, a > 2 -> a > 1) -> a > 1
  the inner a is separate from the outer a, and we don't want to mix
  such bindings up if they are truly separate.
-}
inherited attribute boundVars::[[(String, Maybe<[Type]>)]];
synthesized attribute boundVarsOut::[[(String, Maybe<[Type]>)]];


--Pairs of (attribute name, types it occurs on)
autocopy attribute attrOccurrences::[(String, [Type])];
--Tuples of (WPD relation name, nonterminal type it is for, productions in order)
autocopy attribute wpdRelations::[(String, Type, [String])];

--The current prover state and the translation of the proof state
--We give both because it can be useful to have one or the other at different times
autocopy attribute currentState::ProverState;
autocopy attribute translatedState::ProofState;


--Replace a given name with a given term
autocopy attribute replaceName::String;
autocopy attribute replaceTerm::Term;
functor attribute replaced;
propagate replaced on Metaterm, Term, TermList, PairContents, ListContents
   excluding nameTerm, bindingMetaterm;


--Remove the WPD nonterminal relation for the given tree
autocopy attribute removeWPDTree::String;
synthesized attribute removedWPD::Metaterm;


--Whether we are currently in a proof or not
inherited attribute inProof::Boolean;



--Check for equality
inherited attribute eqTest<a>::a;
synthesized attribute isEq::Boolean;



--Check if a command is a command for quitting
synthesized attribute isQuit::Boolean;

--We let commands determine whether and what to undo
synthesized attribute isUndo::Boolean;



--Name of a hypothesis given as an argument
synthesized attribute name::String;



--Names which occur anywhere in a term or metaterm, including uses and bindings
--(May include unbound names or names which are bound but used nowhere)
synthesized attribute usedNames::[String];



--Find the immediate parent of a tree with a given name in a Term
--Gives both the production name and the index which child it is
--e.g. prod_foo (prod_bar A B) C   gives   ("prod_bar, 2)   when looking for B
inherited attribute findParentOf::String;
synthesized attribute foundParent::Maybe<(String, Integer)>;
synthesized attribute isArgHere::Maybe<Integer>;



--Search for the type of a variable by a particular name at the top level of a metaterm
inherited attribute findNameType::String;
--The type if the name was found at the top level, or a message about not found/no certain type
synthesized attribute foundNameType::Either<String Type>;



--These are just for handling extensible theorems
synthesized attribute translatedTheorem::Metaterm;
synthesized attribute numRelevantProds::Integer;



--A list of types from an arrow type, not including the result
--e.g. A -> B C D -> E F   would give   [A, B C D]
synthesized attribute argumentTypes::[Type];

--Ultimate head of a type---nothing() on arrows or underscores
--e.g.  f A B C   would give   f
synthesized attribute headTypeName::Maybe<String>;

