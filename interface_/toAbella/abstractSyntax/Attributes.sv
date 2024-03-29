grammar interface_:toAbella:abstractSyntax;


imports interface_:common:abstractSyntax;


{-
  How are we going to do translation?  We're going to build an actual
  structured tree, then use pp to get the text to send to Abella.
-}
synthesized attribute translation<a>::a;
flowtype translation {silverContext, boundVars, finalTys,
                      knownTrees, knownDecoratedTrees, knownNames,
                      knownTyParams} on Metaterm;

--new premises we are adding to the current theorem being defined
monoid attribute newPremises::[NewPremise] with [], ++;
propagate newPremises on
   Metaterm, Term, TermList, ListContents, PairContents, ParenthesizedArgs
   excluding bindingMetaterm, attrAccessMetaterm, attrAccessEmptyMetaterm;


monoid attribute errors::[Error] with [], ++;
propagate errors on
   Metaterm, Term, TermList, ListContents, PairContents, HHint, Clearable,
   ProofCommand, TopCommand, NoOpCommand, Type, EWitness, ParenthesizedArgs;

--Whether a command is something to be sent to Abella, or handled internally
synthesized attribute sendCommand::Boolean;

--Our own output, to show the user in the case we shouldn't send to Abella
synthesized attribute ownOutput::String;

--Number of commands sent
synthesized attribute numCommandsSent::Integer;


--Gather new theorems for the prover state
synthesized attribute newKnownTheorems::[(String, String, Metaterm)];

--New theorems to be proven now
synthesized attribute provingTheorems::[(String, String, Metaterm)];



--Translate names into full names with colons
functor attribute colonFullNames;
propagate colonFullNames on
   Metaterm, Term, ListContents, PairContents,
   ParenthesizedArgs, TermList
excluding bindingMetaterm, underscoreTerm, prodTerm,
   attrAccessMetaterm, attrAccessEmptyMetaterm, funMetaterm;



--State list before the command
inherited attribute stateListIn::[(Integer, ProverState)];
--State list after the command
synthesized attribute stateListOut::[(Integer, ProverState)];

--The new proof state read back from Abella
inherited attribute newProofState::ProofState;
--If Abella gave an error on the translation of this command
inherited attribute wasError::Boolean;

--If a command has an error we find before sending to Abella
synthesized attribute isError::Boolean;



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
--A final list of known types for variables
--This is mostly so we know the correct types of trees in structure equality
inherited attribute finalTys::[[(String, Maybe<Type>)]];


--(Name of tree, name of node, child list)
inherited attribute knownDecoratedTrees::[(String, String, Term)];

--Names used somewhere
inherited attribute knownNames::[String];


--Find the types of all the trees
monoid attribute treeTys::[(String, Type)];
propagate treeTys on
   Metaterm, ProofState, CurrentGoal, Context, Hypothesis
   excluding bindingMetaterm;


--The current prover state and the translation of the proof state
--We give both because it can be useful to have one or the other at different times
inherited attribute currentState::ProverState;
inherited attribute translatedState::ProofState;


--Replace a given name with a given term
inherited attribute replaceName::String;
inherited attribute replaceTerm::Term;
functor attribute replaced;
propagate replaced on Metaterm, Term, TermList, PairContents,
                      ListContents, ParenthesizedArgs
   excluding nameTerm, bindingMetaterm;


--Remove the WPD nonterminal relation for the given tree
inherited attribute removeWPDTree::String;
synthesized attribute removedWPD::Metaterm;


--Get all the premises of an implication
--e.g. A -> B -> C   gives   [A, B]
synthesized attribute implicationPremises::[Metaterm];

--Split a metaterm around conjunctions
synthesized attribute conjunctionSplit::[Metaterm];


--Whether we are currently in a proof or not
inherited attribute inProof::Boolean;



--Check for equality
inherited attribute eqTest<a>::a;
synthesized attribute isEq::Boolean;



--Check if a command is a command for quitting
synthesized attribute isQuit::Boolean;

--We let commands determine whether and what to undo
synthesized attribute isUndo::Boolean;

--Check whether we should try cleaning up after a command
--Might not want to if it is too confusing, nothing to clean, etc.
synthesized attribute shouldClean::Boolean;
--Check whether we *need* to clean, since we can turn cleaning off
--Need to clean after extensible theorems to assert them
synthesized attribute mustClean::Boolean;



--Name of a hypothesis given as an argument
synthesized attribute name::String;



--Find the immediate parent of a tree with a given name in a Term
--Gives both the production name and the (zero-based) index which child it is
--e.g. prod_foo (prod_bar A B) C   gives   ("prod_bar", 2)   when looking for B
inherited attribute findParentOf::String;
synthesized attribute foundParent::Maybe<(String, Integer)>;
synthesized attribute isArgHere::Maybe<Integer>;



--Search for the type of a variable by a particular name at the top level of a metaterm
inherited attribute findNameType::String;
--The type if the name was found at the top level, or a message about not found/no certain type
synthesized attribute foundNameType::Either<String Type>;



--These are just for handling extensible theorems
synthesized attribute translatedTheorems::[(String, Metaterm)];
synthesized attribute numRelevantProds::[(String, Integer)];



--A list of types from an arrow type, not including the result
--e.g. A -> B C D -> E F   would give   [A, B C D]
synthesized attribute argumentTypes::[Type];

--Ultimate head of a type---nothing() on arrows or underscores
--e.g.  f A B C   would give   f
synthesized attribute headTypeName::Maybe<String>;

--Ultimate result type of a type constructor being fully applied
--e.g. A -> B C D -> E F   would give   E F
synthesized attribute resultType::Type;

--Generate the is relation for a type or an error for why we can't
synthesized attribute isRelation::Either<String Term>;

--Replace short names with fully-qualified names in a type
synthesized attribute fullType::Type;

--Turn all names with encoded qualification into colon qualification
synthesized attribute colonType::Type;
--and vice versa
synthesized attribute encodedType::Type;


--Type parameters for determining correct type translation
inherited attribute knownTyParams::[String];






--Commands to clean up a proof state
--Point is to do the behind-the-scenes things not immediately part of
--   the command issued by the user
synthesized attribute cleanUpCommands::[String];
synthesized attribute numCleanUpCommands::Integer;
--Let state decide how to handle making the next state
inherited attribute nextStateIn::ProofState;
synthesized attribute nextStateOut::ProofState;


--Whether a term is built by a production at the root
synthesized attribute isProdStructure::Boolean;

