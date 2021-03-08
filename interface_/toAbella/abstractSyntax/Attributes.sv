grammar interface_:toAbella:abstractSyntax;


imports interface_:common;


{-
  How are we going to do translation?  We're going to build an actual
  structured tree, then use pp to get the text to send to Abella.
-}
synthesized attribute translation<a>::a;

--new premises we are adding to the current theorem being defined
monoid attribute newPremises::[NewPremise] with [], ++;
propagate newPremises on Metaterm, Term, TermList, ListContents
   excluding bindingMetaterm, attrAccessTerm;


monoid attribute errors::[Error] with [], ++;
propagate errors on Metaterm, Term, TermList, ListContents,
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
inherited attribute boundVars::[[Pair<String Maybe<[Type]>>]];
synthesized attribute boundVarsOut::[[Pair<String Maybe<[Type]>>]];


--Pairs of (attribute name, types it occurs on)
autocopy attribute attrOccurrences::[Pair<String [Type]>];


--The hypotheses in the current context (name and term)
inherited attribute hypList::[Pair<String Metaterm>];

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

