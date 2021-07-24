grammar interface_:common:abstractSyntax;


{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state of the theorem prover to move things into it if we have
  a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with
   state, debug, clean, knownTheorems,
   replaceState, replacedState<ProverState>;


synthesized attribute state::ProofState;
synthesized attribute debug::Boolean;
synthesized attribute clean::Boolean;

--Theorems we have proven and available
--Not all theorems are included, but anything with trees visible to user is
--Also, not everything in here is guaranteed to be available
synthesized attribute knownTheorems::[(String, Metaterm)];


--We often only want to replace the state and leave everything else
inherited attribute replaceState::ProofState;
synthesized attribute replacedState<a>::a;


abstract production proverState
top::ProverState ::=
   state::ProofState debugMode::Boolean cleanMode::Boolean thms::[(String, Metaterm)]
{
  top.state = state;
  top.debug = debugMode;
  top.clean = cleanMode;

  top.knownTheorems = thms;

  top.replacedState =
      proverState(top.replaceState, debugMode, cleanMode, thms);
}



--Build a prover state as you expect in the beginning
function defaultProverState
ProverState ::=
{
  return proverState(noProof(), false, true, []);
}

