grammar interface_:common;


{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state state of the theorem prover to move things into it if
  we have a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with state, debug;

synthesized attribute state::ProofState;
synthesized attribute debug::Boolean;

abstract production proverState
top::ProverState ::= state::ProofState debugMode::Boolean
{
  top.state = state;
  top.debug = debugMode;
}

