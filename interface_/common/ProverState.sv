grammar interface_:common;


{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state state of the theorem prover to move things into it if
  we have a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with
   state, debug, knownAttrs, knownAttrOccurrences, knownProductions;

synthesized attribute state::ProofState;
synthesized attribute debug::Boolean;
synthesized attribute knownAttrs::[(String, Type)];
synthesized attribute knownAttrOccurrences::[(String, [Type])];
synthesized attribute knownProductions::[(String, Type)];

abstract production proverState
top::ProverState ::=
   state::ProofState debugMode::Boolean attrs::[(String, Type)]
   attrOccurrences::[(String, [Type])] prods::[(String, Type)]
{
  top.state = state;
  top.debug = debugMode;
  top.knownAttrs = attrs;
  top.knownAttrOccurrences = attrOccurrences;
  top.knownProductions = prods;
}

