grammar interface_:common;


{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state of the theorem prover to move things into it if we have
  a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with
   state, debug, clean,
   knownAttrs, knownAttrOccurrences, knownProductions,
   knownWPDRelations, knownInheritedAttrs, knownTheorems,
   replaceState, replacedState<ProverState>;


synthesized attribute state::ProofState;
synthesized attribute debug::Boolean;
synthesized attribute clean::Boolean;

synthesized attribute knownAttrs::[(String, Type)];
synthesized attribute knownAttrOccurrences::[(String, [Type])];
--any attr not in this list (and which is known) is synthesized
synthesized attribute knownInheritedAttrs::[String];

synthesized attribute knownProductions::[(String, Type)];

--The type here is just the nonterminal type---we can deduce the rest
--   of the WPD nonterminal relation's type from that.
--The [String] is the names of the productions in order---we can
--   deduce everything else we need from that, but the right order is
--   going to be helpful in composition.
synthesized attribute knownWPDRelations::[(String, Type, [String])];

--Theorems we have proven and available
--Not all theorems are included, but anything with trees visible to user is
--Also, not everything in here is guaranteed to be available
synthesized attribute knownTheorems::[(String, Metaterm)];


--We often only want to replace the state and leave everything else
inherited attribute replaceState::ProofState;
synthesized attribute replacedState<a>::a;


abstract production proverState
top::ProverState ::=
   state::ProofState debugMode::Boolean attrs::[(String, Type)]
   attrOccurrences::[(String, [Type])] prods::[(String, Type)]
   wpdRelations::[(String, Type, [String])]
   inheritedAttrs::[String] cleanMode::Boolean
   knownTheorems::[(String, Metaterm)]
{
  top.state = state;
  top.debug = debugMode;
  top.clean = cleanMode;
  top.knownAttrs = attrs;
  top.knownAttrOccurrences = attrOccurrences;
  top.knownProductions = prods;
  top.knownWPDRelations = wpdRelations;
  top.knownInheritedAttrs = inheritedAttrs;
  top.knownTheorems = knownTheorems;

  top.replacedState =
      proverState(top.replaceState, debugMode, attrs,
                  attrOccurrences, prods, wpdRelations,
                  inheritedAttrs, cleanMode, knownTheorems);
}

