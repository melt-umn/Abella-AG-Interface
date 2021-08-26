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
--(short name, grammar name, statement)
synthesized attribute knownTheorems::[(String, String, Metaterm)];


--We often only want to replace the state and leave everything else
inherited attribute replaceState::ProofState;
synthesized attribute replacedState<a>::a;


abstract production proverState
top::ProverState ::=
   state::ProofState debugMode::Boolean cleanMode::Boolean
   thms::[(String, String, Metaterm)]
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
  --These are things currently defined directly in the encodings
  --We won't need this list when we can actually compile silver:core,
  --  or, for those which aren't exactly core-related, we can figure
  --  out another way to handle them.
  --The metaterms won't be needed, so we can just leave them out
  local knownThms::[(String, String, Metaterm)] =
        [
         --strings.thm
         ("is_string_append", "silver:core", trueMetaterm()),
         ("is_string_eq_or_not", "silver:core", trueMetaterm()),
         --bools.thm
         ("is_bool_eq_or_not", "silver:core", trueMetaterm()),
         ("and_bool_unique", "silver:core", trueMetaterm()),
         ("and_bool_total", "silver:core", trueMetaterm()),
         ("and_bool_is_bool", "silver:core", trueMetaterm()),
         ("and_bool_comm", "silver:core", trueMetaterm()),
         ("and_bool_true_left", "silver:core", trueMetaterm()),
         ("and_bool_true_left_eq", "silver:core", trueMetaterm()),
         ("and_bool_true_right", "silver:core", trueMetaterm()),
         ("and_bool_true_right_eq", "silver:core", trueMetaterm()),
         ("and_bool_false_left", "silver:core", trueMetaterm()),
         ("and_bool_false_right", "silver:core", trueMetaterm()),
         ("and_bool_associative", "silver:core", trueMetaterm()),
         ("and_bool_idempotent", "silver:core", trueMetaterm()),
         ("or_bool_unique", "silver:core", trueMetaterm()),
         ("or_bool_total", "silver:core", trueMetaterm()),
         ("or_bool_is_bool", "silver:core", trueMetaterm()),
         ("or_bool_comm", "silver:core", trueMetaterm()),
         ("or_bool_true_left", "silver:core", trueMetaterm()),
         ("or_bool_true_right", "silver:core", trueMetaterm()),
         ("or_bool_false_left", "silver:core", trueMetaterm()),
         ("or_bool_false_left_eq", "silver:core", trueMetaterm()),
         ("or_bool_false_right", "silver:core", trueMetaterm()),
         ("or_bool_false_right_eq", "silver:core", trueMetaterm()),
         ("or_bool_associative", "silver:core", trueMetaterm()),
         ("or_bool_idempotent", "silver:core", trueMetaterm()),
         ("not_bool_unique", "silver:core", trueMetaterm()),
         ("not_bool_total", "silver:core", trueMetaterm()),
         ("not_bool_is_bool", "silver:core", trueMetaterm()),
         ("not_bool_double_negation", "silver:core", trueMetaterm()),
         ("and_bool_complementation", "silver:core", trueMetaterm()),
         ("or_bool_complementation", "silver:core", trueMetaterm()),
         ("and_bool__distribute_over__or", "silver:core", trueMetaterm()),
         ("and_bool__undistribute_over__or", "silver:core", trueMetaterm()),
         ("or_bool__distribute_over__and", "silver:core", trueMetaterm()),
         ("or_bool__undistribute_over__and", "silver:core", trueMetaterm()),
         ("DeMorgan__not_bool__and_bool", "silver:core", trueMetaterm()),
         ("DeMorgan__or_bool__not_bool", "silver:core", trueMetaterm()),
         ("DeMorgan__not_bool__or_bool", "silver:core", trueMetaterm()),
         ("DeMorgan__and_bool__not_bool", "silver:core", trueMetaterm()),
         --integers.thm
         ("is_integer_eq_or_not", "silver:core", trueMetaterm()),
         --integer_addition.thm
         ("plus_integer_unique", "silver:core", trueMetaterm()),
         ("plus_integer_is_integer", "silver:core", trueMetaterm()),
         ("plus_integer_total", "silver:core", trueMetaterm()),
         ("plus_integer_comm", "silver:core", trueMetaterm()),
         ("plus_integer_assoc", "silver:core", trueMetaterm()),
         ("minus_integer_unique", "silver:core", trueMetaterm()),
         ("minus_integer_total", "silver:core", trueMetaterm()),
         ("minus_integer_is_integer", "silver:core", trueMetaterm()),
         ("minus_integer_same", "silver:core", trueMetaterm()),
         ("minus_integer_0", "silver:core", trueMetaterm()),
         ("negate_integer_unique", "silver:core", trueMetaterm()),
         ("negate_integer_total", "silver:core", trueMetaterm()),
         ("negate_integer_is_integer", "silver:core", trueMetaterm()),
         ("negate_integer_double", "silver:core", trueMetaterm()),
         ("plus_integer_0_result", "silver:core", trueMetaterm()),
         ("plus_integer_negatives", "silver:core", trueMetaterm()),
         --integer_multiplication.thm
         ("multiply_integer_unique", "silver:core", trueMetaterm()),
         ("multiply_integer_is_integer", "silver:core", trueMetaterm()),
         ("multiply_integer_total", "silver:core", trueMetaterm()),
         ("multiply_integer_0_right", "silver:core", trueMetaterm()),
         ("multiply_integer_1", "silver:core", trueMetaterm()),
         ("multiply_integer_1_right", "silver:core", trueMetaterm()),
         ("multiply_integer_0_result", "silver:core", trueMetaterm()),
         ("multiply_integer_-1_negate", "silver:core", trueMetaterm()),
         ("multiply_integer_negation", "silver:core", trueMetaterm()),
         ("multiply_integer_comm", "silver:core", trueMetaterm()),
         ("multiply_integer_distribute_over_plus", "silver:core", trueMetaterm()),
         ("multiply_integer_assoc", "silver:core", trueMetaterm()),
         ("multiply_integer_undistribute_over_plus", "silver:core", trueMetaterm()),
         --integer_comparison.thm
         ("less_integer_unique", "silver:core", trueMetaterm()),
         ("less_integer_total", "silver:core", trueMetaterm()),
         ("less_integer_is_bool", "silver:core", trueMetaterm()),
         ("lesseq_integer_unique", "silver:core", trueMetaterm()),
         ("lesseq_integer_total", "silver:core", trueMetaterm()),
         ("lesseq_integer_is_bool", "silver:core", trueMetaterm()),
         ("eq_to_lesseq_integer", "silver:core", trueMetaterm()),
         ("less_to_lesseq_integer", "silver:core", trueMetaterm()),
         ("greater_integer_unique", "silver:core", trueMetaterm()),
         ("greater_integer_total", "silver:core", trueMetaterm()),
         ("greater_integer_is_bool", "silver:core", trueMetaterm()),
         ("greatereq_integer_unique", "silver:core", trueMetaterm()),
         ("greatereq_integer_total", "silver:core", trueMetaterm()),
         ("greatereq_integer_is_bool", "silver:core", trueMetaterm()),
         ("eq_to_greatereq_integer", "silver:core", trueMetaterm()),
         ("greater_to_greatereq_integer", "silver:core", trueMetaterm()),
         --lists.thm
         ("append_nil_right", "silver:core", trueMetaterm()),
         ("append_nil_left", "silver:core", trueMetaterm()),
         ("append_unique", "silver:core", trueMetaterm()),
         ("head_unique", "silver:core", trueMetaterm()),
         ("tail_unique", "silver:core", trueMetaterm()),
         ("length_unique", "silver:core", trueMetaterm()),
         ("null_unique", "silver:core", trueMetaterm())
        ];
  return proverState(noProof(), false, true, knownThms);
}


--(full name, statement)
function findTheorem
[(String, Metaterm)] ::= name::String state::ProverState
{
  return
     if isFullyQualifiedName(name)
     then let splitName::(String, String) =
              splitQualifiedName(name)
          in
          let found::[(String, Metaterm)] =
              findAllAssociated(splitName.2, state.knownTheorems)
          in
            case findAssociated(splitName.1, found) of
            | nothing() -> []
            | just(stmt) -> [(name, stmt)]
            end
          end end
     else map(\ p::(String, Metaterm) -> (p.1 ++ ":" ++ name, p.2),
              findAllAssociated(name, state.knownTheorems));
}

