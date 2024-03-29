grammar interface_:toAbella:abstractSyntax;

import interface_:thmInterfaceFile:abstractSyntax;

{-
  We store the pieces of the state of the theorem prover with this
  nonterminal.  It makes it a bit easier to handle changing the form
  of the state of the theorem prover to move things into it if we have
  a nonterminal than if we were to use a tuple.
-}

nonterminal ProverState with
   state, provingThms, debug, clean, knownTheorems, remainingObligations,
   replaceState, replacedState<ProverState>;


synthesized attribute state::ProofState;
synthesized attribute provingThms::[(String, String, Metaterm)];
synthesized attribute debug::Boolean;
synthesized attribute clean::Boolean;

--Theorems we have proven and available
--(short name, grammar name, statement)
synthesized attribute knownTheorems::[(String, String, Metaterm)];

--
synthesized attribute remainingObligations::[ThmElement];


abstract production proverState
top::ProverState ::=
   state::ProofState provingThms::[(String, String, Metaterm)]
   debugMode::Boolean cleanMode::Boolean
   thms::[(String, String, Metaterm)]
   obligations::[ThmElement]
{
  top.state = state;
  top.provingThms = provingThms;
  top.debug = debugMode;
  top.clean = cleanMode;

  top.knownTheorems = thms;

  top.remainingObligations = obligations;

  --Determine whether we need to remove an extensible mutual group
  --   from the beginning because we just proved it
  local newObligations::[ThmElement] =
        case obligations of
        | extensibleMutualTheoremGroup(thms)::rest ->
          if map(\ p::(String, String, Metaterm) -> p.2 ++ ":" ++ p.1,
                 provingThms) ==
             map(fst, thms)
          then rest
          else obligations
        | _ -> obligations
        end;
  top.replacedState =
      case top.replaceState of
      | proofCompleted() ->
        proverState(top.replaceState, [], debugMode, cleanMode,
                    provingThms ++ thms, newObligations)
      | proofAborted() ->
        proverState(top.replaceState, [], debugMode, cleanMode, thms,
                    obligations)
      | _ ->
        proverState(top.replaceState, provingThms, debugMode,
                    cleanMode, thms, obligations)
      end;
}



--Build a prover state as you expect in the beginning
function defaultProverState
ProverState ::= obligations::[ThmElement]
{
  --These are things currently defined directly in the encodings
  --We won't need this list when we can actually compile silver:core,
  --  or, for those which aren't exactly core-related, we can figure
  --  out another way to handle them.
  --The metaterms won't be needed, so we can just leave them out
  local knownThms1::[(String, String, Metaterm)] =
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
         ("and_bool" ++ name_sep ++ "distribute_over" ++ name_sep ++ "or", "silver:core", trueMetaterm()),
         ("and_bool" ++ name_sep ++ "undistribute_over" ++ name_sep ++ "or", "silver:core", trueMetaterm()),
         ("or_bool" ++ name_sep ++ "distribute_over" ++ name_sep ++ "and", "silver:core", trueMetaterm()),
         ("or_bool" ++ name_sep ++ "undistribute_over" ++ name_sep ++ "and", "silver:core", trueMetaterm()),
         ("DeMorgan" ++ name_sep ++ "not_bool" ++ name_sep ++ "and_bool", "silver:core", trueMetaterm()),
         ("DeMorgan" ++ name_sep ++ "or_bool" ++ name_sep ++ "not_bool", "silver:core", trueMetaterm()),
         ("DeMorgan" ++ name_sep ++ "not_bool" ++ name_sep ++ "or_bool", "silver:core", trueMetaterm()),
         ("DeMorgan" ++ name_sep ++ "and_bool" ++ name_sep ++ "not_bool", "silver:core", trueMetaterm())
        ];
  local knownThms2::[(String, String, Metaterm)] =
        [
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
  production attribute knownThms::[(String, String, Metaterm)] with ++;
  knownThms := knownThms1 ++ knownThms2;
  --Prop-quantified theorems handled by asserting for the particular
  --   case, then applying
  knownThms <-
     [
      ("is_list_member", "silver:core", trueMetaterm()),
      ("is_list_append", "silver:core", trueMetaterm()),
      ("symmetry", "silver:core", trueMetaterm()),
      ("attr_unique", "silver:core", trueMetaterm()),
      ("attr_is", "silver:core", trueMetaterm())
     ];
  return proverState(noProof(), [], false, true, knownThms,
                     obligations);
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

