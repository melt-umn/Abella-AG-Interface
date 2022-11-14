grammar interface_:composed;


function handleIncomingThms
IOVal<(Integer, ProverState, String)> ::=
   incomingState::(Integer, ProverState)
   silverContext::Decorated SilverContext
   abella::ProcessHandle ioin::IOToken
{
  local initialState::ProverState = incomingState.2;
  local knownThms::[(String, String, Metaterm)] =
        case initialState of
        | proverState(_, _, _, _, thms, _) -> thms
        end;
  local obligations::[ThmElement] =
        case initialState of
        | proverState(_, _, _, _, _, obligations) -> obligations
        end;
  --
  local doThms::[ThmElement] =
        takeWhile((.is_nonextensible), obligations);
  local translated::[AnyCommand] =
        flatMap(\ t::ThmElement ->
                  flatMap(\ x::AnyCommand ->
                            decorate x with {
                               silverContext = silverContext;
                               currentState = initialState;
                               translatedState = error("translatedState not actually needed");
                               stateListIn = error("stateListIn not actually needed");
                            }.translation,
                          t.encode),
                doThms);
  local translatedString::String =
        implode(", ", map((.pp), translated));
  local numCommands::Integer = length(translated);
  --
  local readBack::IOVal<String> =
        if numCommands > 0
        then sendCmdsToAbella(map((.pp), translated), abella, ioin)
        else ioval(ioin, "");
  --
  local outObligations::[ThmElement] =
        dropWhile((.is_nonextensible), obligations);
  local outThms::[(String, String, Metaterm)] =
        foldl(\ rest::[(String, String, Metaterm)] t::AnyCommand ->
                case t of
                | anyTopCommand(theoremDeclaration(name, _, stmt)) ->
                  let split::(String, String) =
                      splitQualifiedName(encodedToColons(name))
                  in
                    (split.2, split.1, new(stmt))::rest
                  end
                | anyTopCommand(splitTheorem(toSplit, newNames)) ->
                  let split::(String, String) =
                      splitQualifiedName(encodedToColons(toSplit))
                  in
                  let stmt::Metaterm = findThm(split.2, split.1, rest)
                  in
                  let splitThm::[Metaterm] =
                      decorate stmt with {
                         silverContext = silverContext;
                      }.conjunctionSplit
                  in
                    zipWith(\ s::String m::Metaterm ->
                              let split::(String, String) =
                                  splitQualifiedName(encodedToColons(s))
                              in
                                (split.2, split.1, m)
                              end,
                            newNames, splitThm) ++ rest
                  end end end
                | anyProofCommand(_) -> rest
                | _ -> error("Should not have anything else")
                end,
              initialState.knownTheorems, translated);
  --
  return
     ioval(
        readBack.io,
        ( numCommands + incomingState.1,
          case initialState of
          | proverState(a, b, c, d, _, _) ->
            proverState(a, b, c, d, outThms, outObligations)
          end,
          translatedString ));
}


function findThm
Metaterm ::= name::String grmmr::String
             thms::[(String, String, Metaterm)]
{
  local findShort::[(String, Metaterm)] =
        findAllAssociated(name, thms);
  return
     case findAssociated(grmmr, findShort) of
     | just(m) -> m
     | nothing() ->
       error("Did not find theorem " ++ name ++ " from " ++ grmmr)
     end;
}

