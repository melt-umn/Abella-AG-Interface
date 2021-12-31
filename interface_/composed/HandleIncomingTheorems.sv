grammar interface_:composed;


function handleIncomingThms
IOVal<(Integer, ProverState, String)> ::=
   incomingState::(Integer, ProverState)
   silverContext::Decorated SilverContext
   abella::ProcessHandle ioin::IO
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
  local translated::[TopCommand] =
        map(\ t::ThmElement ->
              decorate t.encode with {
                 silverContext = silverContext;
                 currentState = initialState;
              }.translation,
            doThms);
  local translatedString::String =
        implode(", ", map((.pp), translated));
  local numCommands::Integer =
        foldr(\ t::ThmElement rest::Integer ->
                decorate t.encode with {
                   silverContext = silverContext;
                   currentState = initialState;
                }.numCommandsSent + rest,
              0, doThms);
  --
  local send::IO =
        if numCommands > 0
        then sendToProcess(abella, translatedString, ioin)
        else ioin;
  local readBack::IOVal<String> =
        if numCommands > 0
        then read_abella_outputs(numCommands, abella, send)
        else ioval(send, "");
  --
  local outObligations::[ThmElement] =
        dropWhile((.is_nonextensible), obligations);
  local outThms::[(String, String, Metaterm)] =
        foldl(\ rest::[(String, String, Metaterm)] t::TopCommand ->
                case t of
                | theoremAndProof(name, _, stmt, _) ->
                  let split::(String, String) =
                      splitQualifiedName(encodedToColons(name))
                  in
                    (split.2, split.1, new(stmt))::rest
                  end
                | splitTheorem(toSplit, newNames) ->
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

