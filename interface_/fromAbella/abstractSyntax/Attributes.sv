grammar interface_:fromAbella:abstractSyntax;


imports interface_:common:abstractSyntax;


{-
  I don't think the system will ever need anything but the string, but
  making the translation structured allows us to take advantage of any
  pretty printing improvements and keeps us from having to go back if
  there is any reason we need to examine it somehow.
-}
synthesized attribute translation<a>::a;
flowtype translation {} on Metaterm;



--Whether a proof state is during a proof or not
synthesized attribute inProof::Boolean;


--The proof state of a full display
synthesized attribute proof::ProofState;

--Gathering hypotheses in the current proof
synthesized attribute hypList::[(String, Metaterm)];

--Whether an error occurred
synthesized attribute isError::Boolean;
--Whether a warning occurred
synthesized attribute isWarning::Boolean;

--Whether an open proof was ended (completed or aborted)
synthesized attribute proofEnded::Boolean;

