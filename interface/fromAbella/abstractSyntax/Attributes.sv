grammar fromAbella:abstractSyntax;


synthesized attribute pp::String;

--This tells us whether something is essentially atomic for pretty printing purposes
synthesized attribute isAtomic::Boolean;



{-
  I don't think the system will ever need anything but the string, but
  making the translation structured allows us to take advantage of any
  pretty printing improvements and keeps us from having to go back if
  there is any reason we need to examine it somehow.
-}
synthesized attribute translation<a>::a;

--Whether a hypothesis should be hidden from the user (determined from the metaterm)
synthesized attribute shouldHide::Boolean;



--Whether a proof state is during a proof or not
synthesized attribute inProof::Boolean;


--The proof state of a full display
synthesized attribute proof::ProofState;

--Whether an error occurred
synthesized attribute isError::Boolean;
--Whether a warning occurred
synthesized attribute isWarning::Boolean;

