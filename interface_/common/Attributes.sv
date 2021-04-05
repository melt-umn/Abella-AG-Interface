grammar interface_:common;


synthesized attribute pp::String;

--This tells us whether something is essentially atomic for pretty printing purposes
synthesized attribute isAtomic::Boolean;


--Whether a premise should be hidden
--We include this here because we need it in both toAbella and fromAbella
synthesized attribute shouldHide::Boolean;


--The goal we are currently trying to prove, if there is one
synthesized attribute goal::Maybe<Metaterm>;

