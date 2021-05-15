grammar abella_compilation;


synthesized attribute pp::String;

--This tells us whether something is essentially atomic for pretty printing purposes
synthesized attribute isAtomic::Boolean;

--The final type after all the arrows
synthesized attribute resultType::Type;

--Get the functor building a type, or just its name
synthesized attribute headTypeName::Maybe<String>;

--The types before the final arrow
synthesized attribute argumentTypes::[Type];

--The is relation for a given type
synthesized attribute isRelation::String;

