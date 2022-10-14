grammar interface_:common:abstractSyntax;

{-
  The purpose of these productions is to disambiguate between the
  different application types (`f(a, b, c)` vs. `f a b c`) which we
  get from Silver and Abella.  The disambiguation is based on the
  lists of known functions and productions in the current state, as
  well as the forms of the applied term and the arguments.

  These break flow types for forwarding.  This is okay in our
  situation because, in our scheme, these cannot occur anywhere other
  than immediately after parsing in the context of the toAbella
  grammar.  It would be better if they didn't break it, but such is
  life.
-}


abstract production disambiguateEqMetaterm
top::Metaterm ::= leftSide::Term rightSide::Term
{
  top.pp = leftSide.pp ++ " = " ++ rightSide.pp;
  top.isAtomic = true;

  propagate silverContext;

  --function name, function arguments
  production leftFun::Maybe<(String, ParenthesizedArgs)> =
        case leftSide of
        --multiple arguments
        | applicationTerm(nameTerm(fun, _),
             singleTermList(pairTerm(contents)))
          when !null(findFun(fun, top.silverContext)) ->
          just((fun,
                foldr(addParenthesizedArgs(_, _),
                      emptyParenthesizedArgs(),
                      contents.argList)))
        --single argument
        | applicationTerm(nameTerm(fun, _),
             singleTermList(contents))
          when !null(findFun(fun, top.silverContext)) ->
          just((fun, addParenthesizedArgs(contents,
                        emptyParenthesizedArgs())))
        | _ -> nothing()
        end;
  production rightFun::Maybe<(String, ParenthesizedArgs)> =
        case rightSide of
        --multiple arguments
        | applicationTerm(nameTerm(fun, _),
             singleTermList(pairTerm(contents)))
          when !null(findFun(fun, top.silverContext)) ->
          just((fun,
                foldr(addParenthesizedArgs(_, _),
                      emptyParenthesizedArgs(),
                      contents.argList)))
        --single argument
        | applicationTerm(nameTerm(fun, _),
             singleTermList(contents))
          when !null(findFun(fun, top.silverContext)) ->
          just((fun, addParenthesizedArgs(contents,
                        emptyParenthesizedArgs())))
        | _ -> nothing()
        end;
  --praduction term
  local leftProd::Maybe<Term> =
        case leftSide of
        --multiple arguments
        | applicationTerm(nameTerm(prod, _),
             singleTermList(pairTerm(contents)))
          when !null(findProd(prod, top.silverContext)) ->
          just(prodTerm(prod,
                  foldr(addParenthesizedArgs(_, _),
                        emptyParenthesizedArgs(), contents.argList)))
        --single argument
        | applicationTerm(nameTerm(prod, _),
             singleTermList(contents))
          when !null(findProd(prod, top.silverContext)) ->
          just(prodTerm(prod,
                  addParenthesizedArgs(contents,
                     emptyParenthesizedArgs())))
        | _ -> nothing()
        end;
  local rightProd::Maybe<Term> =
        --multiple arguments
        case rightSide of
        | applicationTerm(nameTerm(prod, _),
             singleTermList(pairTerm(contents)))
          when !null(findProd(prod, top.silverContext)) ->
          just(prodTerm(prod,
                  foldr(addParenthesizedArgs(_, _),
                        emptyParenthesizedArgs(), contents.argList)))
        --single argument
        | applicationTerm(nameTerm(prod, _),
             singleTermList(contents))
          when !null(findProd(prod, top.silverContext)) ->
          just(prodTerm(prod,
                  addParenthesizedArgs(contents,
                     emptyParenthesizedArgs())))
        | _ -> nothing()
        end;
  --
  local fwd::Metaterm =
        case leftFun, rightFun, leftProd, rightProd of
        | just((fun, args)), _, _, _ ->
          funMetaterm(fun, args, rightSide, emptyRestriction())
        | _, just((fun, args)), _, _ ->
          funMetaterm(fun, args, leftSide, emptyRestriction())
        | _, _, just(l), just(r) ->
          eqMetaterm(l, r)
        | _, _, just(l), nothing() ->
          eqMetaterm(l, rightSide)
        | _, _, nothing(), just(r) ->
          eqMetaterm(leftSide, r)
        | nothing(), nothing(), nothing(), nothing() ->
          eqMetaterm(leftSide, rightSide)
        end;
  forwards to fwd;
}



abstract production disambiguateApplicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp = f.pp ++ " " ++ args.pp;
  top.isAtomic = false; --might get some extra parentheses

  propagate silverContext;

  local fwd::Term =
        case f, args of
        | nameTerm(prod, _),
          singleTermList(pairTerm(contents))
          when findAssociated(prod,
                  top.silverContext.knownProductions).isJust ->
          prodTerm(prod,
                   foldr(addParenthesizedArgs(_, _),
                         emptyParenthesizedArgs(),
                         args.argList))
        | nameTerm(prod, _), emptyTermList()
          when findAssociated(prod,
                  top.silverContext.knownProductions).isJust ->
          prodTerm(prod, emptyParenthesizedArgs())
        | _, _ -> applicationTerm(f, args)
        end;
  forwards to fwd;
}

