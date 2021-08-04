grammar interface_:toAbella:abstractSyntax;


function tysEqual
Boolean ::= ty1::Type ty2::Type
{
  ty1.eqTest = ty2;
  ty2.eqTest = ty1;
  return ty1.isEq && ty2.isEq;
}

function termsEqual
Boolean ::= tm1::Term tm2::Term silverContext::Decorated SilverContext
{
  tm1.eqTest = tm2;
  tm1.silverContext = silverContext;
  tm2.eqTest = tm1;
  tm2.silverContext = silverContext;
  return tm1.isEq && tm2.isEq;
}



--Check whether a type is nominally a nonterminal
--Does not check if that nonterminal type exists
function tyIsNonterminal
Boolean ::= ty::Type
{
  return
     case ty of
     | nameType(s) -> startsWith("nt_", s)
     | _ -> false
     end;
}




--This isn't included in Silver's library for some reason
function capitalizeString
String ::= s::String
{
  return
     if s == ""
     then ""
     else case substring(0, 1, s) of
          | "a" -> "A" | "b" -> "B" | "c" -> "C" | "d" -> "D" | "e" -> "E"
          | "f" -> "F" | "g" -> "G" | "h" -> "H" | "i" -> "I" | "j" -> "J"
          | "k" -> "K" | "l" -> "L" | "m" -> "M" | "n" -> "N" | "o" -> "O"
          | "p" -> "P" | "q" -> "Q" | "r" -> "R" | "s" -> "S" | "t" -> "T"
          | "u" -> "U" | "v" -> "V" | "w" -> "W" | "x" -> "X" | "y" -> "Y"
          | "z" -> "Z" |  _  -> substring(0, 1, s)
          end ++ substring(1, length(s), s);
}




function buildApplication
Term ::= fun::Term args::[Term]
{
  --I'll make this handle degenerate "applications" as well
  return if null(args)
         then fun
         else applicationTerm(fun, buildApplicationArgs(args));
}

function buildApplicationArgs
TermList ::= args::[Term]
{
  return
     case args of
     | [] ->
       error("Should not call buildApplicationArgs with an empty list")
     | [x] -> singleTermList(x)
     | h::t -> consTermList(h, buildApplicationArgs(t))
     end;
}


--Split based on actual conjunctions
--Different than attribute
function splitMetaterm
[Metaterm] ::= mt::Metaterm silverContext::Decorated SilverContext
{
  mt.silverContext = silverContext;
  return
     case mt of
     | andMetaterm(mt1, mt2) ->
       splitMetaterm(mt1, silverContext) ++
       splitMetaterm(mt2, silverContext)
     | _ -> [mt]
     end;
}




--Find the local attributes which occur on a given (fully-qualified) production
function findProdLocalAttrs
[(String, Type)] ::= prod::String localAttrs::[(String, [(String, String, Type)])]
{
  local splitName::(String, String) = splitQualifiedName(prod);
  return findProdLocalAttrs_help(splitName.2, splitName.1, localAttrs);
}
function findProdLocalAttrs_help
[(String, Type)] ::= prodName::String prodGrammar::String
                     localAttrs::[(String, [(String, String, Type)])]
{
  return
     case localAttrs of
     | [] -> []
     | (attrName, lst)::tl ->
       case findAssociated(prodGrammar,
               findAllAssociated(prodName, lst)) of
       | nothing() -> []
       | just(ty) -> [(attrName, ty)]
       end ++ findProdLocalAttrs_help(prodName, prodGrammar, tl)
     end;
}




--Find all the WPD relations for a given type
function findWPDRelations
[(String, Type, [String])] ::= ty::Type relations::[(String, Type, [String])]
{
  return
     case relations of
     | [] -> []
     | (rel, type, prods)::tl ->
       if tysEqual(ty, type)
       then (rel, type, prods)::findWPDRelations(ty, tl)
       else findWPDRelations(ty, tl)
     end;
}




--Find the metaterm which is the body of a hypothesis
function get_arg_hyp_metaterm
Maybe<Metaterm> ::= arg::ApplyArg hyps::[(String, Metaterm)]
{
  return
     case arg of
     | hypApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     | starApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     end;
}




--Find the WPD nonterminal relation for a given treename, if it exists
function find_WPD_nt_hyp
Maybe<(String, Metaterm)> ::= treename::String hyps::[(String, Metaterm)]
                              silverContext::Decorated SilverContext
{
  local structure::Term =
        case find_structure_hyp(treename, hyps, silverContext) of
        | just((_, s)) -> s
        | nothing() -> nameTerm(treename, nothing())
        end;
  return find_WPD_nt_help(structure, treename, hyps, silverContext);
}


function find_WPD_nt_help
Maybe<(String, Metaterm)> ::= tree::Term treename::String hyps::[(String, Metaterm)]
                              silverContext::Decorated SilverContext
{
  return
     case hyps of
     | [] -> nothing()
     | (hyp, mt)::tl ->
       case decorate mt with {silverContext = silverContext;} of
         --(hyp, wpd_<ty> tr (ntr_<ty> treeNode childList))
       | termMetaterm(applicationTerm(nameTerm(str, x),
            consTermList(tr,
            singleTermList(
               applicationTerm(nameTerm(ntr, ntrty),
                  consTermList(
                     nameTerm(treeNode, treeNodeTy),
                  singleTermList(childList)))))),
            _)
         when isWpdTypeName(str) && termsEqual(tree, tr, silverContext) ->
         just((hyp,
            termMetaterm(applicationTerm(nameTerm(str, x),
                  consTermList(tr,
                  singleTermList(
                     applicationTerm(nameTerm(ntr, ntrty),
                        consTermList(
                           nameTerm(treeNode, treeNodeTy),
                        singleTermList(childList)))))),
                  emptyRestriction())))
         --(hyp, wpd_<ty> tr (ntr_<ty> treeNode childList)) where tr is a tree name
       | termMetaterm(applicationTerm(nameTerm(str, x),
            consTermList(nameTerm(tr, trty),
            singleTermList(
               applicationTerm(nameTerm(ntr, ntrty),
                  consTermList(
                     nameTerm(treeNode, treeNodeTy),
                  singleTermList(childList)))))),
            _)
         when isWpdTypeName(str) && tr == treename ->
         just((hyp,
            termMetaterm(applicationTerm(nameTerm(str, x),
                  consTermList(nameTerm(tr, trty),
                  singleTermList(
                     applicationTerm(nameTerm(ntr, ntrty),
                        consTermList(
                           nameTerm(treeNode, treeNodeTy),
                        singleTermList(childList)))))),
                  emptyRestriction())))
       | _ -> find_WPD_nt_help(tree, treename, tl, silverContext)
       end
     end;
}


--find a hypthesis of the form "<treename> = ___" or "___ = <treename>"
function find_structure_hyp
Maybe<(String, Term)> ::= treename::String hyps::[(String, Metaterm)]
                          silverContext::Decorated SilverContext
{
  return
     case hyps of
     | [] -> nothing()
     | (hyp, mt)::tl ->
       case decorate mt with {silverContext = silverContext;} of
       | treeEqMetaterm(nameTerm(str, _), structure)
         when str == treename &&
              decorate structure with
              {silverContext = silverContext;}.isProdStructure ->
         just((hyp, new(structure)))
       | treeEqMetaterm(structure, nameTerm(str, _))
         when str == treename &&
              decorate structure with
              {silverContext = silverContext;}.isProdStructure ->
         just((hyp, new(structure)))
       | _ -> find_structure_hyp(treename, tl, silverContext)
       end
     end;
}


--Find the tree which is the immediate parent of the given tree and the term it is in
function find_parent_tree
Maybe<(String, Term)> ::= treename::String hyps::[(String, Metaterm)]
                          silverContext::Decorated SilverContext
{
  return
     case hyps of
     | [] -> nothing()
     | (hyp, mt)::tl ->
       case decorate mt with {silverContext = silverContext;} of
       | treeEqMetaterm(nameTerm(prod, _), applicationTerm(f, args))
         when decorate args with {findParentOf = treename;
                                  silverContext = silverContext;}.isArgHere.isJust ->
         just((prod, applicationTerm(f, args)))
       | treeEqMetaterm(applicationTerm(f, args), nameTerm(prod, _))
         when decorate args with {findParentOf = treename;
                                  silverContext = silverContext;}.isArgHere.isJust ->
         just((prod, applicationTerm(f, args)))
       | treeEqMetaterm(nameTerm(tree, _), prodTerm(prodName, args))
         when decorate args with {findParentOf = treename;
                                  silverContext = silverContext;}.isArgHere.isJust ->
         just((tree, prodTerm(prodName, args)))
       | treeEqMetaterm(prodTerm(prodName, args), nameTerm(tree, _))
         when decorate args with {findParentOf = treename;
                                  silverContext = silverContext;}.isArgHere.isJust ->
         just((tree, prodTerm(prodName, args)))
       | _ -> find_parent_tree(treename, tl, silverContext)
       end
     end;
}

