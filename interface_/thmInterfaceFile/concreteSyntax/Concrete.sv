grammar interface_:thmInterfaceFile:concreteSyntax;


--(current grammar, imports, defined relations, theorems)
closed nonterminal Interface_c
   layout {Whitespace_t, BlockComment_t, OneLineComment_t}
   with ast<(String, [String], [DefElement], [ParsedElement])>;


concrete productions top::Interface_c
| g::Qname_colon_t '.' imps::Imports_c '.' defs::Definitions_c
     info::InterfaceContents_c
  { top.ast = (toString(g.lexeme), imps.ast, defs.ast, info.ast); }



closed nonterminal Imports_c with ast<[String]>;
closed nonterminal Imports_List_c with ast<[String]>;

concrete productions top::Imports_c
|
  { top.ast = []; }
| lst::Imports_List_c
  { top.ast = lst.ast; }


concrete productions top::Imports_List_c
| g::Qname_colon_t
  { top.ast = [toString(g.lexeme)]; }
| g::Qname_colon_t ',' rest::Imports_List_c
  { top.ast = toString(g.lexeme)::rest.ast; }



closed nonterminal Definitions_c with ast<[DefElement]>;
closed nonterminal Definitions_List_c with ast<[DefElement]>;
closed nonterminal RelNames_c with ast<[(String, Type)]>;
closed nonterminal Clauses_c with ast<[(Metaterm, Maybe<Metaterm>)]>;

concrete productions top::Definitions_c
| 
  { top.ast = []; }
| '$Def' lst::Definitions_List_c
  { top.ast = lst.ast; }


concrete productions top::Definitions_List_c
| rels::RelNames_c '&' clauses::Clauses_c '.'
  { top.ast = [defineElement(rels.ast, clauses.ast)]; }
| rels::RelNames_c '&' clauses::Clauses_c '.' '$Def' rest::Definitions_List_c
  { top.ast = defineElement(rels.ast, clauses.ast)::rest.ast; }


concrete productions top::RelNames_c
| name::Qname_colon_t ':' ty::Ty_c
  { top.ast = [(name.lexeme, ty.ast)]; }
| name::Qname_colon_t ':' ty::Ty_c ',' rest::RelNames_c
  { top.ast = (name.lexeme, ty.ast)::rest.ast; }


concrete productions top::Clauses_c
| hd::Metaterm_c ',' body::Metaterm_c
  { top.ast = [(hd.ast, just(body.ast))]; }
| hd::Metaterm_c
  { top.ast = [(hd.ast, nothing())]; }
| hd::Metaterm_c ',' body::Metaterm_c ';' rest::Clauses_c
  { top.ast = (hd.ast, just(body.ast))::rest.ast; }
| hd::Metaterm_c ';' rest::Clauses_c
  { top.ast = (hd.ast, nothing())::rest.ast; }



closed nonterminal InterfaceContents_c with ast<[ParsedElement]>;
closed nonterminal InterfaceContents_List_c with ast<[ParsedElement]>;
closed nonterminal InterfaceElement_c with ast<ParsedElement>;

concrete productions top::InterfaceContents_c
|
  { top.ast = []; }
| lst::InterfaceContents_List_c
  { top.ast = lst.ast; }


concrete productions top::InterfaceContents_List_c
| elem::InterfaceElement_c '.'
  { top.ast = [elem.ast]; }
| elem::InterfaceElement_c '.' rest::InterfaceContents_List_c
  { top.ast = elem.ast::rest.ast; }


concrete productions top::InterfaceElement_c
--Extensible Theorems
| thms::ExtensibleTheorems_c
  { top.ast = extensibleMutualTheoremGroup(thms.ast); }
--Non-Extensible Theorem
| name::Qname_colon_t '&' stmt::Metaterm_c
  { top.ast = nonextensibleTheorem(name.lexeme, stmt.ast); }
--Split
| '$Spl' toSplit::Qname_colon_t names::NameList_c
  { top.ast = splitElement(toSplit.lexeme, names.ast); }



closed nonterminal ExtensibleTheorems_c with ast<[(String, Metaterm, String)]>;

concrete productions top::ExtensibleTheorems_c
| name::Qname_colon_t '&' stmt::Metaterm_c '&' tree::Id_t
  { top.ast = [(name.lexeme, stmt.ast, tree.lexeme)]; }
| name::Qname_colon_t '&' stmt::Metaterm_c '&' tree::Id_t ','
     rest::ExtensibleTheorems_c
  { top.ast = (name.lexeme, stmt.ast, tree.lexeme)::rest.ast; }



closed nonterminal NameList_c with ast<[String]>;

concrete productions top::NameList_c
| name::Id_t
  { top.ast = [name.lexeme]; }
| name::Id_t ',' rest::NameList_c
  { top.ast = name.lexeme::rest.ast; }





concrete productions top::Exp_c
--This doesn't work with fromAbella, so we need to add it here
| i::Number_t
  { top.ast = intTerm(toInteger(i.lexeme)); }

