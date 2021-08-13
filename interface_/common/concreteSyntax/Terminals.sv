grammar interface_:common:concreteSyntax;


lexer class LOGIC   dominates Id_t;
lexer class TOKEN   dominates Id_t;
lexer class TACTIC  dominates Id_t;
lexer class COMMENT;


terminal Exists_t       'exists'       lexer classes {TACTIC, LOGIC};
terminal False_t        'false'        lexer classes {LOGIC};
terminal Forall_t       'forall'       lexer classes {LOGIC};
terminal Nabla_t        'nabla'        lexer classes {LOGIC};
terminal True_t         'true'         lexer classes {LOGIC};


terminal Colon_t       ':'       lexer classes {TOKEN};
terminal Comma_t       ','       lexer classes {TOKEN}, precedence=3;
terminal LParen_t      '('       lexer classes {TOKEN};
terminal RParen_t      ')'       lexer classes {TOKEN};
terminal Eq_t          '='       lexer classes {TOKEN};
terminal RightArrow_t  '->'      lexer classes {TOKEN}, precedence=4, association=right;
terminal At_t          '@'       lexer classes {TOKEN};
terminal Octothorpe_t  '#'       lexer classes {TOKEN};
terminal Or_t          '\/'      lexer classes {TOKEN}, precedence=5, association=left;
terminal And_t         '/\'      lexer classes {TOKEN}, precedence=6, association=left;
terminal LBracket_t    '['       lexer classes {TOKEN};
terminal RBracket_t    ']'       lexer classes {TOKEN};
terminal Underscore_t  '_'       lexer classes {TOKEN};
terminal Cons_t        '::'      lexer classes {TOKEN}, precedence=11, association=right;
terminal Nil_t         'nil'     lexer classes {TOKEN};
--These two have Abella uses with no precedence or associativity
--   and Silver uses with precedence and associativity (arithmetic)
terminal Plus_t        '+'       lexer classes {TOKEN}, precedence=9, association=left;
terminal Star_t        '*'       lexer classes {TOKEN}, precedence=10, association=left;


terminal Id_t  /[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;
terminal Number_t  /[0-9]+/;
--Qname_t is a qualified name as in Silver
--The grammar part is a Silver name, so it only needs Silver-allowed characters
terminal Qname_t  /([A-Za-z0-9_]+:)+[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;


--These are the things which we are adding to Abella for Silver
terminal AttrAccess_t  /[a-zA-Z][A-Za-z0-9\_]*\.([a-zA-Z][A-Za-z0-9\_]*:)*([a-zA-Z][A-Za-z0-9\_]*)/;
terminal SilverString_t  /"([^"]|(\\"))*"/;
terminal SilverNegativeInteger_t  /-[0-9]+/ dominates Id_t;

terminal Minus_t      '-'    lexer classes {TOKEN}, precedence=9, association=left;
terminal Divide_t     '/'    lexer classes {TOKEN}, precedence=10, association=left;
--We use 'mod' instead of '%' because of Abella comments
--Alternatively, we could change comments for the interface, but I'd
--   like to leave the syntax the same as much as possible.
terminal Modulus_t    'mod'  lexer classes {TOKEN}, precedence=10, association=left;
terminal Less_t       '<'    lexer classes {TOKEN}, precedence=7, association=left;
terminal LessEq_t     '<='   lexer classes {TOKEN}, precedence=7, association=left;
terminal Greater_t    '>'    lexer classes {TOKEN}, precedence=7, association=left;
terminal GreaterEq_t  '>='   lexer classes {TOKEN}, precedence=7, association=left;
terminal Append_t     '++'   lexer classes {TOKEN}, precedence=8, association=left;
terminal SilverOr_t   '||'   lexer classes {TOKEN}, precedence=3, association=left;
terminal SilverAnd_t  '&&'   lexer classes {TOKEN}, precedence=4, association=left;
terminal SilverNot_t  '!'    lexer classes {TOKEN}, precedence=5;
terminal Tiled_t      '~'    lexer classes {TOKEN};
--Attributes not having any value
terminal No_t         'no'      lexer classes {TOKEN};
terminal Value_t      'value'   lexer classes {TOKEN};


ignore terminal Whitespace_t /[\ \t\n\r]+/;
-- Allows (one level of) nested comments.  Based on Silver comments.
ignore terminal BlockComment_t /\/\*(\/\*([^\*]|\*+[^\/\*])*\*+\/|[^\*]|\*+[^\/\*])*\*+\// lexer classes {COMMENT};
ignore terminal OneLineComment_t /(%.*)/ lexer classes {COMMENT};

