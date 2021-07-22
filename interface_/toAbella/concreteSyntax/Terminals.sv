grammar interface_:toAbella:concreteSyntax;


imports interface_:toAbella:abstractSyntax;
imports interface_:common;


lexer class COMMAND dominates Id_t;
lexer class TACTIC  dominates Id_t;
lexer class LOGIC   dominates Id_t;
lexer class TOKEN   dominates Id_t;
lexer class COMMENT;


terminal Grammar_t        'Grammar'        lexer classes {COMMAND};
terminal Close_t          'Close'          lexer classes {COMMAND};
terminal CoDefine_t       'CoDefine'       lexer classes {COMMAND};
terminal Define_t         'Define'         lexer classes {COMMAND};
terminal KKind_t          'Kind'           lexer classes {COMMAND};
terminal Query_t          'Query'          lexer classes {COMMAND};
terminal Quit_t           'Quit'           lexer classes {COMMAND};
terminal Set_t            'Set'            lexer classes {COMMAND};
terminal Show_t           'Show'           lexer classes {COMMAND};
terminal SSplit_t         'Split'          lexer classes {COMMAND};
terminal Theorem_t        'Theorem'        lexer classes {COMMAND};
terminal TType_t          'Type'           lexer classes {COMMAND};
--New for Silver theorems
terminal ExtTheorem_t   'Extensible_Theorem'   lexer classes {COMMAND};
terminal Prove_t        'Prove'                lexer classes {COMMAND};


terminal Abbrev_t       'abbrev'       lexer classes {COMMAND};
terminal Abort_t        'abort'        lexer classes {TACTIC};
terminal All_t          'all'          lexer classes {COMMAND};
terminal Apply_t        'apply'        lexer classes {TACTIC};
terminal As_t           'as'           lexer classes {COMMAND};
terminal Assert_t       'assert'       lexer classes {TACTIC};
terminal Async_t        'async'        lexer classes {TACTIC};
terminal Backchain_t    'backchain'    lexer classes {TACTIC};
terminal By_t           'by'           lexer classes {COMMAND};
terminal Case_t         'case'         lexer classes {TACTIC};
terminal Clear_t        'clear'        lexer classes {TACTIC};
terminal Coinduction_t  'coinduction'  lexer classes {TACTIC};
terminal Exists_t       'exists'       lexer classes {TACTIC, LOGIC};
terminal False_t        'false'        lexer classes {LOGIC};
terminal Forall_t       'forall'       lexer classes {LOGIC};
terminal Induction_t    'induction'    lexer classes {TACTIC};
terminal Intros_t       'intros'       lexer classes {TACTIC};
terminal Keep_t         'keep'         lexer classes {TACTIC};
terminal Left_t         'left'         lexer classes {TACTIC};
terminal Nabla_t        'nabla'        lexer classes {LOGIC};
terminal On_t           'on'           lexer classes {TACTIC};
terminal Permute_t      'permute'      lexer classes {TACTIC};
terminal Rename_t       'rename'       lexer classes {TACTIC};
terminal Right_t        'right'        lexer classes {TACTIC};
terminal Search_t       'search'       lexer classes {TACTIC};
terminal Skip_t         'skip'         lexer classes {TACTIC};
terminal Split_t        'split'        lexer classes {TACTIC};
terminal SplitStar_t    'split*'       lexer classes {TACTIC};
terminal To_t           'to'           lexer classes {TACTIC};
terminal True_t         'true'         lexer classes {LOGIC};
terminal Type_t         'type'         lexer classes {LOGIC};
terminal Unabbrev_t     'unabbrev'     lexer classes {COMMAND};
terminal Undo_t         'undo'         lexer classes {TACTIC};
terminal Unfold_t       'unfold'       lexer classes {TACTIC};
terminal With_t         'with'         lexer classes {TACTIC};
terminal Witness_t      'witness'      lexer classes {TACTIC};
--New for Silver theorems
terminal ExtInduction_t   'extensible_induction'   lexer classes {TACTIC};
terminal CaseStruct_t     'case_structure'         lexer classes {TACTIC};
terminal CaseLocal_t      'case_local'             lexer classes {TACTIC};
terminal In_t             'in'                     lexer classes {TACTIC};
terminal TreesEq_t        'trees_equal'            lexer classes {TACTIC};

--To show the current state for PG
terminal ShowCurrent_t  'Show $$current.'  lexer classes {COMMAND};


terminal Backs_t       /(#back[\ \n\r\t]*.[\ \n\r\t]*)+/ lexer classes {TOKEN};
terminal Reset_t       '#reset'  lexer classes {TOKEN};
terminal DefEq_t       ':='      lexer classes {TOKEN};
terminal Comma_t       ','       lexer classes {TOKEN}, precedence=3;
terminal Period_t      '.'       lexer classes {TOKEN};
terminal Semicolon_t   ';'       lexer classes {TOKEN};
terminal Backslash_t   '\'       lexer classes {TOKEN}, precedence=7;
terminal LParen_t      '('       lexer classes {TOKEN};
terminal RParen_t      ')'       lexer classes {TOKEN};
terminal Eq_t          '='       lexer classes {TOKEN};
terminal Colon_t       ':'       lexer classes {TOKEN};
terminal RightArrow_t  '->'      lexer classes {TOKEN}, precedence=4, association=right;
terminal At_t          '@'       lexer classes {TOKEN};
terminal Octothorpe_t  '#'       lexer classes {TOKEN};
terminal Or_t          '\/'      lexer classes {TOKEN}, precedence=5, association=left;
terminal And_t         '/\'      lexer classes {TOKEN}, precedence=6, association=left;
terminal LBracket_t    '['       lexer classes {TOKEN};
terminal RBracket_t    ']'       lexer classes {TOKEN};
terminal Underscore_t  '_'       lexer classes {TOKEN};
terminal OptSemi_t     /;?/      lexer classes {TOKEN};
terminal Cons_t        '::'      lexer classes {TOKEN}, precedence=11, association=right;
terminal Nil_t         'nil'     lexer classes {TOKEN};
--These two have Abella uses with no precedence or associativity
--   and Silver uses with precedence and associativity (arithmetic)
terminal Plus_t        '+'       lexer classes {TOKEN}, precedence=9, association=left;
terminal Star_t        '*'       lexer classes {TOKEN}, precedence=10, association=left;


terminal Id_t  /[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;
terminal QString_t  /"[^"]*"/;
terminal Number_t  /[0-9]+/;
--Qname_t is a qualified name as in Silver
--The grammar part is a Silver name, so it only needs Silver-allowed characters
terminal Qname_t  /([A-Za-z0-9_]+:)*[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;


--These are the things which we are adding to Abella for Silver
terminal AttrAccess_t  /[a-zA-Z][A-Za-z0-9\_]*\.[a-zA-Z][A-Za-z0-9\_]*/;
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
--Attributes not having any value
terminal No_t         'no'      lexer classes {TOKEN};
terminal Value_t      'value'   lexer classes {TOKEN};


ignore terminal Whitespace_t /[\ \t\n\r]+/;
-- Allows (one level of) nested comments.  Based on Silver comments.
ignore terminal BlockComment_t /\/\*(\/\*([^\*]|\*+[^\/\*])*\*+\/|[^\*]|\*+[^\/\*])*\*+\// lexer classes {COMMENT};
ignore terminal OneLineComment_t /(%.*)/ lexer classes {COMMENT};

