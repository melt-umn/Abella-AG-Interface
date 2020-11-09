grammar toAbella;


lexer class COMMAND dominates Id_t;
lexer class TACTIC  dominates Id_t;
lexer class LOGIC   dominates Id_t;
lexer class LATER   dominates Id_t; --for the things I'm currently unsure about
lexer class TOKEN   dominates Id_t;
lexer class COMMENT;


terminal Close_t          'Close'          lexer classes {COMMAND};
terminal CoDefine_t       'CoDefine'       lexer classes {COMMAND};
terminal Define_t         'Define'         lexer classes {COMMAND};
terminal Import_t         'Import'         lexer classes {COMMAND};
terminal KKind_t          'Kind'           lexer classes {COMMAND};
terminal Query_t          'Query'          lexer classes {COMMAND};
terminal Quit_t           'Quit'           lexer classes {COMMAND};
terminal Set_t            'Set'            lexer classes {COMMAND};
terminal Show_t           'Show'           lexer classes {COMMAND};
terminal Specification_t  'Specification'  lexer classes {COMMAND};
terminal SSplit_t         'Split'          lexer classes {COMMAND};
terminal Theorem_t        'Theorem'        lexer classes {COMMAND};
terminal TType_t          'Type'           lexer classes {COMMAND};


terminal Abbrev_t  'abbrev'       lexer classes {LATER};
terminal Abort_t  'abort'  lexer classes {TACTIC};
terminal Accumulate_t  'accumulate'       lexer classes {LATER};
terminal All_t  'all'       lexer classes {LATER};
terminal Apply_t  'apply' lexer classes {TACTIC};
terminal As_t  'as'       lexer classes {LATER};
terminal Assert_t  'assert' lexer classes {TACTIC};
terminal Async_t  'async'       lexer classes {LATER};
terminal Backchain_t  'backchain'  lexer classes {TACTIC};
terminal By_t  'by'       lexer classes {LATER};
terminal Case_t  'case'  lexer classes {TACTIC};
terminal Clear_t  'clear'       lexer classes {LATER};
terminal Coinduction_t  'coinduction'  lexer classes {TACTIC};
terminal End_t  'end'       lexer classes {LATER};
terminal Exists_t  'exists'  lexer classes {TACTIC, LOGIC};
terminal False_t  'false'  lexer classes {LOGIC};
terminal Forall_t  'forall'  lexer classes {LOGIC};
terminal From_t  'from'       lexer classes {LATER};
terminal Induction_t  'induction'  lexer classes {TACTIC};
terminal Intros_t  'intros'  lexer classes {TACTIC};
terminal Keep_t  'keep'       lexer classes {LATER};
terminal Left_t  'left'  lexer classes {TACTIC};
terminal Nabla_t  'nabla'  lexer classes {LOGIC};
terminal On_t  'on'       lexer classes {LATER};
terminal Permute_t  'permute'  lexer classes {TACTIC};
terminal Rename_t  'rename'  lexer classes {TACTIC};
terminal Right_t  'right'  lexer classes {TACTIC};
terminal Search_t  'search'  lexer classes {TACTIC};
terminal Skip_t  'skip'  lexer classes {TACTIC};
terminal Split_t  'split'  lexer classes {TACTIC};
terminal SplitStar_t  'split*'  lexer classes {TACTIC};
terminal To_t  'to'       lexer classes {LATER};
terminal True_t  'true'  lexer classes {LOGIC};
terminal Unabbrev_t  'unabbrev'       lexer classes {LATER};
terminal Undo_t  'undo'  lexer classes {TACTIC};
terminal Unfold_t  'unfold'  lexer classes {TACTIC};
terminal With_t  'with'       lexer classes {LATER};
terminal Witness_t  'witness'  lexer classes {TACTIC};


terminal Back_t        '#back'  lexer classes {TOKEN};
terminal Reset_t       '#reset'  lexer classes {TOKEN};
terminal DefEq_t       ':='  lexer classes {TOKEN};
terminal Comma_t       ','  lexer classes {TOKEN}, precedence=3;
terminal Period_t      '.'  lexer classes {TOKEN};
terminal Semicolon_t   ';'  lexer classes {TOKEN};
terminal Backslash_t   '\'  lexer classes {TOKEN}, precedence=7;
terminal LParen_t      '('  lexer classes {TOKEN};
terminal RParen_t      ')'  lexer classes {TOKEN};
terminal Eq_t          '='  lexer classes {TOKEN};
terminal Colon_t       ':'  lexer classes {TOKEN};
terminal RightArrow_t  '->'  lexer classes {TOKEN}, association=right, precedence=4;
terminal Star_t        '*'  lexer classes {TOKEN};
terminal At_t          '@'  lexer classes {TOKEN};
terminal Octothorpe_t  '#'  lexer classes {TOKEN};
terminal Plus_t        '+'  lexer classes {TOKEN};
terminal Or_t          '\/'  lexer classes {TOKEN}, precedence=5, association=left;
terminal And_t         '/\'     lexer classes {TOKEN}, precedence=6, association=left;
terminal LBracket_t    '['   lexer classes {TOKEN};
terminal RBracket_t    ']'   lexer classes {TOKEN};
terminal Underscore_t  '_'  lexer classes {TOKEN};


terminal Id_t  /[-A-Za-z^=`'?$][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;


terminal QString_t  /"[^"]*"/;


terminal Number_t  /[0-9]+/;


ignore terminal Whitespace_t /[\ \t\n\r]+/;

-- Allows (one level of) nested comments.  Based on Silver comments
ignore terminal BlockComment_t /\/\*(\/\*([^\*]|\*+[^\/\*])*\*+\/|[^\*]|\*+[^\/\*])*\*+\// lexer classes {COMMENT};
ignore terminal OneLineComment_t /(%.*)/ lexer classes {COMMENT};

