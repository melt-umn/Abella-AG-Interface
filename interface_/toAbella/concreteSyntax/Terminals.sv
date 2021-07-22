grammar interface_:toAbella:concreteSyntax;


imports interface_:toAbella:abstractSyntax;
imports interface_:common:abstractSyntax;
imports interface_:common:concreteSyntax;


lexer class COMMAND dominates Id_t;


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
terminal Induction_t    'induction'    lexer classes {TACTIC};
terminal Intros_t       'intros'       lexer classes {TACTIC};
terminal Keep_t         'keep'         lexer classes {TACTIC};
terminal Left_t         'left'         lexer classes {TACTIC};
terminal On_t           'on'           lexer classes {TACTIC};
terminal Permute_t      'permute'      lexer classes {TACTIC};
terminal Rename_t       'rename'       lexer classes {TACTIC};
terminal Right_t        'right'        lexer classes {TACTIC};
terminal Search_t       'search'       lexer classes {TACTIC};
terminal Skip_t         'skip'         lexer classes {TACTIC};
terminal Split_t        'split'        lexer classes {TACTIC};
terminal SplitStar_t    'split*'       lexer classes {TACTIC};
terminal To_t           'to'           lexer classes {TACTIC};
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
terminal Period_t      '.'       lexer classes {TOKEN};
terminal Semicolon_t   ';'       lexer classes {TOKEN};
terminal Backslash_t   '\'       lexer classes {TOKEN}, precedence=7;
terminal OptSemi_t     /;?/      lexer classes {TOKEN};


terminal QString_t  /"[^"]*"/;

