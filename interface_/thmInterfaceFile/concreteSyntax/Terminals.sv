grammar interface_:thmInterfaceFile:concreteSyntax;


imports interface_:thmInterfaceFile:abstractSyntax;
imports interface_:common;


terminal Qname_colon_t  /([a-zA-Z0-9_]+:)*[-A-Za-z^=`'?][-A-Za-z^=`'?$0-9_*@+#!~\/]*/;
terminal Separate_t     '&';
terminal SplitInterf_t  '$Spl';
terminal DefInterf_t    '$Def';


terminal Dot_t    '.';
terminal Semi_t   ';';

