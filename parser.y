%{
    
    
%}

%union {
    int num;
    char sym;
}

%token EOL
%token<num> NUMBER
%type<num> exp
%token PLUS


%%

input: 
    exp EOL {printf("%d\n", $1); }
|   EOL;

exp: 
   NUMBER {$$ = $1;}
 | NUMBER PLUS NUMBER {$$ = $1 + $3}
%%

yywrap() {}

