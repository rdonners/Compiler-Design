%{
    /*definitions*/
%}

%%
[a-z] {printf("%s is a lowercase\n", yytext);}              /* [0-9]+ {yylval.num = atoi(yytext); return NUMBER;  } */
. {printf("%s is not a lowercase character\n", yytext);}    /* \n {return EOL;} */
                                                            /* . {} */
%%

yywrap() {}

/* Below not for when I've the parser running */
int main () {
    printf("Enter String: ");
    yylex();
    return 0;
}