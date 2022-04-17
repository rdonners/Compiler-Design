%{
    /*definitions*/
#include <string>
#include "node.h"
#include "parser.hpp"
#define SAVE_TOKEN yylval.string = new std::string(yytext, yyleng)
#define TOKEN(t) (yylval.token = t)
extern "C" int yywrap() { }
%}

%%




"[a-z]*" {printf("VALID")}
‘\[a-zA-Z0-9_]+’ {printf("VALID")}
[Integer.MIN_VALUE-Integer.MAX_VALUE] {printf("VALID")}

[ \t\n]                 ;
[a-zA-Z_][a-zA-Z0-9_]*  printf("valid!n");SAVE_TOKEN; return TIDENTIFIER;
[0-9]+.[0-9]*           printf("valid!n");SAVE_TOKEN; return TDOUBLE;
[0-9]+                  printf("valid!n");SAVE_TOKEN; return TINTEGER;
"="                     printf("valid!n");return TOKEN(TEQUAL);
"=="                    printf("valid!n");return TOKEN(TCEQ);
"!="                    printf("valid!n");return TOKEN(TCNE);
"<"                     printf("valid!n");return TOKEN(TCLT);
"<="                    printf("valid!n");return TOKEN(TCLE);
">"                     printf("valid!n");return TOKEN(TCGT);
">="                    printf("valid!n");return TOKEN(TCGE);
"("                     printf("valid!n");return TOKEN(TLPAREN);
")"                     printf("valid!n");return TOKEN(TRPAREN);
"{"                     printf("valid!n");return TOKEN(TLBRACE);
"}"                     printf("valid!n");return TOKEN(TRBRACE);
"."                     printf("valid!n");return TOKEN(TDOT);
","                     printf("valid!n");return TOKEN(TCOMMA);
"+"                     printf("valid!n");return TOKEN(TPLUS);
"-"                     printf("valid!n");return TOKEN(TMINUS);
"*"                     printf("valid!n");return TOKEN(TMUL);
"/"                     printf("valid!n");return TOKEN(TDIV);
.                       printf("Unknown token!n"); yyterminate();



%%Everything Else
. {printf("INVALID")}

%%

yywrap() {}
