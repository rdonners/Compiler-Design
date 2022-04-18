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
[ \t\n]                 ;
[a-zA-Z_][a-zA-Z0-9_]*  printf("valid!n");SAVE_TOKEN; return TIDENTIFIER;
[0-9]+.[0-9]*           printf("valid!n");SAVE_TOKEN; return TDOUBLE;
[0-9]+                  printf("valid!n");SAVE_TOKEN; return TINTEGER;
"bool"                 return TOKEN(BOOL);
"String"              return TOKEN(STRING);
"void"                  return TOKEN(VOID);
"struct"               return TOKEN(STRCT);
"for"                   return TOKEN(FOR);
"if"                    return TOKEN(TIF);
"then"                  return TOKEN(THEN);
"else"                  return TOKEN(ELSE);
"printf"                return TOKEN(PRINT);
"return"                return TOKEN(RTRN);
"true"                  return TOKEN(TTRUE);
"false"                  return TOKEN(TFALSE);
";"                     return TOKEN(SEMICOLON);
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
"//".*                  printf("valid!n");{/* DO NOTHING */}
.                       printf("INVALID Unknown token!n"); yyterminate();




{LineTerminator}	    { yylineno++; } 
{WhiteSpace}            { /* ignore */ }

{Integer} 		{
						yylval = atoi(yytext) ;
						if(  yylval > 32767 )
						{
							yyerror("INVALID: Integer OOB") ;
				//			return INVALID;
						}
						else if (yylval < -32768){
							yyerror("INVALID: Integer OOB") ;
				//			return INVALID;
						}
						else
						{
							return ICONST; 
						} 
				}
				
				

{String} 		{ 
					int present = 0;
					for(int i = 0; yytext[i] != '\0'; i++)
				  	{
						if(yytext[i] == '\\')
							present = 1;
				  	}
					if(present == 1)
						yyerror("INVALID: STRING OUT OF BOUNDS");
					//	return INVALID;
					else
					{
                    	return SCONST; 
					} 
				}
%%Everything Else
. {printf("INVALID")}

%%

yywrap() {}
