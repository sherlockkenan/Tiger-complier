%{
#include <string.h>
#include "util.h"
#include "tokens.h"
#include "errormsg.h"

int charPos=1;
int start_pos=1;
char str[10];

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

void init_str(){
    str[0]=0;
}
/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

%}
  /* You can add lex definitions here. */

%x  COMMENT_STA STRING_STA
%%
  /* 
  * Below are some examples, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 




","       {adjust(); return COMMA;}
":"       {adjust(); return COLON;}
";"       {adjust(); return SEMICOLON;}
"("       {adjust(); return LPAREN;}
")"       {adjust(); return RPAREN;}
"["       {adjust(); return LBRACK;}
"]"       {adjust(); return RBRACK;}
"{"       {adjust(); return LBRACE;}
"}"       {adjust(); return RBRACE;}
"."       {adjust(); return DOT;}
"+"       {adjust(); return PLUS;}
"-"       {adjust(); return MINUS;}
"*"       {adjust(); return TIMES;}
"/"       {adjust(); return DIVIDE;}
"="       {adjust(); return EQ;}
"<>"      {adjust(); return NEQ;}
"<"       {adjust(); return LT;}
"<="      {adjust(); return LE;}
">"       {adjust(); return GT;}
">="      {adjust(); return GE;}
"&"       {adjust(); return AND;}
"|"       {adjust(); return OR;}
":="      {adjust(); return ASSIGN;}
array     {adjust(); return ARRAY;}
if        {adjust(); return IF;}
then      {adjust(); return THEN;}
else      {adjust(); return ELSE;}
while     {adjust(); return WHILE;}
for       {adjust(); return FOR;}
to        {adjust(); return TO;}
do        {adjust(); return DO;}
let       {adjust(); return LET;}
in        {adjust(); return IN;}
end       {adjust(); return END;}
of        {adjust(); return OF;}
break     {adjust(); return BREAK;}
nil       {adjust(); return NIL;}
function  {adjust(); return FUNCTION;}
var       {adjust(); return VAR;}
type      {adjust(); return TYPE;}



" "  {adjust(); continue;} 
\n	 {adjust(); EM_newline(); continue;}
[ \r\t ] {adjust(); continue;}

[0-9]+	 {adjust(); yylval.ival=atoi(yytext); return INT;}

[a-zA-Z][a-zA-Z0-9_]*  {adjust();yylval.sval=String(yytext);return ID;}


\"  { adjust(); start_pos=charPos-1;BEGIN(STRING_STA);}


"/*" {adjust();BEGIN(COMMENT_STA);}

<STRING_STA>{
    \" {
        adjust();
        if(str[0]==0){
            yylval.sval="(null)";
        }else{
        yylval.sval=String(str);
        //printf(" str %s\n",str);
        }
        
        init_str();

        EM_tokPos = start_pos;
        BEGIN(INITIAL);
        return STRING;
    }


    \\n {adjust();strcat(str,"\n");}
    
   
    .	 {adjust(); strcat(str,yytext);}

    
}



<COMMENT_STA>{
    "*/" {
        adjust();
        BEGIN(INITIAL);
    }

    \n  {
        adjust();
        EM_newline();
        continue;
    }

    . {
        adjust();
    }
    
}

.	 {adjust(); EM_error(EM_tokPos,"illegal token");}

