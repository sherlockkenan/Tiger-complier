%{
#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h" 
#include "errormsg.h"
#include "absyn.h"

int yylex(void); /* function prototype */

A_exp absyn_root;

void yyerror(char *s)
{
 EM_error(EM_tokPos, "%s", s);
 exit(1);
}
%}


%union {
	int pos;
	int ival;
	string sval;
	A_var var;
	A_exp exp;
	/* et cetera */

    A_ty ty;
    A_dec dec;
    A_expList	explist;
    A_decList	declist;
    A_field	field;
    A_fieldList fieldlist;
    A_namety namety;
    A_nametyList nametylist;
    A_fundec funcdec;
    A_fundecList funcdeclist;
    A_efield efield;
    A_efieldList efieldlist;
	}

%token <sval> ID STRING
%token <ival> INT

%token 
  COMMA COLON SEMICOLON LPAREN RPAREN LBRACK RBRACK 
  LBRACE RBRACE DOT 
  PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE
  AND OR ASSIGN
  ARRAY IF THEN ELSE WHILE FOR TO DO LET IN END OF 
  BREAK NIL
  FUNCTION VAR TYPE
  UMINUS

%type <exp> exp program varexp opexp recordexp seqexp assignexp ifexp whileexp  forexp letexp arrayexp callexp minusexp
%type <var> lvalue
%type <dec> dec typeDec funcDec varDec
%type <explist> expseq args args_
%type <declist> decs
%type <field> field
%type <fieldlist> fieldList fieldList_
%type <namety> namety
%type <nametylist> nametyList 
%type <funcdeclist> funcDecList
%type <funcdec> funcDec_
%type <efield> efield
%type <efieldlist> efieldList efieldList_
/* et cetera */
%left ELSE
%nonassoc ASSIGN
%left OR AND
%nonassoc EQ NEQ GT LT GE LE
%left PLUS MINUS
%left TIMES DIVIDE
%nonassoc UMINUS

%start program

%%

program:   exp    {absyn_root=$1;}



exp :   varexp    {$$=$1;}
		|   opexp     {$$=$1;}
		|   recordexp {$$=$1;}
		|   seqexp    {$$=$1;}
		|   assignexp {$$=$1;}
		|   ifexp     {$$=$1;}
		|   whileexp  {$$=$1;}
		|   forexp    {$$=$1;}
		|   letexp    {$$=$1;}
		|   arrayexp  {$$=$1;}
        |   callexp  {$$=$1;}
        |   minusexp {$$=$1;}

        |   NIL     {$$=A_NilExp(EM_tokPos);}
        |   INT     {$$=A_IntExp(EM_tokPos,$1);}
        |   STRING  {$$=A_StringExp(EM_tokPos,$1);}
        |   BREAK   {$$=A_BreakExp(EM_tokPos);}




varexp :  lvalue  {$$=A_VarExp(EM_tokPos,$1);}

callexp:   ID LPAREN args RPAREN {$$=A_CallExp(EM_tokPos,S_Symbol($1),$3);}

opexp :     exp PLUS exp {$$=A_OpExp(EM_tokPos,A_plusOp,$1,$3);}
		|   exp MINUS exp {$$=A_OpExp(EM_tokPos,A_minusOp,$1,$3);}
		|   exp TIMES exp {$$=A_OpExp(EM_tokPos,A_timesOp,$1,$3);}
		|   exp DIVIDE exp {$$=A_OpExp(EM_tokPos,A_divideOp,$1,$3);}
		|   exp EQ exp {$$=A_OpExp(EM_tokPos,A_eqOp,$1,$3);}
		|   exp NEQ exp {$$=A_OpExp(EM_tokPos,A_neqOp,$1,$3);}
		|   exp LT exp {$$=A_OpExp(EM_tokPos,A_ltOp,$1,$3);}
		|   exp LE exp {$$=A_OpExp(EM_tokPos,A_leOp,$1,$3);}
		|   exp GT exp {$$=A_OpExp(EM_tokPos,A_gtOp,$1,$3);}
		|   exp GE exp {$$=A_OpExp(EM_tokPos,A_geOp,$1,$3);}
minusexp: MINUS exp  %prec UMINUS {$$=A_OpExp(EM_tokPos,A_minusOp,A_IntExp(EM_tokPos,0),$2);}

recordexp : ID LBRACE efieldList RBRACE {$$=A_RecordExp(EM_tokPos,S_Symbol($1),$3);}

seqexp :  LPAREN expseq RPAREN {$$=A_SeqExp(EM_tokPos,$2);}

assignexp : lvalue ASSIGN exp {$$=A_AssignExp(EM_tokPos,$1,$3);}

ifexp : IF exp THEN exp ELSE exp {$$=A_IfExp(EM_tokPos,$2,$4,$6);}
		|   IF exp THEN exp {$$=A_IfExp(EM_tokPos,$2,$4,A_NilExp(EM_tokPos));}
		|   exp OR exp {$$=A_IfExp(EM_tokPos,$1,A_IntExp(EM_tokPos,1),$3);}
		|   exp AND exp {$$=A_IfExp(EM_tokPos,$1,$3,A_IntExp(EM_tokPos,0));}

whileexp :  WHILE exp DO exp  {$$=A_WhileExp(EM_tokPos,$2,$4);}

forexp :  FOR ID ASSIGN exp TO exp DO exp {$$=A_ForExp(EM_tokPos,S_Symbol($2),$4,$6,$8);}


letexp :  LET decs IN expseq END  {$$=A_LetExp(EM_tokPos,$2,A_SeqExp(EM_tokPos, $4));}

arrayexp: ID LBRACK exp RBRACK OF exp {$$=A_ArrayExp(EM_tokPos,S_Symbol($1),$3,$6);}








lvalue: ID{$$=A_SimpleVar(EM_tokPos,S_Symbol($1));}
		|   lvalue LBRACK exp RBRACK {$$=A_SubscriptVar(EM_tokPos,$1,$3);}
		|   ID LBRACK exp RBRACK  {$$=A_SubscriptVar(EM_tokPos,A_SimpleVar(EM_tokPos,S_Symbol($1)),$3);}
		|   lvalue DOT ID {$$=A_FieldVar(EM_tokPos,$1,S_Symbol($3));}





args : {$$=NULL;}
     |exp {$$=A_ExpList($1,NULL);}
	 |   exp COMMA args_ {$$=A_ExpList($1,$3);}

args_ : exp{$$=A_ExpList($1,NULL);}
		|   exp COMMA args_  {$$=A_ExpList($1,$3);}



expseq : {$$=NULL;}
		|   exp  {$$=A_ExpList($1,NULL);}
		|   exp SEMICOLON expseq {$$=A_ExpList($1,$3);}





efield :  ID EQ exp {$$=A_Efield(S_Symbol($1),$3);}




efieldList :  {$$=NULL;}
        |   efield {$$=A_EfieldList($1,NULL);}
		|   efield  COMMA efieldList_ {$$=A_EfieldList($1,$3);}

efieldList_ :efield {$$=A_EfieldList($1,NULL);}
		|   efield COMMA  efieldList_ {$$=A_EfieldList($1,$3);}






decs : dec  {$$=A_DecList($1,NULL);}
		|   dec decs {$$=A_DecList($1,$2);}

dec :   typeDec {$$=$1;}
		|   varDec  {$$=$1;}
		|   funcDec {$$=$1;}



typeDec : nametyList {$$=A_TypeDec(EM_tokPos,$1);}

varDec : VAR ID ASSIGN exp {$$=A_VarDec(EM_tokPos,S_Symbol($2),NULL,$4);}
		|   VAR ID COLON ID ASSIGN exp {$$=A_VarDec(EM_tokPos,S_Symbol($2),S_Symbol($4),$6);}





funcDec : funcDecList {$$=A_FunctionDec(EM_tokPos,$1);}

funcDec_ : FUNCTION ID LPAREN fieldList RPAREN COLON ID EQ exp  {$$=A_Fundec(EM_tokPos,S_Symbol($2),$4,S_Symbol($7),$9);}
		|    FUNCTION ID LPAREN fieldList RPAREN EQ exp {$$=A_Fundec(EM_tokPos,S_Symbol($2),$4,NULL,$7);}


funcDecList : funcDec_ {$$=A_FundecList($1,NULL);}
		|   funcDec_ funcDecList  {$$=A_FundecList($1,$2);}






namety: TYPE ID EQ ID {$$=A_Namety(S_Symbol($2),A_NameTy(EM_tokPos,S_Symbol($4)));}
		|   TYPE ID EQ LBRACE fieldList RBRACE {$$=A_Namety(S_Symbol($2),A_RecordTy(EM_tokPos,$5));}
		|   TYPE ID EQ ARRAY OF ID {$$=A_Namety(S_Symbol($2),A_ArrayTy(EM_tokPos,S_Symbol($6)));}


nametyList :  namety  {$$=A_NametyList($1,NULL);}
		|   namety nametyList {$$=A_NametyList($1,$2);}







field : ID COLON ID {$$=A_Field(EM_tokPos,S_Symbol($1),S_Symbol($3));}

fieldList :  {$$=NULL;}
        |  field {$$=A_FieldList($1,NULL);}
		|  field COMMA fieldList_ {$$=A_FieldList($1,$3);}

fieldList_ :field {$$=A_FieldList($1,NULL);}
		|   field COMMA fieldList_ {$$=A_FieldList($1,$3);}




