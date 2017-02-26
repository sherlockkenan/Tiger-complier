/*
 * main.c
 */

#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "absyn.h"
#include "errormsg.h"
#include "temp.h" /* needed by translate.h */
#include "tree.h" /* needed by frame.h */
#include "assem.h"
#include "frame.h" /* needed by translate.h and printfrags prototype */
#include "translate.h"
#include "env.h"
#include "semant.h" /* function prototype for transProg */
#include "canon.h"
#include "prabsyn.h"
#include "printtree.h"
#include "escape.h" /* needed by escape analysis */
#include "parse.h"
#include "codegen.h"
#include "regalloc.h"
#include <string.h>

extern bool anyErrors;

/* print the assembly language instructions to filename.s */
static void doProc(FILE *out, F_frame frame, T_stm body)
{
 AS_proc proc;
 T_stmList stmList;
 AS_instrList iList;

 F_tempMap = Temp_empty();
T_stmList stmList_temp=T_StmList(body,NULL);
 //printStmList(stdout, stmList_temp);
 stmList = C_linearize(body);
 stmList = C_traceSchedule(C_basicBlocks(stmList));
 //printStmList(stdout, stmList);
 iList  = F_codegen(frame, stmList); /* 9 */

 string fun_name=Temp_labelstring(F_name(frame));
 fprintf(out, ".text\n.globl %s\n.type %s, @function\n %s:\n",fun_name,fun_name,fun_name);
 //AS_printInstrList (out, iList,Temp_layerMap(F_tempMap,Temp_name()));
 RA_result ra = RA_regAlloc(frame, iList);  /* 10, 11 */



 
  AS_printInstrList (out, iList,Temp_layerMap(F_tempMap,ra->coloring));
 //AS_printInstrList (out, iList,Temp_layerMap(F_tempMap,Temp_name()));
 fprintf(out, "movl %s,%s\n","%ebp","%esp");
 fprintf(out, "addl %s,%s\n","$-12","%esp");
 fprintf(out, "popl %s\n","%esi");
 fprintf(out, "popl %s\n","%edi");
 fprintf(out, "popl %s\n","%ebx");
  fprintf(out, "popl %s\n","%ebp");
 fprintf(out, "ret \n" );
 fprintf(out, "\n\n\n");
}

int main(int argc, string *argv)
{
 A_exp absyn_root;
 S_table base_env, base_tenv;
 F_fragList frags;
 char outfile[100];
 FILE *out = stdout;

 if (argc==2) {
   absyn_root = parse(argv[1]);
   if (!absyn_root)
     return 1;
     
#if 0
   pr_exp(out, absyn_root, 0); /* print absyn data structure */
   fprintf(out, "\n");
#endif
	//If you have implemented escape analysis, uncomment this
   Esc_findEscape(absyn_root); /* set varDec's escape field */

   frags = SEM_transProg(absyn_root);
   if (anyErrors) return 1; /* don't continue */

   /* convert the filename */
   sprintf(outfile, "%s.s", argv[1]);
   out = fopen(outfile, "w");
   /* Chapter 8, 9, 10, 11 & 12 */
   fprintf(out, ".section .rodata\n" );
 
   for (;frags;frags=frags->tail)
     if (frags->head->kind == F_procFrag) 
       doProc(out, frags->head->u.proc.frame, frags->head->u.proc.body);
     else if (frags->head->kind == F_stringFrag) {
       string str=frags->head->u.stringg.str;
       unsigned int len= strlen(str);
       char  size[4];
       char sbuf[100];
      
       int i=0,j=0;
       int tab_size=0;
       for(i=0;str[i]!='\0';i++){
          if(str[i]=='\n'){
            sbuf[j++]='\\';
            sbuf[j++]='n';
          }else{
            if(str[i]=='\\'&&str[i+1]=='t'){
              tab_size++;
            }
            sbuf[j++]=str[i];
          }
        } 
       sbuf[j]='\0';
       len-=tab_size;
       memcpy(size,(char*)(&len),4);
       fprintf(out, "%s:\n",Temp_labelstring(frags->head->u.stringg.label) );
       fprintf(out, ".string \"%c%c%c%c%s\"\n",size[0],size[1],size[2],size[3],sbuf);
     }
   fclose(out);
   return 0;
 }
 EM_error(0,"usage: tiger file.tig");
 return 1;
}
