#include "util.h"
#include "symbol.h" 
#include "absyn.h"  
#include <stdlib.h>
#include <stdio.h>
#include "table.h"
#include "escape.h"


typedef struct dec_depth_ *dec_depth;

struct dec_depth_{
  int depth;
};
//the value declation list,for rewrite escape
A_decList var_declist=NULL;
//for append var_declist
A_decList append_list(A_decList dec_list,A_dec dec){

      if(dec_list==NULL){
      	 A_decList tmp = checked_malloc(sizeof(*tmp));
    	tmp->head=dec;
    	tmp->tail=NULL;
    	return tmp;
    }else {
    	A_decList tmp = checked_malloc(sizeof(*tmp));
    	tmp->head=dec;
    	tmp->tail=dec_list;
        return tmp;
    }

}

dec_depth Dec_depth(int depth){
   dec_depth dec = checked_malloc(sizeof(*dec));
   dec->depth = depth;
   return dec;
}
//for get from declist
A_dec get_dec(A_decList dec_list,A_var var){
     while (dec_list){
     	if(dec_list->head->u.var.var==var->u.simple){
     		return dec_list->head;
     	}
     	dec_list=dec_list->tail;
     }
     return NULL;

}

static void tranExp(S_table env,int depth,A_exp a);
static void tranDec(S_table env,int depth,A_dec d);
static void tranVar(S_table env,int depth,A_var v);

static void tranExp(S_table env,int depth,A_exp a){

  switch(a->kind){

    case A_opExp:{
      printf("opexp\n");
      tranExp(env,depth,a->u.op.left);
      tranExp(env,depth,a->u.op.right);
      break;

    }
    case A_letExp:{
      printf("letexp\n");
      A_decList decs = a->u.let.decs;
      S_beginScope(env);
      while(decs!=NULL){
        tranDec(env,depth,decs->head);
        decs = decs->tail;
      }
      printf("let in\n");
      A_expList body = a->u.let.body;
      
      tranExp(env,depth,body);
  
      S_endScope(env);
      printf("end let\n");
       break;

    }
    case A_callExp:{
      printf("callexp\n");
       A_expList args = a->u.call.args;
      while(args!=NULL){
        tranExp(env,depth,args->head);
        args=args->tail;
      }
      break;
    }

    case A_recordExp:{
      printf("A_recordExp\n");
      A_efieldList efields = a->u.record.fields;
      while(efields!=NULL){
        tranExp(env,depth,efields->head->exp);
         efields = efields->tail;
      }
       printf("end record\n");
      break;
    }
    case A_seqExp:{
      printf("seqexp\n");
      A_expList seq = a->u.seq;
      while(seq!=NULL){
        tranExp(env,depth,seq->head);
        seq = seq->tail;
      }
    break;
    }


    case A_assignExp:{
      printf("A_assignExp\n");
      tranVar(env,depth,a->u.assign.var);
      tranExp(env,depth,a->u.assign.exp);
      break;
    }
    case A_ifExp:{
        printf("ifexp\n");
      tranExp(env,depth,a->u.iff.test);
      tranExp(env,depth,a->u.iff.then);
      if(a->u.iff.elsee){
        tranExp(env,depth,a->u.iff.elsee);
      }
       break;
    }

    case A_whileExp:{
      printf("whileexp\n");
      tranExp(env,depth,a->u.whilee.test);
      tranExp(env,depth,a->u.whilee.body);
      break;

    }
    case A_forExp:{
      printf("forexp\n");
      S_enter(env,a->u.forr.var,Dec_depth(depth));
      tranExp(env,depth,a->u.forr.lo);
      tranExp(env,depth,a->u.forr.hi);
      tranExp(env,depth,a->u.forr.body);
      break;

    }
 
    case A_arrayExp:{
      printf("arrayexp\n");
      tranExp(env,depth,a->u.array.size);
      tranExp(env,depth,a->u.array.init);
      break;

    }
    case A_varExp:{
        printf("varexp\n");
      tranVar(env,depth,a->u.var);
      break;

    }
  }
}

static void tranDec(S_table env,int depth,A_dec d){
  switch(d->kind){


  case A_varDec:{
    printf("vardec\n");
    S_symbol var = d->u.var.var;
    A_exp init = d->u.var.init;
    var_declist=append_list(var_declist,d);
    tranExp(env,depth,init);

    //default is false
    d->u.var.escape=FALSE;

    S_enter(env,var,&depth);
    break;
  }
  case A_functionDec:{
    printf("fundec\n");
    A_fundecList a_fundecList = d->u.function;
    while(a_fundecList!=NULL){
      A_fundec a_fundec = a_fundecList->head;
      A_fieldList a_fieldList = a_fundec->params;
      S_beginScope(env);
      while(a_fieldList!=NULL){
     
        S_enter(env,a_fieldList->head->name,Dec_depth(depth+1));
        a_fieldList = a_fieldList->tail;
      }
      tranExp(env,depth+1,a_fundec->body);
      S_endScope(env);
      a_fundecList = a_fundecList->tail;
    }
    break;
  }
 
  }
}
static void tranVar(S_table env,int depth,A_var v){
  switch(v->kind){
    
  case A_simpleVar:{
    printf("simplevar\n");
    dec_depth dec_dep= S_look(env,v->u.simple);
    A_dec dec=get_dec(var_declist,v);
      if(dec_dep){
 
      if(dec_dep->depth< depth){
       // *esc_binding->escape = TRUE;
        if(dec)
         dec->u.var.escape=TRUE;
       // printf("ture depth %d esc depth:%d\n",depth,dec_dep->depth);
      }
    }
       
 
    break;
  }
  case A_fieldVar:
    printf("fieldvar\n");
    tranVar(env,depth,v->u.field.var);
    break;
  case A_subscriptVar:
  printf("subscriptvar\n");
    tranVar(env,depth,v->u.subscript.var);
    break;
  }
}
void Esc_findEscape(A_exp exp){
  S_table escape_env = TAB_empty();

  tranExp(escape_env,0,exp);
  // traverseExp(TAB_empty(),0,exp);
}