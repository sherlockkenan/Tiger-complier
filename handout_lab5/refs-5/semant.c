#include <stdio.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"
#include "semant.h"

/*Lab4: Your implementation of lab4*/
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
  struct expty e;
  
  e.exp = exp;
  e.ty = ty;
  return e;
}

string for_index;

/*
 * useful function skip pass all the 'Names'
 * Note: a little change from the textbook
 * consider the recursive record type-defination: first add a Ty_Name type in case
 * to avoid undefined types, then add the actual type(record type) in the
 * type-table, so when find a Ty_Name type has a NULL value in his 'u.name.ty'
 * you have to search the type-table again (from the head )to find the right type.
 * This is becuase of the shadowing attribute of symbol-table.
 * when find illegal cycle return NULL, unclosed recursive defination, return ty
 */

Ty_ty actual_ty(S_table tenv,Ty_ty ty)
{
  Ty_ty record = ty;
  while (ty && ty->kind == Ty_name) {
    if (ty->u.name.ty) {
      ty = ty->u.name.ty;

      if(ty->kind == Ty_name &&
         strcmp(S_name(record->u.name.sym),S_name(ty->u.name.sym)) == 0){
        return NULL; // means illegal cycle happen
      }
    } else {
      /*may cause infinite loop for some poor program*/
      ty = S_look(tenv,ty->u.name.sym);
      /*add the following statement to avoid infinite loop*/
      if (ty && ty->kind == Ty_name && ty->u.name.ty == NULL) {
        /*report illegal recursive defination and accurate error-info*/
        //should not happen
        break;
      }
    }
  }
  
  return ty;
}

// when enconter a var(l-value), it must be already in venv
struct expty transVar(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_var v)
{
  switch(v->kind)
  {
    case A_simpleVar:{
      EM_error(v->pos,"simplevar");
      E_enventry entry= S_look(venv,v->u.simple);
        EM_error(v->pos,"getvar");
      if(entry && entry->kind == E_varEntry) {
        Tr_exp var = Tr_simpleVar(entry->u.var.access,level);
        EM_error(v->pos,"getvar");
        return expTy(var,actual_ty(tenv,entry->u.var.ty));
      }
      else{
        // when doesn't exist or error type(e.g function)
        if(!entry)
          EM_error(v->pos,"undefined variable: %s", S_name(v->u.simple));
        else if (entry->kind == E_funEntry)
          EM_error(v->pos,"wrong type variable: %s, expected variable \
                                    but get function", S_name(v->u.simple));
        return expTy(NULL,Ty_Void());
      }
    }
      
    case A_fieldVar:{
      EM_error(v->pos,"fieldvar");
      struct expty record = transVar(venv,tenv,level,lbreak,v->u.field.var);
      //check record
      if (record.ty->kind == Ty_record) {
        //check field name
        Ty_fieldList field = record.ty->u.record;
        int index = 0;
        while(field){
          //string compare, check if the record have the named field
          if(strcmp(S_name(field->head->name),S_name(v->u.field.sym)) == 0)
             break;
          index++;
          field = field->tail;
        }
        if (field) {
          Tr_exp exp = Tr_fieldVar(record.exp,index);
          return expTy(exp,actual_ty(tenv,field->head->ty));
        }else{
          EM_error(v->pos,"undefined record field: %s",S_name(v->u.field.sym));
          return expTy(NULL,Ty_Void());
        }
      }else{
        //var'name may not right
        EM_error(v->pos,"undefined record: %s", S_name(v->u.field.var->u.simple));
        return expTy(NULL,Ty_Void());
      }
    }

    case A_subscriptVar:{
      EM_error(v->pos,"subscriptvar");
      struct expty array = transVar(venv,tenv,level,lbreak,v->u.subscript.var);

      if(array.ty->kind == Ty_array){
        // check index, index must be integer belongs to [0,size-1]
        struct expty index = transExp(venv,tenv,level,lbreak,v->u.subscript.exp);

        if(index.ty->kind != Ty_int){
          EM_error(v->u.subscript.exp->pos,"invalid array index: not integer");
          return expTy(NULL,Ty_Void());
        }
        Tr_exp exp = Tr_subscriptVar(array.exp,index.exp);
        /*Note: for a subscriptVar, return the actually type(e.g. int or string)*/
        return expTy(exp, actual_ty(tenv,array.ty->u.array));
      } else {
        //var's name may not right
        EM_error(v->pos,"undefined array:%s",S_name(v->u.subscript.var->u.simple));
        return expTy(NULL,Ty_Void());
      }
    }
    default: break;
  }
  
  return expTy(NULL,Ty_Void());
}

// no need break in swith-case
struct expty transExp(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_exp a)
{
  //track nesting while-for loop, for break check
  static U_boolList loopstack = NULL;
  static S_symbol forvar = NULL;
  EM_error(a->pos,"transExp");
  
  switch(a->kind)
  {
    
    case A_varExp:   {  EM_error(a->pos,"varExp");return transVar(venv,tenv,level,lbreak,a->u.var); }
      /*
        it seems no need the return value with addition
        type-checking just return
      */   
    case A_nilExp:   { EM_error(a->pos,"nilExp");return expTy(Tr_nilExp() ,Ty_Nil());    }
    case A_intExp:   {
      return expTy(Tr_intExp(a->u.intt),Ty_Int());
    }
    case A_stringExp:{
      EM_error(a->pos,"stingExp");
      return expTy(Tr_stringExp(a->u.stringg,level),Ty_String()); 
    }

    /*
     * check parameter's type and count, and return func's return value
     */
    case A_callExp:{
      // first: func must exist
      EM_error(a->pos,"callExp");
      E_enventry entry = S_look(venv,a->u.call.func);
      if(entry && entry->kind == E_funEntry) {
        // second: formals must match (numbers and type, recursive)
        A_expList explist = a->u.call.args;
        Ty_tyList tylist = entry->u.fun.formals;
        Tr_expList arglist=NULL, argtail = NULL;
     
        while (explist && tylist) {
       
          struct expty arg = transExp(venv,tenv,level,lbreak,explist->head);
          // type not match
          if(arg.ty != tylist->head){
            EM_error(explist->head->pos,"function parameter type error");
            /*
             * remark by xdl2007: donot return so early, a compiler should detect
             * as much errors as it can
             */
          }
       
          if(arglist == NULL) {
            arglist = argtail = Tr_ExpList(arg.exp,NULL);
          } else {
            argtail->tail = Tr_ExpList(arg.exp,NULL);
            argtail = argtail->tail;
          }
          explist = explist->tail;
          tylist = tylist->tail;
        }

        if(!explist && !tylist){
           EM_error(a->pos,"endcallExp");
          // Note: result type
          return expTy(Tr_callExp(entry->u.fun.label,level,entry->u.fun.level,arglist),
                        actual_ty(tenv,entry->u.fun.result));
        }else{
          /*give more info, like formas or actuals who is less */
          if(explist)
            EM_error(a->u.call.args->head->pos,"more argument than expected");
          else
            EM_error(a->u.call.args->head->pos,"less argument than expected");
        }
      }else{
        EM_error(a->pos,"undefined function: %s", S_name(a->u.call.func));
      }

      return expTy(NULL,Ty_Void());
    }
      
    case A_opExp:{
      //just from textbook
      EM_error(a->pos,"opExp");
      A_oper oper = a->u.op.oper;
      struct expty left = transExp(venv,tenv,level,lbreak,a->u.op.left);
      
      struct expty right = transExp(venv,tenv,level,lbreak,a->u.op.right);

      if(!right.exp)
      {
        EM_error(a->pos,"right null--------------------------------!!!!!");
      }
      Tr_exp exp = Tr_opExp(oper,left.exp, right.exp);

      if(oper==A_plusOp || oper==A_minusOp || oper==A_timesOp || oper==A_divideOp){
        if(left.ty->kind != Ty_int){
          EM_error(a->u.op.left->pos,"lhs integer required");
          return expTy(NULL,Ty_Void());
        }
        if(right.ty->kind != Ty_int){
          EM_error(a->u.op.right->pos,"rhs integer required");
          return expTy(NULL,Ty_Void());
        }
        return expTy(exp,Ty_Int());


      }else if(oper==A_eqOp || oper==A_neqOp){
       
        if((left.ty == right.ty) && (left.ty->kind == Ty_record ||
                                     left.ty->kind == Ty_int    ||
                                     left.ty->kind == Ty_string ||
                                     left.ty->kind == Ty_array)) {
        
          return expTy(exp,Ty_Int()); // should return 0/1 (integer type)
        }else{
          /* consider the nil and record types */
       
          if((left.ty->kind == Ty_nil && right.ty->kind == Ty_record) ||
             (left.ty->kind == Ty_record && right.ty->kind == Ty_nil))
            return expTy(exp,Ty_Int()); // should return 0/1 (integer type)
        }
     
      }else if(oper==A_ltOp || oper==A_leOp || oper==A_gtOp || oper==A_geOp)
      {
        if((left.ty == right.ty) && (left.ty->kind == Ty_int    ||
                                     left.ty->kind == Ty_string)){
          return expTy(exp,Ty_Int()); // should return 0/1 (integer type)
        }
      }
      
      EM_error(a->pos,"invaid type of two operands");
      return expTy(NULL,Ty_Void());
    }

    // similiar with callexp
    case A_recordExp: {
       EM_error(a->pos,"recordExp");
      // fist the recore type must exise
      Ty_ty entry = S_look(tenv,a->u.record.typ);

      if(entry != NULL) {
        if(entry->kind == Ty_record){
          A_efieldList efields = a->u.record.fields;
          Ty_fieldList fields = entry->u.record;
          Tr_expList arglist=NULL, argtail = NULL;
          int cnt = 0;
          while (efields && fields) {
            struct expty efield_exp = transExp(venv,tenv,level,lbreak,efields->head->exp);
            Ty_ty efield_type = efield_exp.ty;

            //TODO: also need construct a Tr_expList to feed the function 
            if(efield_type != actual_ty(tenv,fields->head->ty)) {
              if(!(efield_type->kind == Ty_nil &&
                 actual_ty(tenv,fields->head->ty)->kind == Ty_record)) {
                // another right case
                EM_error(a->pos,"record field type error");
                return expTy(NULL,Ty_Void());
              }
            }

            if(arglist == NULL) {
              arglist = argtail = Tr_ExpList(efield_exp.exp,NULL);
            } else {
              argtail->tail = Tr_ExpList(efield_exp.exp,NULL);
              argtail = argtail->tail;
            }
            cnt++;
            efields = efields->tail;
            fields = fields->tail;
          }

          if(!efields && !fields){
            // call external function to create a record
            return expTy(Tr_recordExp(cnt,arglist),entry);
          } else {
            if(efields)
              EM_error(a->pos,"more record field than declaration");
            else
              EM_error(a->pos,"less record field than declaration");
            return expTy(NULL,Ty_Void());
          }
        }else{
          EM_error(a->pos,"not record type");
          return expTy(NULL,Ty_Void());
        }
      } else {
        EM_error(a->pos,"unknow type, %s record type not defined", 
                        S_name(a->u.record.typ));
        return expTy(NULL,Ty_Void());
      }
      return expTy(NULL,Ty_Void());
    }

    // according to Tiger grammar: return type is the last exp
    case A_seqExp:{
       EM_error(a->pos,"seqExp");
      A_expList exps = a->u.seq;
      /*remark by xdl2007: in case of null seqExp, initial ret to nil type*/
      struct expty ret = expTy(NULL,Ty_Nil());

      while(exps){
        /*normal: return the last exp's type*/
        ret = transExp(venv,tenv,level,lbreak,exps->head);
        exps = exps->tail;
      }
      return ret;
    }

    /*remark by xdl2007: no-value means Ty_Nil() not Ty_Void()*/
    case A_assignExp:{
       EM_error(a->pos,"assignExp");
      struct expty var = transVar(venv,tenv,level,lbreak,a->u.assign.var);
      struct expty exp = transExp(venv,tenv,level,lbreak,a->u.assign.exp);

      // check forvar, may be assigned in exp
      if (a->u.assign.var->kind == A_simpleVar) {
           if(for_index && !strcmp(S_name(a->u.assign.var->u.simple), for_index)){
  				    EM_error(a->pos, "loop variable can't be assigned");
                return expTy(NULL,Ty_Void());
           }
      }

      if(var.ty == exp.ty || 
        (var.ty->kind == Ty_record && exp.ty->kind == Ty_nil)) {
        return expTy(Tr_assignExp(var.exp,exp.exp),Ty_Nil());
      } else {
        EM_error(a->pos,"assignment unmatched type");
        return expTy(NULL,Ty_Void());
      }
    }

    /*
     * accoring to the Tiger grammar:
     * exp1 must be integer exptression
     * exp3 is optional
     * if exp3 not exist, return no-valud
     * if exists, exp2 and exp3 must has the same type
     */

    case A_ifExp:{
     EM_error(a->pos,"ifExp-----------------------------------------------------------");
      EM_error(a->pos,"ifpart---------------------------------------------------");

      struct expty ifexp = transExp(venv,tenv,level,lbreak,a->u.iff.test);
       EM_error(a->pos,"thenpart---------------------------------------------------------");
      struct expty thenexp = transExp(venv,tenv,level,lbreak,a->u.iff.then);
      struct expty elseexp;
      if(ifexp.ty->kind == Ty_int) {
        /* elsee not exists, Note: not nil-exp, but NULL pointer */
        if(a->u.iff.elsee == NULL) {
          if(thenexp.ty->kind != Ty_nil){
            EM_error(a->pos,"error: then is not nil type, has ret value");
            return expTy(NULL,Ty_Void());
          }

          return expTy(Tr_ifExp(ifexp.exp,thenexp.exp,NULL),Ty_Nil());
        } else {
               EM_error(a->pos,"elsepart------------------------------------------------");

          elseexp = transExp(venv,tenv,level,lbreak,a->u.iff.elsee);
            EM_error(a->pos,"elsepart------------------------------------------------");
          Tr_exp exp = Tr_ifExp(ifexp.exp,thenexp.exp,elseexp.exp);
          if(thenexp.ty == elseexp.ty){
            return expTy(exp,thenexp.ty);
          }
          /* don't forget the nil and record brother, which be thought the same*/
          else if(thenexp.ty->kind == Ty_record && elseexp.ty->kind == Ty_nil) {
            return expTy(exp,thenexp.ty);
          } else if(thenexp.ty->kind == Ty_nil && elseexp.ty->kind == Ty_record) {
            return expTy(exp,elseexp.ty);
          } else {
            EM_error(a->pos,"error: types of then-else differ");
            return expTy(NULL,Ty_Void());
          }
        }
      } else {
        EM_error(a->pos,"if test fail, not integer expression");
        return expTy(NULL,Ty_Void());
      }
    }

    /*
     * according to Tiger grammar:
     * exp1 must be integer exp
     * exp2 must produce no value
     * And to process 'break', use loopstack to record every while exp
     * the hard point is to process 'nested break statement'
     */
    case A_whileExp:{
      EM_error(a->pos,"whileExp");
      struct expty test = transExp(venv,tenv,level,lbreak,a->u.whilee.test);
      if(test.ty->kind == Ty_int){
        // 1: track while-expression for break expression: push
        if (loopstack == NULL) {
            loopstack = U_BoolList(TRUE,NULL);
        } else {
            U_boolList tmp = U_BoolList(TRUE,NULL);
            tmp->tail = loopstack;
            loopstack = tmp;
        }
        // the done label must be called here, in order to process by break
        Temp_label ldone = Temp_newlabel();
        struct expty body = transExp(venv,tenv,level,lbreak,a->u.whilee.body);
        
        // 2: pop, loopstack must not NULL
        assert(loopstack);
        loopstack = loopstack->tail;
        if(body.ty->kind != Ty_nil){
          EM_error(a->pos,"body of while not nil type");
          return expTy(NULL,Ty_Void());
        }
        Tr_exp exp = Tr_whileExp(test.exp,body.exp,ldone);
        return expTy(exp,Ty_Nil());
      }else{
        EM_error(a->pos,"test in while not integer type");
        return expTy(NULL,Ty_Void());
      }
    }

    /*
     * according to Tiger grammar:
     * var must be in table, a little completed
     * exp1 and exp2 must be integer exp
     * exp3 must produce no value
     */
    case A_forExp:{
      EM_error(a->pos,"forExp");
      Tr_access access = Tr_allocLocal(level,TRUE);
      S_enter(venv, a->u.forr.var, E_VarEntry(access,Ty_Int()));

      for_index=S_name(a->u.forr.var);
      S_beginScope(venv);
      /*
       * there is another check need to do which is according to tiger grammar
       * 'The variable id is a new variable implicityly declared by the for
       * statement, whose scope covers only exp3, and may not be assigned to'
       * Q: how to check var whether or not be assigned to ?
       * A: use S_symbol type record for var stack, then check in assignExp
       */
      struct expty lo = transExp(venv,tenv,level,lbreak,a->u.forr.lo);
      struct expty hi = transExp(venv,tenv,level,lbreak,a->u.forr.hi);
    
      if(lo.ty->kind != Ty_int){
        EM_error(a->u.forr.lo->pos,"for lo exp is not integer exp");
        return expTy(NULL,Ty_Void());
      }
      if(hi.ty->kind != Ty_int){
        EM_error(a->u.forr.hi->pos,"for hi exp is not integer exp");
        return expTy(NULL,Ty_Void());
      }

      /*do not forget to add variable 'id' before trans body*/

      // 1: track while-expression for break expression: push
      if (loopstack == NULL) {
        loopstack = U_BoolList(TRUE,NULL);
      } else {
        U_boolList tmp = U_BoolList(TRUE,NULL);
        tmp->tail = loopstack;
        loopstack = tmp;
      } 
      EM_error(a->pos,"begin");
      struct expty body = transExp(venv,tenv,level,lbreak,a->u.forr.body);
      EM_error(a->pos,"end!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
      //2: pop
      assert(loopstack);
      //assert(forvar);
      loopstack = loopstack->tail;
      //forvar = forvar->next;

      if(body.ty->kind != Ty_nil){
        EM_error(a->u.forr.body->pos,"for body not nil type");
        return expTy(NULL,Ty_Void());
      }
      S_endScope(venv);
      for_index=NULL;
      // according to WhileExp, done labe must also be created here
      Temp_label ldone = Temp_newlabel();
      Tr_exp exp = Tr_forExp(lo.exp,hi.exp,body.exp, ldone);
      return expTy(exp,Ty_Nil());
    }

    /*
     * according to tiger language reference manual:
     * break expression terminates evaluation of nearest enclosing 
     * while/for expression. A break that is not within a while or 
     * for is illegal.
     * Q: How to check break is in a while or for expression ?
     * A: need a U_BoolList to track nesting while/for expression
     */
    case A_breakExp: {
       EM_error(a->pos,"breakExp");
      if(loopstack == NULL) {
        EM_error(a->pos,"break error, not in while/for expression");
        return expTy(NULL,Ty_Void());
      }
      return expTy(Tr_breakExp(lbreak),Ty_Nil());
    }

    /*
     * only letexp can have decList
     */

    // TODO: need modify when transDec is done.
    case A_letExp:{
        EM_error(a->pos,"letExp");
      // just from textbook
      struct expty exp;
      A_decList dec;
      S_beginScope(venv);
      S_beginScope(tenv);
      for(dec=a->u.let.decs; dec; dec=dec->tail)
        transDec(venv,tenv,level,lbreak,dec->head);
      EM_error(a->pos,"letbody----------------------------------------");
      exp = transExp(venv,tenv,level,lbreak,a->u.let.body);
      S_endScope(tenv);
      S_endScope(venv);
      return exp;
    }

    /*
     * according to Tiger grammar:
     * type-id must be array-type
     * exp1 must be integer type
     * exp2 must same with type-id
     */
    case A_arrayExp:{
       EM_error(a->pos,"arryExp");
      Ty_ty typ = actual_ty(tenv,S_look(tenv,a->u.array.typ));
      if(typ && typ->kind == Ty_array){
        struct expty size = transExp(venv,tenv,level,lbreak,a->u.array.size);
        if(size.ty->kind != Ty_int){
          EM_error(a->pos,"size exp in arrayExp is not integer type");
          return expTy(NULL,Ty_Void());
        }
        struct expty init = transExp(venv,tenv,level,lbreak,a->u.array.init);
        if(init.ty != actual_ty(tenv,typ->u.array)){
          EM_error(a->pos,"init exp in arrayExp is not same with array type");
          return expTy(NULL,Ty_Void());
        }
        /* Note: typ is a actual_ty */
        return expTy(Tr_arrayExp(size.exp,init.exp),typ);
      } else {
        EM_error(a->pos,"array expression not array type");
        return expTy(NULL,Ty_Void());
      }
    }

    default: break;
  }
}

// little complicated
Tr_exp transDec(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_dec d)
{
  // augment env
  switch(d->kind){
    /*
     * (1) first pass: enter function header
     * (2) check same name in mutually recursive functions, test39/48.tig
     * (3) second pass: process body
     * (4) handle function and procedure
     * (5) handle function parameters types
     * (6) handle resultTy and bodyexpty
     */
    case A_functionDec:{
      EM_error(d->pos,"fun dec-------------------------------------");

      // first pass
      A_fundecList function, check = d->u.function;
      Ty_tyList formalsTys;
      Ty_ty resultTy;
      bool samename = FALSE;
      /* Keeping Trace of levels */

      U_boolList escapelist = makeEscapeFormalList(check->head->params);
      Temp_label funame = check->head->name;
      Tr_level newlevel = Tr_newLevel(level,funame,escapelist);
      struct expty bodyty;
      Tr_exp result;

      for(function=d->u.function;function;function=function->tail) {
        if(function->head->result != NULL) {
          resultTy = S_look(tenv,function->head->result);
        } else {
          resultTy = Ty_Nil();
        }
        formalsTys = makeFormalTyList(tenv,function->head->params);
        while(function != check){
          if(strcmp(S_name(function->head->name),S_name(check->head->name))==0){
            samename = TRUE;
            break;
          }
          check = check->tail;
        }
        //check samename
        if(samename){
          EM_error(function->head->pos,"same function name in recursive declaration");
        }
        else{
          S_enter(venv,function->head->name,E_FunEntry(newlevel,funame,formalsTys,resultTy));
        }
      }

      // second pass
      for(function=d->u.function;function;function=function->tail){
        EM_error(d->pos,"the next function ---------------------------------");
        if(function->head->result != NULL){
          resultTy = S_look(tenv,function->head->result);
        }
        else{
          resultTy = Ty_Nil();
        }
        formalsTys = makeFormalTyList(tenv,function->head->params);

        // first: function name
        S_enter(venv,function->head->name,E_FunEntry(newlevel,funame,formalsTys,resultTy));
        S_beginScope(venv);
          // second: formal variable
          A_fieldList l;
          Ty_tyList t;
          for(l=function->head->params,t=formalsTys; l; l=l->tail, t=t->tail){
            S_enter(venv,l->head->name,E_VarEntry(Tr_allocLocal(newlevel,TRUE),t->head));
        }
        bodyty = transExp(venv,tenv,newlevel,lbreak,function->head->body);
        result=Tr_funDec(newlevel,bodyty.exp);
         EM_error(d->pos,"end funbody dec-------------------------------------");
        if(bodyty.ty != resultTy){
          EM_error(function->head->pos,"function return value type error");
        }

        S_endScope(venv);
      }
      EM_error(d->pos,"end fun dec-------------------------------------");
      return result;
    }

    /*
     * if type-id exist, must match with exp-type
     */
    case A_varDec:{
      EM_error(d->pos,"var dec");
      struct expty init = transExp(venv,tenv,level,lbreak,d->u.var.init);
     
      Ty_ty type;
      if(d->u.var.typ != NULL) {
        type = actual_ty(tenv,S_look(tenv,d->u.var.typ));
        //Note: init.ty is also the actual type
        if((init.ty != type) && ((init.ty->kind == Ty_nil) &&
                                (type->kind != Ty_record))){
          EM_error(d->pos,"unmatched var type");
        }
        EM_error(d->pos,"2:");
        Tr_access access = Tr_allocLocal(level,TRUE);
        EM_error(d->pos,"1:");
        S_enter(venv,d->u.var.var,E_VarEntry(access,type));
EM_error(d->pos,"1:");
        return Tr_varDec(access,init.exp);
      } else {
        /*should not be nil*/
EM_error(d->pos,"1:");
        if(init.ty->kind == Ty_nil){
          EM_error(d->pos,"invalid nil");
        }
        Tr_access access = Tr_allocLocal(level,TRUE);
        S_enter(venv,d->u.var.var,E_VarEntry(access,init.ty));
        EM_error(d->pos,"1:");
        return Tr_varDec(access,init.exp);
      }
      assert(0);
    }
      
    /*
     * (1) handle type dec-headers
     * (2) then process the body(or definations)
     * (3) illegal cycles should be detected by the type-checker
     * (4) detect recursive types with same name, e.g test38/47.tig
     */
    case A_typeDec:{
       EM_error(d->pos,"type dec");
      A_nametyList type, check=d->u.type;
      bool samename = FALSE;

      // first pass: enter the header, leave body untouched
      for (type=d->u.type;type;type=type->tail) {
        // addition: same name check in recursive type decs
        check = d->u.type;
        while (type != check) {
          if(strcmp(S_name(type->head->name),S_name(check->head->name)) == 0){
            samename = TRUE;
            break;
          }
          check=check->tail;
        }
        if (samename) {
          EM_error(type->head->ty->pos,"same type name in recursive types");
        } else {
          S_enter(tenv,type->head->name,Ty_Name(type->head->name,NULL));
        }
      }

      // second pass: TransTy(body)
      for(type=d->u.type;type;type=type->tail){
        Ty_ty ty = TransTy(tenv,type->head->ty);

        /*check illegal cycle*/
        if (ty->kind == Ty_name) {
          // actual_ty should not return a Ty_name type, excetp error
          Ty_ty test = actual_ty(tenv,ty);
          if(test == NULL){
            EM_error(type->head->ty->pos,"illgal cycle of type dec");
          } else if(test->kind == Ty_name) {
            // should never go here, would be catch by other check 
            EM_error(type->head->ty->pos,"unclosed recursive type");
          }
        }

        //assert(ty->kind != Ty_name);
        S_enter(tenv,type->head->name,ty);
      }
      return Tr_typeDec();
    }
    default:break;
  }
}

/*
 * translate A_ty to Ty_ty
 * Note: int, string already in tenv, as well as several predefined functions
 */
Ty_ty TransTy(S_table tenv, A_ty a)
{
  switch(a->kind){
    case A_nameTy:
       EM_error(a->pos,"nameTy");
      return Ty_Name(a->u.name,S_look(tenv,a->u.name));
      
   /*
    * Note: here {} is necessary
    */
    case A_recordTy:{
      EM_error(a->pos,"recordTy");
      Ty_fieldList head=NULL,tail,node;
      Ty_ty nodeTy;
      A_fieldList record;
      for(record = a->u.record;record;record=record->tail){
        /*Note: in recursive record dec, nodeTy is Ty_name type*/
        // which is the fake the first pass Ty_ty
        // e.g."Ty_Name(name,NULL)" ref: 560
        // This reality make actual_ty little tricky, ref: 64
        nodeTy = S_look(tenv,record->head->typ);
        if(nodeTy != NULL)
          node = Ty_FieldList(Ty_Field(record->head->name,nodeTy),NULL);
        else{
          EM_error(record->head->pos,"undefined type");
          return Ty_Nil();
        }

        // little ugly, have to record the head
        if(head == NULL) {
          head = node;
          tail = head;
        }else{
          tail->tail = node;
          tail = tail->tail;
        }
      }
      return Ty_Record(head);
    }
    case A_arrayTy:
      EM_error(a->pos,"arrayTy");
      return Ty_Array(S_look(tenv,a->u.array));
    default:break;
  }

  return Ty_Void();
}

/*
 * for a function: params's type is really matter
 */
Ty_tyList makeFormalTyList(S_table tenv, A_fieldList p)
{
  Ty_tyList tail, node, list=NULL;
  for(;p;p=p->tail){
    Ty_ty nodeTy = S_look(tenv,p->head->typ);
    if(nodeTy != NULL){
      node = Ty_TyList(nodeTy,NULL);
    }
    else{
      EM_error(p->head->pos,"undefined type");
      return NULL;
    }
    /*
     * little ugly, have to record the head
     */
    if(list == NULL) {
      list = node;
      tail = list;
    }else{
      tail->tail = node;
      tail = tail->tail;
    }
  }
  return list;
}

/* Treat all parameter escaped */
U_boolList makeEscapeFormalList(A_fieldList p)
{
   EM_error(1,"4444");
    if(p==NULL) return NULL;
    U_boolList list=NULL,pre,cut;

    cut = U_BoolList(TRUE,NULL);
    list = pre = cut;
    while (p->tail) {
       cut = U_BoolList(TRUE,NULL);
       pre->tail = cut;
       pre = cut;
       p = p->tail;
    }
    return list;
}

// a driver
F_fragList SEM_transProg(A_exp exp)
{
 EM_error(1,"19");
  // first: initial two env, one for type, the other for var/func
  S_table tenv, venv;
  string s;

  tenv = E_base_tenv();
  venv = E_base_venv();

  // 'int' 'string'
  S_enter(tenv,S_Symbol(String("int")),Ty_Int());
  S_enter(tenv,S_Symbol(String("string")),Ty_String());
  
  // for 'queen.tig' and 'merge.tig' need add predefined function
  // 'print(s:string)'
  s = String("print");
  Ty_tyList formalsTys = Ty_TyList(Ty_String(),NULL);
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_Nil()));
  // 'flush()'
  s = String("flush");
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),NULL,Ty_Nil()));
  // 'getchar():string'
  s = String("getchar");
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),NULL,Ty_String()));
  // 'ord(s:string) : int'
  s = String("ord");
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_Int()));
  // 'size(s:string):int'
  s = String("size");
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_Int()));
  // 'chr(i:int):string'
  s = String("chr");
  formalsTys = Ty_TyList(Ty_Int(),NULL);
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_String()));
  // 'substring(s:string,first:int,n:int):string'
  s = String("substring");
  formalsTys = Ty_TyList(Ty_String(),Ty_TyList(Ty_Int(),Ty_TyList(Ty_Int(),NULL)));
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_String()));
  // 'not(i:int):int'
  s = String("int");
  formalsTys = Ty_TyList(Ty_Int(),NULL);
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_Int()));
  // 'exit(i:int)'
  s = String("not");
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_Nil()));

  if(exp){
    (void)transExp(venv,tenv,Tr_outermost(),Temp_newlabel(),exp);
  }
   EM_error(1,"19");
  return Tr_getResult();
}

