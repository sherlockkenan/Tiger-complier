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
//for forexp
string for_index;


F_fragList SEM_transProg(A_exp exp)
{

  S_table tenv, venv;

  tenv = E_base_tenv();
  venv = E_base_venv();


  if(exp){
    (void)transExp(venv,tenv,Tr_outermost(),Temp_newlabel(),exp);
  }
  Tr_stringExp("main",Tr_outermost());
  return Tr_getResult();
}



Ty_ty actual_ty(S_table tenv,Ty_ty ty)
{
  Ty_ty record = ty;
  while (ty && ty->kind == Ty_name) {
    if (ty->u.name.ty) {
      ty = ty->u.name.ty;

      if(ty->kind == Ty_name &&
         strcmp(S_name(record->u.name.sym),S_name(ty->u.name.sym)) == 0){
        return NULL; 
      }
    } else {

      ty = S_look(tenv,ty->u.name.sym); 
      if (ty && ty->kind == Ty_name && ty->u.name.ty == NULL) {

        break;
      }
    }
  }
  return ty;
}

// when enconter a var(l-value), it must be already in venv


// no need break in swith-case
struct expty transExp(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_exp a)
{
    switch(a->kind)
    {
         //EM_error(a->pos,"transExp");
        case A_opExp:
        {

           // EM_error(a->pos,"opExp");
            A_oper oper = a->u.op.oper;
             struct expty left = transExp(venv,tenv,level,lbreak,a->u.op.left);
             struct expty right = transExp(venv,tenv,level,lbreak,a->u.op.right);


             Tr_exp exp = Tr_opExp(oper,left.exp, right.exp);

            if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp)
            {
                if(left.ty->kind != Ty_int)
                {
                     EM_error(a->u.op.left->pos,"integer required");
                      return expTy(NULL, Ty_Int());
                }
                if(right.ty->kind != Ty_int)
                {
                    EM_error(a->u.op.right->pos,"integer required");
                     return expTy(NULL, Ty_Int());
                }
                 return expTy(exp,Ty_Int());
            }
            else if(oper==A_eqOp || oper==A_neqOp){
       
                if((left.ty == right.ty) && (left.ty->kind == Ty_record || left.ty->kind == Ty_int || left.ty->kind == Ty_string || left.ty->kind == Ty_array)) {
        
                        return expTy(exp,Ty_Int()); // should return 0/1 (integer type)
                }else{
                     /* consider the nil and record types */
       
                    if((left.ty->kind == Ty_nil && right.ty->kind == Ty_record) ||(left.ty->kind == Ty_record && right.ty->kind == Ty_nil))
                        return expTy(exp,Ty_Int()); // should return 0/1 (integer type)
                }
     
            }else if(oper==A_ltOp || oper==A_leOp || oper==A_gtOp || oper==A_geOp){
                if((left.ty == right.ty) && (left.ty->kind == Ty_int  || left.ty->kind == Ty_string)){
                        return expTy(exp,Ty_Int()); // should return 0/1 (integer type)
                }
            } 
           
            EM_error(a->pos,"same type required");
            return expTy(NULL,Ty_Void());
        }




        case A_whileExp:{

        // EM_error(a->pos,"whileExp");
           struct expty test = transExp(venv,tenv,level,lbreak,a->u.whilee.test);
          Temp_label ldone = Temp_newlabel();
          // EM_error(a->pos,"whilebody");
        struct expty body = transExp(venv,tenv,level,lbreak,a->u.whilee.body);


        Tr_exp exp = Tr_whileExp(test.exp,body.exp,ldone);
   // something wrong
            if(body.ty->kind == Ty_int) {
               EM_error(a->u.whilee.body->pos, "while body must produce no value");
            }

            return expTy(exp, Ty_Void());
        }


        case A_forExp:{
           // EM_error(a->pos,"forExp");

            struct expty lo = transExp(venv,tenv,level,lbreak,a->u.forr.lo);
            struct expty hi = transExp(venv,tenv,level,lbreak,a->u.forr.hi);

            if(hi.ty->kind != Ty_int) {
               EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
            }
            Tr_access access = Tr_allocLocal(level,TRUE);
            S_enter(venv, a->u.forr.var, E_VarEntry(access,Ty_Int()));

            S_beginScope(venv);

            for_index=S_name(a->u.forr.var);
            struct expty body = transExp(venv,tenv,level,lbreak,a->u.forr.body);
            for_index=NULL;
            S_endScope(venv);
     
           // according to WhileExp, done labe must also be created here
           Temp_label ldone = Temp_newlabel();
           Tr_exp exp = Tr_forExp(lo.exp,hi.exp,body.exp, ldone);
           return expTy(exp,Ty_Void());      
            
        }


        case A_varExp:{
          //  EM_error(a->pos,"varExp");
            return transVar(venv,tenv,level,lbreak,a->u.var); 

        }

        case A_nilExp:{
         //EM_error(a->pos,"nilExp");
            return expTy(Tr_nilExp() ,Ty_Nil());
            
        }

        case A_intExp:{
        // EM_error(a->pos,"intExp");
             return expTy(Tr_intExp(a->u.intt),Ty_Int());
         }

        case A_stringExp:{
          //EM_error(a->pos,"stringExp");
            return expTy(Tr_stringExp(a->u.stringg,level),Ty_String()); 
            
        }

        case A_callExp:{
            //
           // EM_error(a->pos,"callExp");

           
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
                    EM_error(explist->head->pos,"para type mismatch");
         
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


        case A_recordExp:{

        	//EM_error(a->pos,"recordExp");

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

        case A_seqExp:{

           // EM_error(a->pos,"seqExp");
            A_expList list = a->u.seq;

             struct expty ret = expTy(NULL, Ty_Void());
            if (!list) {
            	//EM_error(a->pos,"debug");
                 return expTy(Tr_voidExp(), Ty_Void());
            }
            while (list->tail) {
            	 //EM_error(a->pos,"debug");
                ret = transExp(venv,tenv,level,lbreak,list->head);
                list = list->tail;
            }

           ret = transExp(venv,tenv,level,lbreak,list->head);

            return ret;


        }

        case A_assignExp:{
        // EM_error(a->pos,"assign Exp");

              struct expty var = transVar(venv,tenv,level,lbreak,a->u.assign.var);
              struct expty exp = transExp(venv,tenv,level,lbreak,a->u.assign.exp);
               // EM_error(a->pos,"%s",S_name(a->u.assign.var->u.simple));
            if(a->u.assign.var->kind == A_simpleVar) {
                //EM_error(a->pos,"%s",S_name(a->u.assign.var->u.simple));
                if(for_index && !strcmp(S_name(a->u.assign.var->u.simple), for_index)){
                    EM_error(a->pos, "loop variable can't be assigned");
                    return expTy(NULL, Ty_Void());
                }
            }
           
            if(actual_ty(tenv,var.ty)->kind== actual_ty(tenv,exp.ty)->kind || (var.ty->kind == Ty_record && exp.ty->kind == Ty_nil)){
                   return expTy(Tr_assignExp(var.exp,exp.exp),Ty_Nil());
            } else {
                EM_error(a->pos,"nmatched assign exp");
                return expTy(NULL,Ty_Void());
            }
           
          
            
        }


        case A_ifExp:{
         //  EM_error(a->pos,"if Exp");

            struct expty ifexp = transExp(venv,tenv,level,lbreak,a->u.iff.test);
          // EM_error(a->pos,"then Exp");
            struct expty thenexp = transExp(venv,tenv,level,lbreak,a->u.iff.then);
          // EM_error(a->pos,"else Exp");
            struct expty elseexp;
            if(ifexp.ty->kind == Ty_int) {
              /* elsee not exists, Note: not nil-exp, but NULL pointer */

                if(a->u.iff.elsee ==NULL) {
                    //if(thenexp.ty->kind == Ty_nil){
                      //  EM_error(a->pos,"if-then exp's body must produce no value");
                        //return expTy(NULL,Ty_Void());
                    //}

                   // EM_error(a->pos,"else Exp not exist");
                    return expTy(Tr_ifExp(ifexp.exp,thenexp.exp,NULL),Ty_Void());
                } else {
             
                 // EM_error(a->pos,"else Exp exist");
                    elseexp = transExp(venv,tenv,level,lbreak,a->u.iff.elsee);
           
                    Tr_exp exp = Tr_ifExp(ifexp.exp,thenexp.exp,elseexp.exp);
           
                    if(thenexp.ty == elseexp.ty){
          
                        return expTy(exp,thenexp.ty);
                    }
               /* don't forget the nil and record brother, which be thought the same*/
                    else if(thenexp.ty->kind == Ty_record && elseexp.ty->kind == Ty_nil) {
                    	//EM_error(a->pos,"then is record , else is nil");
                        return expTy(exp,thenexp.ty);
                    } else if(thenexp.ty->kind == Ty_nil && elseexp.ty->kind == Ty_record) {
                            return expTy(exp,elseexp.ty);
                        } else {
                            EM_error(a->pos,"then exp and else exp type mismatched");
                            return expTy(NULL,Ty_Void());
                        }
                }
            } else {
                    EM_error(a->pos,"if test fail, not integer expression");
                    return expTy(NULL,Ty_Void());
            }

        } 

        case A_breakExp:{
        // EM_error(a->pos,"breakExp");
            return expTy(Tr_breakExp(lbreak),Ty_Void());
        }

        case A_letExp:{
       //  EM_error(a->pos,"letExp");
            struct expty exp;
            A_decList d;
            S_beginScope(venv);
            S_beginScope(tenv);
            for(d=a->u.let.decs;d;d=d->tail){
               transDec(venv,tenv,level,lbreak,d->head);
            }
         // EM_error(a->pos, "let body--------------------------------------");
            exp = transExp(venv,tenv,level,lbreak,a->u.let.body);
          //EM_error(a->pos, "let in");
            S_endScope(tenv);
            S_endScope(venv);

            return exp;

        }

    case A_arrayExp:{
    	  //EM_error(a->pos,"array Exp");
      
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
  return expTy(Tr_nilExp() ,Ty_Nil());
}

// little complicated
Tr_exp transDec(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_dec d)
{
  // augment env
  switch(d->kind){
 
    case A_functionDec:{
     
    //  EM_error(d->pos,"function Dec");
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
          resultTy = Ty_Void();
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
       
        if(function->head->result != NULL){
          resultTy = S_look(tenv,function->head->result);
        }
        else{
          resultTy = Ty_Void();;
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
        
        if(bodyty.ty != resultTy){
          EM_error(function->head->pos,"function return value type error");
        }

        S_endScope(venv);
      }

      return result;
    }

    case A_varDec:{
    	  //EM_error(d->pos,"var Dec");

      struct expty init = transExp(venv,tenv,level,lbreak,d->u.var.init);
     
      Ty_ty type;
      if(d->u.var.typ != NULL) {
        type = actual_ty(tenv,S_look(tenv,d->u.var.typ));
        //Note: init.ty is also the actual type
        if((init.ty != type) && ((init.ty->kind == Ty_nil) &&
                                (type->kind != Ty_record))){
          EM_error(d->pos,"unmatched var type");
        }
    
        Tr_access access = Tr_allocLocal(level,TRUE);
   
        S_enter(venv,d->u.var.var,E_VarEntry(access,type));

        return Tr_varDec(access,init.exp);
      } else {
        /*should not be nil*/

        if(init.ty->kind == Ty_nil){
          EM_error(d->pos,"invalid nil");
        }
        Tr_access access = Tr_allocLocal(level,TRUE);
        S_enter(venv,d->u.var.var,E_VarEntry(access,init.ty));

        return Tr_varDec(access,init.exp);
      }
      assert(0);
    }
      
   
    case A_typeDec:{
    	//  EM_error(d->pos,"type Dec");
      
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

struct expty transVar(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_var v)
{
  switch(v->kind)
  {
    case A_simpleVar:{
   
      E_enventry entry= S_look(venv,v->u.simple);
     
      if(entry && entry->kind == E_varEntry) {
        Tr_exp var = Tr_simpleVar(entry->u.var.access,level);

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


Ty_ty TransTy(S_table tenv, A_ty a)
{
  switch(a->kind){
    case A_nameTy:
   
      return Ty_Name(a->u.name,S_look(tenv,a->u.name));
      
   /*
    * Note: here {} is necessary
    */
    case A_recordTy:{

      Ty_fieldList head=NULL,tail,node;
      Ty_ty nodeTy;
      A_fieldList record;
      for(record = a->u.record;record;record=record->tail){
     
        nodeTy = S_look(tenv,record->head->typ);
        if(nodeTy != NULL)
          node = Ty_FieldList(Ty_Field(record->head->name,nodeTy),NULL);
        else{
    
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
 
      return Ty_Array(S_look(tenv,a->u.array));
    default:break;
  }

  return Ty_Void();
}


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




