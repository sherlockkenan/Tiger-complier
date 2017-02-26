#include <stdio.h>
#include <string.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"
#include "errormsg.h"

F_fragList gFrags = NULL;

struct Tr_level_ {
   Tr_level parent;
   Temp_label name;
   F_frame frame;
   Tr_accessList formals;
};

struct Tr_access_ { Tr_level level; F_access access; };

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
    Tr_expList ret = checked_malloc(sizeof(*ret));
    ret->head = head;
    ret->tail = tail;
    return ret;
}



/* every time Tr_outermost() will return the same Tr_level */
static Tr_level outer = NULL;
Tr_level Tr_outermost(void) {
	/* the outest level, like global-env */
	if (!outer) outer = Tr_newLevel(NULL, Temp_newlabel(), NULL);
	return outer;
}

Tr_access Tr_makeAccess(Tr_level level, F_access access)
{
    if(access == NULL || level == NULL) return NULL;
    Tr_access ret = checked_malloc(sizeof(*ret));
    ret->level = level;
    ret->access = access;
    return ret;
}

/* must be called after frame is set */
Tr_accessList Tr_makeAccessList(Tr_level level)
{
   if(level == NULL) return NULL;
   assert(level->frame);

   F_accessList formals = F_formals(level->frame);
   /* skip static link */
   formals = formals->tail;

   Tr_accessList list,temp;
   list = checked_malloc(sizeof(*list));
   list->head = NULL;
   list->tail = NULL;
   temp = list;

   while(formals) {
        temp->head = Tr_makeAccess(level, formals->head);
        if(formals->tail)
            temp->tail = checked_malloc(sizeof(*temp->tail));
        else
            temp->tail = NULL;
        formals = formals->tail;
        temp = temp->tail;
   }
   return list;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
   Tr_level level = checked_malloc(sizeof(*level));
   level->parent = parent;
   level->name = name;
   /* add static link */
   level->frame = F_newFrame(name,U_BoolList(TRUE,formals));
   level->formals = Tr_makeAccessList(level);

   return level;
}

Tr_accessList Tr_formals(Tr_level level) 
{
    return level->formals;    
}

Tr_access Tr_allocLocal(Tr_level level, bool escape)
{

  F_frame frame = level->frame;


  F_access f_access = F_allocLocal(frame,escape);

  Tr_access tr_access = checked_malloc(sizeof(*tr_access));
  tr_access->access = f_access;
  tr_access->level = level;
  return tr_access;
}

struct Cx { patchList trues; patchList falses; T_stm stm; };

struct Tr_exp_ {
    enum {Tr_ex, Tr_nx, Tr_cx} kind;
    union {
        T_exp ex;
        T_stm nx;
        struct Cx cx;
    }u;
};

static Tr_exp Tr_Ex(T_exp ex) {
    Tr_exp ret = checked_malloc(sizeof(*ret));
    ret->kind = Tr_ex;
    ret->u.ex = ex;
    return ret;
}

static Tr_exp Tr_Nx(T_stm nx) {
    Tr_exp ret = checked_malloc(sizeof(*ret));
    ret->kind = Tr_nx;
    ret->u.nx = nx;
    return ret;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) {
    Tr_exp ret = checked_malloc(sizeof(*ret));
    ret->kind = Tr_cx;
    ret->u.cx.trues = trues;
    ret->u.cx.falses = falses;
    ret->u.cx.stm = stm;
    return ret;
}

struct patchList_ {Temp_label *head; patchList tail; };
static patchList PatchList(Temp_label *head, patchList tail) {
    patchList ret = checked_malloc(sizeof(*ret));
    ret->head = head;
    ret->tail = tail;
    return ret;
}

static T_exp unEx(Tr_exp e) {

    switch (e->kind) {
        case Tr_ex: return e->u.ex;
        case Tr_nx: return T_Eseq(e->u.nx,T_Const(0));
        case Tr_cx: {
           
            Temp_temp r = Temp_newtemp();
            Temp_label t = Temp_newlabel(), f = Temp_newlabel();
            doPatch(e->u.cx.trues,t);
            doPatch(e->u.cx.falses,f);
            return T_Eseq(T_Move(T_Temp(r),T_Const(1)),
                    T_Eseq(e->u.cx.stm,
                     T_Eseq(T_Label(f),
                      T_Eseq(T_Move(T_Temp(r),T_Const(0)),
                        T_Eseq(T_Label(t),T_Temp(r))))));
        }
       
        assert(0);
    }
      
}

/* TODO: invoke unEx(), right or wrong? */
static T_stm unNx(Tr_exp e) {
    switch(e->kind) {
        case Tr_ex: return T_Exp(e->u.ex);
        case Tr_nx: return e->u.nx;
        case Tr_cx: return T_Exp(unEx(e));
    }
    assert(0);
}

static struct Cx unCx(Tr_exp e) {
    switch(e->kind) {
        case Tr_ex: {
            struct Cx ret;
            ret.trues = NULL;
            ret.falses = NULL;
            ret.stm = T_Exp(e->u.ex);
            return ret;
        }
        /* According to the book should not come here */
        case Tr_nx: break;
        case Tr_cx: return e->u.cx;
    }
    assert(0);
}

void doPatch(patchList tList, Temp_label label) {
    for(; tList; tList = tList->tail)
        *(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second) {
    if(!first) return second;
    for (; first->tail; first=first->tail); /* go to the end of list*/
    first->tail = second;
    return first;
}


Tr_exp Tr_simpleVar(Tr_access acc, Tr_level level) {

    Tr_level defined = acc->level;
    Tr_level used = level;
    T_exp fp = T_Temp(F_FP());


    while(used != defined) {
        fp = T_Mem(fp);
        used = used->parent;
    }

    T_exp var = F_Exp(acc->access, fp);
    return Tr_Ex(var);
}

Tr_exp Tr_fieldVar(Tr_exp record, int index) {
    T_exp exp = T_Binop(T_plus, unEx(record),
                        T_Binop(T_mul, 
                            T_Const(index), T_Const(F_wordSize)));
    return Tr_Ex(exp);
}

Tr_exp Tr_subscriptVar(Tr_exp array, Tr_exp index) {
    T_exp exp = T_Binop(T_plus, unEx(array),
                        T_Binop(T_mul, 
                            unEx(index), T_Const(F_wordSize)));
    return Tr_Ex(exp);
}

Tr_exp Tr_nilExp() {
    return Tr_Ex(T_Const(0));
}

Tr_exp Tr_voidExp(){
    return Tr_Nx(T_Exp(T_Const(0)));
}

Tr_exp Tr_intExp(int val) {
    return Tr_Ex(T_Const(val));
}

Tr_exp Tr_stringExp(string str, Tr_level level) {
    // alloc a new label
    Temp_label lab = F_name(level->frame);
    // build a chain
    gFrags = F_FragList(F_StringFrag(lab,str),gFrags);
    
    // return a NAME not a label
    return Tr_Ex(T_Name(lab));
}


Tr_exp Tr_callExp(Temp_label fun, Tr_level called, Tr_level defined, Tr_expList args) {
    T_expList list = NULL, exps = NULL;

    while(args) {
        exps = T_ExpList(unEx(args->head),NULL);
        if(list == NULL) {
            list = exps;
        } else {
            exps = exps->tail;
        }
        args = args->tail;        
    }


    if(called == defined) {
        // recursive, pass static link of callee function
        list = T_ExpList(T_Mem(T_Temp(F_FP())),list);
    } else {
    
        list = T_ExpList(T_Temp(F_FP()),list);
    }

    return Tr_Ex(T_Call(T_Name(fun),list));
}

Tr_exp Tr_opExp(A_oper op, Tr_exp left, Tr_exp right) {
    bool isbin = FALSE;
    bool isrel = FALSE;

    T_binOp binop;
    T_relOp relop;

    switch(op) {
        case A_plusOp:   binop = T_plus; isbin = TRUE; break;
        case A_minusOp:  binop = T_minus; isbin = TRUE; break;
        case A_timesOp:  binop = T_mul; isbin = TRUE; break;
        case A_divideOp: binop = T_div; isbin = TRUE; break;
        case A_eqOp:     relop = T_eq; isrel = TRUE; break;
        case A_neqOp:    relop = T_ne; isrel = TRUE; break;
        case A_ltOp:     relop = T_lt; isrel = TRUE; break;
        case A_leOp:     relop = T_le; isrel = TRUE; break;
        case A_gtOp:     relop = T_gt; isrel = TRUE; break;
        case A_geOp:     relop = T_ge; isrel = TRUE; break;
        default: break; 
    }

    if(isbin) {
  
        return Tr_Ex(T_Binop(binop,unEx(left),unEx(right)))
        ;
    } else if(isrel) {
         
        // TODO: true and false label all NULL, is it right?
        T_stm stm = T_Cjump(relop,unEx(left),unEx(right),NULL,NULL);
       
        patchList trues = PatchList(&stm->u.CJUMP.true,NULL);
        
        patchList falses = PatchList(&stm->u.CJUMP.false,NULL);
           
        return Tr_Cx(trues,falses,stm);
    }     
    assert(0);
}

Tr_exp Tr_ifExp(Tr_exp ifexp, Tr_exp thenexp, Tr_exp elseexp) {
    // without else branch, the then branch must be a NX type
    // treate ifexp as Tr_CX type    

    struct Cx sifexp = unCx(ifexp);    

    if(elseexp == NULL) {

        Temp_label t = Temp_newlabel(), f = Temp_newlabel();
        doPatch(sifexp.trues,t);
        doPatch(sifexp.falses,f);

        return Tr_Nx(T_Seq(sifexp.stm,
                        T_Seq(T_Label(t),
                            T_Seq(thenexp->u.nx,T_Label(f)))));
    } 
    // with else branch
    else {
        if(thenexp->kind == Tr_ex || elseexp->kind == Tr_ex) {
            // then and else branch all values
            Temp_temp r = Temp_newtemp();
            Temp_label t = Temp_newlabel(), f = Temp_newlabel();
            Temp_label join = Temp_newlabel();

            doPatch(sifexp.trues,t);
            doPatch(sifexp.falses,f);
            T_exp left = unEx(thenexp);
            T_exp right = unEx(elseexp);

            return Tr_Ex(T_Eseq(sifexp.stm,
                            T_Eseq(T_Label(t),
                                T_Eseq(T_Move(T_Temp(r),left),
                                    T_Eseq(T_Jump(T_Name(join),Temp_LabelList(join,NULL)),
                                        T_Eseq(T_Label(f),
                                            T_Eseq(T_Move(T_Temp(r),right),
                                                T_Eseq(T_Label(join),
                                                    T_Temp(r)))))))));

        } else if (thenexp->kind == Tr_nx || elseexp->kind == Tr_nx) {
            // then and else branch all statements
         
            Temp_label t = Temp_newlabel(), f = Temp_newlabel();
            Temp_label join = Temp_newlabel();
            doPatch(sifexp.trues,t);
            doPatch(sifexp.falses,f);
            T_stm left = unNx(thenexp);
            T_stm right = unNx(elseexp);

            return Tr_Nx(T_Seq(sifexp.stm,
                            T_Seq(T_Label(t),
                                T_Seq(left,
                                    T_Seq(T_Jump(T_Name(join),Temp_LabelList(join,NULL)),
                                        T_Seq(T_Label(f),
                                            T_Seq(right,T_Label(join))))))));
        } else {
          
           

            struct Cx sthenexp = unCx(thenexp);
            struct Cx selseexp = unCx(elseexp);

            Temp_label t = Temp_newlabel(), f = Temp_newlabel();
            Temp_label join = Temp_newlabel();

            doPatch(sifexp.trues,t);
            doPatch(sifexp.falses,f);

            doPatch(sthenexp.trues,join);
            doPatch(sthenexp.falses,f);

            doPatch(selseexp.trues,join);
            doPatch(selseexp.falses,join);

            return Tr_Nx(T_Seq(sifexp.stm,
                            T_Seq(T_Label(t),
                                T_Seq(sthenexp.stm,
                                    T_Seq(T_Jump(T_Name(join),Temp_LabelList(join,NULL)),
                                        T_Seq(T_Label(f),
                                            T_Seq(selseexp.stm,T_Label(join))))))));
        }
    }
}

Tr_exp Tr_whileExp(Tr_exp t, Tr_exp b, Temp_label ldone) {
    Temp_label ltest = Temp_newlabel();
    Temp_label lbody = Temp_newlabel();


    T_exp test = unEx(t);
    T_stm body = unNx(b); 

    return Tr_Nx(T_Seq(T_Label(ltest),
                    T_Seq(T_Cjump(T_ne,test,T_Const(0),lbody,ldone),
                        T_Seq(T_Label(lbody),
                            T_Seq(body,
                                T_Seq(T_Jump(T_Name(ltest),Temp_LabelList(ltest,NULL)),T_Label(ldone)))))));
}

Tr_exp Tr_breakExp(Temp_label label) {
    return Tr_Nx(T_Jump(T_Name(label),Temp_LabelList(label,NULL)));
}

Tr_exp Tr_forExp(Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label ldone) {

    Temp_temp  temp = Temp_newtemp();
    Temp_label ltest = Temp_newlabel();
    Temp_label lbody = Temp_newlabel();
    //Temp_label ldone = Temp_newlabel();

    T_exp loexp = unEx(lo);

    T_exp hiexp = unEx(hi);

    T_stm bodystm = unNx(body); // produce no value
  

    return Tr_Nx(T_Seq(T_Move(T_Temp(temp),loexp),
                    T_Seq(T_Label(ltest),
                        T_Seq(T_Cjump(T_lt,T_Temp(temp),hiexp,lbody,ldone),
                            T_Seq(T_Label(lbody),
                                T_Seq(bodystm,
                                    T_Seq(T_Jump(T_Name(ltest),Temp_LabelList(ltest,NULL)),T_Label(ldone))))))));
}

Tr_exp Tr_recordExp(int n/*field cnt, n*W */, Tr_expList fields) {
    // first call external function to alloc n*W words
    T_expList args = T_ExpList(T_Binop(T_mul,T_Const(n),T_Const(F_wordSize)),NULL);
    // TODO: how to call malloc? malloc: run-time library 
    T_exp call = F_externalCall("malloc",args);

    Temp_temp r = Temp_newtemp();
    int count = n;

    T_stm seq = T_Seq(T_Move(T_Temp(r),call),NULL);
    T_stm head = seq, temp;

    while(fields && n) {
        temp = T_Seq(T_Move(T_Mem(T_Binop(T_plus,T_Temp(r),T_Const((count-n)*F_wordSize))),
                            unEx(fields->head)),NULL);
        fields = fields->tail;
        n--;
        seq->u.SEQ.right = temp;
        seq = seq->u.SEQ.right;
    }

    return Tr_Ex(T_Eseq(head,T_Temp(r)));
}

Tr_exp Tr_assignExp(Tr_exp var, Tr_exp val) {
    return Tr_Nx(T_Move(unEx(var),unEx(val)));
}

// same with record, return r, the address
Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init) {
    // first : malloc some memory
    T_expList args0 = T_ExpList(T_Binop(T_mul,unEx(size),T_Const(F_wordSize)),NULL);
    T_exp call0 = F_externalCall("malloc",args0);
    Temp_temp r= Temp_newtemp();

    // second : init array
    T_expList args1 = T_ExpList(T_Binop(T_mul,unEx(size),T_Const(F_wordSize)),
                    T_ExpList(unEx(init),NULL));
    T_exp call1 = F_externalCall("initArray",args1);
    T_stm seq = T_Seq(T_Move(T_Temp(r),call0),T_Exp(call1));

    return Tr_Ex(T_Eseq(seq,T_Temp(r)));
}

// should be a Tr_Nx and actually a MOVE T_stm
Tr_exp Tr_varDec(Tr_access acc, Tr_exp init) {
    // var must be in current frame, so use FP directly
    T_exp var = F_Exp(acc->access, T_Temp(F_FP()));
    T_exp val = unEx(init);
    return Tr_Nx(T_Move(var,val));
}

Tr_exp Tr_funDec(Tr_level level, Tr_exp body) {
    T_stm sbody = unNx(body);

    //TODO: add Move body ot RV

    // build a chain
    gFrags = F_FragList(F_ProcFrag(sbody,level->frame),gFrags);

    return Tr_Ex(T_Const(0));
}

Tr_exp Tr_typeDec() {
    return Tr_Ex(T_Const(0));
}

F_fragList Tr_getResult(void) {
    return gFrags;
}
