#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"
#include "assem.h"
#include "printtree.h"

//extern Temp_map F_tempMap;
static F_frame  Co_frame = NULL; /* current function frame */

static void emit(AS_instr);
static Temp_temp munchExp(T_exp);
static void munchStm(T_stm);
static Temp_tempList munchArgs(int, T_expList);

#define MATCH_OP(I, Op, Sign) \
	switch (I) { \
		case T_plus: Op = "addl"; Sign = "+"; break; \
		case T_minus: Op = "subl"; Sign = "-"; break; \
		case T_mul: Op = "imull"; Sign = "*"; break; \
		case T_div: Op = "idivl"; Sign = "/"; break; \
		default : assert( 0 && "invalid Oper"); \
	} "for short ';'" 

#define WRITE_ASM_STR(Str, Arg) \
	sprintf(assem_string, Str, Arg); \
p2asm_str = String(assem_string)

#define WRITE_ASM_STR2(Str, A1, A2) \
	sprintf(assem_string, Str, A1, A2); \
p2asm_str = String(assem_string)

#define WRITE_ASM_STR3(Str, A1, A2, A3) \
	sprintf(assem_string, Str, A1, A2, A3); \
p2asm_str = String(assem_string)

static Temp_temp munchExp(T_exp e)
{
	char assem_string[100];
	string p2asm_str;
	Temp_temp r = Temp_newtemp(); /* return value */

    switch (e->kind) {
        case T_BINOP: 
        {
            char * op = NULL, * sign = NULL;
            T_exp left = e->u.BINOP.left, right = e->u.BINOP.right;
            MATCH_OP(e->u.BINOP.op, op, sign);
          //idivl r2 ,r
            if(e->u.BINOP.op==T_div){
                r=munchExp(e->u.BINOP.left);
                Temp_temp r2=munchExp(e->u.BINOP.right);
                //push %edx
                emit(AS_Oper(String("pushl `s0"), NULL, TL(F_EDX(), NULL), NULL));
                //push %eax
                emit(AS_Oper(String("pushl `s0"), NULL, TL(F_RV(), NULL), NULL));
                //movl r ,%eax
                emit(AS_Oper(String("movl `s0, `d0"),TL(F_RV(),NULL),TL(r,NULL),NULL));
                //movl $0,%edx
                emit(AS_Oper(String("movl $0, `d0"),TL(F_EDX(),NULL),TL(r,NULL),NULL));
                //push r2
                emit(AS_Oper(String("pushl `s0"), NULL, TL(r2, NULL), NULL));
                //idivl (%esp)
                emit(AS_Oper(String("idivl (`s0)"),TL(F_RV(),NULL),TL(F_SP(),NULL),NULL));
                //movl %eax r
                emit(AS_Oper(String("movl `s0, `d0"),TL(r,NULL),TL(F_RV(),NULL),NULL));
                //popl r2
                emit(AS_Oper(String("popl `d0"),TL(r2,NULL),NULL,NULL));
                //popl %eax
                emit(AS_Oper(String("popl `d0"),TL(F_RV(),NULL),NULL,NULL));
                //popl %edx
                emit(AS_Oper(String("popl `d0"),TL(F_EDX(),NULL),NULL,NULL));
                 
                return r;

            }
			
			if (e->u.BINOP.right->kind == T_CONST) { /* BINOP(op, e, CONST) */
                //for %ebp, e should not change
                emit(AS_Move(String ("movl `s0, `d0"), TL(r, NULL), TL(munchExp(left),NULL)));
                WRITE_ASM_STR2("%s $%d, `d0", op,e->u.BINOP.right->u.CONST);   
                emit(AS_Oper(p2asm_str,TL(r,NULL),TL(r,NULL),NULL));
            } else if (left->kind == T_CONST) { /* BINOP(op, CONST, e) */
                WRITE_ASM_STR("movl $%d,`d0",e->u.BINOP.left->u.CONST);
                emit(AS_Move(p2asm_str, TL(r, NULL), NULL));
				WRITE_ASM_STR("%s `s0, `d0", op);	
                emit(AS_Oper(p2asm_str, TL(r,NULL),TL(munchExp(e->u.BINOP.right),TL(r,NULL)), NULL));
            
            } else { /* BINOP(op, e, e) */
                WRITE_ASM_STR("%s `s0, `d0", op);
                r= munchExp(e->u.BINOP.left);
                emit(AS_Oper(p2asm_str,TL(r,NULL),TL(munchExp(e->u.BINOP.right),TL(r,NULL)),NULL));
                //emit(AS_Oper(p2asm_str, TL(r = munchExp(right), NULL), TL(munchExp(left), NULL), NULL));
            }
            return r;
		}
		case T_MEM: 
        {
            T_exp mem = e->u.MEM;
            if (mem->kind == T_BINOP && mem->u.BINOP.op == T_plus) {
                T_exp left = mem->u.BINOP.left, right = mem->u.BINOP.right;
                if (left->kind == T_CONST) { /* MEM(BINOP(+, CONST, e)) */
                    WRITE_ASM_STR("movl %d(`s0), `d0", left->u.CONST);
                    emit(AS_Move(p2asm_str, TL(r, NULL), TL(munchExp(right), NULL)));
                } else if (right->kind == T_CONST) { /**/ //T_MEM(T_BINOP(+,T_CONST d,e1))
                    WRITE_ASM_STR("movl %d(`s0), `d0", right->u.CONST);
                    emit(AS_Move(p2asm_str, TL(r, NULL), TL(munchExp(left), NULL)));
                } else {//??? //T_MEM(T_BINOP(+,e1,e2))
                    T_exp e1 = e->u.MEM->u.BINOP.left;
                    Temp_temp temp_temp_t1 = munchExp(e1);
                    T_exp e2 = e->u.MEM->u.BINOP.right;
                    string instr = string_format("addl `s0,`d0\n");
                    emit(AS_Oper(instr,TL(temp_temp_t1,NULL),TL(munchExp(e2),TL(temp_temp_t1,NULL)),NULL));
                    instr = string_format("movl (`s0),`d0\n");
                    emit(AS_Move(instr,TL(r,NULL),TL(temp_temp_t1,NULL)));
                }
            } else if (mem->kind == T_CONST) { /* MEM(CONST) */
                WRITE_ASM_STR("movl ($0x%x), `d0", mem->u.CONST);
                emit(AS_Move(p2asm_str, TL(r, NULL), NULL));
            } else { /* MEM(e) */
                emit(AS_Move(String("movl (`s0), `d0"), TL(r, NULL), TL(munchExp(mem->u.MEM), NULL)));
            }
            return r;
        }
        case T_TEMP: return e->u.TEMP;
		case T_ESEQ: munchStm(e->u.ESEQ.stm); return munchExp(e->u.ESEQ.exp);
		case T_NAME: Temp_enter(F_tempMap, r, Temp_labelstring(e->u.NAME)); return r;
		case T_CONST: 
        {
            WRITE_ASM_STR("movl $0x%x, `d0", e->u.CONST);
            emit(AS_Move(p2asm_str, TL(r, NULL), NULL));
            return r;
        }
        case T_CALL: 
        {
            r = munchExp(e->u.CALL.fun);
            emit(AS_Oper(String("pushl `s0"), NULL, TL(F_RV(), NULL), NULL));
            emit(AS_Oper(String("pushl `s0"), NULL, TL(F_ECX(), NULL), NULL));
             emit(AS_Oper(String("pushl `s0"), NULL, TL(F_EDX(), NULL), NULL));
             
            int arg_size=0;
            emit(AS_Oper(String("call `s0"), F_calldefs(), TL(r, munchArgs(0, e->u.CALL.args)), NULL));
             T_expList arg=e->u.CALL.args;
            while(arg){
                arg_size++;
                arg=arg->tail;
            }
            WRITE_ASM_STR("addl $%d, `d0", arg_size*4);
            emit(AS_Oper(p2asm_str,TL(F_SP(),NULL),TL(F_SP(),NULL), NULL));
            emit(AS_Oper(String("popl `d0"),TL(F_EDX(),NULL),NULL,NULL));
            emit(AS_Oper(String("popl `d0"),TL(F_ECX(),NULL),NULL,NULL));
           
			return r; /* return value unsure */
        }
		default: assert(0 && "invalid T_exp");
	}
}


#define ASSEM_MOVE_MEM_PLUS(Dst, Src, Constt) \
	T_exp e1 = Dst, e2 = Src; \
    int constt = Constt; \
    sprintf(assem_string, "movl `s0, %d(`s1)", constt); \
    p2asm_str = String(assem_string); \
    emit(AS_Move(p2asm_str, NULL, TL(munchExp(e2), TL(munchExp(e1), NULL))))

#define MATCH_CMP(I, Op) \
	switch (I) { \
		case T_eq: Op = "je"; break; \
		case T_ne: Op = "jne"; break; \
		case T_lt: Op = "jl"; break; \
		case T_gt: Op = "jg"; break; \
		case T_le: Op = "jle"; break; \
		case T_ge: Op = "jge"; break; \
		default: assert(0 && "Invalid CMP SIGN"); \
	} \
"for short ';'"

static void munchStm(T_stm s)
{
	char assem_string[100];
	string p2asm_str;

	switch (s->kind) {
		case T_MOVE:
        {
            T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;
            if (dst->kind == T_MEM) {
                if (dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus&&dst->u.MEM->u.BINOP.right->kind == T_CONST) {
                     /* MOVE (MEM(BINOP(+, e, CONST)), e) */
                        ASSEM_MOVE_MEM_PLUS(dst->u.MEM->u.BINOP.left, src, dst->u.MEM->u.BINOP.right->u.CONST);	
                } else if (dst->u.MEM->kind == T_BINOP && dst->u.MEM->u.BINOP.op == T_plus&&dst->u.MEM->u.BINOP.left->kind == T_CONST) { 
                     /* MOVE (MEM(BINOP(+, CONST, e)), e) */
                        ASSEM_MOVE_MEM_PLUS(dst->u.MEM->u.BINOP.right, src, dst->u.MEM->u.BINOP.left->u.CONST);			
                } else if (dst->u.MEM->kind == T_CONST) { /* MOVE(MEM(CONST), e) */
                    WRITE_ASM_STR("movl `s0, (%d)", dst->u.MEM->u.CONST);
                    emit(AS_Move(p2asm_str, NULL, TL(munchExp(src), NULL)));
                } else if (src->kind == T_MEM) { /* MOVE(MEM(e), MEM(e)) */

                    Temp_temp src_result=Temp_newtemp();
                    emit(AS_Move("movl (`s0), `d0", TL(src_result, NULL), TL(munchExp(src->u.MEM), NULL)));

                    emit(AS_Move("movl `s1, (`s0)", NULL, TL(munchExp(dst->u.MEM), TL(src_result, NULL))));
                } else { 
                /* MOVE(MEM(e), e) */
                    if(src->kind==T_CALL){
                       munchExp(src);
                       emit(AS_Move(String("movl `s1, (`s0)"),  NULL, TL(munchExp(dst->u.MEM),TL(F_RV(), NULL))));
                    }else
                        emit(AS_Move(String("movl `s1, (`s0)"), NULL, TL(munchExp(dst->u.MEM), TL(munchExp(src), NULL))));
                }	
            } else if(dst->kind == T_TEMP) { /* MOVE(TEMP(e), e) */

                //for call function
                if(src->kind==T_CALL){
                    munchExp(src);
                    emit(AS_Move(String("movl `s0, `d0"), TL(munchExp(dst), NULL), TL(F_RV(), NULL)));
                    emit(AS_Oper(String("popl `d0"),TL(F_RV(),NULL),NULL,NULL));
                }else if (src->kind==T_NAME){ //for string ,should add $
                    string label = Temp_look(F_tempMap, munchExp(src));
                    string str= string_format("movl $%s,`d0",label);
                    emit(AS_Move(str, TL(munchExp(dst), NULL), NULL));	
                }else {
                    emit(AS_Move(String("movl `s0, `d0"), TL(munchExp(dst), NULL), TL(munchExp(src), NULL)));
                }
            } else assert(0 && "MOVE dst error");
            break;
        }
		case T_SEQ: munchStm(s->u.SEQ.left); munchStm(s->u.SEQ.right); break;
		case T_LABEL: 
        {
            WRITE_ASM_STR("%s", Temp_labelstring(s->u.LABEL));
            emit(AS_Label(p2asm_str, s->u.LABEL)); 
            break;
        }
		case T_JUMP: 
        {
            Temp_temp r = munchExp(s->u.JUMP.exp);
            emit(AS_Oper(String("jmp `d0"), TL(r, NULL), NULL, AS_Targets(s->u.JUMP.jumps)));
            break;
        }
		case T_CJUMP: 
        {
            char * cmp;
            Temp_temp left = munchExp(s->u.CJUMP.left), right = munchExp(s->u.CJUMP.right);
            emit(AS_Oper(String("cmp `s0, `s1"), NULL, TL(right, TL(left, NULL)), NULL));
            MATCH_CMP(s->u.CJUMP.op, cmp);	
            WRITE_ASM_STR("%s `j0", cmp);
            emit(AS_Oper(p2asm_str, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
            break;	
        }
		case T_EXP: munchExp(s->u.EXP); break;
		default: assert("Invalid T_stm" && 0);
	}
}

static string reg_names[] = {"eax", "ebx", "ecx", "edx", "edi", "esi"}; 
static int    reg_count = 0;
static Temp_tempList munchArgs(int i, T_expList args/*, F_accessList formals*/) 
{
	/* pass params to function
	 * actually use all push stack, no reg pass paras
	 */

	/* get args register-list */
	if (!args) return NULL;

	Temp_tempList tlist = munchArgs(i + 1, args->tail);
	Temp_temp rarg = munchExp(args->head);
	char assem_string[100];
	string p2asm_str;
    if(args->head->kind==T_NAME){
        emit(AS_Oper(String("pushl $`s0"), NULL, TL(rarg, NULL), NULL));
    }else 
	     emit(AS_Oper(String("pushl `s0"), NULL, TL(rarg, NULL), NULL));	
	return (rarg, tlist);
}

static AS_instrList instrList = NULL, last = NULL;
static void emit (AS_instr instr) {
	if (!instrList) {
		instrList = AS_InstrList(instr, NULL);
		last = instrList;
	} else {
		last->tail = AS_InstrList(instr, NULL);
		last = last->tail;
	}
}

AS_instrList F_codegen(F_frame f, T_stmList s)
{
    /* interface */
    AS_instrList al = NULL;
    T_stmList sl    = s;
    Co_frame = f;
    for (; sl; sl = sl->tail) {
        munchStm(sl->head);
    }
    al = instrList;
    al=prologue(f,al);
    instrList = last = NULL;
    return al;
}
