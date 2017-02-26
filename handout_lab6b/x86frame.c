/*
 * Implementation of frame interface for Intel x86 architecture
 * using Intel® 64 and IA-32 Architectures Software Developer’s Manual
 *
*/
#include "frame.h"

const int F_WORD_SIZE = 4; // Stack grows to lower address (64-bit machine - 8 bytes)
static const int F_K = 6; // Number of parameters kept in registers





struct F_frame_ {
	Temp_label name;
	F_accessList formals;
	int local_count;
	/* instructions required to implement the "view shift" needed */
};

Temp_map F_tempMap = NULL;
static void F_add_to_map(string str, Temp_temp temp)
{
	if (!F_tempMap) {
		F_tempMap = Temp_name();
	}
	Temp_enter(F_tempMap, temp, str);
}


Temp_temp F_EAX(){
  static Temp_temp eax;
  if(eax==NULL){
    eax = Temp_newtemp();
    F_add_to_map("%eax", eax);
  }
  return eax;
}
Temp_temp F_EBX(){
  static Temp_temp ebx;
  if(ebx==NULL){
    ebx = Temp_newtemp();
    F_add_to_map("%ebx", ebx);
  }
  return ebx;
}
Temp_temp F_ECX(){
  static Temp_temp ecx;
  if(ecx==NULL){
    ecx = Temp_newtemp();
    F_add_to_map("%ecx", ecx);
  }
  return ecx;
}
Temp_temp F_EDX(){
  static Temp_temp edx;
  if(edx==NULL){
    edx = Temp_newtemp();
    F_add_to_map("%edx", edx);
  }
  return edx;
}
Temp_temp F_EDI(){
  static Temp_temp edi;
  if(edi==NULL){
    edi = Temp_newtemp();
    F_add_to_map("%edi", edi);
  }
  return edi;
}
Temp_temp F_ESI(){
  static Temp_temp esi;
  if(esi==NULL){
    esi = Temp_newtemp();
    F_add_to_map("%esi", esi);
  }
  return esi;
}
Temp_temp F_EBP(){
  static Temp_temp ebp;
  if(ebp==NULL){
    ebp = Temp_newtemp();
    F_add_to_map("%ebp", ebp);
  }
  return ebp;
}
Temp_temp F_ESP(){
  static Temp_temp esp;
  if(esp==NULL){
    esp = Temp_newtemp();
    F_add_to_map("%esp", esp);
  }
  return esp;
}


static F_access InFrame(int offset);
static F_access InReg(Temp_temp reg);
static F_accessList F_AccessList(F_access head, F_accessList tail);
static F_accessList makeFormalAccessList(F_frame f, U_boolList formals);

/* Make register functions should only be called once (inside one
 * of the temp list register generator functions).
 */
static Temp_tempList F_make_arg_regs(void);
static Temp_tempList F_make_calle_saves(void);
static Temp_tempList F_make_caller_saves(void);

static Temp_tempList F_special_registers(void);
static Temp_tempList F_arg_registers(void);
static Temp_tempList F_callee_saves(void);

static void F_add_to_map(string str, Temp_temp temp);

static F_accessList F_AccessList(F_access head, F_accessList tail)
{
	F_accessList list = checked_malloc(sizeof(*list));
	list->head = head;
	list->tail = tail;
	return list;
}

static F_accessList makeFormalAccessList(F_frame f, U_boolList formals)
{
	U_boolList fmls;
	F_accessList headList = NULL, tailList = NULL;
	int i = 0;
	for (fmls = formals; fmls; fmls = fmls->tail, i++) {
		F_access access = NULL;
		if (i < F_K && !fmls->head) {
			access = InReg(Temp_newtemp());
		} else {
			/* Keep a space for return address space. */
			access = InFrame((2 + i) * F_WORD_SIZE);
		}
		if (headList) {
			tailList->tail = F_AccessList(access, NULL);
			tailList = tailList->tail;
		} else {
			headList = F_AccessList(access, NULL);
			tailList = headList;
		}
	}
	return headList;
}

static F_access InFrame(int offset)
{
	F_access fa = checked_malloc(sizeof(*fa));
	fa->kind = inFrame;
	fa->u.offset = offset;
	return fa;
}

static F_access InReg(Temp_temp reg)
{
	F_access fa = checked_malloc(sizeof(*fa));
	fa->kind = inReg;
	fa->u.reg = reg;
	return fa;
}

static Temp_tempList F_make_arg_regs(void)
{
	/*Temp_temp eax = Temp_newtemp(), ebx = Temp_newtemp(),
		ecx = Temp_newtemp(), edx = Temp_newtemp(), edi = Temp_newtemp(),
		esi = Temp_newtemp();*/
	F_add_to_map("%eax", F_EAX()); F_add_to_map("%ebx", F_EBX()); F_add_to_map("%ecx", F_ECX());
	F_add_to_map("%edx", F_EDX()); F_add_to_map("%edi", F_EDI()); F_add_to_map("%esi", F_ESI());
	return TL(F_EAX(), TL(F_EBX(), TL(F_ECX(), TL(F_EDX(), TL(F_EDI(), TL(F_ESI(), NULL))))));
}

static Temp_tempList F_make_calle_saves(void)
{
	//Temp_temp ebx = Temp_newtemp();
	F_add_to_map("%ebx",  F_EBX());
	return TL(F_SP(), TL(F_FP(), TL(F_EBX(), NULL)));
}

static Temp_tempList F_make_caller_saves(void)
{
	return TL(F_RV(), F_make_arg_regs());
}

static Temp_tempList F_special_registers(void)
{
	static Temp_tempList spregs = NULL;
	if (!spregs) {
		spregs = Temp_TempList(F_SP(), Temp_TempList(F_FP(),
			Temp_TempList(F_RV(), NULL)));
	}
	return spregs;
}

static Temp_tempList F_arg_registers(void)
{
	static Temp_tempList rarg = NULL;
	if (!rarg) {
		rarg = F_make_arg_regs();
	}
	return rarg;
}

static Temp_tempList F_callee_saves(void)
{
	static Temp_tempList callee_saves = NULL;
	if (!callee_saves) {
		callee_saves = F_make_calle_saves();
	}
	return callee_saves;
}

Temp_tempList F_caller_saves(void)
{
	static Temp_tempList caller_saves = NULL;
	if (!caller_saves) {
		caller_saves = F_make_caller_saves();
	}
	return caller_saves;
}

static Temp_tempList callersaves() 
{
	/* assist-function of calldefs() */

	/*Temp_temp ebx = Temp_newtemp(),
			  ecx = Temp_newtemp(),
			  edx = Temp_newtemp(),
			  edi = Temp_newtemp(),
			  esi = Temp_newtemp();*/
	Temp_enter(F_tempMap, F_EBX(), "%ebx");
	Temp_enter(F_tempMap, F_ECX(), "%ecx");
	Temp_enter(F_tempMap, F_EDX(), "%edx");
	Temp_enter(F_tempMap, F_EDI(), "%edi");
	Temp_enter(F_tempMap, F_ESI(), "%esi");
	return TL(F_RV(), TL(F_EBX(), TL(F_ECX(), TL(F_EDX(), TL(F_EDI(), TL(F_ESI(), NULL))))));
}
Temp_tempList F_calldefs() 
{
	/* some registers that may raise side-effect (caller procted, return-val-reg, return-addr-reg) */
	static Temp_tempList protected_regs = NULL;
	return protected_regs ? protected_regs : (protected_regs = callersaves());
}


F_frame F_newFrame(Temp_label name, U_boolList formals)
{
	F_frame f = checked_malloc(sizeof(*f));
	f->name = name;
	f->formals = makeFormalAccessList(f, formals);
	f->local_count = 3;
	return f;
}
 
Temp_label F_name(F_frame f)
{
	return f->name;
}

F_accessList F_formals(F_frame f)
{
	return f->formals;
}

F_access F_allocLocal(F_frame f, bool escape)
{
	f->local_count++;
	if (escape) return InFrame(F_WORD_SIZE * (- f->local_count));
	return InReg(Temp_newtemp());
}

bool F_doesEscape(F_access access)
{
	return (access != NULL && access->kind == inFrame);
}

F_frag F_StringFrag(Temp_label label, string str)
{
	F_frag strfrag = checked_malloc(sizeof(*strfrag));
	strfrag->kind = F_stringFrag;
	strfrag->u.stringg.label = label;
	strfrag->u.stringg.str = str;
	return strfrag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame)
{
	F_frag pfrag = checked_malloc(sizeof(*pfrag));
	pfrag->kind = F_procFrag;
	pfrag->u.proc.body = body;
	pfrag->u.proc.frame = frame;
	return pfrag;
}

F_fragList F_FragList(F_frag head, F_fragList tail)
{
	F_fragList fl = checked_malloc(sizeof(*fl));
	fl->head = head;
	fl->tail = tail;
	return fl;
}

Temp_tempList F_registers(void)
{
	static Temp_tempList registers = NULL;
	if (registers == NULL){
		registers = Temp_TempList(F_EAX(),
			Temp_TempList(F_EBX(),
			Temp_TempList(F_ECX(),
			Temp_TempList(F_EDX(),
			Temp_TempList(F_ESI(),
			Temp_TempList(F_EDI(),
			NULL))))));
	}
	return registers;
}

//static Temp_temp fp = NULL;
Temp_temp F_FP(void)
{
	/*if (!fp) {
		fp = Temp_newtemp();
		F_add_to_map("ebp", fp);
	}
	return fp;*/
	return F_EBP();
}

//static Temp_temp sp = NULL;
Temp_temp F_SP(void)
{
	/*if (!sp) {
		sp = Temp_newtemp();
		F_add_to_map("esp", sp);
	}
	return sp;*/
	return F_ESP();
}

static Temp_temp ra = NULL;
Temp_temp F_RA(void)
{
	if (!ra) {
		ra = Temp_newtemp();
		F_add_to_map("%rdkd", ra);
	}
	return ra;
}

//static Temp_temp rv = NULL;
Temp_temp F_RV(void)
{
	/*if (!rv) {
		rv = Temp_newtemp();
		F_add_to_map("eax", rv);
	}
	return rv;*/
	return F_EAX();
}

T_exp F_Exp(F_access access, T_exp framePtr)
{
	if (access->kind == inFrame) {
		return T_Mem(T_Binop(T_plus, framePtr, T_Const(access->u.offset)));
	} else {
		return T_Temp(access->u.reg);
	}
}

T_exp F_externalCall(string str, T_expList args)
{
	return T_Call(T_Name(Temp_namedlabel(str)), args);
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm)
{
	return stm; // dummy implementation
}

static Temp_tempList returnSink = NULL;
AS_instrList F_procEntryExit2(AS_instrList body)
{
	if (!returnSink) {
		returnSink = TL(F_RA(), F_callee_saves());
	}
	return AS_splice(body, 
		AS_InstrList(AS_Oper("", NULL, returnSink, NULL), NULL));
}

/*AS_proc F_procEntryExit3(F_frame frame, AS_instrList body)
{
	return AS_Proc("prolog", body, "epilog"); // dummy implementation
}*/

Temp_map F_temp2Name(){
  static Temp_map temp2map = NULL;
  if(temp2map==NULL){
    temp2map = Temp_layerMap(Temp_empty(),Temp_name());
	Temp_enter(Temp_name(), F_EAX(), "%eax");
	Temp_enter(Temp_name(), F_EBX(), "%ebx");
	Temp_enter(Temp_name(), F_ECX(), "%ecx");
	Temp_enter(Temp_name(), F_EDX(), "%edx");
	Temp_enter(Temp_name(), F_ESI(), "%esi");
	Temp_enter(Temp_name(), F_EDI(), "%edi");
	Temp_enter(Temp_name(), F_ESP(), "%esp");
	Temp_enter(Temp_name(), F_EBP(), "%ebp");
  }
  return temp2map;
}
Temp_map F_precolored(){
  static Temp_map initial = NULL;
  if(initial==NULL){
    initial = Temp_empty();
    Temp_enter(initial, F_EAX(), "%eax");
    Temp_enter(initial, F_EBX(), "%ebx");
    Temp_enter(initial, F_ECX(), "%ecx");
    Temp_enter(initial, F_EDX(), "%edx");
    Temp_enter(initial, F_ESI(), "%esi");
    Temp_enter(initial, F_EDI(), "%edi");
    Temp_enter(initial, F_EBP(), "%ebp");
    Temp_enter(initial, F_ESP(), "%esp");
  }
  return initial;
}

void AS_instrListAppend(AS_instrList as_instrList1,AS_instrList as_instrList2){
  if(as_instrList1==NULL) return;
  AS_instrList p = as_instrList1;
  while(p->tail!=NULL){p=p->tail;}
  p->tail = as_instrList2;
}

AS_instrList prologue(F_frame f,AS_instrList as_instrList){
  assert(as_instrList&&as_instrList->head->kind==I_LABEL);
  AS_instr as_instr_0 = as_instrList->head;
  as_instrList = as_instrList->tail;
  string instr_1 = string_format("pushl `s0");
  string instr_2 = string_format("movl `s0,`d0");
  string instr_3 = string_format("pushl `s0");
  string instr_4 = string_format("pushl `s0");
  string instr_5 = string_format("pushl `s0");
  string instr_6= string_format("subl $%d,`s0",200);
  AS_instr as_instr_1 = AS_Oper(instr_1,NULL,Temp_TempList(F_EBP(),NULL),NULL);
  AS_instr as_instr_2 = AS_Move(instr_2,Temp_TempList(F_EBP(),NULL),Temp_TempList(F_ESP(),NULL));
  AS_instr as_instr_3 = AS_Oper(instr_3,NULL,Temp_TempList(F_EBX(),NULL),NULL);
  AS_instr as_instr_4 = AS_Oper(instr_4,NULL,Temp_TempList(F_EDI(),NULL),NULL);
   AS_instr as_instr_5 = AS_Oper(instr_5,NULL,Temp_TempList(F_ESI(),NULL),NULL);
  AS_instr as_instr_6 = AS_Oper(instr_6,NULL,Temp_TempList(F_ESP(),NULL),NULL);
  if(f->local_count!=0){
    return AS_InstrList(as_instr_0,
                        AS_InstrList(as_instr_1,
                                     AS_InstrList(as_instr_2,
                                     	 AS_InstrList(as_instr_3,
                                     	 	 AS_InstrList(as_instr_4,
                                     	 	 AS_InstrList(as_instr_5,
                                                  AS_InstrList(as_instr_6,as_instrList)))))));
  }else{
    return AS_InstrList(as_instr_0,
                        AS_InstrList(as_instr_1,
                        	 AS_InstrList(as_instr_2,
                                     	 AS_InstrList(as_instr_3,
                                     	 	 AS_InstrList(as_instr_4,
                                                   AS_InstrList(as_instr_5,as_instrList))))));
  }
}
AS_instrList epilogue(F_frame f,AS_instrList as_instrList){
  assert(as_instrList&&as_instrList->head->kind==I_LABEL);
  string instr_4 = string_format("movl `s0,`d0");
  string instr_5 = string_format("popl `d0");
  string instr_6 = string_format("ret");
  //AS_instr as_instr_3 = AS_Oper("",NULL,F_callee_saves(),NULL);
  AS_instr as_instr_4 = AS_Move(instr_4,Temp_TempList(F_ESP(),NULL),Temp_TempList(F_EBP(),NULL));
  AS_instr as_instr_5 = AS_Oper(instr_5,Temp_TempList(F_EBP(),NULL),NULL,NULL);
  AS_instr as_instr_6 = AS_Oper(instr_6,F_registers(),NULL,NULL);
  AS_instrListAppend(as_instrList,
                    // AS_InstrList(as_instr_3,
                                  AS_InstrList(as_instr_4,
                                               AS_InstrList(as_instr_5,
                                                            AS_InstrList(as_instr_6,NULL))));
  return as_instrList;

}