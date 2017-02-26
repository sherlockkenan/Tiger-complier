#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "env.h"

/*Lab4: Your implementation of lab4*/

E_enventry E_VarEntry(Tr_access access, Ty_ty ty)
{
  E_enventry entry = checked_malloc(sizeof(*entry));
  entry->kind = E_varEntry;
  entry->u.var.access = access;
  entry->u.var.ty = ty;

  return entry;
}

E_enventry E_FunEntry(Tr_level level, Temp_label label,
                Ty_tyList formals, Ty_ty result)
{
  E_enventry entry = checked_malloc(sizeof(*entry));
  entry->kind = E_funEntry;
  entry->u.fun.level = level;
  entry->u.fun.label = label;
  entry->u.fun.formals = formals;
  entry->u.fun.result = result;

  return entry;
}


S_table E_base_tenv(void){
  S_table s_table = S_empty();
  S_enter(s_table,S_Symbol("nil"),Ty_Nil());
  S_enter(s_table,S_Symbol("int"),Ty_Int());
  S_enter(s_table,S_Symbol("string"),Ty_String());
  S_enter(s_table,S_Symbol("void"),Ty_Void());
  return s_table;
}

S_table E_base_venv(void){
  S_table venv= S_empty();

  string s = String("print");
  Ty_tyList formalsTys = Ty_TyList(Ty_String(),NULL);
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_Void()));
  // 'flush()'
  s = String("flush");
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),NULL,Ty_Void()));
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
  S_enter(venv,S_Symbol(s),E_FunEntry(Tr_outermost(),S_Symbol(s),formalsTys,Ty_Void()));

 return venv;
}
