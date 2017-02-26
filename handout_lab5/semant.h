/*
 * semantic analysis
 */

#ifndef __SEMANT_H__
#define __SEMANT_H__

#include "absyn.h"
#include "types.h"
#include "translate.h"
#include "errormsg.h"

struct expty {Tr_exp exp; Ty_ty ty;};

struct expty expTy(Tr_exp exp, Ty_ty ty);

// type-checking and translate into intermediate code
struct expty transVar(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_var v);

struct expty transExp(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_exp a);

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList p);

U_boolList makeEscapeFormalList(A_fieldList p);
    
Tr_exp transDec(S_table venv, S_table tenv, Tr_level level, Temp_label lbreak, A_dec d);

Ty_ty TransTy(S_table tenv, A_ty a);

F_fragList SEM_transProg(A_exp exp);

#endif
