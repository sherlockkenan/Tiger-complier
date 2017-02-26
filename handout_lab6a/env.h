/*Lab4: Your implementation of lab4*/
#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "translate.h"


typedef struct E_enventry_ *E_enventry;

// just a wrapper
struct E_enventry_
{
  enum {E_varEntry, E_funEntry} kind;
  union
  {
    struct {Tr_access access; Ty_ty ty;} var;
    struct {Tr_level level; Temp_label label;
            Ty_tyList formals; Ty_ty result;} fun;
  }u;
};

// constructor
E_enventry E_VarEntry(Tr_access access, Ty_ty ty);
E_enventry E_FunEntry(Tr_level level, Temp_label label,
                Ty_tyList formals, Ty_ty result);

// build type-env and var-func-env
S_table E_base_tenv(void); /* Ty_ty environment */
S_table E_base_venv(void); /* E_enventry environment */
