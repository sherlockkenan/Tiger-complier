#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "color.h"
#include "liveness.h"
#include "regalloc.h"
#include "table.h"

static int newOffset(TAB_table table,F_frame f,Temp_temp temp);
static Temp_temp getNewTemp(TAB_table table, Temp_temp oldTemp);
static void RewriteProgram(F_frame f,Temp_tempList temp_tempList,AS_instrList il);
static void  delete_sameMoves(Temp_map m,AS_instrList il);


RA_result RA_regAlloc(F_frame f,AS_instrList il){
 // printf("....1\n");
  G_graph g_graph = FG_AssemFlowGraph(il);
  Live_graph live_graph = Live_liveness(g_graph);
  Temp_map initial = Temp_layerMap(Temp_empty(),F_precolored());
  Temp_tempList regs = F_registers();
  COL_result col_result = COL_color(live_graph,initial,regs);
  int i = 0;
  if(col_result->spills!=NULL){
    RewriteProgram(f, col_result->spills, il);
    return RA_regAlloc(f,il);
  }
  RA_result ra_result = checked_malloc(sizeof(*ra_result));
  ra_result->coloring = col_result->coloring;
  delete_sameMoves(ra_result->coloring,il);
  ra_result->il = il;
  return ra_result;
}


static void RewriteProgram(F_frame f,Temp_tempList temp_tempList,AS_instrList il){
	AS_instrList pre = NULL, cur = il;
        TAB_table tempMapOffset = TAB_empty();
	while (cur != NULL){
		AS_instr as_Instr = cur->head;
                Temp_tempList defList = NULL;
                Temp_tempList useList = NULL;
		switch (as_Instr->kind){
		case I_OPER:
                  defList = as_Instr->u.OPER.dst;
                  useList = as_Instr->u.OPER.src;
                  break;
		case I_MOVE:
                  defList = as_Instr->u.MOVE.dst;
                  useList = as_Instr->u.MOVE.src;
                  break;
                default:
                  break;
    }

  if(useList!=NULL||defList!=NULL){
			TAB_table oldMapNew = TAB_empty();
      while (defList != NULL){
        if (inTemp_tempList(defList->head, temp_tempList)){
          assert(pre);
          Temp_temp newTemp = getNewTemp(oldMapNew, defList->head);
          int offset = newOffset(tempMapOffset, f, defList->head);
          string instr = string_format("     movl `s0,%d(`s1)\n", offset);
          AS_instr as_instr = AS_Move(instr,NULL, Temp_TempList(newTemp,Temp_TempList(F_FP(),NULL)));
          cur->tail = AS_InstrList(as_instr, cur->tail);
                                        defList->head = newTemp;
        }
        defList = defList->tail;
      }
			while (useList != NULL){
				if (inTemp_tempList(useList->head, temp_tempList)){
					assert(pre);
					Temp_temp newTemp = getNewTemp(oldMapNew, useList->head);
					int offset = newOffset(tempMapOffset,f,useList->head);
					string instr = string_format("     movl %d(`s0),`d0\n", offset);
					AS_instr as_instr = AS_Move(instr, Temp_TempList(newTemp,NULL),Temp_TempList(F_FP(),NULL));
          useList->head = newTemp;
          pre = pre->tail = AS_InstrList(as_instr,cur);
				}
				useList = useList->tail;
			}
		
   }
      pre = cur;
      cur = cur->tail;
	}
}
static void  delete_sameMoves(Temp_map m,AS_instrList instrlist){
  AS_instrList pre = NULL;
  while(instrlist!=NULL){
    AS_instr as_instr = instrlist->head;
    if(as_instr->kind==I_MOVE&&strcmp(as_instr->u.MOVE.assem,"movl `s0, `d0")==0){
      Temp_tempList dst = as_instr->u.MOVE.dst;
      Temp_tempList src = as_instr->u.MOVE.src;
 
      if(strcmp(Temp_look(m,dst->head),Temp_look(m,src->head))==0){
        assert(pre);
        pre->tail = instrlist->tail;
        instrlist = instrlist->tail;
        continue;
      }
    }
    pre = instrlist;
    instrlist =instrlist->tail;
  }
}


static int newOffset(TAB_table table,F_frame f,Temp_temp temp){
  F_access f_access = TAB_look(table, temp);
  if (f_access == NULL){
    f_access = F_allocLocal(f, TRUE);
    TAB_enter(table, temp, f_access);
  }
  return f_access->u.offset*F_WORD_SIZE;
}
static Temp_temp getNewTemp(TAB_table table, Temp_temp oldTemp){
  Temp_temp newTemp = TAB_look(table, oldTemp);
  if (newTemp == NULL){
    newTemp = Temp_newtemp();
    TAB_enter(table, oldTemp, newTemp);
  }
  return newTemp;
}