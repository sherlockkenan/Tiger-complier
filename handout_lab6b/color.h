/*
 * color.h - Data structures and function prototypes for coloring algorithm
 *             to determine register allocation.
 */

/*struct COL_result {Temp_map coloring; Temp_tempList spills;};
struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs);*/
#include "liveness.h"
typedef struct COL_result_ *COL_result;

struct COL_result_ {Temp_map coloring; Temp_tempList spills;};

COL_result COL_color(Live_graph ig, Temp_map initial, Temp_tempList regs);




