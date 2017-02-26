/* function prototype from regalloc.c */
/*struct RA_result {Temp_map coloring; AS_instrList il;};
struct RA_result RA_regAlloc(F_frame f, AS_instrList il);*/
typedef struct RA_result_ *RA_result;
struct RA_result_ {Temp_map coloring; AS_instrList il;};
RA_result RA_regAlloc(F_frame f, AS_instrList il);