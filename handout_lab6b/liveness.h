#ifndef TIGER_LIVENESS_H_
#define TIGER_LIVENESS_H_

typedef struct Live_moveList_ *Live_moveList;
typedef struct Live_graph_ *Live_graph;
struct Live_moveList_ {
	G_node src, dst;
	Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

struct Live_graph_  {
	G_graph graph;
	Live_moveList moves;
};
Temp_temp Live_gtemp(G_node n);

Live_graph Live_liveness(G_graph flow);

#endif