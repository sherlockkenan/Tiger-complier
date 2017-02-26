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
#include "table.h"
typedef struct G_node_color_ *G_node_color;
typedef struct G_node_color_list_ *G_node_color_list;
typedef struct Live_moveList_colornode_ *Live_moveList_colornode;
typedef struct Live_moveList_color_ *Live_moveList_color;
typedef struct Stringlist_ *Stringlist;
typedef enum { PRECOLORED, SIMPLIFYWORKLIST, FREEZEWORKLIST, SPILLWORKLIST, SPILLEDNODES, COALESCEDNODES, COLOREDNODES, SELECTSTACK,DEFAULT1 } KIND1;
typedef enum{ COALESCEDMOVES, CONSTRAINTMOVES, FROZENMOVES, WORKLISTMOVES, ACTIVEMOVES ,DEFAULT2}KIND2;
struct G_node_color_{
	G_node node;
	KIND1 kind;
};

struct G_node_color_list_{
  G_node_color value;
  G_node_color_list pre;
  G_node_color_list next;
  
};

struct Live_moveList_colornode_{
	Live_moveList move;
	KIND2 kind;
};

struct Live_moveList_color_{
	Live_moveList_colornode value;
	 Live_moveList_color pre;
	 Live_moveList_color next;
};

struct Stringlist_{
	string node;
	Stringlist pre;
	Stringlist next;
};

static G_node_color_list precolored = NULL;
static G_node_color_list simplifyWorklist = NULL;
static G_node_color_list freezeWorklist = NULL;
static G_node_color_list spillWorklist = NULL;
static G_node_color_list spilledNodes  = NULL;
static G_node_color_list coalescedNodes = NULL;
static G_node_color_list coloredNodes = NULL;
static G_node_color_list selectStack = NULL;

static Live_moveList_color coalescedMoves = NULL;
static Live_moveList_color constraintMoves = NULL;
static Live_moveList_color frozenMoves = NULL;
static Live_moveList_color worklistMoves = NULL;
static Live_moveList_color activeMoves = NULL;

static int length;
static int K;
static int* degree = NULL;
static G_node_color_list* adjList = NULL;
static bool* adjSet = NULL;
static TAB_table moveList = NULL;
static TAB_table alias = NULL;
static Temp_map color = NULL;
static TAB_table G_nodeMapG_node_color = NULL;
static Temp_tempList registers = NULL;

void init(int n, Temp_map inital,Temp_tempList regs);
G_node_color g_node_color(G_node node);
G_node_color_list g_node_color_list(G_node_color node,G_node_color_list pre,G_node_color_list next);
Live_moveList_colornode live_moveList_colornode(Live_moveList move);
Live_moveList_color live_moveList_color(Live_moveList_colornode value, Live_moveList_color pre, Live_moveList_color next);
static bool isEmpty(void* set);

static bool isContain_node(G_node_color_list*,G_node_color);
static bool isContain_movelist(Live_moveList_color*,Live_moveList_colornode);
static G_node_color_list unionSet_node(G_node_color_list set1_,G_node_color_list set2_);
static Live_moveList_color unionSet_movelist(Live_moveList_color set1_, Live_moveList_color set2_);
static void append_node(G_node_color_list* set,G_node_color node);
static void append_movelist(Live_moveList_color* set, Live_moveList_colornode node);
static G_node_color_list diffSet_node(G_node_color_list set1_,G_node_color_list set2_);
static Live_moveList_color interSet_movelist(Live_moveList_color set1, Live_moveList_color set2);
static void delete_node(G_node_color_list* set_, G_node_color node);
static void delete_movelist(Live_moveList_color* set_, Live_moveList_colornode node);
static void delete_string(Stringlist * set_, string node);
static G_node_color peek_node(G_node_color_list* set);
static G_node_color pop_node(G_node_color_list* stack);
static Live_moveList_colornode peek_movelist(Live_moveList_color* set);
static void push(G_node_color_list* stack, G_node_color node);
static bool isLink(int m, int n);

static void addEdge_(int m,int n);
static void addEdge(G_node_color node1, G_node_color node2);
static Live_moveList_color NodeMoves(G_node_color node);
static bool moveRelated(G_node_color node);
static void makeWorklist(G_node_color_list initial);
static G_node_color_list adjacent(G_node_color node);
static void enableMoves(G_node_color_list G_node_color_list);
static void decrementDegree(G_node_color node);
static G_node_color getAlias(G_node_color node);
static void addWorkList(G_node_color node);
static bool OK(G_node_color t, G_node_color r);
//for allocate color
static Stringlist StringList(string node,Stringlist pre,Stringlist next);
//by briggs ,combine
static bool conservative(G_node_color_list nodes);
static void combine(G_node_color u, G_node_color v);
static void simplify();
static void coalesce();
static void freezeMoves(G_node_color u);
static void freeze();
static void selectSpill();
static Stringlist allColors();
static void assignColors();


COL_result COL_color(Live_graph ig, Temp_map inital, Temp_tempList regs){
	G_graph graph = ig->graph;
	Live_moveList moves = ig->moves;
	G_nodeList g_nodeList = G_nodes(graph);
	init(graph->nodecount, inital,regs);
	G_node_color_list g_nodeList2 = NULL;
	while (g_nodeList != NULL){
		G_node g_node = g_nodeList->head;
        G_node_color node_color = g_node_color(g_node);
        if (Temp_look(inital,g_node->info)!=NULL){
           // printf("pre,%d\n",g_node->mykey);
            append_node(&precolored,node_color);
            if(node_color->kind==PRECOLORED){
				//printf("precolored\n");
			}
        }else{
			append_node(&g_nodeList2, node_color);
			//printf("init,%d\n",g_node->mykey);
			//node1->kind != PRECOLORED
			if(node_color->kind==PRECOLORED){
				//printf("precolored\n");
			}
			if(node_color->kind==DEFAULT1){
				//printf("SIMPLIFYWORKLIST\n");
			}			
		}
		g_nodeList = g_nodeList->tail;
	}
	g_nodeList = G_nodes(graph);
	//initial adjSet and adjList
	while (g_nodeList != NULL){
		G_node g_node = g_nodeList->head;
		G_node_color node_color = TAB_look(G_nodeMapG_node_color, g_node);
		G_nodeList adjNodeList = G_adj(g_node);

		while (adjNodeList != NULL){
		
			G_node otherG_node = adjNodeList->head;
			G_node_color othernode_color = TAB_look(G_nodeMapG_node_color, otherG_node);
			if(othernode_color==NULL){
				printf("notfund\n");
			}
			addEdge(node_color, othernode_color);
			adjNodeList = adjNodeList->tail;
		}
		g_nodeList = g_nodeList->tail;
	}
	//initial moveList and worklistMoves
	while (moves != NULL){
          Live_moveList_colornode Live_moveList_colornode = NULL;
          assert(moves->dst!=NULL&&moves->src!=NULL);

          Live_moveList_colornode = live_moveList_colornode(moves);
          append_movelist(&worklistMoves, Live_moveList_colornode);
          G_node_color dst = TAB_look(G_nodeMapG_node_color, moves->dst);
          G_node_color src = TAB_look(G_nodeMapG_node_color, moves->src);
          TAB_enter(moveList, dst, unionSet_movelist(TAB_look(moveList, dst), live_moveList_color(Live_moveList_colornode,NULL,NULL)));
          TAB_enter(moveList, src, unionSet_movelist(TAB_look(moveList, src), live_moveList_color(Live_moveList_colornode, NULL, NULL)));
          moves = moves->tail;
	}
	makeWorklist(g_nodeList2);
	do{
		if (!isEmpty(simplifyWorklist)){
			printf("hhhhhhhhhhhhhhhhhhhhhhhhhhsimplifyWorklist %d\n",K);
            simplify();
		}
		else if (!isEmpty(worklistMoves)){
			printf("hhhhhhhhhhhhhhhhhhhhhhhhhhcoalesce\n");
			coalesce();
		}
		else if (!isEmpty(freezeWorklist)){
			printf("hhhhhhhhhhhhhhhhhhhhhhhhhhfreeze\n");
			freeze();
		}
		else if (!isEmpty(spillWorklist)){
			printf("hhhhhhhhhhhhhhhhhhhhhhhhhhspill\n");
			selectSpill();
        }
	} while (!isEmpty(simplifyWorklist)||!isEmpty(worklistMoves)||!isEmpty(freezeWorklist)||!isEmpty(spillWorklist));
	assignColors();
	COL_result col_result = checked_malloc(sizeof(*col_result));
	col_result->coloring = Temp_layerMap(color,F_temp2Name());
	Temp_tempList spills = NULL;
	while (spilledNodes != NULL){
		spills = Temp_TempList(spilledNodes->value->node->info,spills);
		spilledNodes = spilledNodes->next;
	}
	col_result->spills = spills;
	return col_result;
}

void init(int n, Temp_map inital,Temp_tempList regs){
        precolored = NULL;
        simplifyWorklist = NULL;
        freezeWorklist = NULL;
        spillWorklist = NULL;
        spilledNodes  = NULL;
        coalescedNodes = NULL;
        coloredNodes = NULL;
        selectStack = NULL;
        coalescedMoves = NULL;
        constraintMoves = NULL;
        frozenMoves = NULL;
        worklistMoves = NULL;
        activeMoves = NULL;
	length = n;
	K = lengthOfTempList(regs);
	printf("k %d\n",K);

	//initAdjSet;
	adjSet = checked_malloc(n*n*sizeof(bool));
	int i;
	for(i=0;i<n*n;i++){
		adjSet[i] = FALSE;
	}
	//initAdjList;
	adjList = checked_malloc(n*sizeof(G_node_color_list));

	for(i = 0;i < n;i++){
		adjList[i] = NULL;
	}
	//initDegree;
	degree = checked_malloc(n*sizeof(int));

	for(i = 0;i < n;i++){
		degree[i] = 0;
	}

	moveList = TAB_empty();
	alias = TAB_empty();
	color = inital;
	G_nodeMapG_node_color = TAB_empty();
    registers = regs;
}


static void assignColors(){
	while (!isEmpty(selectStack)){
		G_node_color n = pop_node(&selectStack);
		Stringlist okColors = allColors();
		G_node_color_list g_nodeList2 = adjList[n->node->mykey];
		//printf("the assign node key %d\n",n->node->mykey);
		while (g_nodeList2){
			G_node_color w = g_nodeList2->value;
			//printf("adj %d\n",w->node->mykey);
            getAlias(w);
            G_node_color_list tempNodeList = unionSet_node(coloredNodes,precolored);
            if(isEmpty(okColors)){
                          break;
                        }
			if (isContain_node(&tempNodeList,getAlias(w))){

				string strColor = Temp_look(color, getAlias(w)->node->info);
				delete_string(&okColors, strColor);
			}
			g_nodeList2 = g_nodeList2->next;
		}
		if (isEmpty(okColors)){

			append_node(&spilledNodes, n);
		}
		else{
			append_node(&coloredNodes, n);
			Temp_enter(color, n->node->info, okColors->node);
			string strColor = Temp_look(color, n->node->info);
		}
	}
	G_node_color_list g_nodeList2 = coalescedNodes;
	while (g_nodeList2 != NULL){
		Temp_enter(color, g_nodeList2->value->node->info, Temp_look(color, getAlias(g_nodeList2->value)->node->info));
		g_nodeList2 = g_nodeList2->next;
	}
}


static Live_moveList_color NodeMoves(G_node_color node){
	return interSet_movelist(TAB_look(moveList, node), unionSet_movelist(activeMoves, worklistMoves));
}
static bool moveRelated(G_node_color node){
	return !isEmpty(NodeMoves(node));
}
static void makeWorklist(G_node_color_list initial){
	while (initial != NULL){
		G_node_color g_node_color = initial->value;
		int pos = g_node_color->node->mykey;
		printf(" 1   %d\n",K);
		if (degree[pos] >= K){
				printf(" 6\n");
			append_node(&spillWorklist, g_node_color);
		}
		else if (moveRelated(g_node_color)){
				printf(" 3\n");
			append_node(&freezeWorklist, g_node_color);
		}
		else{
				printf(" 4\n");
			append_node(&simplifyWorklist, g_node_color);
		}
		initial = initial->next;
	}
}
static G_node_color_list adjacent(G_node_color node){
	return diffSet_node(adjList[node->node->mykey], unionSet_node(selectStack, coalescedNodes));
}
static void enableMoves(G_node_color_list g_nodeList2){
	while (g_nodeList2 != NULL){
		Live_moveList_color live_moveList2 = NodeMoves(g_nodeList2->value);
		while (live_moveList2 != NULL){
			if (live_moveList2->value->kind == ACTIVEMOVES){
				delete_movelist(&activeMoves, live_moveList2->value);
				append_movelist(&worklistMoves, live_moveList2->value);
			}
			live_moveList2 = live_moveList2->next;
		}
		g_nodeList2 = g_nodeList2->next;
	}
}
static void decrementDegree(G_node_color node){
	int d = degree[node->node->mykey];
	degree[node->node->mykey]--;
	if (d == K){
		enableMoves(unionSet_node(adjacent(node), g_node_color_list(node, NULL, NULL)));
		delete_node(&spillWorklist, node);
		if (moveRelated(node)){
			append_node(&freezeWorklist, node);
		}
		else{
			append_node(&simplifyWorklist, node);
		}
	}
}
static void simplify(){
	if (simplifyWorklist != NULL){
		G_node_color node = peek_node(&simplifyWorklist);
		push(&selectStack, node);
		G_node_color_list g_nodeList = adjacent(node);
		while (g_nodeList != NULL){
			decrementDegree(g_nodeList->value);
			g_nodeList = g_nodeList->next;
		}
	}
}
static G_node_color getAlias(G_node_color node){
  assert(node);
	if (isContain_node(&coalescedNodes, node)){
		getAlias(TAB_look(alias, node));
	}
	return node;
}
static void addWorkList(G_node_color node){
	if (!isContain_node(&precolored,node) && !moveRelated(node) && degree[node->node->mykey] < K){
		delete_node(&freezeWorklist, node);
		append_node(&simplifyWorklist, node);
	}
}
static bool OK(G_node_color t, G_node_color r){
	return degree[t->node->mykey] < K || isContain_node(&precolored, t) || isLink(t->node->mykey, r->node->mykey);
}
static bool conservative(G_node_color_list nodes){
	int k = 0;
	while (nodes != NULL){
		if (degree[nodes->value->node->mykey] >= K){
			k++;
		}
		nodes = nodes->next;
	}
	return k < K;
}
static void combine(G_node_color u, G_node_color v){
	if (isContain_node(&freezeWorklist,v)){
		delete_node(&freezeWorklist, v);
	}
	else{
		delete_node(&spillWorklist, v);
	}
	append_node(&coalescedNodes, v);
	TAB_enter(alias, v, u);
	TAB_enter(moveList,u,unionSet_movelist(TAB_look(moveList, u), TAB_look(moveList, v)));
	enableMoves(g_node_color_list(v, NULL, NULL));
	G_node_color_list g_nodeList2 = adjacent(v);
	while (g_nodeList2 != NULL){
		addEdge(g_nodeList2->value, u);
		decrementDegree(g_nodeList2->value);
		g_nodeList2 = g_nodeList2->next;
	}
	if (degree[u->node->mykey] >= K&&isContain_node(&freezeWorklist,u)){
		delete_node(&freezeWorklist, u);
		append_node(&spillWorklist, u);
	}
}
static void coalesce(){
	Live_moveList_colornode  node = peek_movelist(&worklistMoves);
        assert(node->move->dst&&node->move->src);
	G_node_color x = getAlias(TAB_look(G_nodeMapG_node_color, node->move->dst));
	G_node_color y = getAlias(TAB_look(G_nodeMapG_node_color, node->move->src));
	G_node_color u = x;
	G_node_color v = y;
	if (isContain_node(&precolored, y)){
		u = y;
		v = x;
	}
	if (u == v){
		append_movelist(&coalescedMoves, node);
		addWorkList(u);
	}
	else if (isContain_node(&precolored, v) || isLink(u->node->mykey,v->node->mykey)){
		append_movelist(&constraintMoves, node);
		addWorkList(u);
		addWorkList(v);
	}
	else {
		bool bFlag = TRUE;
		if (isContain_node(&precolored, u)){
			G_node_color_list g_nodeList2 = adjacent(v);
			while (g_nodeList2 != NULL){
				if (!OK(g_nodeList2->value, u)){
					bFlag = FALSE;
					break;
				}
				g_nodeList2 = g_nodeList2->next;
			}
		}
		else{
			bFlag = FALSE;
		}
		if (bFlag || (!isContain_node(&precolored, u) && conservative(unionSet_node(adjacent(u), adjacent(v))))){
			append_movelist(&coalescedMoves, node);
			combine(u, v);
			addWorkList(u);
		}
		else{
			append_movelist(&activeMoves, node);
		}
	}
}
static void freezeMoves(G_node_color u){
	Live_moveList_color live_moveList2 = NodeMoves(u);
	while (live_moveList2 != NULL){
		Live_moveList_colornode m = live_moveList2->value;
		G_node_color x = TAB_look(G_nodeMapG_node_color,m->move->dst);
		G_node_color y = TAB_look(G_nodeMapG_node_color, m->move->src);
		G_node_color v = getAlias(y);
		if (getAlias(y) == getAlias(u)){
			v = getAlias(x);
		}
		delete_movelist(&activeMoves, m);
		append_movelist(&frozenMoves, m);
		if (isEmpty(NodeMoves(v)) && degree[v->node->mykey] < K){
			delete_node(&freezeWorklist, v);
			append_node(&simplifyWorklist, v);
		}
		live_moveList2 = live_moveList2->next;
	}
}
static void freeze(){
	G_node_color node = peek_node(&freezeWorklist);
	append_node(&simplifyWorklist, node);
	freezeMoves(node);
}
static void selectSpill(){
	G_node_color m = peek_node(&spillWorklist);
	append_node(&simplifyWorklist, m);
	freezeMoves(m);
}
static void addEdge_(int m,int n){
	adjSet[m*length + n] = TRUE;
}
static void addEdge(G_node_color node1, G_node_color node2){
	int m = node1->node->mykey;
	int n = node2->node->mykey;
	if (m != n&&!isLink(m,n)){
		//printf("m %d, n %d\n",m,n);
		addEdge_(m, n);
		addEdge_(n, m);
		if (node1->kind != PRECOLORED){
			//printf("here1\n");
			append_node(&adjList[m], node2);
			degree[m]+=1;
		}
		if (node2->kind != PRECOLORED){
			//printf("here2 \n");
			append_node(&adjList[n], node1);
			degree[n]+=1;
		}
	}
}

static Stringlist StringList(string node,Stringlist pre,Stringlist next){
	Stringlist stringlist = checked_malloc(sizeof(*stringlist));
	stringlist->node = node;
	stringlist->pre = pre;
	stringlist->next = next;
	return stringlist;
}
static Stringlist allColors(){
	Stringlist head = NULL,tail = NULL;
	Temp_tempList regs = registers;
	while(regs!=NULL){
		string node = Temp_look(color,regs->head);
		Stringlist temp  = StringList(node,tail,NULL);
		if(tail == NULL){
			head = tail = temp;
		}else{
			tail = tail->next = temp;
		}
                regs = regs->tail;
	}
	return head;
}



G_node_color g_node_color(G_node node){
	G_node_color g_node_color = checked_malloc(sizeof(*g_node_color));
	g_node_color->node = node;
	g_node_color->kind = DEFAULT1;
    TAB_enter(G_nodeMapG_node_color, node, g_node_color);
	return g_node_color;
}
G_node_color_list g_node_color_list(G_node_color node,G_node_color_list pre,G_node_color_list next){
  G_node_color_list g_nodeList2 = checked_malloc(sizeof(*g_nodeList2));
  g_nodeList2->value = node;
  g_nodeList2->pre = pre;
  g_nodeList2->next = next;
  return g_nodeList2;
}
Live_moveList_colornode live_moveList_colornode(Live_moveList move){
	Live_moveList_colornode live_moveList2node = checked_malloc(sizeof(*live_moveList2node));
	live_moveList2node->move = move;
	live_moveList2node->kind = DEFAULT2;
	return live_moveList2node;
}
Live_moveList_color live_moveList_color(Live_moveList_colornode value, Live_moveList_color pre, Live_moveList_color next){
  Live_moveList_color live_moveList2 = checked_malloc(sizeof(*live_moveList2));
  live_moveList2->value = value;
  live_moveList2->pre = pre;
  live_moveList2->next = next;
  return live_moveList2;
}
static bool isEmpty(void* set){
  return set==NULL;
}

static G_node_color_list unionSet_node(G_node_color_list set1_,G_node_color_list set2_){
  G_node_color_list head = NULL,tail = NULL,set1=set1_,set2=set2_;
  while(set1!=NULL){
    G_node_color_list node = g_node_color_list(set1->value,tail,NULL);
    if(tail==NULL){
      head = tail = node;
    }else{
      tail = tail->next = node;
    }
    set1 = set1->next;
  }
  while(set2!=NULL){
    G_node_color_list node = g_node_color_list(set2->value,tail,NULL);
    //a bug at here
    if(!isContain_node(&set1_,set2->value)){
      if(tail==NULL){
        head = tail = node;
      }else{
        tail = tail->next = node;
      }
    }
    set2 = set2->next;
  }
  return head;
}
static Live_moveList_color unionSet_movelist(Live_moveList_color set1_, Live_moveList_color set2_){
  Live_moveList_color head = NULL, tail = NULL,set1 = set1_,set2=set2_;
	while (set1 != NULL){
		Live_moveList_color node = live_moveList_color(set1->value, tail, NULL);
		if (tail == NULL){
			head = tail = node;
		}
		else{
			tail = tail->next = node;
		}
		set1 = set1->next;
	}
	while (set2 != NULL){
		Live_moveList_color node = live_moveList_color(set2->value, tail, NULL);
                if(!isContain_movelist(&set1_,set2->value)){
                  if (tail == NULL){
                    head = tail = node;
                  }
                  else{
                    tail = tail->next = node;
                  }
                }
		set2 = set2->next;
	}
	return head;
}
static void append_node(G_node_color_list* set,G_node_color node){
	/*
	 * node<------->(node2<----->node1)==set
	 */
	
	
	if (set == &precolored){
		//printf("pre\n");
		node->kind = PRECOLORED;
	}
	else if (set == &simplifyWorklist){
		node->kind = SIMPLIFYWORKLIST;
	}
	else if (set == &freezeWorklist){
		node->kind = FREEZEWORKLIST;
	}
	else if (set == &spillWorklist){
		node->kind = SPILLWORKLIST;
	}
	else if (set == &spilledNodes){
		node->kind = SPILLEDNODES;
	}
	else if (set == &coalescedNodes){
		node->kind = COALESCEDNODES;
	}
	else if (set == &coloredNodes){
		node->kind = COLOREDNODES;
	}
	else if (set == &selectStack){
		node->kind = SELECTSTACK;
	}
	G_node_color_list g_nodeList2 = g_node_color_list(node, NULL, NULL);
	if (*set == NULL){
		*set = g_nodeList2;
	}
	else{
		(*set)->pre = g_nodeList2;
		g_nodeList2->next = (*set);
		(*set) = g_nodeList2;
	}
}
static void append_movelist(Live_moveList_color* set, Live_moveList_colornode node){
	/*
	* node<------->(node2<----->node1)==set
	*/
	if (*set == coalescedMoves){
		node->kind = COALESCEDMOVES;
	}
	else if (*set == constraintMoves){
		node->kind = CONSTRAINTMOVES;
	}
	else if (*set == frozenMoves){
		node->kind = FROZENMOVES;
	}
	else if (*set == worklistMoves){
		node->kind = WORKLISTMOVES;
	}
	else if (*set == activeMoves){
		node->kind = ACTIVEMOVES;
	}
	Live_moveList_color Live_moveList_color = live_moveList_color(node, NULL, NULL);
	if (*set == NULL){
		*set = Live_moveList_color;
	}
	else{
		(*set)->pre = Live_moveList_color;
		Live_moveList_color->next = (*set);
		(*set) = Live_moveList_color;
	}
}
static bool isContain_node(G_node_color_list* set, G_node_color node){
  assert(set&&node);
	if (set == &precolored){
		return node->kind == PRECOLORED;
	}
	else if (set == &simplifyWorklist){
		return node->kind == SIMPLIFYWORKLIST;
	}
	else if (set == &freezeWorklist){
		return node->kind == FREEZEWORKLIST;
	}
	else if (set == &spillWorklist){
		return node->kind == SPILLWORKLIST;
	}
	else if (set == &spilledNodes){
		return node->kind == SPILLEDNODES;
	}
	else if (set == &coalescedNodes){
		return node->kind == COALESCEDNODES;
	}
	else if (set == &coloredNodes){
		return node->kind == COLOREDNODES;
	}
	else if (set == &selectStack){
		return node->kind == SELECTSTACK;
	}
        G_node_color_list set_ = *set;
	while (set_ != NULL){
		if (set_->value == node){
			return TRUE;
		}
		set_ = set_->next;
	}
	return FALSE;
}
static bool isContain_movelist(Live_moveList_color* set, Live_moveList_colornode node){
  assert(set&&node);
	if (set == &coalescedMoves){
		return node->kind == COALESCEDMOVES;
	}
	else if (set == &constraintMoves){
		return node->kind == CONSTRAINTMOVES;
	}
	else if (set == &frozenMoves){
		return node->kind == FROZENMOVES;
	}
	else if (set == &worklistMoves){
		return node->kind == WORKLISTMOVES;
	}
	else if (set == &activeMoves){
		return node->kind == ACTIVEMOVES;
	}
        Live_moveList_color set_ = *set;
	while (set_ != NULL){
		if (set_->value == node){
			return TRUE;
		}
		set_ = set_->next;
	}
	return FALSE;
}
static G_node_color_list diffSet_node(G_node_color_list set1_,G_node_color_list set2_){
  G_node_color_list head = NULL, tail=NULL,set1=set1_;
	while (set1 != NULL){
		if (!isContain_node(&set2_, set1->value)){
			if (tail == NULL){
				head = tail = g_node_color_list(set1->value, NULL, NULL);
			}
			else{
				G_node_color_list node =  g_node_color_list(set1->value, tail, NULL);
				tail = tail->next = node;
			}
		}
		set1 = set1->next;
	}
	return head;
}
static Live_moveList_color interSet_movelist(Live_moveList_color set1, Live_moveList_color set2){
	Live_moveList_color head=NULL, tail=NULL;
	while (set1 != NULL){
		if (isContain_movelist(&set2, set1->value)){
			if (tail == NULL){
				head = tail = live_moveList_color(set1->value, NULL, NULL);
			}
			else{
				Live_moveList_color node = live_moveList_color(set1->value, tail, NULL);
				tail = tail->next = node;
			}
		}
		set1 = set1->next;
	}
	return head;
}
static void delete_node(G_node_color_list* set_, G_node_color node){
	assert(*set_);
	G_node_color_list set = *set_;
	while (set != NULL){
		if (set->value == node){
			if (set->pre != NULL){
				set->pre->next = set->next;
			}
			if (set->next != NULL){
				set->next->pre = set->pre;
			}
			break;
		}
		set = set->next;
	}
	if ((*set_)->value == node){
          *set_ = (*set_)->next;
	}
}
static void delete_movelist(Live_moveList_color* set_, Live_moveList_colornode node){
	assert(*set_);
	Live_moveList_color set = *set_;
	while (set != NULL){
		if (set->value == node){
			if (set->pre != NULL){
				set->pre->next = set->next;
			}
			if (set->next != NULL){
				set->next->pre = set->pre;
			}
			break;
		}
		set = set->next;
	}
	if ((*set_)->value == node){
          *set_ = (*set_)->next;
	}
}
static void delete_string(Stringlist * set_, string node){
	assert(*set_);
	Stringlist set = *set_;
	while (set != NULL){
		if (set->node == node){
			if (set->pre != NULL){
				set->pre->next = set->next;
			}
			if (set->next != NULL){
				set->next->pre = set->pre;
			}
			break;
		}
		set = set->next;
	}
	if ((*set_)->node == node){
          *set_ = (*set_)->next;
	}
}
static G_node_color peek_node(G_node_color_list* set){
  assert(*set);
  G_node_color node = (*set)->value;
  delete_node(set, node);
  return node;
}
static G_node_color pop_node(G_node_color_list* stack){
	return peek_node(stack);
}
static Live_moveList_colornode peek_movelist(Live_moveList_color* set){
	if (*set != NULL){
		Live_moveList_colornode node = (*set)->value;
		delete_movelist(set, node);
		return node;
	}
	return NULL;
}
static void push(G_node_color_list* stack, G_node_color node){
	append_node(stack, node);
}
static bool isLink(int m, int n){
	return adjSet[m*length + n];
}
