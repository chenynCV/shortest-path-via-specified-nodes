// Copyright 2016 Ya-Nan Chen. All rights reserved.
// https://chenyncv.github.io/
//
// 华为软件精英挑战赛西北赛区32强
//
// 功能：找到重合边数最少且经过必经点的最短路径

#include "stdafx.h"
#define PRINTOUT
#define TIME_LIMIT

#include "route.h"
#include "lib_record.h"
#include <stdio.h>
#include <queue>

#include "string.h"
#include <vector>
#include <time.h>
#include <algorithm>
#include <bitset>         // std::bitset
#include <map>

using namespace  std;

//赛题设置
#define MAX_WEIGHT 100
#define NODE_NUM 2000
#define OUT_NUM 20
#define IN_NUM 200
#define DEMAND 100

#define INF 60000

#define WHITE   0
#define GRAY    1
#define BLACK   2

struct edge_node{
	unsigned int next_node;  //下一节点的编号，为  NP[600] 数组中的编号
	int edge_weight;  //有向边的代价
	unsigned int  edge_num;  //有向边的编号
	edge_node()
	{
		next_node = INF;
		edge_weight = INF;
		edge_num = INF;
	}
};

struct NodePoint{
	unsigned int  cost;   //dijistra算法的节点累加代价
	bool dm_flag;  //是否为demand点（必经点）标志位
	bool active;  //节点是否走过的标志位
	unsigned int  parent;  //父节点编号  ，用于回溯
	unsigned short edge_node_num;//实际出度个数
	struct edge_node  child[OUT_NUM];   //出度

	unsigned short parentsNum;//实际入度个数
	struct edge_node  parents[IN_NUM];   //入度
} NP[NODE_NUM];   //大小为六百的节点


unsigned short adjacent_index[NODE_NUM][NODE_NUM] = { 0 };
unsigned short adjacent_weight[NODE_NUM][NODE_NUM] = { 0 };
unsigned short start_route=0, end_route=0;
unsigned long int total_count = 0;

int numOfNode = 0;

unsigned short countofdemand = 0;
unsigned short numOfDemand = 0;

int start_time = 0, end_time = 0;
struct tm *local;
time_t t;// long t;

vector <unsigned short> startDemandEnd;

bool clear_flag = false;

inline 	bool operator < (const edge_node& lhs, const edge_node&rhs)
{
	return lhs.edge_weight > rhs.edge_weight;
}


struct PathDetected{
	vector<unsigned short> nodeID;  //节点的编号
	//vector<unsigned short> edgeID;  //有向边的编号
	unsigned int  cost;  //累积代价
	bitset<NODE_NUM> nodeColor;
	bitset<NODE_NUM * OUT_NUM> edgeColor;

	PathDetected()
	{
		cost = INF;
	}
};

struct PathNode{
	vector<PathDetected> nodePath;
	unsigned int  cost;  //累积代价
	bitset<NODE_NUM> nodeColor;
	bitset<NODE_NUM * OUT_NUM> edgeColor;

	unsigned int  end;

	PathNode()
	{
		cost = INF;
	}
};

inline 	bool operator < (const PathNode& lhs, const PathNode&rhs)
{
	return lhs.cost < rhs.cost;
}

bool pathCompare(const PathDetected& a, const PathDetected& b)
{
	return a.nodeID.size() < b.nodeID.size();
}

bool pathCompare1(const PathDetected& a, const PathDetected& b)
{
	return a.cost < b.cost;
}

bool pathCompare2(const PathDetected& a, const PathDetected& b)
{
	return (a.nodeID.size() * MAX_WEIGHT + a.cost) < (b.nodeID.size() * MAX_WEIGHT + b.cost);
}

bool pathCompare3(const PathDetected& a, const PathDetected& b)
{
	return (a.nodeID.size() + a.cost) <= (b.nodeID.size() + b.cost);
}

void pathSort(vector<PathDetected>& path, const unsigned char way)
{
	switch (way)
	{
	case 0:
		sort(path.begin(), path.end(), pathCompare); break;
	case 1:
		sort(path.begin(), path.end(), pathCompare1); break;
	case 2:
		sort(path.begin(), path.end(), pathCompare2); break;
	case 3:
		sort(path.begin(), path.end(), pathCompare3); break;
	default:
		sort(path.begin(), path.end(), pathCompare);
	}

}


void destroyMemory()
{
	for (int i = 0; i < NODE_NUM; i++)   //节点数组初始化
	{
		NP[i].cost = INF;
		NP[i].dm_flag = false;
		NP[i].active = false;
		NP[i].parent = INF;
		NP[i].edge_node_num = 0;
		for (int j = 0; j < OUT_NUM; j++)
		{
			NP[i].child[j].next_node = INF;
			NP[i].child[j].edge_weight = MAX_WEIGHT + 1;
			NP[i].child[j].edge_num = INF;
		}

		NP[i].parentsNum = 0;
		for (int j = 0; j < IN_NUM; j++)
		{
			NP[i].parents[j].next_node = INF;
			NP[i].parents[j].edge_weight = MAX_WEIGHT + 1;
			NP[i].parents[j].edge_num = INF;
		}
	}
}


int charToNum(char in[], int  out[])
{
	int i = 0, j = 0;
	int tmp = 0;
	while (in[i] != '\0' && in[i] != '\n')
	{
		if (in[i] >= '0' && in[i] <= '9')
		{
			out[j] = 10 * tmp + in[i] - 48;
			tmp = out[j];
		}
		else
		{

			if (in[i] == 'N' || in[i] == 'A')
			{
				j = 2;
				break;
			}

			tmp = 0;
			j++;
		}

		i++;
	}

	j++;
	return j;
}


int getAdjacent(char *topo[5000], int edge_num)
{
	for (int i = 0; i < NODE_NUM; i++)
	{
		for (int j = 0; j < NODE_NUM; j++)
		{
			adjacent_index[i][j] = INF;
			adjacent_weight[i][j] = INF;
		}
	}

	int node_num = 0, from_index = 0, to_index = 0, edge_index = 0, edge_weight = 0;
	for (int i = 0; i < edge_num; i++)
	{
		int topoInNum[4] = { 0, 0, 0, 0 };
		charToNum(&topo[i][0], topoInNum);
		from_index = topoInNum[1];
		to_index = topoInNum[2];

		if (from_index == to_index) continue;

		edge_index = topoInNum[0];
		edge_weight = topoInNum[3];
		if (adjacent_weight[from_index][to_index] > edge_weight)
		{
			adjacent_index[from_index][to_index] = edge_index;
			adjacent_weight[from_index][to_index] = edge_weight;
		}

		if (from_index > node_num)
		{
			node_num = from_index;
		}
		if (to_index > node_num)
		{
			node_num = to_index;
		}

	}

	return node_num + 1;
}

int loadMap2(char *topo[MAX_EDGE_NUM], int edge_num)
{
	unsigned int node_num = 0;
	unsigned short from_index = 0, to_index = 0, edge_index = 0;
	int edge_weight = 0;
	for (int i = 0; i < edge_num; i++)
	{
		int topoInNum[4] = { 0, 0, 0, 0 };
		charToNum(&topo[i][0], topoInNum);
		from_index = topoInNum[1];
		to_index = topoInNum[2];

		if (from_index == to_index) continue;

		edge_index = topoInNum[0];
		edge_weight = topoInNum[3];

		if (NP[from_index].edge_node_num < OUT_NUM)
		{
			NP[from_index].child[NP[from_index].edge_node_num].next_node = to_index;
			NP[from_index].child[NP[from_index].edge_node_num].edge_weight = edge_weight;
			NP[from_index].child[NP[from_index].edge_node_num].edge_num = edge_index;
			NP[from_index].edge_node_num++;   //出度数加1
		}

		if (NP[to_index].parentsNum < IN_NUM)
		{
			NP[to_index].parents[NP[to_index].parentsNum].next_node = from_index;
			NP[to_index].parents[NP[to_index].parentsNum].edge_weight = edge_weight;
			NP[to_index].parents[NP[to_index].parentsNum].edge_num = edge_index;
			NP[to_index].parentsNum++;//入度数加1
		}

		if (from_index > node_num)	node_num = from_index;
		if (to_index > node_num)	node_num = to_index;

	}

	return node_num + 1;
}


int loadDemand(char *demand)
{
	int demandInNum[DEMAND + 3] = { 0 };
	int demand_num = charToNum(demand, demandInNum) - 3;

	start_route = demandInNum[1];
	end_route = demandInNum[2];

	startDemandEnd.clear();
	startDemandEnd.push_back(start_route);
	for (int i = 0; i < demand_num; i++)    ////将必经点标志位置为1；
	{
		NP[demandInNum[i + 3]].dm_flag = true;
		startDemandEnd.push_back(demandInNum[i + 3]);
	}
	startDemandEnd.push_back(end_route);

	return demand_num;
}


int clearDemand(char *demand)
{
	startDemandEnd.clear();

	start_route = INF;
	end_route = INF;

	int demandInNum[DEMAND + 3] = { 0 };
	int demand_num = charToNum(demand, demandInNum) - 3;

	for (int i = 0; i < demand_num; i++)    ////将必经点标志位置为0；
	{
		NP[demandInNum[i + 3]].dm_flag = false;
	}

	return demand_num;
}


bool compare(const struct edge_node& a, const struct edge_node& b)
{
	return a.edge_weight < b.edge_weight;
}

void sortMap(int node_num)
{
	for (int i = 0; i < node_num; i++)
	{
		int numChild = NP[i].edge_node_num;
		if (numChild > 1)
		{
			sort(NP[i].child, NP[i].child + numChild, compare);
		}

		int numParent = NP[i].parentsNum;
		if (numParent > 1)
		{
			for (int j = 0; j < numParent; j++)
			{
				if (NP[NP[i].parents[j].next_node].dm_flag == true) NP[i].parents[j].edge_weight -= MAX_WEIGHT+1;
			}
			sort(NP[i].parents, NP[i].parents + numParent, compare);
			for (int j = 0; j < numParent; j++)
			{
				if (NP[NP[i].parents[j].next_node].dm_flag == true) NP[i].parents[j].edge_weight += MAX_WEIGHT+1;
			}
		}

	}
}


bool BFS_VISIT_DEMAND2(const unsigned short start, const unsigned short numEnd, const bitset<NODE_NUM>& colorPath)
{
	bitset<NODE_NUM> colorVisit = colorPath;

	queue<short> Q;
	Q.push(start);
	colorVisit[start] = true;

	unsigned short count = 0;

	if (NP[start].dm_flag == true)		count++;

	while (Q.empty() != true && count < numEnd)
	{
		int u = Q.front();
		Q.pop();
		for (int i = 0; i < NP[u].edge_node_num; i++)
		{
			int v = NP[u].child[i].next_node;

			//if (NP[v].active == false && v != end_route)
			if (colorVisit[v] == false && v != end_route)
			{
				//NP[v].active = true;
				colorVisit[v] = true;

				Q.push(v);

				if (NP[v].dm_flag == true)		count++;
			}

			if (count >= numEnd)	break;

		}
	}

	if (count >= numEnd)
		return true;
	else
		return false;
}

bool BFS_VISIT_DEMANDBit(const unsigned short start, const unsigned short numEnd, const bitset<NODE_NUM>& colorPath,
	const vector<vector<PathDetected> >& G)
{
	bitset<NODE_NUM> colorVisit = colorPath;

	queue<short> Q;
	Q.push(start);
	colorVisit[start] = true;

	unsigned short count = 0;

	if (NP[start].dm_flag == true)		count++;

	while (Q.empty() != true && count < numEnd)
	{
		int u = Q.front();
		Q.pop();
		for (int i = 0; i < G[u].size(); i++)
		{
			PathDetected uPath = G[u][i];

			//检测是否有重节点
			bitset<NODE_NUM> colorTmp = colorVisit&uPath.nodeColor;
			colorTmp[uPath.nodeID.front()] = 0;
			if (colorTmp.any())		continue;

			//无重节点
			int v = uPath.nodeID.back();;
			colorVisit[v] = true;
			Q.push(v);

			if (NP[v].dm_flag == true)		count++;

			if (count >= numEnd)	break;
		}
	}

	if (count == numEnd)
		return true;
	else
		return false;
}


bool BFS_VISIT_END2(const unsigned short start, const unsigned short numEnd, const bitset<NODE_NUM>& colorPath)
{
	bitset<NODE_NUM> colorVisit = colorPath;

	colorVisit[start] = true;

	queue<short> Q;
	Q.push(end_route);
	colorVisit[end_route] = true;

	unsigned short count = 0;

	while (Q.empty() != true && count < numEnd)
	{
		int u = Q.front();
		Q.pop();
		for (int i = 0; i < NP[u].parentsNum; i++)
		{
			int v = NP[u].parents[i].next_node;

			if (colorVisit[v] == false && v != start_route)
			{
				colorVisit[v] = true;

				Q.push(v);

				if (NP[v].dm_flag == true)	count++;
			}
			if (count >= numEnd)	break;
		}
	}

	if (count >= numEnd)
		return true;
	else
		return false;
}

bool BFS_VISIT_NODE(unsigned short start, unsigned short end, vector<unsigned short>& retPath,
	bitset<NODE_NUM>& color, bitset<NODE_NUM * OUT_NUM>& edgeColor, unsigned int& retcost)
{
	color.reset();
	edgeColor.reset();
	retcost = INF;

	vector <unsigned short> changedNode;

	queue<short> Q;
	Q.push(start);
	NP[start].active = true;
	NP[start].cost = 0;
	changedNode.push_back(start);

	unsigned short count = 0;

	while (Q.empty() != true && count < 1)
	{
		int u = Q.front();
		Q.pop();
		for (int i = 0; i < NP[u].edge_node_num; i++)
		{
			int v = NP[u].child[i].next_node;

			if (NP[v].active == true ||
				(v != end && v == end_route) ||
				(v != end && v == start_route) ||
				(v != end && NP[v].dm_flag == true))
			{
				continue;
			}

			NP[v].active = true;
			NP[v].parent = u;
			NP[v].cost = NP[u].cost + adjacent_weight[u][v];
			changedNode.push_back(v);

			Q.push(v);

			if (v == end)
			{
				unsigned short par = NP[v].parent;
				retPath.clear();
				retPath.insert(retPath.begin(), v);
				color[v] = 1;
				edgeColor[adjacent_index[par][v]] = 1;
				while (par != start)
				{
					retPath.insert(retPath.begin(), par);
					color[par] = 1;
					edgeColor[adjacent_index[NP[par].parent][par]] = 1;

					par = NP[par].parent;
				}
				retPath.insert(retPath.begin(), start);
				color[start] = 1;
				retcost = NP[v].cost;

				count++;

				break;
			}
		}

	}

	for (int i = 0; i < changedNode.size(); i++)
	{
		NP[changedNode[i]].active = false;
		NP[changedNode[i]].parent = INF;
		NP[changedNode[i]].cost = INF;
	}

	if (count == 1)
		return true;
	else
		return false;
}

unsigned int BFS_VISIT_NODE(unsigned short start, unsigned short numEnd, vector<PathDetected>& pathAll)
{
	pathAll.clear();

	vector <unsigned short> changedNode;

	queue<short> Q;
	Q.push(start);
	NP[start].active = true;
	NP[start].cost = 0;
	changedNode.push_back(start);

	unsigned short count = 0;

	while (Q.empty() != true && count < numEnd)
	{
		int u = Q.front();
		Q.pop();
		for (int i = 0; i < NP[u].edge_node_num; i++)
		{
			int v = NP[u].child[i].next_node;

			if (NP[v].active == true ||
				(v == end_route) ||
				(v == start_route) ||
				(NP[v].active == true && NP[v].dm_flag == true)
				)
			{
				continue;
			}

			NP[v].active = true;
			NP[v].parent = u;
			NP[v].cost = NP[u].cost + adjacent_weight[u][v];
			changedNode.push_back(v);

			//Q.push(v);

			if (NP[v].dm_flag==true)
			{
				PathDetected retTmp;

				unsigned short par = NP[v].parent;
				retTmp.nodeID.clear();
				retTmp.nodeID.insert(retTmp.nodeID.begin(), v);
				retTmp.nodeColor[v] = 1;
				retTmp.edgeColor[adjacent_index[par][v]] = 1;
				while (par != start)
				{
					retTmp.nodeID.insert(retTmp.nodeID.begin(), par);
					retTmp.nodeColor[par] = 1;
					retTmp.edgeColor[adjacent_index[NP[par].parent][par]] = 1;

					par = NP[par].parent;
				}
				retTmp.nodeID.insert(retTmp.nodeID.begin(), start);
				retTmp.nodeColor[start] = 1;
				retTmp.cost = NP[v].cost;

				pathAll.push_back(retTmp);

				count++;

				if(count==numEnd) break;
			}
			else
			{
				Q.push(v);
			}

		}

	}

	for (int i = 0; i < changedNode.size(); i++)
	{
		NP[changedNode[i]].active = false;
		NP[changedNode[i]].parent = INF;
		NP[changedNode[i]].cost = INF;
	}

	return count;
}


bool  dijikstraPriorQueue(unsigned short start, unsigned short end, bitset<NODE_NUM>& colorPath, vector<unsigned short>& retPath,
	bitset<NODE_NUM>& color, unsigned int& retcost)
{
	color.reset();
	retcost = INF;

	unsigned short count = 0;

	vector <unsigned short> S;
	vector <unsigned short> changedNode;
	bitset<NODE_NUM> colorPathOri = colorPath;

	S.push_back(start);
	//if (NP[next].active != true)
	//if (colorPath[start] != true)
	//{
	NP[start].cost = INF;
	//NP[start].active = true;
	colorPath[start] = true;
	changedNode.push_back(start);
	//}

	priority_queue<edge_node> Q;

	for (int i = 0; i < NP[start].edge_node_num; i++)
	{
		unsigned short next = NP[start].child[i].next_node;
		//if (NP[next].active != true)
		if (colorPath[next] != true)
		{
			NP[next].cost = NP[start].child[i].edge_weight;
			NP[next].parent = start;

			Q.push(NP[start].child[i]);

			changedNode.push_back(next);
		}
	}

	while (Q.empty() != true && count < 1)
	{
		//Extract min
		edge_node minNode = Q.top();
		Q.pop();
		bool emptyFlag = false;
		while (colorPath[minNode.next_node] == true ||
			(minNode.next_node != end && minNode.next_node == end_route) ||
			(minNode.next_node != end && minNode.next_node == start_route) ||
			(minNode.next_node != end && NP[minNode.next_node].dm_flag == true))
		{
			if (Q.empty() == true)
			{
				emptyFlag = true;
				break;
			}

			minNode = Q.top();
			Q.pop();
		}
		if (emptyFlag == true) break;
		unsigned short u = minNode.next_node;

		//合并
		S.push_back(u);
		//NP[u].active = true;
		colorPath[u] = true;
		changedNode.push_back(u);

		if (NP[u].dm_flag == true || u == end)
		{
			unsigned short  par = NP[u].parent;
			retPath.clear();
			//retEdge.clear();
			retPath.insert(retPath.begin(), u);
			//retEdge.insert(retEdge.begin(), adjacent_index[par][u]);
			color[u] = 1;
			while (par != start)
			{
				retPath.insert(retPath.begin(), par);
				//retEdge.insert(retEdge.begin(), adjacent_index[NP[par].parent][par]);
				color[par] = 1;

				par = NP[par].parent;
			}
			retPath.insert(retPath.begin(), start);
			retcost = NP[u].cost;
			color[start] = 1;

			count++;
		}

		if (count >= 1) break;


		//Relax
		for (int i = 0; i < NP[u].edge_node_num; i++)
		{
			unsigned short v = NP[u].child[i].next_node;
			//if (NP[v].active != true)
			if (colorPath[v] != true)
			{
				unsigned short weight = NP[u].child[i].edge_weight;
				if (NP[u].cost + weight < NP[v].cost)
				{
					NP[v].cost = NP[u].cost + weight;
					NP[v].parent = u;

					changedNode.push_back(v);
				}

				edge_node QNode;
				QNode.next_node = v;
				QNode.edge_num = NP[u].child[i].edge_num;
				QNode.edge_weight = NP[v].cost;
				Q.push(QNode);
			}
		}

	}

	for (int i = 0; i < changedNode.size(); i++)
	{
		NP[changedNode[i]].cost = INF;
		//NP[changedNode[i]].active = false;
		//colorPath[changedNode[i]] = false;

		NP[changedNode[i]].parent = INF;
	}
	colorPath = colorPathOri;

	if (count == 1)
		return true;
	else
		return false;
}


bool pathCombineBFS(const unsigned short u, const unsigned short end, const vector<vector<PathDetected> >& G, 
	vector<PathDetected>& pathNow, vector<PathDetected>& pathMin, vector<vector<PathDetected> >& pathAll,
	float time_limit)
{
	total_count++;

	if (pathMin.size() > 0)
	{
		if (total_count % 80 == 0)
		{
			time(&t);
			local = localtime(&t);
			end_time = 3600 * local->tm_hour + 60 * local->tm_min + local->tm_sec;
			if (end_time > start_time + time_limit)	return true;     //time is up
		}
	}

	static unsigned int minCost = INF;

	static bitset<NODE_NUM> colorPath;

	if (clear_flag)
	{
		minCost = INF;
		colorPath.reset();
		clear_flag = false;
	}

	bitset<NODE_NUM> colorOri = colorPath;

	unsigned int sumCost = 0;

	for (int i = 0; i < G[u].size(); i++)
	{
		PathDetected v = G[u][i];

		//检测是否有重节点
		bitset<NODE_NUM> colorTmp = colorPath&v.nodeColor;
		colorTmp[v.nodeID.front()] = 0;
		if (colorTmp.any())		continue;

		//test cost
		if (numOfDemand - pathNow.size()<numOfDemand - 5)
		{
			sumCost = 0;
			for (int j = 0; j < pathNow.size(); j++)
			{
				sumCost += pathNow[j].cost;
			}
			sumCost += v.cost;

			if (sumCost>minCost) continue;
		}

		////预检测：该点是否能经过所有未到达的必经点
		//if (BFS_VISIT_DEMANDBit(v.nodeID.back(), numOfDemand - pathNow.size(), colorPath, G) == false)	continue;

		////if (total_count % 100 == 0)
		////if (total_count % (pathNow.size() + 1) == 0)
		//if (numOfDemand - pathNow.size()>numOfDemand / 2)
		//{
		//	bitset<NODE_NUM> colorDemand = colorPath | v.nodeColor;
		//	//检测该点是否能经过所有未到达的必经点
		//	if (BFS_VISIT_DEMAND2(v.nodeID.back(), numOfDemand - pathNow.size(), colorDemand) == false)	continue;

		//	bitset<NODE_NUM> colorEnd = colorPath | v.nodeColor;
		//	//colorEnd[v.nodeID.back()] = false;
		//	//检测是否所有未到达的必经点均能到达终点
		//	if (BFS_VISIT_END2(v.nodeID.back(), numOfDemand - pathNow.size() - 1, colorEnd) == false)   continue;
		//}


		//无重节点
		pathNow.push_back(v);
		colorPath = colorPath | v.nodeColor;

		if (pathNow.size() == numOfDemand)		//检测是否成功经过所有必经点
		{
			PathDetected retTmp;
			bitset<NODE_NUM> colorDij;
			colorDij = colorPath;
			if (dijikstraPriorQueue(v.nodeID.back(), end_route, colorDij, retTmp.nodeID, retTmp.nodeColor, retTmp.cost))
			{
				pathNow.push_back(retTmp);

				sumCost = 0;
				for (int j = 0; j < pathNow.size(); j++)
				{
					sumCost += pathNow[j].cost;
				}

				if (sumCost < minCost)
				{
			
					minCost = sumCost;
					pathMin = pathNow;

					//pathAll.push_back(pathMin);
					pathAll.insert(pathAll.begin(),pathMin);
#ifdef PRINTOUT
					time(&t);
					local = localtime(&t);
					end_time = 3600 * local->tm_hour + 60 * local->tm_min + local->tm_sec;
					//打印
					printf("cost:%d--used time is %d s\n", minCost, end_time - start_time);
					printf("PathDij-");
					for (int j = 0; j < pathMin.size(); j++)
					{
						for (int k = 0; k < pathMin[j].nodeID.size() - 1; k++)
						{
							printf("-%d", pathMin[j].nodeID[k]);
						}
					}
					printf("-%d", pathMin.back().nodeID.back());
					printf("\n");
#endif

				}
				pathNow.pop_back();

				//return false;
			}

			pathNow.pop_back();
			colorPath = colorOri;
		}
		else
		{
			//pathNow.push_back(v);
			//colorPath = colorPath | v.nodeColor;
			if (pathCombineBFS(v.nodeID.back(), end, G, pathNow, pathMin, pathAll, time_limit) == true)	return true;

			pathNow.pop_back();
			colorPath = colorOri;
		}
	}

	return false;
}


bool pathCombineBFS(const unsigned short u, const unsigned short end, vector<vector<PathDetected> >& G,
	vector<PathDetected *>& pathNow, vector<PathDetected>& pathMin, vector<vector<PathDetected> >& pathAll,
	float time_limit)
{
	total_count++;

	if (pathMin.size() > 0)
	{
		if (total_count % 80 == 0)
		{
			time(&t);
			local = localtime(&t);
			end_time = 3600 * local->tm_hour + 60 * local->tm_min + local->tm_sec;
			if (end_time > start_time + time_limit)	return true;     //time is up
		}
	}

	static unsigned int minCost = INF;

	static bitset<NODE_NUM> colorPath;

	if (clear_flag)
	{
		minCost = INF;
		colorPath.reset();
		clear_flag = false;
	}

	bitset<NODE_NUM> colorOri = colorPath;

	unsigned int sumCost = 0;

	bitset<NODE_NUM> colorTmp;

	for (int i = 0; i < G[u].size(); i++)
	{
		PathDetected *v =&(G[u][i]);

		//检测是否有重节点
		//bitset<NODE_NUM> colorTmp;
		colorTmp.reset();
		colorTmp = colorPath&v->nodeColor;
		colorTmp[v->nodeID.front()] = 0;
		if (colorTmp.any())		continue;

		//test cost
		if (numOfDemand - pathNow.size()<numOfDemand - 5)
		{
			sumCost = 0;
			for (int j = 0; j < pathNow.size(); j++)
			{
				sumCost += pathNow[j]->cost;
			}
			sumCost += v->cost;

			if (sumCost>minCost) continue;
		}

		////预检测：该点是否能经过所有未到达的必经点
		//if (BFS_VISIT_DEMANDBit(v->nodeID.back(), numOfDemand - pathNow.size(), colorPath, G) == false)	continue;

		////if (total_count % 100 == 0)
		////if (total_count % (pathNow.size() + 1) == 0)
		//if (numOfDemand - pathNow.size()>numOfDemand / 2)
		//{
		//	bitset<NODE_NUM> colorDemand = colorPath | v->nodeColor;
		//	//检测该点是否能经过所有未到达的必经点
		//	if (BFS_VISIT_DEMAND2(v->nodeID.back(), numOfDemand - pathNow.size(), colorDemand) == false)	continue;

		//	bitset<NODE_NUM> colorEnd = colorPath | v->nodeColor;
		//	//colorEnd[v.nodeID.back()] = false;
		//	//检测是否所有未到达的必经点均能到达终点
		//	if (BFS_VISIT_END2(v->nodeID.back(), numOfDemand - pathNow.size() - 1, colorEnd) == false)   continue;
		//}


		//无重节点
		pathNow.push_back(v);
		colorPath = colorPath | v->nodeColor;

		if (pathNow.size() == numOfDemand)		//检测是否成功经过所有必经点
		{
			PathDetected retTmp;
			//bitset<NODE_NUM> colorDij;
			colorTmp.reset();
			colorTmp = colorPath;
			if (dijikstraPriorQueue(v->nodeID.back(), end_route, colorTmp, retTmp.nodeID, retTmp.nodeColor, retTmp.cost))
			{
				pathNow.push_back(&retTmp);

				sumCost = 0;
				for (int j = 0; j < pathNow.size(); j++)
				{
					sumCost += pathNow[j]->cost;
				}

				if (sumCost < minCost)
				{

					minCost = sumCost;

					//pathMin = pathNow;
					pathMin.clear();
					pathMin.resize(pathNow.size());
					for (int j = 0; j < pathNow.size(); j++)
					{
						pathMin[j] = *pathNow[j];
					}

					//pathAll.push_back(pathMin);
					pathAll.insert(pathAll.begin(), pathMin);
#ifdef PRINTOUT
					time(&t);
					local = localtime(&t);
					end_time = 3600 * local->tm_hour + 60 * local->tm_min + local->tm_sec;
					//打印
					printf("cost:%d--used time is %d s\n", minCost, end_time - start_time);
					printf("PathDij-");
					for (int j = 0; j < pathMin.size(); j++)
					{
						for (int k = 0; k < pathMin[j].nodeID.size() - 1; k++)
						{
							printf("-%d", pathMin[j].nodeID[k]);
						}
					}
					printf("-%d", pathMin.back().nodeID.back());
					printf("\n");
#endif

				}
				pathNow.pop_back();

				//return false;
			}

			pathNow.pop_back();
			colorPath = colorOri;
		}
		else
		{
			//pathNow.push_back(v);
			//colorPath = colorPath | v.nodeColor;
			//if (pathCombineBFS(v->nodeID.back(), end, G, pathNow, pathMin, pathAll, time_limit) == true)	return true;
			if (pathCombineBFS(v->nodeID.back(), end, G, pathNow, pathMin, pathAll, time_limit) == true)	return true;

			pathNow.pop_back();
			colorPath = colorOri;
		}
	}

	return false;
}


void FindrouteBFS( vector<vector<PathDetected> >& pathAll,
	const unsigned char way, const unsigned int maxPathCost, float time_limit)
{
	vector<vector<PathDetected > >   retAll(numOfNode);

	//起点到必经点
	for (int i = 0; i < 1; i++)
	{
		//for (int j = 1; j < startDemandEnd.size() - 1; j++)
		//{
		//	if (i == j) continue;
		//	PathDetected retTmp;
		//	if (BFS_VISIT_NODE(startDemandEnd[i], startDemandEnd[j], retTmp.nodeID, 
		//		retTmp.nodeColor, retTmp.edgeColor, retTmp.cost))
		//	{
		//		retAll[startDemandEnd[i]].push_back(retTmp);
		//	}
		//}

		BFS_VISIT_NODE(startDemandEnd[i], numOfDemand, retAll[startDemandEnd[i]]);
	}
	//必经点到必经点
	for (int i = 1; i < startDemandEnd.size() - 1; i++)
	{
		//for (int j = 1; j < startDemandEnd.size() - 1; j++)
		//{
		//	if (i == j) continue;
		//	PathDetected retTmp;
		//	if (BFS_VISIT_NODE(startDemandEnd[i], startDemandEnd[j], retTmp.nodeID, 
		//		retTmp.nodeColor, retTmp.edgeColor, retTmp.cost))
		//	{
		//		retAll[startDemandEnd[i]].push_back(retTmp);
		//	}
		//}

		BFS_VISIT_NODE(startDemandEnd[i], numOfDemand-1, retAll[startDemandEnd[i]]);
	}

	//排序
	for (int i = 0; i < startDemandEnd.size() - 1; i++)
	{
		//剪枝
		pathSort(retAll[startDemandEnd[i]], 1);
		for (int j = 0; j<retAll[startDemandEnd[i]].size(); j++)
		{
			if (retAll[startDemandEnd[i]][j].cost>maxPathCost)
			{
				retAll[startDemandEnd[i]].erase(retAll[startDemandEnd[i]].begin() + j, retAll[startDemandEnd[i]].end());
				break;
			}
		}

		pathSort(retAll[startDemandEnd[i]], way);
	}

#ifdef PRINTOUT
	//打印
	for (int i = 0; i < startDemandEnd.size() - 1; i++)
	{
		for (int j = 0; j < retAll[startDemandEnd[i]].size(); j++)
		{
			printf("Path-");
			for (int k = 0; k < retAll[startDemandEnd[i]][j].nodeID.size(); k++)
			{
				printf("-%d", retAll[startDemandEnd[i]][j].nodeID[k]);
			}
			printf("--Cost:%d", retAll[startDemandEnd[i]][j].cost);
			printf("\n");
		}

	}
#endif

	vector<PathDetected *> pathNow;
	vector<PathDetected> pathDijMin;
	pathCombineBFS(start_route, end_route, retAll, pathNow, pathDijMin, pathAll, time_limit);

	//print_time("End");

	//if (pathDijMin.size() > 0)
	//{
	//	minPath.clear();
	//	for (int j = 0; j < pathDijMin.size(); j++)
	//	{
	//		minPath.insert(minPath.end(), pathDijMin[j].nodeID.begin(), pathDijMin[j].nodeID.end() - 1);
	//	}
	//	minPath.push_back(end_route);
	//}

	//print_time("End");
}


bool  dijikstraPriorQueue(unsigned short start, unsigned short end,
	bitset<NODE_NUM>& colorPath, const bitset<NODE_NUM * OUT_NUM>& edgeColorPath,
	vector<unsigned short>& retPath, bitset<NODE_NUM>& color, bitset<NODE_NUM * OUT_NUM>& edgeColor, unsigned int& retcost)
{
	color.reset();
	retcost = INF;

	unsigned short count = 0;

	vector <unsigned short> S;
	vector <unsigned short> changedNode;
	bitset<NODE_NUM> colorPathOri = colorPath;

	S.push_back(start);
	NP[start].cost = INF;
	colorPath[start] = true;
	changedNode.push_back(start);

	priority_queue<edge_node> Q;

	for (int i = 0; i < NP[start].edge_node_num; i++)
	{
		unsigned short next = NP[start].child[i].next_node;
		if (colorPath[next] != true)
		{
			NP[next].cost = NP[start].child[i].edge_weight;
			NP[next].parent = start;

			Q.push(NP[start].child[i]);

			changedNode.push_back(next);
		}
	}

	while (Q.empty() != true && count < 1)
	{
		//Extract min
		edge_node minNode = Q.top();
		Q.pop();
		bool emptyFlag = false;
		while (colorPath[minNode.next_node] == true ||
			edgeColorPath[adjacent_index[NP[minNode.next_node].parent][minNode.next_node]] == true ||
			(minNode.next_node != end && minNode.next_node == end_route) ||
			(minNode.next_node != end && minNode.next_node == start_route) ||
			(minNode.next_node != end && NP[minNode.next_node].dm_flag == true))
		{
			if (Q.empty() == true)
			{
				emptyFlag = true;
				break;
			}

			minNode = Q.top();
			Q.pop();
		}
		if (emptyFlag == true) break;
		unsigned short u = minNode.next_node;

		//合并
		S.push_back(u);
		colorPath[u] = true;
		changedNode.push_back(u);

		if (NP[u].dm_flag == true || u == end)
		{
			unsigned short  par = NP[u].parent;
			retPath.clear();
			//retEdge.clear();
			retPath.insert(retPath.begin(), u);
			//retEdge.insert(retEdge.begin(), adjacent_index[par][u]);
			color[u] = 1;
			edgeColor[adjacent_index[par][u]] = 1;
			while (par != start)
			{
				retPath.insert(retPath.begin(), par);
				//retEdge.insert(retEdge.begin(), adjacent_index[NP[par].parent][par]);
				color[par] = 1;
				edgeColor[adjacent_index[NP[par].parent][par]] = 1;

				par = NP[par].parent;
			}
			retPath.insert(retPath.begin(), start);
			retcost = NP[u].cost;
			color[start] = 1;

			count++;
		}

		if (count >= 1) break;


		//Relax
		for (int i = 0; i < NP[u].edge_node_num; i++)
		{
			unsigned short v = NP[u].child[i].next_node;
			//if (NP[v].active != true)
			if (colorPath[v] != true)
			{
				unsigned short weight = NP[u].child[i].edge_weight;
				if (NP[u].cost + weight < NP[v].cost)
				{
					NP[v].cost = NP[u].cost + weight;
					NP[v].parent = u;

					changedNode.push_back(v);
				}

				edge_node QNode;
				QNode.next_node = v;
				QNode.edge_num = NP[u].child[i].edge_num;
				QNode.edge_weight = NP[v].cost;
				Q.push(QNode);
			}
		}

	}

	for (int i = 0; i < changedNode.size(); i++)
	{
		NP[changedNode[i]].cost = INF;
		//NP[changedNode[i]].active = false;
		//colorPath[changedNode[i]] = false;

		NP[changedNode[i]].parent = INF;
	}
	colorPath = colorPathOri;

	if (count == 1)
		return true;
	else
		return false;
}


bool partPathRefine(PathDetected& path, const bitset<NODE_NUM>& color, const bitset<NODE_NUM * OUT_NUM > edgePath)
{
	PathDetected retRefineTmp;
	bitset<NODE_NUM> colorRefine = color&(~path.nodeColor);
	if (dijikstraPriorQueue(path.nodeID.front(), path.nodeID.back(),
		colorRefine, edgePath,
		retRefineTmp.nodeID, retRefineTmp.nodeColor, retRefineTmp.edgeColor, retRefineTmp.cost))
	{
		if (path.nodeColor != retRefineTmp.nodeColor)
		{
#ifdef PRINTOUT
			printf("Refine-(Ori:%d)", path.cost);
#endif
			path = retRefineTmp;
#ifdef PRINTOUT
			printf("-(New:%d)", path.cost);
#endif
			return true;
		}
	}

	return false;
}


//Refine
unsigned short pathRefine(const vector<PathDetected>& pathOri1, const vector<PathDetected>& pathOri2,
	vector<unsigned short>& pathRefine1, vector<unsigned short>& pathRefine2,
	unsigned int& cost, bool& timeFlag)
{
	vector<PathDetected> path1(pathOri1);
	vector<PathDetected> path2(pathOri2);

	bitset<NODE_NUM> colorPath1;
	bitset<NODE_NUM * OUT_NUM > colorPathEdge1;
	for (int i = 0; i < path1.size(); i++)
	{
		colorPath1 = colorPath1 | path1[i].nodeColor;
		colorPathEdge1 = colorPathEdge1 | path1[i].edgeColor;
	}

	bitset<NODE_NUM> colorPath2;
	bitset<NODE_NUM * OUT_NUM > colorPathEdge2;
	for (int i = 0; i < path2.size(); i++)
	{
		colorPath2 = colorPath2 | path2[i].nodeColor;
		colorPathEdge2 = colorPathEdge2 | path2[i].edgeColor;
	}

	bitset<NODE_NUM> colorRefine = colorPath1 | colorPath2;
	bitset<NODE_NUM> colorRefineLast = colorRefine;
	for (int iter = 0; iter<20; iter++)
	{
#ifdef TIME_LIMIT
		time(&t);
		local = localtime(&t);
		end_time = 3600 * local->tm_hour + 60 * local->tm_min + local->tm_sec;
		if (end_time >= start_time + 18.5)
		{
			timeFlag = true;
			break;
		}
#endif

		for (int j = 0; j < path1.size(); j++)
		{
			colorRefine = colorRefine&(~path1[j].nodeColor);
			colorPathEdge1 = colorPathEdge1&(~path1[j].edgeColor);
			partPathRefine(path1[j], colorRefine, colorPathEdge2);
			colorRefine = colorRefine | path1[j].nodeColor;
			colorPathEdge1 = colorPathEdge1 | path1[j].edgeColor;
		}

		for (int j = 0; j < path2.size(); j++)
		{
			colorRefine = colorRefine&(~path2[j].nodeColor);
			colorPathEdge2 = colorPathEdge2&(~path2[j].edgeColor);
			partPathRefine(path2[j], colorRefine, colorPathEdge1);
			colorRefine = colorRefine | path2[j].nodeColor;
			colorPathEdge2 = colorPathEdge2 | path2[j].edgeColor;
		}

		if (colorRefine == colorRefineLast)
		{
#ifdef PRINTOUT
			printf("\n");
#endif
			break;
		}

		colorRefineLast = colorRefine;
	}

	cost = 0;

	if (path1.size() > 0)
	{
		pathRefine1.clear();
		for (int j = 0; j < path1.size(); j++)
		{
			pathRefine1.insert(pathRefine1.end(), path1[j].nodeID.begin(), path1[j].nodeID.end() - 1);
			cost += path1[j].cost;
		}
		pathRefine1.push_back(end_route);
	}

	if (path2.size() > 0)
	{
		pathRefine2.clear();
		for (int j = 0; j < path2.size(); j++)
		{
			pathRefine2.insert(pathRefine2.end(), path2[j].nodeID.begin(), path2[j].nodeID.end() - 1);
			cost += path2[j].cost;
		}
		pathRefine2.push_back(end_route);
	}

	colorPathEdge1.reset();
	for (int i = 0; i < pathRefine1.size() - 1; i++)
	{
		colorPathEdge1[adjacent_index[pathRefine1[i]][pathRefine1[i + 1]]] = 1;
	}

	colorPathEdge2.reset();
	for (int i = 0; i < pathRefine2.size() - 1; i++)
	{
		colorPathEdge2[adjacent_index[pathRefine2[i]][pathRefine2[i + 1]]] = 1;
	}

	bitset<NODE_NUM * OUT_NUM > colorPathEdge = colorPathEdge1&colorPathEdge2;
	unsigned short repassEdgeNum = colorPathEdge.count();

#ifdef PRINTOUT
	printf("\nRefine Result-(repass:%d)(cost:%d)", repassEdgeNum, cost);
#endif

	return repassEdgeNum;
}

void pathSearchDemand(unsigned int demandNow, unsigned int length,
	map<unsigned int, vector<PathNode> >& nodeMap, const vector<vector<PathDetected> >& G,
	map<unsigned int, vector<PathNode> >& nodeMapNew)
{
	priority_queue<PathNode> nodePathTmpNew;

	for (int i = 1; i < startDemandEnd.size() - 1; i++)	//对每一个必经点进行遍历
	{
		if (startDemandEnd[i] == demandNow) continue;

		//vector<PathNode> nodePathTmp(nodeMap[startDemandEnd[i]]);
		vector<PathNode> *nodePathTmpPtr=&nodeMap[startDemandEnd[i]];

		for (int j = 0; j < nodePathTmpPtr->size(); j++)  //对一个特定必经点的每一条路进行遍历
		{
			if (nodePathTmpNew.size() >= length &&
				(*nodePathTmpPtr)[j].cost >= nodePathTmpNew.top().cost)
			{
				break;
			}

			//PathNode nodeSinglePathTmp(nodePathTmp[j]);
			PathNode *nodeSinglePathTmpPtr = &((*nodePathTmpPtr)[j]);

			unsigned int index = INF;
			for (int k = 0; k < G[nodeSinglePathTmpPtr->end].size(); k++)
			{
				if (G[nodeSinglePathTmpPtr->end][k].nodeID.back() == demandNow)
				{
					index = k;
					break;
				}
			}

			if (index != INF)
			{
				PathDetected partPathTmp = G[nodeSinglePathTmpPtr->end][index];
				bitset<NODE_NUM> colorTmp = nodeSinglePathTmpPtr->nodeColor & partPathTmp.nodeColor;
				colorTmp[partPathTmp.nodeID.front()] = 0;
				if (colorTmp.any())
				{
					continue;
				}
				else
				{
					//if (nodeSinglePathTmpPtr->nodePath.size()>numOfDemand-5 &&
					//	nodeSinglePathTmpPtr->nodePath.size() < numOfDemand-2)
					//{
					//	//预检测：该点是否能经过所有未到达的必经点
					//	if (BFS_VISIT_DEMANDBit(nodeSinglePathTmpPtr->end, numOfDemand - nodeSinglePathTmpPtr->nodePath.size(),
					//		nodeSinglePathTmpPtr->nodeColor, G) == false)
					//		continue;
					//}

					//if (nodeSinglePathTmpPtr->nodePath.size() > 10 &&
					//	nodeSinglePathTmpPtr->nodePath.size() < numOfDemand - 2)
					//{

					//	//检测是否所有未到达的必经点均能到达终点
					//	bitset<NODE_NUM> colorEnd = nodeSinglePathTmpPtr->nodeColor | partPathTmp.nodeColor;
					//	//colorEnd[nodeSinglePathTmp.end] = false;
					//	if (BFS_VISIT_END2(nodeSinglePathTmpPtr->end, numOfDemand - nodeSinglePathTmpPtr->nodePath.size() - 1, colorEnd) == false)
					//		continue;
					//}


					if (nodePathTmpNew.size() >= length)
					{
						if (nodePathTmpNew.top().cost > nodeSinglePathTmpPtr->cost + partPathTmp.cost)
						{
							PathNode nodeSinglePathTmp(((*nodePathTmpPtr)[j]));

							nodeSinglePathTmp.nodePath.push_back(partPathTmp);
							nodeSinglePathTmp.cost = nodeSinglePathTmp.cost + partPathTmp.cost;
							nodeSinglePathTmp.edgeColor = nodeSinglePathTmp.edgeColor | partPathTmp.edgeColor;
							nodeSinglePathTmp.end = demandNow;
							nodeSinglePathTmp.nodeColor = nodeSinglePathTmp.nodeColor | partPathTmp.nodeColor;

							nodePathTmpNew.pop();
							nodePathTmpNew.push(nodeSinglePathTmp);

							break;
						}
					}
					else
					{
						PathNode nodeSinglePathTmp(((*nodePathTmpPtr)[j]));

						nodeSinglePathTmp.nodePath.push_back(partPathTmp);
						nodeSinglePathTmp.cost = nodeSinglePathTmp.cost + partPathTmp.cost;
						nodeSinglePathTmp.edgeColor = nodeSinglePathTmp.edgeColor | partPathTmp.edgeColor;
						nodeSinglePathTmp.end = demandNow;
						nodeSinglePathTmp.nodeColor = nodeSinglePathTmp.nodeColor | partPathTmp.nodeColor;

						nodePathTmpNew.push(nodeSinglePathTmp);
					}
				}
			}

		}
	}

	vector<PathNode> vectorTmp(nodePathTmpNew.size());
	for (int i = nodePathTmpNew.size() - 1; i >= 0; i--)
	{
		vectorTmp[i] = nodePathTmpNew.top();
		nodePathTmpNew.pop();
	}

	nodeMapNew[demandNow] = vectorTmp;
}

void pathSearchEnd(unsigned int end, unsigned int length,
	map<unsigned int, vector<PathNode> >& nodeMap, vector<vector<PathDetected> >& pathAll)
{
	priority_queue<PathNode> nodePathTmpNew;
	for (int i = 1; i < startDemandEnd.size() - 1; i++)	//对每一个必经点进行遍历
	{
		//vector<PathNode> nodePathTmp(nodeMap[startDemandEnd[i]]);
		vector<PathNode> *nodePathTmpPtr=&nodeMap[startDemandEnd[i]];

		for (int j = 0; j < nodePathTmpPtr->size(); j++)  //对一个特定必经点的每一条路进行遍历
		{
			if (nodePathTmpNew.size() >= length &&
				(*nodePathTmpPtr)[j].cost >= nodePathTmpNew.top().cost)
			{
				break;
			}

			//PathNode nodeSinglePathTmp(nodePathTmp[j]);
			PathNode *nodeSinglePathTmpPtr = &((*nodePathTmpPtr)[j]);

			PathDetected retTmp;
			bitset<NODE_NUM> colorDij = nodeSinglePathTmpPtr->nodeColor;
			if (dijikstraPriorQueue(nodeSinglePathTmpPtr->end, end, colorDij, retTmp.nodeID, retTmp.nodeColor, retTmp.cost))
			{
				if (nodePathTmpNew.size() >= length)
				{
					if (nodePathTmpNew.top().cost > nodeSinglePathTmpPtr->cost + retTmp.cost)
					{
						PathNode nodeSinglePathTmp(((*nodePathTmpPtr)[j]));

						nodeSinglePathTmp.nodePath.push_back(retTmp);
						nodeSinglePathTmp.cost = nodeSinglePathTmp.cost + retTmp.cost;
						nodeSinglePathTmp.edgeColor = nodeSinglePathTmp.edgeColor | retTmp.edgeColor;
						nodeSinglePathTmp.end = end;
						nodeSinglePathTmp.nodeColor = nodeSinglePathTmp.nodeColor | retTmp.nodeColor;

						nodePathTmpNew.pop();
						nodePathTmpNew.push(nodeSinglePathTmp);
					}
				}
				else
				{
					PathNode nodeSinglePathTmp(((*nodePathTmpPtr)[j]));

					nodeSinglePathTmp.nodePath.push_back(retTmp);
					nodeSinglePathTmp.cost = nodeSinglePathTmp.cost + retTmp.cost;
					nodeSinglePathTmp.edgeColor = nodeSinglePathTmp.edgeColor | retTmp.edgeColor;
					nodeSinglePathTmp.end = end;
					nodeSinglePathTmp.nodeColor = nodeSinglePathTmp.nodeColor | retTmp.nodeColor;

					nodePathTmpNew.push(nodeSinglePathTmp);
				}
			}
		}
	}

	vector<PathNode> vectorTmp(nodePathTmpNew.size());
	pathAll.clear();
	pathAll.resize(nodePathTmpNew.size());
	for (int i = nodePathTmpNew.size() - 1; i >= 0; i--)
	{
		vectorTmp[i] = nodePathTmpNew.top();
		pathAll[i] = nodePathTmpNew.top().nodePath;
		nodePathTmpNew.pop();
	}

	nodeMap[end] = vectorTmp;
}


void FindrouteBFS( vector<vector<PathDetected> >& pathAll,const unsigned char way, 
	const unsigned int maxPathCost)
{
	vector<vector<PathDetected > >   retAll(numOfNode);

	//起点到必经点
	for (int i = 0; i < 1; i++)
	{
		//for (int j = 1; j < startDemandEnd.size() - 1; j++)
		//{
		//	if (i == j) continue;
		//	PathDetected retTmp;
		//	if (BFS_VISIT_NODE(startDemandEnd[i], startDemandEnd[j], retTmp.nodeID,
		//		retTmp.nodeColor, retTmp.edgeColor, retTmp.cost))
		//	{
		//		retAll[startDemandEnd[i]].push_back(retTmp);
		//	}
		//}

		BFS_VISIT_NODE(startDemandEnd[i], numOfDemand, retAll[startDemandEnd[i]]);
	}
	//必经点到必经点
	for (int i = 1; i < startDemandEnd.size() - 1; i++)
	{
		//for (int j = 1; j < startDemandEnd.size() - 1; j++)
		//{
		//	if (i == j) continue;
		//	PathDetected retTmp;
		//	if (BFS_VISIT_NODE(startDemandEnd[i], startDemandEnd[j], retTmp.nodeID,
		//		retTmp.nodeColor, retTmp.edgeColor, retTmp.cost))
		//	{
		//		retAll[startDemandEnd[i]].push_back(retTmp);
		//	}
		//}

		BFS_VISIT_NODE(startDemandEnd[i], numOfDemand-1, retAll[startDemandEnd[i]]);
	}

	////排序
	//for (int i = 0; i < startDemandEnd.size() - 1; i++)
	//{
	//	//剪枝
	//	pathSort(retAll[startDemandEnd[i]], 1);
	//	for (int j = 0; j<retAll[startDemandEnd[i]].size(); j++)
	//	{
	//		if (retAll[startDemandEnd[i]][j].cost>maxPathCost)
	//		{
	//			retAll[startDemandEnd[i]].erase(retAll[startDemandEnd[i]].begin() + j, retAll[startDemandEnd[i]].end());
	//			break;
	//		}
	//	}

	//	pathSort(retAll[startDemandEnd[i]], way);
	//}

#ifdef PRINTOUT
	//打印
	for (int i = 0; i < startDemandEnd.size() - 1; i++)
	{
		for (int j = 0; j < retAll[startDemandEnd[i]].size(); j++)
		{
			printf("Path-");
			for (int k = 0; k < retAll[startDemandEnd[i]][j].nodeID.size(); k++)
			{
				printf("-%d", retAll[startDemandEnd[i]][j].nodeID[k]);
			}
			printf("--Cost:%d", retAll[startDemandEnd[i]][j].cost);
			printf("\n");
		}

	}
#endif

	//初始化
	map<unsigned int, vector<PathNode> >  nodePathMap;
	for (int i = 0; i < retAll[start_route].size(); i++)
	{
		PathNode nodePathTmp;
		PathDetected partPathTmp;
		partPathTmp = retAll[start_route][i];
		nodePathTmp.nodePath.push_back(partPathTmp);
		nodePathTmp.cost = partPathTmp.cost;
		nodePathTmp.edgeColor = partPathTmp.edgeColor;
		nodePathTmp.nodeColor = partPathTmp.nodeColor;
		nodePathTmp.end = partPathTmp.nodeID.back();

		nodePathMap[partPathTmp.nodeID.back()].push_back(nodePathTmp);
	}

	for (int iter = 1; iter < startDemandEnd.size() - 2; iter++)
	{
		map<unsigned int, vector<PathNode> >  nodePathMapOri = nodePathMap;
		//unsigned int num = 10 * iter / numOfDemand + 3;
		//unsigned int num = iter / 10 + 5;
		unsigned int num = numOfDemand - iter;
		if (num < 3)	num = 3;

		if (num > 20) num = 20;

		if (iter == 1) num = numOfDemand - iter;
		
		for (int i = 1; i < startDemandEnd.size() - 1; i++)
		{
			pathSearchDemand(startDemandEnd[i], num, nodePathMapOri, retAll, nodePathMap);
		}
	}
	pathSearchEnd(startDemandEnd.back(), numOfDemand, nodePathMap, pathAll);

#ifdef PRINTOUT
	//打印
	if (nodePathMap[startDemandEnd.back()].size()>0> 0)
	{
		vector<PathDetected> pathFound = nodePathMap[startDemandEnd.back()].front().nodePath;
		printf("Path-");
		for (int j = 0; j < pathFound.size(); j++)
		{
			for (int k = 0; k < pathFound[j].nodeID.size() - 1; k++)
			{
				printf("-%d", pathFound[j].nodeID[k]);
			}
		}
		printf("-%d", pathFound.back().nodeID.back());
		printf("\n");
	}
#endif


}

//你要完成的功能总入口
void search_route(char *topo[MAX_EDGE_NUM], int edge_num, char *demand[MAX_DEMAND_NUM], int demand_num)
{
	time(&t);
	local = localtime(&t);
	start_time = 3600 * local->tm_hour + 60 * local->tm_min + local->tm_sec;

	destroyMemory(); //clear the original memory
	numOfNode = getAdjacent(topo, edge_num);
	numOfNode = loadMap2(topo, edge_num);
	sortMap(numOfNode);


	vector<vector<PathDetected> > pathAll_1;
	vector<vector<PathDetected> > pathAll_2;
	/****************************WAY-1*****************************/
	numOfDemand = loadDemand(demand[0]);
	if (numOfDemand == 0)
	{
		bitset<NODE_NUM> colorPath;
		bitset<NODE_NUM * OUT_NUM> edgeColorPath;
		PathDetected partPathTmp;
		if (dijikstraPriorQueue(start_route, end_route, 
			colorPath, edgeColorPath, 
			partPathTmp.nodeID, partPathTmp.nodeColor, partPathTmp.edgeColor, partPathTmp.cost))
		{
			vector<PathDetected> pathTmp;
			pathTmp.push_back(partPathTmp);
			pathAll_1.push_back(pathTmp);
		}
	}
	else if (numOfDemand >= 60)
	{
		pathAll_1.clear();

		FindrouteBFS(pathAll_1, 1, 2000, 5);
	}
	else
	{
		pathAll_1.clear();

		//FindrouteBFS(pathAll_1, 1, 2000);

		FindrouteBFS(pathAll_1, 1, 2000, 5);
	}
	/****************************END*******************************/
	vector<unsigned short> bfsPathMin;
	if (pathAll_1[0].size() > 0)
	{
		bfsPathMin.clear();
		for (int j = 0; j < pathAll_1[0].size(); j++)
		{
			bfsPathMin.insert(bfsPathMin.end(), pathAll_1[0][j].nodeID.begin(), pathAll_1[0][j].nodeID.end() - 1);
		}
		bfsPathMin.push_back(end_route);
	}
	for (int i = 0; i < bfsPathMin.size() - 1; i++)
		record_result(WORK_PATH, adjacent_index[bfsPathMin[i]][bfsPathMin[i + 1]]);



	/****************************CLEAR*****************************/
	clearDemand(demand[0]);
	clear_flag = true;
	/****************************END*******************************/


	/****************************WAY-2*****************************/
	numOfDemand = loadDemand(demand[1]);
	if (numOfDemand == 0)
	{
		bitset<NODE_NUM> colorPath;
		bitset<NODE_NUM * OUT_NUM> edgeColorPath;
		PathDetected partPathTmp;
		if (dijikstraPriorQueue(start_route, end_route,
			colorPath, edgeColorPath,
			partPathTmp.nodeID, partPathTmp.nodeColor, partPathTmp.edgeColor, partPathTmp.cost))
		{
			vector<PathDetected> pathTmp;
			pathTmp.push_back(partPathTmp);
			pathAll_2.push_back(pathTmp);
		}
	}
	else if (numOfDemand >= 40)
	{
		pathAll_2.clear();

		FindrouteBFS(pathAll_2, 1, 2000, 16);
	}
	else
	{
		pathAll_2.clear();

		//FindrouteBFS(pathAll_2, 1, 2000);

		FindrouteBFS(pathAll_2, 1, 2000, 16);
	}
	/****************************END*******************************/
	bfsPathMin.clear();
	if (pathAll_2[0].size() > 0)
	{
		bfsPathMin.clear();
		for (int j = 0; j < pathAll_2[0].size(); j++)
		{
			bfsPathMin.insert(bfsPathMin.end(), pathAll_2[0][j].nodeID.begin(), pathAll_2[0][j].nodeID.end() - 1);
		}
		bfsPathMin.push_back(end_route);
	}
	for (int i = 0; i < bfsPathMin.size() - 1; i++)
		record_result(BACK_PATH, adjacent_index[bfsPathMin[i]][bfsPathMin[i + 1]]);

	return;


	/****************************Refine****************************/
	vector<unsigned short> bfsPath1, bfsPath2;
	vector<unsigned short> bfsPathMin1, bfsPathMin2;
	unsigned short minRepass = INF;
	unsigned int minWeight = INF;
	bool timeUp_flag = false;
	for (int i = pathAll_1.size() - 1; i >= 0; i--)
	{
		for (int j = pathAll_2.size() - 1; j >= 0; j--)
		{
			unsigned int weight = 0;
			unsigned short repassNum = pathRefine(pathAll_1[i], pathAll_2[j], bfsPath1, bfsPath2, weight, timeUp_flag);
			if (repassNum < minRepass)
			{
				bfsPathMin1 = bfsPath1;
				bfsPathMin2 = bfsPath2;

				minRepass = repassNum;
				minWeight = weight;
			}
			else if (repassNum == minRepass)
			{
				if (weight < minWeight)
				{
					bfsPathMin1 = bfsPath1;
					bfsPathMin2 = bfsPath2;

					minWeight = weight;
				}
			}

			if (timeUp_flag) break;
		}

		if (timeUp_flag) break;
	}

#ifdef PRINTOUT
	printf("\nResult-(repass:%d)(cost:%d)\n", minRepass, minWeight);
#endif

	if (bfsPathMin1.size() > 0)
	{
		for (int i = 0; i < bfsPathMin1.size() - 1; i++)
			record_result(WORK_PATH, adjacent_index[bfsPathMin1[i]][bfsPathMin1[i + 1]]);
	}
	else
	{
		//record_result(WORK_PATH, 'NA');
		return;
	}

	if (bfsPathMin2.size() > 0)
	{
		for (int i = 0; i < bfsPathMin2.size() - 1; i++)
			record_result(BACK_PATH, adjacent_index[bfsPathMin2[i]][bfsPathMin2[i + 1]]);
	}
	else
	{
		//record_result(BACK_PATH, 'NA');
		return;
	}
	/****************************END*******************************/

}
