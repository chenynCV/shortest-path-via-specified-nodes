#include "stdafx.h"

#include "route.h"
#include "lib_io.h"
#include "lib_time.h"
#include "stdio.h"

#include <iostream>

int main(int argc, char *argv[])
{
	argc = 3;
	argv[1] = "../case0/topo0.csv";
	argv[2] = "../case0/demand0.csv";
	argv[3] = "../case0/result.csv";

	//argv[1] = "../case1/topo.csv";
	//argv[2] = "../case1/demand.csv";
	//argv[3] = "../case1/result0.csv";

    print_time("Begin");
    char *topo[MAX_EDGE_NUM];
    int edge_num;
    char *demand[MAX_DEMAND_NUM];
    int demand_num;

    char *topo_file = argv[1];
    edge_num = read_file(topo, MAX_EDGE_NUM, topo_file);
    if (edge_num == 0)
    {
        printf("Please input valid topo file.\n");
        return -1;
    }
    char *demand_file = argv[2];
    demand_num = read_file(demand, MAX_DEMAND_NUM, demand_file);
    if (demand_num != MAX_DEMAND_NUM)
    {
        printf("Please input valid demand file.\n");
        return -1;
    }

    search_route(topo, edge_num, demand, demand_num);

    char *result_file = argv[3];
    write_result(result_file);
    release_buff(topo, edge_num);
    release_buff(demand, demand_num);

    print_time("End");

	int debug_in = 0;
	std::cin >> debug_in;

	return 0;
}

