#include "dflow_calc.h"
#include <stdlib.h>
#include <stdio.h>
#include <iostream>
#include <vector>
#include <functional>
#include <queue>
enum node_type{
    regular,
    ENTRY,
    EXIT
};
class my_node{
    public:
    node_type nodetype;
    unsigned int index;
    const InstInfo* inst;
    unsigned int instr_cycles;
    my_node *dep1;
    my_node *dep2;

    my_node(node_type nodetype,const InstInfo* inst, unsigned int instr_cycles,unsigned int index){
        this->inst = nodetype==regular?inst:NULL;
        this->instr_cycles = nodetype==regular?instr_cycles:0;
        this->index = index;
        this->dep1 = NULL;
        this->dep2 = NULL;
    }
    void check_dep_helper(unsigned int tmp_src,unsigned int tmp_dst,my_node** dep,my_node* nodes_arr[],int i){
            if(tmp_src == tmp_dst){
                if(*dep == nodes_arr[i]){
                    //already found this dependency
                    return;
                }
                if(*dep == NULL){
                    *dep = nodes_arr[i];
                    return;
                }
                // this is an earlier assignment to the same dependenciy register;and we assume no strucutral hazards
            }
    }
    void find_dependencies(my_node* nodes_arr[], unsigned int numOfInsts){
        for(int i = index-1; i>=0; i--){
            unsigned int tmp_src1_id = this->inst->src1Idx;
            unsigned int tmp_src2_id = this->inst->src2Idx;
            unsigned int tmp_dst_id = nodes_arr[i]->inst->dstIdx;
            check_dep_helper(tmp_src1_id,tmp_dst_id,&dep1,nodes_arr,i);
            check_dep_helper(tmp_src2_id,tmp_dst_id,&dep2,nodes_arr,i);
        }

    }
    bool if_fictive(){
        return nodetype==ENTRY || nodetype==EXIT;
    }
    bool if_entry(){
        return nodetype==ENTRY;
    }
    bool if_exit(){
        return nodetype==EXIT;
    }
    
};

class dependency_graph{
    public:
    std::vector<my_node*> nodes_with_no_dependencies;
    my_node* entry_node;
    my_node* exit_node;
    my_node** nodes_arr;
    const InstInfo* progTrace;
    unsigned int numOfInsts;
    dependency_graph(const unsigned int opsLatency[], const InstInfo progTrace[], unsigned int numOfInsts){
        nodes_arr = new my_node*[numOfInsts];
        entry_node = new my_node(ENTRY,NULL,0,0);
        exit_node = new my_node(EXIT,NULL,0,numOfInsts+1);
        this->progTrace = progTrace;
        this->numOfInsts = numOfInsts;
    }
    unsigned int find_opcode_latency(const unsigned int opsLatency[], const InstInfo* inst){
        return opsLatency[inst->opcode];
    }
    void find_nodes_no_one_depend_on(my_node* nodes_arr[],unsigned int numOfInsts){
    bool all_nodes[numOfInsts];
    for(unsigned int i = 0; i < numOfInsts; i++){
        all_nodes[i] = false;
    }
    for(unsigned int i = 0; i < numOfInsts; i++){
        if(nodes_arr[i]->dep1 != NULL){
            all_nodes[nodes_arr[i]->dep1->index] = true;
        }
        if(nodes_arr[i]->dep2 != NULL){
            all_nodes[nodes_arr[i]->dep2->index] = true;
        }
    }
    for(unsigned int i = 0; i < numOfInsts; i++){
        if(!all_nodes[i]){
            nodes_with_no_dependencies.push_back(nodes_arr[i]);
        }
    }
}
    void fill_fictive_node(node_type nodetype,my_node* fictive_node,my_node* nodes_arr[],unsigned int numOfInsts){
        if(nodetype==ENTRY){
            for(unsigned int i = 0; i < numOfInsts; i++){
                if(nodes_arr[i]->dep1 == NULL){
                    nodes_arr[i]->dep1 = fictive_node;
                }
                if(nodes_arr[i]->dep2 == NULL){
                    nodes_arr[i]->dep2 = fictive_node;
                }
            }
        }else if(nodetype==EXIT){
            //find the nodes that no one depend on them
            find_nodes_no_one_depend_on(nodes_arr,numOfInsts);
        }else{
            printf("Error: wrong node type\n");
            return;
        }
    }
    ProgCtx do_analyzeProg(const unsigned int opsLatency[], const InstInfo progTrace[], unsigned int numOfInsts){
        for(unsigned int i = 0; i < numOfInsts; i++){
            nodes_arr[i] = new my_node(regular,&progTrace[i],find_opcode_latency(opsLatency,&progTrace[i]),i);
        }
        for(unsigned int i = numOfInsts-1; i > 0; i--){ // > 0 because 0 surly have no dependes
            nodes_arr[i]->find_dependencies(nodes_arr,numOfInsts);
        }
        fill_fictive_node(ENTRY,entry_node,nodes_arr,numOfInsts);
        fill_fictive_node(EXIT,exit_node,nodes_arr,numOfInsts);
        return (ProgCtx)this;
    } 
    int do_getInstDepth(unsigned int theInst){
        my_node* src_node;
        if (theInst >= numOfInsts) {
            return -1; // invalid instr index
        }
        src_node = nodes_arr[theInst];
        std::function<int(my_node*)> findDepth = [&](my_node* node) -> int {
            if (node == entry_node) {
                return 0; // Entry node has depth weight of 0
            }
            int dep1_depth = 0, dep2_depth = 0;
            if (node->dep1) {
                dep1_depth = findDepth(node->dep1);
            }
            if (node->dep2) {
                dep2_depth = findDepth(node->dep2);
            }
            return std::max(dep1_depth, dep2_depth) + node->instr_cycles;
        };
        return (findDepth(src_node)-src_node->instr_cycles);
    }
    int getInstDeps(unsigned int theInst, int *src1DepInst, int *src2DepInst){
        if (theInst >= numOfInsts) {
            return -1; // invalid instr index
        }
        my_node* src_node = nodes_arr[theInst];
        *src1DepInst = (src_node->dep1 && src_node->dep1!=entry_node) ? src_node->dep1->index : -1;
        *src2DepInst = (src_node->dep2 && src_node->dep2!=entry_node) ? src_node->dep2->index : -1;
        return 0;
    }
    int getProgDepth(){
        std::priority_queue<int> maxHeap;
        for(auto i : nodes_with_no_dependencies){
            maxHeap.push(do_getInstDepth(i->index)+i->instr_cycles);
        }
        return maxHeap.top();
    }
    ~dependency_graph(){
        for(unsigned int i = 0; i < numOfInsts; i++){
            delete nodes_arr[i];
        }
        delete[] nodes_arr;
        delete entry_node;
        delete exit_node;

    }

};
ProgCtx analyzeProg(const unsigned int opsLatency[], const InstInfo progTrace[], unsigned int numOfInsts){
    dependency_graph* graph = new dependency_graph(opsLatency,progTrace,numOfInsts);
    return graph->do_analyzeProg(opsLatency,progTrace,numOfInsts);
}
int getInstDepth(ProgCtx ctx, unsigned int theInst){
    return ((dependency_graph*)ctx)->do_getInstDepth(theInst);
}
int getInstDeps(ProgCtx ctx, unsigned int theInst, int *src1DepInst, int *src2DepInst){
    return ((dependency_graph*)ctx)->getInstDeps(theInst,src1DepInst,src2DepInst);
}
int getProgDepth(ProgCtx ctx){
    return ((dependency_graph*)ctx)->getProgDepth();
}
void freeProgCtx(ProgCtx ctx){
    delete (dependency_graph*)ctx;
}