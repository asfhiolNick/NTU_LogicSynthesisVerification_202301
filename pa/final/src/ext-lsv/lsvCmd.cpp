#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <queue>
extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_TravAll(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_trav_all", Lsv_TravAll, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this root:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

//************************************************************//
//  2023.12.12 10:38pm                                        //
//************************************************************//
// Abc_CommandShowBdd(abc.c) -> Abc_NodeShowBdd(abcShow.c) -> //
// Cudd_DumpDot(cuddExport.c) -> cuddCollectNodes(cuddUtil.c) //
// This shows how author implement "bdd_show" and traversal   //
//************************************************************//
pair<int,int> collectEdge(DdManager* dd, DdNode* source){
    queue<pair<DdNode*,int>> q;
    q.push(make_pair(source, 0));
    unordered_set<DdNode*> visited;
    int terminal = 0;

    while(!q.empty()){
        //#0 Visit a node
        pair<DdNode*,int> node = q.front(); q.pop();
        DdNode* curr = node.first; int currVar = node.second;
        //#1 special case: terminal/visited
        if(curr == Cudd_ReadOne(dd) ||curr == Cudd_ReadZero(dd) || curr == Cudd_Not(Cudd_ReadOne(dd)) || curr == Cudd_Not(Cudd_ReadZero(dd)) || visited.count(curr)){
            terminal += (curr == Cudd_ReadOne(dd) || curr == Cudd_Not(Cudd_ReadZero(dd))); continue;
        }
        else visited.insert(curr);

        //#2 recursive call: move down the var index until sensitive to var
        int nextVar;
        for(nextVar = currVar; curr == Cudd_Cofactor(dd, curr, Cudd_bddIthVar(dd, nextVar)); nextVar++){}
        DdNode* curr_T = Cudd_Cofactor(dd, curr, Cudd_bddIthVar(dd, nextVar));
        q.push(make_pair(curr_T, nextVar+1));
        DdNode* curr_E = Cudd_Cofactor(dd, curr, Cudd_Not(Cudd_bddIthVar(dd, nextVar)));
        q.push(make_pair(curr_E, nextVar+1));
    }
    return make_pair(int(visited.size()),terminal);
}

//************************************************************//
//  2023.12.24                                                //
//************************************************************//
double layerTraversal(DdManager * dd, vector<DdNode*> f_vec, const int bdd_num){
    unordered_map<DdNode*,double> factor;
    unordered_map<DdNode*, vector<pair<DdNode*,bool>>> parents;
    unordered_map<DdNode*, pair<int,int>> duplicate;
    vector<vector<DdNode*>> table(bdd_num+1);

    //#step0: initialize
    DdNode* pseudo = (DdNode*)(0); factor[pseudo] = 1.0;
    for(int i=0; i<f_vec.size(); ++i){
        parents[f_vec[i]].push_back(make_pair(pseudo,0));
        table[0].push_back(f_vec[i]);
    }

    //#step1: traversal each layer i
    for(int i=0; i<bdd_num; ++i){
        if(table[i].size()==0) continue;
        //remove duplicate node
        sort(table[i].begin(), table[i].end());
        table[i].erase(unique(table[i].begin(), table[i].end()), table[i].end());

        for(int j=0; j<table[i].size(); ++j){
            //part 1: calculate node's factor
            DdNode* curr = table[i][j];
            const vector<pair<DdNode*,bool>>& parent_vec = parents[curr];
            const int income_sz = parent_vec.size();
            double mini = 1.0;
            for(int k=0; k<income_sz; ++k){
                DdNode* pre = parent_vec[k].first;
                const bool isCNot = parent_vec[k].second;
                mini = min(mini, factor[pre]*(isCNot?0.8:1.0));
            }
            mini /= income_sz;
            factor[curr] = mini;

            //part 2: recursion on child nodes
            int next_i;
            DdNode* curr_T = Cudd_Cofactor(dd, curr, Cudd_bddIthVar(dd, i));
            for(next_i = i+1; next_i < bdd_num; next_i++){
                if(curr_T != Cudd_Cofactor(dd, curr_T, Cudd_bddIthVar(dd, next_i))) break;
            }
            table[next_i].push_back(curr_T);
            parents[curr_T].push_back(make_pair(curr,0));

            DdNode* curr_E = Cudd_Cofactor(dd, curr, Cudd_Not(Cudd_bddIthVar(dd, i)));
            for(next_i = i+1; next_i < bdd_num; next_i++){
                if(curr_E != Cudd_Cofactor(dd, curr_E, Cudd_bddIthVar(dd, next_i))) break;
            }
            table[next_i].push_back(curr_E);
            parents[curr_E].push_back(make_pair(curr,1));

            //#part 3: node duplication
            if(income_sz == 1) continue;
            pair<int,int> count = collectEdge(dd, curr);
            duplicate.insert(make_pair(curr, count));
        }
    }
    //#step2: terminal layer
    DdNode* curr = Cudd_ReadOne(dd);
    const vector<pair<DdNode*,bool>>& parent_vec = parents[curr];
    const int terminal_sz = parent_vec.size();
    double mini = 1.0;
    for(int k=0; k<terminal_sz; ++k){
        DdNode* pre = parent_vec[k].first;
        const bool isCNot = parent_vec[k].second;
        mini = min(mini, factor[pre]*(isCNot?0.8:1.0));
    }
    mini /= terminal_sz;
    factor[curr] = mini;

    //#step3: find the critical path
    DdNode* chosen = (DdNode*)0;
    double record = 1.0;
    while(find(f_vec.begin(), f_vec.end(), curr)==f_vec.end() || abs(mini-1.0)>1e-6){
        const vector<pair<DdNode*,bool>>& parent_vec = parents[curr];
        const int income_sz = parent_vec.size();

        if(duplicate.count(curr) && record){
            double ratio = double(income_sz*terminal_sz)/(terminal_sz+(income_sz-1)*duplicate[curr].second);
            if(record < ratio){
                record = ratio;
                chosen = curr;
            }
        }

        for(int k=0; k<income_sz; ++k){
            DdNode* pre = parent_vec[k].first;
            const bool isCNot = parent_vec[k].second;
            if(abs(mini - factor[pre]*(isCNot?0.8:1.0)/income_sz) < 1e-6){
                curr = pre; mini = factor[pre];
                break;
            }
        }
    }

    //step4: output answer
    if(record > 1.0+1e-6){
        const int income_sz = parents[chosen].size();
        cout << "duplicate " << chosen << " " << (income_sz-1) << " times, eff-factor: " << factor[Cudd_ReadOne(dd)] << " -> " <<  factor[Cudd_ReadOne(dd)]*record;
        cout << " (" << record << "x)" << endl;
        cout << "costing " << duplicate[chosen].first*(income_sz-1) << " nodes" << endl;
    }
    else{
        cout << "no duplication benifit, eff-factor: " << factor[Cudd_ReadOne(dd)] << " (0x)" << endl;
    }

    double terminal_ratio = (double)parents[Cudd_ReadOne(dd)].size()/(duplicate[chosen].first*(parents[chosen].size()-1) + parents[Cudd_ReadOne(dd)].size());
    cout << "terminal ratio: " << terminal_ratio << endl;

    return factor[Cudd_ReadOne(dd)];
}
//************************************************************//
//  2023.12.20 start                                          //
//************************************************************//
int Lsv_TravAll(Abc_Frame_t* pAbc, int argc, char** argv){
    vector<DdNode*> f_vec;
    int bdd_num = 0;

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc); Abc_Obj_t* pPo; int ithPo = 0;
    Abc_NtkForEachPo(pNtk, pPo, ithPo){
        Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
        assert( Abc_NtkIsBddLogic(pRoot->pNtk) );
        DdManager * dd = (DdManager *)pRoot->pNtk->pManFunc;
        DdNode* f = (DdNode *)pRoot->pData;
        bdd_num = max(bdd_num, Abc_ObjFaninNum(pRoot));

        f_vec.push_back(f);
        if(ithPo == Abc_NtkPoNum(pNtk)-1){
            const double eff_factor = layerTraversal(dd, f_vec, bdd_num);
            cout << " -> mini: " << eff_factor << endl;
        }
    }
    cout << "===============================" << endl;
    return 0;
}
