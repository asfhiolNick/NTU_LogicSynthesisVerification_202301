#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <unordered_map>
#include <queue>
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SimBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SimAig(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SymBdd(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_bdd", Lsv_SimBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_aig", Lsv_SimAig, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_bdd", Lsv_SymBdd, 0);
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
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
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

//***************************//
//  2023.11.25 10pm          //
//***************************//
bool dfsSolver(DdManager* dd, DdNode* f, string& answer, int bdd_th){
    //#0 terminal condition
    if(f==DD_ONE(dd) || f==Cudd_Not(DD_ZERO(dd))) return true;
    if(f==DD_ZERO(dd) || f==Cudd_Not(DD_ONE(dd))) return false;

    //#1 left-side recursion
    DdNode* pos_bddNode = Cudd_bddIthVar(dd, bdd_th);
    DdNode* f_pos = Cudd_Cofactor(dd, f, pos_bddNode);
    Cudd_Ref(f_pos);
    if(dfsSolver(dd, f_pos, answer, bdd_th+1)==true){
        answer[bdd_th] = '1';
        Cudd_RecursiveDeref(dd, f_pos);
        return true;
    }

    //#2 right-side recursion
    DdNode* neg_bddNode = Cudd_Not(pos_bddNode);
    DdNode* f_neg = Cudd_Cofactor(dd, f, neg_bddNode);
    Cudd_Ref(f_neg);
    if(dfsSolver(dd, f_neg, answer, bdd_th+1)==true){
        answer[bdd_th] = '0';
        Cudd_RecursiveDeref(dd, f_neg);
        return true;
    }

    Cudd_RecursiveDeref(dd, f_pos);
    Cudd_RecursiveDeref(dd, f_neg);
    return false;
}
//
int Lsv_SymBdd(Abc_Frame_t* pAbc, int argc, char** argv){
    //#0 Readin
    if(argc<4){
        cout << "error: read input failed." << endl;
        return 0;
    }
    const int out_th = stoi(argv[1]);
    const int in_0th = stoi(argv[2]);
    const int in_1th = stoi(argv[3]);

    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    const int inp_num = Abc_NtkPiNum(pNtk);
    if(out_th >= inp_num || in_0th>= inp_num|| in_1th>= inp_num){
        cout << "error: outside BDD index." << endl; return 0;
    }
    else if(in_0th == in_1th){
        cout << "error: two inputs are the same." << endl; return 0;
    }

    //#1 Pre-process
    Abc_Obj_t* pPo = Abc_NtkPo(pNtk, out_th);
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
    assert( Abc_NtkIsBddLogic(pRoot->pNtk) );
    DdManager * dd = (DdManager *)pRoot->pNtk->pManFunc;
    DdNode* f = (DdNode *)pRoot->pData;

    unordered_map<string, int> name2input;
    Abc_Obj_t* pPi;
    int ithPi = 0;
    Abc_NtkForEachPi(pNtk, pPi, ithPi){
        name2input[Abc_ObjName(pPi)] = ithPi;
    }

    //#2 index -> bdd order
    char** bdd2name_arr = (char**)Abc_NodeGetFaninNames(pRoot)->pArray;
    const int bdd_num = Abc_ObjFaninNum(pRoot);
    int bdd_0th = -1;
    int bdd_1th = -1;

    for(int i=0; i<bdd_num; ++i){
        if(strcmp(bdd2name_arr[i], Abc_ObjName(Abc_NtkPi(pNtk, in_0th)))==0)
            bdd_0th = i;
        if(strcmp(bdd2name_arr[i], Abc_ObjName(Abc_NtkPi(pNtk, in_1th)))==0)
            bdd_1th = i;
    }

    //#3 bdd order -> in BDD or not
    DdNode* counterNode;
    if(bdd_0th==-1 && bdd_1th==-1){
        cout << "symmetric" << endl;
        return 0;
    }
    else if(bdd_0th!=-1 && bdd_1th==-1){
        cout << "asymmetric" << endl;
        counterNode = Cudd_bddBooleanDiff(dd, f, bdd_0th);
        Cudd_Ref(counterNode);
    }
    else if(bdd_0th==-1 && bdd_1th!=-1){
        cout << "asymmetric" << endl;
        counterNode = Cudd_bddBooleanDiff(dd, f, bdd_1th);
        Cudd_Ref(counterNode);
    }
    else{
        DdNode* zero_0th = Cudd_Not(Cudd_bddIthVar(dd, bdd_0th));
        DdNode* one_0th = Cudd_bddIthVar(dd, bdd_0th);
        DdNode* zero_1th = Cudd_Not(Cudd_bddIthVar(dd, bdd_1th));
        DdNode* one_1th = Cudd_bddIthVar(dd, bdd_1th);
        Cudd_Ref(zero_0th);
        Cudd_Ref(one_0th);
        Cudd_Ref(zero_1th);
        Cudd_Ref(one_1th);

        //#3.1 compute f_01
        DdNode* f_0 = Cudd_Cofactor(dd, f, zero_0th);
        Cudd_Ref(f_0);
        Cudd_RecursiveDeref(dd, zero_0th);

        DdNode* f_01 = Cudd_Cofactor(dd, f_0, one_1th);
        Cudd_Ref(f_01);
        Cudd_RecursiveDeref(dd, f_0);
        Cudd_RecursiveDeref(dd, one_1th);

        //#3.2 compute f_10
        DdNode* f_1 = Cudd_Cofactor(dd, f, one_0th);
        Cudd_Ref(f_1);
        Cudd_RecursiveDeref(dd, one_0th);

        DdNode* f_10 = Cudd_Cofactor(dd, f_1, zero_1th);
        Cudd_Ref(f_10);
        Cudd_RecursiveDeref(dd, f_1);
        Cudd_RecursiveDeref(dd, zero_1th);

        //#3.3 f_01 vs f_10
        counterNode = Cudd_bddXor(dd, f_01, f_10);
        Cudd_Ref(counterNode);
        Cudd_RecursiveDeref(dd, f_01);
        Cudd_RecursiveDeref(dd, f_10);

        if(counterNode == DD_ZERO(dd) || counterNode == Cudd_Not(DD_ONE(dd))){
            Cudd_RecursiveDeref(dd, counterNode);
            cout << "symmetric" << endl;
            return 0;
            //  Cudd_Not(...) is necessary   //
            //  otherwise 0!=6 in benchmark  //
        }
        cout << "asymmetric" << endl;
    }
    //#4 search counterNode's onset
    string example_orderbdd(bdd_num,'1');
    string example_f01(inp_num,'1');
    string example_f10(inp_num,'1');

    const bool solvable = dfsSolver(dd, counterNode, example_orderbdd, 0);
    Cudd_RecursiveDeref(dd, counterNode);
    if(!solvable){
        cout << "error: failed to find a counterexample." << endl;
        return 0;
    }

    //#5 give counter-example
    for(int i=0; i<bdd_num; ++i){
        example_f01[name2input[bdd2name_arr[i]]] = example_orderbdd[i];
        example_f10[name2input[bdd2name_arr[i]]] = example_orderbdd[i];
    }
    example_f01[in_0th] = '0'; example_f01[in_1th] = '1';
    example_f10[in_0th] = '1'; example_f10[in_1th] = '0';
    cout << example_f01 << endl;
    cout << example_f10 << endl;
    return 0;
}

//***************************//
//  2023.10.01 4pm           //
//***************************//
vector<bool> Readin(char* arr){
    vector<bool> ans;

    for(int i=0; i<strlen(arr)/sizeof(char); ++i){
        ans.push_back(arr[i] - '0');
    }
    return ans;
}
//
int Lsv_SimBdd(Abc_Frame_t* pAbc, int argc, char** argv){
    //#1 Readin
    if(argc<2){
        cout << "error: read pattern failed." << endl;
        return 0;
    }
    vector<bool> pattern = Readin(argv[1]);

    //#2 Top down
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    Abc_Obj_t* pPo;
    int ithPo = 0;
    Abc_NtkForEachPo(pNtk, pPo, ithPo){
        Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
        assert( Abc_NtkIsBddLogic(pRoot->pNtk) );
        DdManager * dd = (DdManager *)pRoot->pNtk->pManFunc;
        DdNode* ddnode = (DdNode *)pRoot->pData;

        Abc_Obj_t* pPi;
        int ithPi = 0;
        Abc_NtkForEachPi(pNtk, pPi, ithPi){
            int ithCube = Vec_IntFind(&pRoot->vFanins, pPi->Id);
            if(ithCube==-1) continue;

            //iteration
            DdNode* tmp = (pattern[ithPi])? Cudd_bddIthVar(dd, ithCube) : Cudd_Not(Cudd_bddIthVar(dd, ithCube));
            ddnode = Cudd_Cofactor(dd, ddnode, tmp);
        }

        cout << Abc_ObjName(pPo) << ": " << (ddnode == dd->one) << endl;
    }
    return 0;
}

//***************************//
//  2023.09.30 5pm           //
//***************************//
vector<vector<bool> > ReadFile(char* path){
    vector<vector<bool> > ans;

    ifstream ifs(path);
    if (!ifs){
        cout << "error: open file failed." << endl;
        return ans;
    }

    string buf;
    while(getline(ifs, buf)){
        vector<bool> temp;
        for(int i=0; i<buf.size(); ++i){
            temp.push_back(buf[i] - '0');
        }
        ans.push_back(temp);
    }
    return ans;
}
//
vector<bool> BFS_Simulation(Abc_Ntk_t* pNtk, vector<bool> input){
    unordered_map<Abc_Obj_t*, bool> nodeValue;
    queue<Abc_Obj_t*> q;

    // Initialize for PIs and constants
    Abc_Obj_t* pObj;
    int iObj = 0;
    Abc_NtkForEachPi(pNtk, pObj, iObj){
      nodeValue[pObj] = input[iObj];
        q.push(pObj);
    }

    // Simulate using BFS
    while (!q.empty()){
        Abc_Obj_t* currNode = q.front();
        q.pop();

        // Perform logic operation (AND gate)
        if(nodeValue.count(currNode)==0){
            if(nodeValue.count(Abc_ObjFanin0(currNode))==0 || nodeValue.count(Abc_ObjFanin1(currNode))==0)
                continue;

            bool input0 = (Abc_ObjFaninC0(currNode))? !nodeValue[Abc_ObjFanin0(currNode)] : nodeValue[Abc_ObjFanin0(currNode)];
            bool input1 = (Abc_ObjFaninC1(currNode))? !nodeValue[Abc_ObjFanin1(currNode)] : nodeValue[Abc_ObjFanin1(currNode)];
            nodeValue[currNode] = input0 & input1;
        }

        Abc_Obj_t* pFanout;
        int i_tmp=0;
        Abc_ObjForEachFanout(currNode, pFanout, i_tmp){
            q.push(pFanout);
        }
    }

    // Print PO values
    vector<bool> output;
    Abc_NtkForEachPo(pNtk, pObj, iObj){
        bool ans = (Abc_ObjFaninC0(pObj))? !nodeValue[Abc_ObjFanin0(pObj)] : nodeValue[Abc_ObjFanin0(pObj)];
        output.push_back(ans);
    }
    return output;
}
//
int Lsv_SimAig(Abc_Frame_t* pAbc, int argc, char** argv) {
    //#1 Readin
    vector<vector<bool> > inputVal = ReadFile(argv[1]);

    //#2 BFS+queue to simulate
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    vector<vector<bool> > outputVal;
    for(int i=0; i<inputVal.size(); ++i){
        outputVal.push_back( BFS_Simulation(pNtk, inputVal[i]) );
    }

    //#3 Output bitwisely
    Abc_Obj_t* pObj;
    int iObj = 0;
    Abc_NtkForEachPo(pNtk, pObj, iObj){
        cout << Abc_ObjName(pObj) << ": ";
        for(int i=0; i<outputVal.size(); ++i){
            cout << outputVal[i][iObj];
        }
        cout << endl;
    }
    return 0;
}
