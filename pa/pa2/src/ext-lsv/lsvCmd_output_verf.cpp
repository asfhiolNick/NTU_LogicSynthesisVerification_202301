#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <unordered_map>
#include <queue>
//FOR lsv_sym_sat
#include "sat/cnf/cnf.h"
extern "C"{
Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SimBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SimAig(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SymBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_SymSAT(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_bdd", Lsv_SimBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_aig", Lsv_SimAig, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_bdd", Lsv_SymBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_sat", Lsv_SymSAT, 0);
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
int Lsv_SymSAT(Abc_Frame_t* pAbc, int argc, char** argv){
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
    Abc_Obj_t* output = Abc_NtkPo(pNtk, out_th);
    Abc_Ntk_t* cone = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(output), Abc_ObjName(output), 1/*int fUseAllCis*/);
    Aig_Man_t* pAig = Abc_NtkToDar(cone, 0/*int fExors*/, 1/*int fRegisters*/);
    sat_solver* pSat = sat_solver_new();
    Cnf_Dat_t*  pCnf = Cnf_Derive(pAig, 1/*int nOutputs*/);
    pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1/*int nFrames*/, 0/*int fInit*/);
    Cnf_DataLift(pCnf, pCnf->nVars);
    //
    pSat = (sat_solver *)Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2/*int nFrames*/, 0/*int fInit*/);
    Cnf_DataLift(pCnf, -1*pCnf->nVars/*-(nTimes-1) * pCnf->nVars*/);

    //#2 add clauses for input
    int pLits[2];
    Aig_Obj_t* pObj; int iObj;
    Aig_ManForEachCi(pAig, pObj, iObj){
        if(iObj==in_0th || iObj==in_1th){
            //v_A(t) == v_B(t)', v_A <-> v_B'
            //v_A + v_B
            pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id],0/*conjugate*/);
            pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id]+pCnf->nVars,0/*conjugate*/);
            sat_solver_addclause(pSat, pLits, pLits+2);

            //v_A' + v_B'
            pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id],1/*conjugate*/);
            pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id]+pCnf->nVars,1/*conjugate*/);
            sat_solver_addclause(pSat, pLits, pLits+2);
            continue;
        }
        //v_A(t) == v_B(t), v_A <-> v_B
        //v_A + v_B'
        pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id],0/*conjugate*/);
        pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id]+pCnf->nVars,1/*conjugate*/);
        sat_solver_addclause(pSat, pLits, pLits+2);

        //v_A' + v_B
        pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id],1/*conjugate*/);
        pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id]+pCnf->nVars,0/*conjugate*/);
        sat_solver_addclause(pSat, pLits, pLits+2);
    }
    //v_A(i) ^ v_A(j) = v_A*v_A' + v_A'*v_A = (v_A+v_A)(v_A'+v_A')
    //v_A(i)+v_A(j)
    pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id],0/*conjugate*/);
    pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id],0/*conjugate*/);
    sat_solver_addclause(pSat, pLits, pLits+2);

    //v_A(i)'+v_A(j)'
    pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id],1/*conjugate*/);
    pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id],1/*conjugate*/);
    sat_solver_addclause(pSat, pLits, pLits+2);

    //v_B(i) ^ v_B(j) = (v_B+v_B)(v_B'+v_B')
    //v_B(i)+v_B(j)
    pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id]+pCnf->nVars,0/*conjugate*/);
    pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id]+pCnf->nVars,0/*conjugate*/);
    sat_solver_addclause(pSat, pLits, pLits+2);

    //v_B(i)'+v_B(j)'
    pLits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_0th)->Id]+pCnf->nVars,1/*conjugate*/);
    pLits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(pAig, in_1th)->Id]+pCnf->nVars,1/*conjugate*/);
    sat_solver_addclause(pSat, pLits, pLits+2);

    //#3 add clauses for output
    //the only output of cone is out_th
    Aig_ManForEachCo(pAig, pObj, iObj){
        //v_A(y) ^ v_B(y) = (v_A+v_B)(v_A'+v_B')
        //v_A + v_B
        pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id],0/*conjugate*/);
        pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id]+pCnf->nVars,0/*conjugate*/);
        sat_solver_addclause(pSat, pLits, pLits+2);

        //v_A' + v_B'
        pLits[0] = toLitCond(pCnf->pVarNums[pObj->Id],1/*conjugate*/);
        pLits[1] = toLitCond(pCnf->pVarNums[pObj->Id]+pCnf->nVars,1/*conjugate*/);
        sat_solver_addclause(pSat, pLits, pLits+2);
    }

    //#4 solve by SAT
    //RetValue == l_Undef || RetValue == l_True || RetValue == l_False
    int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);
    if(status == l_Undef){
        cout << "error: SAT cannot solve it!" << endl;
        return 0;
    }
    else if(status == l_False){
        //cout << "symmetric" << endl;
        return 0;
    }

    //#5 give counterexample
    //cout << "asymmetric" << endl;
    cout << "lsv_sim_sat ";
    Aig_ManForEachCi(pAig, pObj, iObj){
        cout << sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id]);
    }
    cout << endl;

    cout << "lsv_sim_sat ";
    Aig_ManForEachCi(pAig, pObj, iObj){
        cout << sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id]+pCnf->nVars);
    }
    cout << endl;


    return 0;
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
        //cout << "symmetric" << endl;
        return 0;
    }
    else if(bdd_0th!=-1 && bdd_1th==-1){
        //cout << "asymmetric" << endl;
        counterNode = Cudd_bddBooleanDiff(dd, f, bdd_0th);
        Cudd_Ref(counterNode);
    }
    else if(bdd_0th==-1 && bdd_1th!=-1){
        //cout << "asymmetric" << endl;
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
            //cout << "symmetric" << endl;
            return 0;
            //  Cudd_Not(...) is necessary   //
            //  otherwise 0!=6 in benchmark  //
        }
        //cout << "asymmetric" << endl;
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
    cout << "lsv_sim_bdd " << example_f01 << endl;
    cout << "lsv_sim_bdd " << example_f10 << endl;
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
