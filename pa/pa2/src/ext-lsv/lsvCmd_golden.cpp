#include <stdlib.h>

#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include "sat/cnf/cnf.h"

extern "C" {
Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSimBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSimAIG(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSymBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSymSAT(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSymAll(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
    Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_bdd", Lsv_CommandSimBdd, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_aig", Lsv_CommandSimAIG, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_bdd", Lsv_CommandSymBdd, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_sat", Lsv_CommandSymSAT, 0);
    Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_all", Lsv_CommandSymAll, 0);
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

using namespace std;

// for a given bdd, find the pattern that makes it 1
bool findOnes(DdManager* dd, DdNode* f, string& result, int currentVar) {
    if (f == Cudd_ReadZero(dd) || f == Cudd_Not(DD_ONE(dd))) {
        return false;
    }
    if (f == Cudd_ReadOne(dd) || f == Cudd_Not(Cudd_ReadZero(dd))) {
        return true;
    }

    DdNode* currentVarNode = Cudd_bddIthVar(dd, currentVar);
    DdNode* next_f = Cudd_Cofactor(dd, f, currentVarNode);
    Cudd_Ref(next_f);
    if (findOnes(dd, next_f, result, currentVar + 1)) {
        result[currentVar] = '1';
        Cudd_RecursiveDeref(dd, next_f);
        return true;
    }
    Cudd_RecursiveDeref(dd, next_f);
    next_f = Cudd_Cofactor(dd, f, Cudd_Not(currentVarNode));
    Cudd_Ref(next_f);
    if (findOnes(dd, next_f, result, currentVar + 1)) {
        result[currentVar] = '0';
        Cudd_RecursiveDeref(dd, next_f);
        return true;
    }
    Cudd_RecursiveDeref(dd, next_f);
    return false;
}

int Lsv_CommandSymBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk;
    Abc_Obj_t *kth_pPo, *pPi;

    pNtk = Abc_FrameReadNtk(pAbc);
    int in0_th, in1_th, out_th, ithPi, in0_th_bdd = -1, in1_th_bdd = -1;

    // ensure Ntk exist
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsBddLogic(pNtk)) {
        Abc_Print(-1, "Simulating BDDs can only be done for BDD networks (run \"collapse\").\n");
        return 1;
    }

    if (argc != 4) goto usage;
    out_th = stoi(argv[1]);
    in0_th = stoi(argv[2]);
    in1_th = stoi(argv[3]);

    if (in0_th > in1_th) {
        in0_th = in1_th;
        in1_th = stoi(argv[2]);
    }
    // check if valid
    if ((in0_th >= Abc_NtkPiNum(pNtk)) || (in1_th >= Abc_NtkPiNum(pNtk)) || (out_th >= Abc_NtkPoNum(pNtk)) || (in0_th == in1_th)) goto usage;

    {
        // find po
        kth_pPo = Abc_NtkPo(pNtk, out_th);
        Abc_Obj_t* pRoot = Abc_ObjFanin0(kth_pPo);
        assert(Abc_NtkIsBddLogic(pRoot->pNtk));
        DdManager* dd = (DdManager*)pRoot->pNtk->pManFunc;
        DdNode* ddnode = (DdNode*)pRoot->pData;
        DdNode *f_01 = NULL, *f_10 = NULL, *temp, *temp_in0, *temp_in1, *XOR;

        // record the origin order (we need to recover the order after reordering)
        unordered_map<string, int> piName_2_abc_Order;
        Abc_NtkForEachPi(pNtk, pPi, ithPi) {
            string piName = Abc_ObjName(pPi);
            piName_2_abc_Order[piName] = ithPi;
        }
        // bdd order
        char** bdd_Order_2_piName = (char**)Abc_NodeGetFaninNames(pRoot)->pArray;
        int bdd_supportNum = Abc_ObjFaninNum(pRoot);

        // find the bdd order of in0_th in1_th
        for (int i = 0; i < bdd_supportNum; i++) {
            if (strcmp(bdd_Order_2_piName[i], Abc_ObjName(Abc_NtkPi(pNtk, in0_th))) == 0) {
                in0_th_bdd = i;
            }
            if (strcmp(bdd_Order_2_piName[i], Abc_ObjName(Abc_NtkPi(pNtk, in1_th))) == 0) {
                in1_th_bdd = i;
            }
        }

       // debug
        // cout << "Abc order" << endl;
        // Abc_NtkForEachPi(pNtk, pPi, ithPi) {
        //     if (ithPi == in0_th || ithPi == in1_th)
        //         cout << "*";
        //     else
        //         cout << " ";
        //     cout << " [" << ithPi << "]: " << Abc_ObjName(pPi) << endl;
        // }
        // cout << "Bdd order : (size " << bdd_supportNum << ")" << endl;
        // for (int ithPi = 0; ithPi < bdd_supportNum; ithPi++) {
        //     if (ithPi == in0_th_bdd || ithPi == in1_th_bdd)
        //         cout << "*";
        //     else
        //         cout << " ";
        //     cout << " [" << ithPi << "]: " << bdd_Order_2_piName[ithPi] << endl;
        // }

        if (in0_th_bdd == -1 && in1_th_bdd == -1) {  //-> should be symmetric
            cout << "symmetric" << endl;
            return 0;
        }

        if ((in0_th_bdd == -1) ^ (in1_th_bdd == -1))  //-> should be asymmetric
        {
            if (in0_th_bdd == -1) {
                XOR = Cudd_bddBooleanDiff(dd, ddnode, in1_th_bdd);
                Cudd_Ref(XOR);
            } else {
                XOR = Cudd_bddBooleanDiff(dd, ddnode, in0_th_bdd);
                Cudd_Ref(XOR);
            }
        } else {
            // find f_01 f_10
            // f_01
            temp_in0 = Cudd_Not(Cudd_bddIthVar(dd, in0_th_bdd));
            temp_in1 = Cudd_bddIthVar(dd, in1_th_bdd);
            Cudd_Ref(temp_in0);
            Cudd_Ref(temp_in1);

            temp = Cudd_Cofactor(dd, ddnode, temp_in0);
            Cudd_Ref(temp);
            f_01 = Cudd_Cofactor(dd, temp, temp_in1);
            Cudd_RecursiveDeref(dd, temp_in0);
            Cudd_RecursiveDeref(dd, temp_in1);
            Cudd_RecursiveDeref(dd, temp);
            Cudd_Ref(f_01);

            // f_10
            temp_in0 = Cudd_bddIthVar(dd, in0_th_bdd);
            temp_in1 = Cudd_Not(Cudd_bddIthVar(dd, in1_th_bdd));
            Cudd_Ref(temp_in0);
            Cudd_Ref(temp_in1);

            temp = Cudd_Cofactor(dd, ddnode, temp_in0);
            Cudd_Ref(temp);
            f_10 = Cudd_Cofactor(dd, temp, temp_in1);
            Cudd_RecursiveDeref(dd, temp_in0);
            Cudd_RecursiveDeref(dd, temp_in1);
            Cudd_RecursiveDeref(dd, temp);
            Cudd_Ref(f_10);

            // XOR for f(0,1) f(1,0)
            XOR = Cudd_bddXor(dd, f_01, f_10);
            Cudd_Ref(XOR);

            // if (XOR) == 0 then symmetric
            if (XOR == Cudd_Not(DD_ONE(dd)) || XOR == DD_ZERO(dd)) {
                cout << "symmetric" << endl;
                Cudd_RecursiveDeref(dd, XOR);
                Cudd_RecursiveDeref(dd, f_01);
                Cudd_RecursiveDeref(dd, f_10);
                return 0;
            }
        }
        cout << "asymmetric" << endl;
        string counter_example = "";
        string abc_counter_example = "";
        for (int i = 0; i < bdd_supportNum; i++) counter_example += "0";
        for (int i = 0; i < Abc_NtkPiNum(pNtk); i++) abc_counter_example += "0";

        if (!findOnes(dd, XOR, counter_example, 0)) {
            cout << "something error" << endl;
        }
        // translate to abc order
        for (size_t i = 0; i < bdd_supportNum; i++) {
            abc_counter_example[piName_2_abc_Order[bdd_Order_2_piName[i]]] = counter_example[i];
        }
        // pattern 0 (f_01)
        for (size_t i = 0; i < abc_counter_example.size(); i++) {
            if (i == in0_th)
                cout << "0";
            else if (i == in1_th)
                cout << "1";
            else
                cout << abc_counter_example[i];
        }
        cout << endl;

        // pattern 1 (f_10)
        for (size_t i = 0; i < abc_counter_example.size(); i++) {
            if (i == in0_th)
                cout << "1";
            else if (i == in1_th)
                cout << "0";
            else
                cout << abc_counter_example[i];
        }
        cout << endl;
        Cudd_RecursiveDeref(dd, XOR);
        if (f_01 != NULL) Cudd_RecursiveDeref(dd, f_01);
        if (f_10 != NULL) Cudd_RecursiveDeref(dd, f_10);
    }
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_sym_bdd <k> <i> <j>\n");
    Abc_Print(-2, "\t          do Symmetry Checking for a given BDD and inputs \n");
    return 1;
}

int Lsv_CommandSymAll(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t *pNtk, *pNtk_new;

    int out_th;
    Aig_Man_t* aig_pMan;
    sat_solver* pSat;
    Aig_Obj_t* pObj;
    // read Ntk
    pNtk = Abc_FrameReadNtk(pAbc);
    int Lits[3];
    int i;

    // ensure Ntk exist
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Simulating AIGs can only be done for AIG networks (run \"strash\").\n");
        return 1;
    }
    if (argc != 2) goto usage;
    out_th = stoi(argv[1]);

    if ((out_th >= Abc_NtkPoNum(pNtk))) goto usage;

    {
        pNtk_new = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(Abc_NtkPo(pNtk, out_th)), Abc_ObjName(Abc_NtkPo(pNtk, out_th)), 1);
        aig_pMan = Abc_NtkToDar(pNtk_new, 0, 1);
        pSat = sat_solver_new();
        Cnf_Dat_t* pCnf = Cnf_Derive(aig_pMan, 1);
        Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
        Cnf_DataLift(pCnf, pCnf->nVars);
        Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2, 0);
        Cnf_DataLift(pCnf, pCnf->nVars);
        Cnf_DataWriteIntoSolverInt(pSat, pCnf, 3, 0);
        Cnf_DataLift(pCnf, -2 * (pCnf->nVars));
        Aig_ManForEachCi(aig_pMan, pObj, i) {
            //  (vA(t) = vB(t) , vA(t) -> vB(t) ,  (vA(t)' + vB(t) + VH) & (vA(t) + vB(t)' + VH) )
            Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
            Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 1);
            Lits[2] = toLitCond(pCnf->pVarNums[pObj->Id] + 2 * (pCnf->nVars), 0);
            if (!sat_solver_addclause(pSat, Lits, Lits + 3))
                assert(0);
            Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
            Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 0);
            Lits[2] = toLitCond(pCnf->pVarNums[pObj->Id] + 2 * (pCnf->nVars), 0);
            if (!sat_solver_addclause(pSat, Lits, Lits + 3))
                assert(0);
        }
        // (c) type clause
        for (int i = 0; i < Aig_ManCiNum(aig_pMan) - 1; ++i) {
            for (int j = i + 1; j < Aig_ManCiNum(aig_pMan); ++j) {
                // {vA(i) ,vA(j)} = 10 or 01 for (VH(i) & VH(j))
                Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id], 0);
                Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id], 0);
                Lits[2] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id] + 2 * (pCnf->nVars), 1);
                Lits[3] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id] + 2 * (pCnf->nVars), 1);
                if (!sat_solver_addclause(pSat, Lits, Lits + 4))
                    assert(0);
                Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id], 1);
                Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id], 1);
                Lits[2] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id] + 2 * (pCnf->nVars), 1);
                Lits[3] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id] + 2 * (pCnf->nVars), 1);
                if (!sat_solver_addclause(pSat, Lits, Lits + 4))
                    assert(0);

                //  same in vB
                Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id] + (pCnf->nVars), 0);
                Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id] + (pCnf->nVars), 0);
                Lits[2] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id] + 2 * (pCnf->nVars), 1);
                Lits[3] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id] + 2 * (pCnf->nVars), 1);
                if (!sat_solver_addclause(pSat, Lits, Lits + 4))
                    assert(0);
                Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id] + (pCnf->nVars), 1);
                Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id] + (pCnf->nVars), 1);
                Lits[2] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id] + 2 * (pCnf->nVars), 1);
                Lits[3] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id] + 2 * (pCnf->nVars), 1);
                if (!sat_solver_addclause(pSat, Lits, Lits + 4))
                    assert(0);
            }
        }
        // output XOR
        Aig_ManForEachCo(aig_pMan, pObj, i) {
            // 0 -> 1
            Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
            Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 0);
            if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                assert(0);
            // 1 -> 0
            Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
            Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 1);
            if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                assert(0);
        }

        int status;
        vector<vector<bool> > sym_table(Aig_ManCiNum(aig_pMan));
        for (int i = 0; i < Aig_ManCiNum(aig_pMan); ++i) {
            sym_table[i].resize(Aig_ManCiNum(aig_pMan));
        }
        // assumption
        for (int i = 0; i < Aig_ManCiNum(aig_pMan) - 1; ++i) {
            for (int j = i + 1; j < Aig_ManCiNum(aig_pMan); ++j) {
                if (sym_table[i][j]) {
                    cout << i << " " << j << endl;
                    continue;
                }
                Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, i)->Id] + 2 * (pCnf->nVars), 0);
                Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, j)->Id] + 2 * (pCnf->nVars), 0);
                status = sat_solver_solve(pSat, Lits, Lits + 2, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
                if (status == l_False){
                    cout << i << " " << j << endl;
                    sym_table[i][j]=true;
                }
            }
            // more sym relation in same row
            for (int k = 0; k < Aig_ManCiNum(aig_pMan) - 1; ++k) {
                for (int r = k + 1; r < Aig_ManCiNum(aig_pMan); ++r) {
                    if (sym_table[i][k] && sym_table[i][r]) {
                        sym_table[k][r] = true;
                    }
                }
            }
        }

        return 0;
    }

usage:
    Abc_Print(-2, "usage: lsv_sym_all <k>\n");
    Abc_Print(-2, "\t          do Symmetry Checking with Incremental SAT\n");
    return 1;
}

int Lsv_CommandSymSAT(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t *pNtk, *pNtk_new;
    int out_th, in0_th, in1_th;
    Aig_Man_t* aig_pMan;
    sat_solver* pSat;
    Aig_Obj_t* pObj;
    // read Ntk
    pNtk = Abc_FrameReadNtk(pAbc);
    int Lits[3];
    int i;

    // ensure Ntk exist
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Simulating AIGs can only be done for AIG networks (run \"strash\").\n");
        return 1;
    }
    if (argc != 4) goto usage;
    out_th = stoi(argv[1]);
    in0_th = stoi(argv[2]);
    in1_th = stoi(argv[3]);

    if ((in0_th >= Abc_NtkPiNum(pNtk)) || (in1_th >= Abc_NtkPiNum(pNtk)) || (out_th >= Abc_NtkPoNum(pNtk)) || (in0_th == in1_th)) goto usage;

    {

        // (1) Use Abc NtkCreateCone to extract the cone of yk
        pNtk_new = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(Abc_NtkPo(pNtk, out_th)), Abc_ObjName(Abc_NtkPo(pNtk, out_th)), 1);
        // (2) Use Abc NtkToDar to derive a corresponding AIG circuit.
        aig_pMan = Abc_NtkToDar(pNtk_new, 0, 1);
        // (3) Use sat solver new to initialize an SAT solver
        pSat = sat_solver_new();
        // (4) Use Cnf Derive to obtain the corresponding CNF formula CA, which
        // depends on variables v1, . . . , vn.
        Cnf_Dat_t* pCnf = Cnf_Derive(aig_pMan, 1);
        // (5) Use Cnf DataWriteIntoSolverInt to add the CNF into the SAT
        // solver
        Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
        // (6) Use Cnf DataLift to create another CNF formula CB that depends
        // on different input variables vn+1, . . . , v2n. Again, add the CNF into
        // the SAT solver.
        Cnf_DataLift(pCnf, pCnf->nVars);
        // actually not timeFrame = 2 , bus nVars = 2n
        Cnf_DataWriteIntoSolverInt(pSat, pCnf, 2, 0);
        Cnf_DataLift(pCnf, -pCnf->nVars);
        // (7) For each input xt of the circuit, find its corresponding CNF variables
        // vA(t) in CA and vB(t) in CB. Set vA(t) = vB(t) ∀t ̸∈ {i, j}, and set
        // vA(i) = vB(j), vA(j) = vB(i). This step can be done by adding
        // corresponding clauses to the SAT solver.
        Aig_ManForEachCi(aig_pMan, pObj, i) {
            if (i == in0_th || i == in1_th) {
                // vA(t) != vB(t)  for all t = {i,j}
                Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
                Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 0);
                if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                    assert(0);
                Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
                Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 1);
                if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                    assert(0);
            } else {
                //  (vA(t) = vB(t) , vA(t) -> vB(t) , vA(t)' + vB(t) )
                Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
                Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 1);
                if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                    assert(0);
                Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
                Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 0);
                if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                    assert(0);
            }
        }
        // {vA(i) ,vA(j)} = 10 or 01
        Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in0_th)->Id], 0);
        Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in1_th)->Id], 0);
        if (!sat_solver_addclause(pSat, Lits, Lits + 2))
            assert(0);
        Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in0_th)->Id], 1);
        Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in1_th)->Id], 1);
        if (!sat_solver_addclause(pSat, Lits, Lits + 2))
            assert(0);
        //  same in vB
        Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in0_th)->Id] + (pCnf->nVars), 0);
        Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in1_th)->Id] + (pCnf->nVars), 0);
        if (!sat_solver_addclause(pSat, Lits, Lits + 2))
            assert(0);
        Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in0_th)->Id] + (pCnf->nVars), 1);
        Lits[1] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in1_th)->Id] + (pCnf->nVars), 1);
        if (!sat_solver_addclause(pSat, Lits, Lits + 2))
            assert(0);

        // default setting: vA(x) = 0  for x = min (i,j)
        if (in0_th < in1_th)
            Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in0_th)->Id], 1);
        else
            Lits[0] = toLitCond(pCnf->pVarNums[Aig_ManCi(aig_pMan, in1_th)->Id], 1);
        if (!sat_solver_addclause(pSat, Lits, Lits + 1))
            assert(0);

        // (8) Use sat solver solve to solve the SAT problem. Note that yk is
        // symmetric in xi and xj if and only if vA(yk)⊕vB(yk) is unsatisfiable,
        // where vA(yk) and vB(yk) are the CNF variables in CA and CB that
        // corresponds to yk.

        // output XOR
        Aig_ManForEachCo(aig_pMan, pObj, i) {
            // 0 -> 1
            Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 0);
            Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 0);
            if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                assert(0);
            // 1 -> 0
            Lits[0] = toLitCond(pCnf->pVarNums[pObj->Id], 1);
            Lits[1] = toLitCond(pCnf->pVarNums[pObj->Id] + (pCnf->nVars), 1);
            if (!sat_solver_addclause(pSat, Lits, Lits + 2))
                assert(0);
        }

        int status = sat_solver_solve(pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
        if (status == l_False)
            cout << "symmetric" << endl;
        else if (status == l_True)
            cout << "asymmetric" << endl;
        else
            cerr << "UNDECIDED" << endl;

        // (9) If yk is asymmetric in xi and xj , use sat solver var value to
        // obtain the satisfying assignment, which can be used to derive the
        // counterexample
        if (status == l_True) {
            // Sat_SolverPrintStats( stdout, pSat );
            Aig_ManForEachCi(aig_pMan, pObj, i) {
                // for pattern 0
                if (sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id]))
                    printf("1");
                else
                    printf("0");
            }
            cout << endl;
            Aig_ManForEachCi(aig_pMan, pObj, i) {
                // for pattern 1
                if (sat_solver_var_value(pSat, pCnf->pVarNums[pObj->Id] + (pCnf->nVars)))
                    printf("1");
                else
                    printf("0");
            }
            cout << endl;
        }
        return 0;
    }

usage:
    Abc_Print(-2, "usage: lsv_sym_sat <k> <i> <j>\n");
    Abc_Print(-2, "\t          do Symmetry Checking for a given AIG and inputs \n");
    return 1;
}



using namespace std;

int Lsv_CommandSimBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk;
    Abc_Obj_t *pPo, *pPi;
    int ithPo, ithPi;
    int c = 0;

    pNtk = Abc_FrameReadNtk(pAbc);
    string inputPattern;
    unordered_map<string, int> piName2Value;

    // ensure Ntk exist
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsBddLogic(pNtk)) {
        Abc_Print(-1, "Simulating BDDs can only be done for BDD networks (run \"collapse\").\n");
        return 1;
    }

    // get input pattern, assume input pattern = order
    if (argc != 2) goto usage;
    inputPattern = argv[1];

    // check if valid
    if (inputPattern.length() != Abc_NtkPiNum(pNtk)) goto usage;
    Abc_NtkForEachPi(pNtk, pPi, ithPi) {
        if (inputPattern[ithPi] != '1' && inputPattern[ithPi] != '0') goto usage;
        string piName = Abc_ObjName(pPi);
        piName2Value[piName] = inputPattern[ithPi] == '1' ? 1 : 0;
    }

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    // 1. To find the BDD node associated with each PO, use the codes below.
    Abc_NtkForEachPo(pNtk, pPo, ithPo) {
        Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo);
        assert(Abc_NtkIsBddLogic(pRoot->pNtk));
        DdManager* dd = (DdManager*)pRoot->pNtk->pManFunc;
        DdNode* ddnode = (DdNode*)pRoot->pData;  // origin

        // 2. To find the variable order of the BDD, you may use the following codes to find the variable name array.
        char** vNamesIn = (char**)Abc_NodeGetFaninNames(pRoot)->pArray;
        Abc_Obj_t* pFanin;
        DdNode* g;
        int j;
        Abc_ObjForEachFanin(pRoot, pFanin, j) {
            g = (piName2Value[vNamesIn[j]] == 1) ? Cudd_bddIthVar(dd, j) : (Cudd_Not(Cudd_bddIthVar(dd, j)));
            ddnode = Cudd_Cofactor(dd, ddnode, g);  // f with respect to g
        }

        // print result
        cout << Abc_ObjName(pPo) << ": ";
        if (ddnode == DD_ONE(dd))
            cout << "1";
        else if (ddnode == Cudd_Not(DD_ONE(dd)) || ddnode == DD_ZERO(dd))
            cout << "0";
        else
            assert(0);
        cout << endl;
    }
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_sim_bdd <input_pattern>\n");
    Abc_Print(-2, "\t          do simulations for a given BDD and an input pattern\n");
    return 1;
}

void simulateAIG32times(Abc_Ntk_t* pNtk, vector<int>& inputPattern) {
    Abc_Obj_t *pObj, *pPi, *pPo, *pFanin;
    int ithObj, ithPi, ithPo, ithFanin;

    // assign inputpattern
    Abc_NtkForEachPi(pNtk, pPi, ithPi) {
        pPi->iTemp = inputPattern[ithPi];
    }

    // propogate value
    Abc_NtkForEachObj(pNtk, pObj, ithObj) {
        if (pObj->Type != 7) continue;
        vector<Abc_Obj_t*> fanin;
        Abc_ObjForEachFanin(pObj, pFanin, ithFanin) {
            fanin.__emplace_back(pFanin);
        }
        pObj->iTemp = (pObj->fCompl0 ? ~fanin[0]->iTemp : fanin[0]->iTemp) & (pObj->fCompl1 ? ~fanin[1]->iTemp : fanin[1]->iTemp);
    }

    // output read
    Abc_NtkForEachPo(pNtk, pPo, ithPo) {
        Abc_Obj_t* fanin;
        Abc_ObjForEachFanin(pPo, pFanin, ithFanin) {
            fanin = pFanin;
        }
        pPo->iTemp = pPo->fCompl0 ? ~fanin->iTemp : fanin->iTemp;
    }

    return;
}

int Lsv_CommandSimAIG(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk;
    int c = 0,ithPo,restOfPattern;
    vector<int> inputPattern;
    string inputFileName;
    ifstream patternFile;
    Abc_Obj_t* pPo;

    // read Ntk
    pNtk = Abc_FrameReadNtk(pAbc);
    vector<string> outputPattern(Abc_NtkPoNum(pNtk));

    // ensure Ntk exist
    if (pNtk == NULL) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }
    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "Simulating AIGs can only be done for AIG networks (run \"strash\").\n");
        return 1;
    }

    // get input name
    if (argc != 2) goto usage;
    inputFileName = argv[1];

    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
        switch (c) {
            case 'h':
                goto usage;
            default:
                goto usage;
        }
    }

    // read inputFile
    patternFile.open(inputFileName);
    if (patternFile.is_open()) {
        string line;
        int count_32 = 0;
        inputPattern.clear();
        inputPattern = vector<int>(Abc_NtkPiNum(pNtk));

        while (patternFile >> line) {
            if (line.size() != Abc_NtkPiNum(pNtk)) {
                cout << "Error: Pattern(" << line << ") length(" << line.size() << ") does not match the number of inputs(" << Abc_NtkPiNum(pNtk) << ") in a circuit !!" << endl;
                return 0;
            }
            for (size_t i = 0; i < Abc_NtkPiNum(pNtk); ++i) {
                if (line[i] == '0')
                    inputPattern[i] = inputPattern[i] << 1;
                else if (line[i] == '1') {
                    inputPattern[i] = inputPattern[i] << 1;
                    inputPattern[i] += 1;
                } else {
                    cout << "  Error: Pattern(" << line << ") contains a non-0/1 character('" << line[i] << "')." << endl;
                    cout << "0 patterns simulated." << endl;
                    inputPattern.clear();
                    return 0;
                }
            }
            ++count_32;
            if (count_32 == 32) {
                count_32 = 0;
                simulateAIG32times(pNtk, inputPattern);  //<< TODO
                inputPattern.clear();
                inputPattern = vector<int>(Abc_NtkPiNum(pNtk));

                // record the output
                Abc_NtkForEachPo(pNtk, pPo, ithPo) {
                    for (int i = sizeof(int) * 8 - 1; i >= 0; i--) {
                        int bit = (pPo->iTemp >> i) & 1;
                        outputPattern[ithPo] += (bit) ? "1" : "0";
                    }
                }
            }
        }

        restOfPattern = count_32;
        // fill in 0
        while (count_32 != 32) {
            for (size_t i = 0; i < Abc_NtkPiNum(pNtk); ++i) {
                inputPattern[i] = inputPattern[i] << 1;
            }
            ++count_32;
        }
        simulateAIG32times(pNtk, inputPattern);

        // record the output (restOfPattern)
        Abc_NtkForEachPo(pNtk, pPo, ithPo) {
            for (int i = sizeof(int) * 8 - 1; i >= sizeof(int) * 8 - restOfPattern; i--) {
                int bit = (pPo->iTemp >> i) & 1;
                outputPattern[ithPo] += (bit) ? "1" : "0";
            }
        }

        // print result
        Abc_NtkForEachPo(pNtk, pPo, ithPo) {
            cout << Abc_ObjName(pPo) << ": " << outputPattern[ithPo] << endl;
        }
    } else {
        cout << "   Error: file can't open" << endl;
        return 1;
    }

    return 0;

usage:
    Abc_Print(-2, "usage: lsv_sim_aig <input_pattern>\n");
    Abc_Print(-2, "\t          do simulations for a given AIG and an input pattern\n");
    return 1;
}
