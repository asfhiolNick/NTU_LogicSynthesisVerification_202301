#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

const unsigned int ALL_ONES_32BIT = 4294967295;
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandSimBdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandParaSimAig(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_bdd", Lsv_CommandSimBdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_aig", Lsv_CommandParaSimAig, 0);
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

int Bdd_EvalNode(Abc_Obj_t *pNode, DdManager *dd, DdNode *node, int *varValues) {
  if (!node) {
    Abc_Print(-1, "Something went wrong.\n");
    return -1;
  }
  if (node == Cudd_ReadLogicZero(dd)) {
    return 0;
  }
  if (node == Cudd_ReadOne(dd)) {
    return 1;
  }
  int vidx = Cudd_NodeReadIndex(node);
  DdNode *covar = Cudd_bddIthVar(dd, vidx);
  DdNode *nextNode = (varValues[Abc_ObjId(Abc_ObjFanin(pNode, vidx)) - 1] == 0) ? Cudd_Cofactor(dd, node, Cudd_Not(covar)) : Cudd_Cofactor(dd, node, covar);
  return Bdd_EvalNode(pNode, dd, nextNode, varValues);
}

void Lsv_NtkSimBdd(Abc_Ntk_t *pNtk, char *pPattern) {
  int i;
  int nInputs = Abc_NtkCiNum(pNtk);
  int *varValue = ABC_ALLOC(int, nInputs);
  for (i = 0; i < nInputs; i++) {
    varValue[i] = pPattern[i] - '0';
  }

  DdManager *dd = ( DdManager * ) pNtk->pManFunc;
  Abc_Obj_t *pNode;
  Abc_NtkForEachNode(pNtk, pNode, i) {
    DdNode *node = ( DdNode * ) pNode->pData;
    int val = Bdd_EvalNode(pNode, dd, node, varValue);
    printf("%s: %d\n",  Abc_ObjName(Abc_ObjFanout(pNode, 0)), val);
  }
  ABC_FREE(varValue);
}

int Lsv_CommandSimBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Extra_UtilGetoptReset();
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (argc != 2) {
    Abc_Print(-1, "Invalid number of arguments. Usage: lsv_sim_bdd <input_pattern>\n");
    return 1;
  }
  if (!Abc_NtkIsBddLogic(pNtk)) {
    Abc_Print(-1, "Invalid current network type. Apply \"collapse\" before use.\n");
    return 1;
  }
  if (strlen(argv[1]) != Abc_NtkCiNum(pNtk)) {
    Abc_Print(-1, "Invalid input pattern.\n");
    return 1;
  }
  Lsv_NtkSimBdd(pNtk, argv[1]);
  return 0;
}

void Aig_ParaSim(Abc_Ntk_t *pNtk, int *pPatterns, int numPatterns, char* outputs[]) {
  if (numPatterns > 32) {
    Abc_Print(-1, "Number of patterns exceeds 32.\n");
    return;
  }
  int nNodes = Abc_NtkObjNumMax(pNtk);
  unsigned int *pNodeValues = ABC_ALLOC(unsigned int, nNodes);
  int i, j;
  Abc_Obj_t *pNode;
  // printf("%d\n", nNodes);
  Abc_NtkForEachPi(pNtk, pNode, i) { // i starts from 0, id starts from 1
    // printf("(%d) %s: %d\n", i, Abc_ObjName(pNode), Abc_ObjId(pNode));
    pNodeValues[Abc_ObjId(pNode) - 1] = pPatterns[i];
  }
  unsigned int fanin0, fanin1;
  Abc_NtkForEachNode(pNtk, pNode, i) {
    // printf("(%d) %s: %d\n", i, Abc_ObjName(pNode), Abc_ObjId(pNode));
    fanin0 = pNodeValues[Abc_ObjId(Abc_ObjFanin0(pNode)) - 1];
    fanin1 = pNodeValues[Abc_ObjId(Abc_ObjFanin1(pNode)) - 1];
    if (Abc_ObjFaninC0(pNode)) {
      fanin0 ^= ALL_ONES_32BIT;
    }
    if (Abc_ObjFaninC1(pNode)) {
      fanin1 ^= ALL_ONES_32BIT;
    }
    // printf("f0: %d/%u\nf1: %d/%u\n", Abc_ObjId(Abc_ObjFanin0(pNode)), fanin0, Abc_ObjId(Abc_ObjFanin1(pNode)), fanin1);
    pNodeValues[Abc_ObjId(pNode) - 1] = fanin0 & fanin1;
    // printf("(%d) %s: %d/%u\n", i, Abc_ObjName(pNode), Abc_ObjId(pNode), fanin0 & fanin1);
  }
  unsigned int val;
  char *bin_val = ABC_ALLOC(char, 33);
  Abc_NtkForEachPo(pNtk, pNode, i) {
    // printf("fanin of %s: %d\n", Abc_ObjName(pNode), Abc_ObjId(Abc_ObjFanin0(pNode)));
    if (Abc_ObjId(Abc_ObjFanin0(pNode)) == 0) {
      val = ALL_ONES_32BIT;
    }
    else {
      val = pNodeValues[Abc_ObjId(Abc_ObjFanin0(pNode)) - 1];
    }
    if (Abc_ObjFaninC0(pNode)) {
      val ^= ALL_ONES_32BIT;
    }
    val >>= (32 - numPatterns);
    // printf("%s: %u\n", Abc_ObjName(pNode), val);
    bin_val[numPatterns] = '\0';
    for (j = numPatterns - 1; j >= 0; j--) {
      bin_val[j] = (val & 1) + '0';
      val >>= 1;
    }
    strcat(outputs[i], bin_val);
  }
  ABC_FREE(pNodeValues);
  ABC_FREE(bin_val);
  return;
}

void Lsv_NtkParaSimAig(Abc_Ntk_t *pNtk, char *inputPatternFile) {

  FILE* inFile = fopen(inputPatternFile, "r");
  if (!inFile) {
    Abc_Print(-1, "Error: Could not open input pattern file '%s'.\n", inputPatternFile);
    return;
  }

  int total_pattern_num = 0;
  char line[1000000]; // Assume number of PI is at most 999999
  while (fgets(line, sizeof(line), inFile)) {
    total_pattern_num++;
  }
  fclose(inFile);

  int i, j;
  Abc_Obj_t *pNode;
  int nInputs = Abc_NtkPiNum(pNtk);
  int *pPatterns = ABC_ALLOC(int, nInputs);
  for (i = 0; i < nInputs; i++) {
    pPatterns[i] = 0;
  }

  int nOutputs = Abc_NtkPoNum(pNtk);
  char *outputs[nOutputs];
  for (i = 0; i < nOutputs; i++) {
    outputs[i] = ABC_ALLOC(char, total_pattern_num + 2);
    outputs[i][0] = '\0';
  }

  int patCount = 0; // for each round, at most 32 patterns
  inFile = fopen(inputPatternFile, "r");
  while (fgets(line, sizeof(line), inFile)) {
    for (j = 0; j < nInputs; j++) {
      pPatterns[j] |= (line[j] - '0') << (31 - patCount);
    }
    patCount++;
    if (patCount == 32) {
      Aig_ParaSim(pNtk, pPatterns, patCount, outputs);
      for (i = 0; i < nInputs; i++) {
        pPatterns[i] = 0;
      }
      patCount = 0;
    }
  }
  fclose(inFile);
  if (patCount > 0) {
    Aig_ParaSim(pNtk, pPatterns, patCount, outputs);
  }

  Abc_NtkForEachPo(pNtk, pNode, i) {
    printf("%s: %s\n", Abc_ObjName(pNode), outputs[i]);
  }
  ABC_FREE(pPatterns);
  for (i = 0; i < nOutputs; i++) {
    ABC_FREE(outputs[i]);
  }
}

int Lsv_CommandParaSimAig(Abc_Frame_t *pAbc, int argc, char **argv) {
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);
  Extra_UtilGetoptReset();
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (argc != 2) {
    Abc_Print(-1, "Invalid number of arguments. Usage: lsv_sim_bdd <input pattern>\n");
    return 1;
  }
  Lsv_NtkParaSimAig(pNtk, argv[1]);
  return 0;
}
