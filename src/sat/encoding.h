
#ifndef DOMPASCH_TREE_REXX_ENCODING_H
#define DOMPASCH_TREE_REXX_ENCODING_H

extern "C" {
    #include "sat/ipasir.h"
}

#include <initializer_list>
#include <fstream>
#include <string>
#include <iostream>

#include "data/layer.h"
#include "data/signature.h"
#include "data/htn_instance.h"
#include "data/action.h"
#include "sat/variable_domain.h"

#define PRINT_TO_FILE true

typedef std::unordered_map<int, SigSet> State;

struct PlanItem {
    int id;
    Signature abstractTask;
    Signature reduction;
    std::vector<int> subtaskIds;
};

class Encoding {

private:
    HtnInstance& _htn;
    std::vector<Layer>* _layers;
    
    std::unordered_map<Signature, int, SignatureHasher> _substitution_variables;

    void* _solver;
    std::ofstream _out;

    Signature _sig_primitive;
    int _substitute_name_id;

    std::unordered_set<int> _q_constants;
    std::unordered_map<int, std::vector<int>> _q_constants_per_arg;

    std::vector<int> _last_assumptions;

public:
    Encoding(HtnInstance& htn, std::vector<Layer>& layers);
    ~Encoding();

    void encode(int layerIdx, int pos);
    bool solve();

    std::vector<PlanItem> extractClassicalPlan();
    std::vector<PlanItem> extractDecompositionPlan();

    void printFailedVars(Layer& layer);

private:

    Signature sigSubstitute(int qConstId, int trueConstId) {
        assert(!_htn._q_constants.count(trueConstId) || trueConstId < qConstId);
        std::vector<int> args(2);
        args[0] = (qConstId);
        args[1] = (trueConstId);
        return Signature(_substitute_name_id, args);
    }

    void addClause(std::vector<int> lits);
    void addClause(std::initializer_list<int> lits);
    void appendClause(std::initializer_list<int> lits);
    void endClause();
    void assume(int lit);

    int varPrimitive(int layer, int pos);
    int varSubstitution(Signature sigSubst);
    bool isEncoded(int layer, int pos, const Signature& sig);
    bool isEncodedSubstitution(Signature& sig);

    std::string varName(int layer, int pos, const Signature& sig);
    void printVar(int layer, int pos, const Signature& sig);

    bool value(int layer, int pos, const Signature& sig);
    Signature getDecodedQOp(int layer, int pos, Signature sig);
    void checkAndApply(Action& a, CausalSigSet& state, CausalSigSet& newState, int layer, int pos);

};

#endif