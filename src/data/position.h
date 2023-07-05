
#ifndef DOMPASCH_LILOTANE_POSITION_H
#define DOMPASCH_LILOTANE_POSITION_H

#include <vector>
#include <set>

#include "util/hashmap.h"
#include "data/signature.h"
#include "util/names.h"
#include "sat/variable_domain.h"
#include "util/log.h"
#include "sat/literal_tree.h"
#include "data/substitution_constraint.h"

typedef NodeHashMap<USignature, IntPairTree, USignatureHasher> IndirectFactSupportMapEntry;
typedef NodeHashMap<USignature, IndirectFactSupportMapEntry, USignatureHasher> IndirectFactSupportMap;
typedef NodeHashMap<USignature, Substitution, USignatureHasher> USigSubstitutionMap;

enum VarType { FACT, OP };

struct Position {

public:
    static NodeHashMap<USignature, USigSet, USignatureHasher> EMPTY_USIG_TO_USIG_SET_MAP;
    static IndirectFactSupportMap EMPTY_INDIRECT_FACT_SUPPORT_MAP;

private:
    size_t _layer_idx;
    size_t _pos;

    size_t _ltp_pos;

    size_t _above_pos = -1;

    USigSet _actions;
    USigSet _reductions;

    USigSetUniqueID _actionsWithUniqueID;
    USigSetUniqueID _reductionsWithUniqueID;

    NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> _expansions;
    NodeHashMap<USignature, USigSet, USignatureHasher> _predecessors; // FOR STRANGE REASON, I CANNOT PUT USignatureHasherWithUniqueID AS HASH HERE ???


    NodeHashMap<int, USigSetUniqueID> _predecessors_with_unique_id; 
    NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher> _expansion_substitutions;

    // TEST ===========================================================

    NodeHashMap<int, USigSetUniqueID> _previous;
    NodeHashMap<int, USigSetUniqueID> _nexts;

    // test (under the test...)
    // Get all the next and previous which are not blank actions
    // Get all the new next and previous which are not blank actions
    NodeHashMap<int, PositionUSigSetUniqueID> _previous_primitive_tree;
    NodeHashMap<int, PositionUSigSetUniqueID> _nexts_primitive_tree;
    NodeHashMap<int, PositionUSigSetUniqueID> _new_previous_primitive_tree;
    NodeHashMap<int, PositionUSigSetUniqueID> _new_nexts_primitive_tree;

    // Indicate for each Usignature its last parent method (only one parent method is allowed)
    // NodeHashMap<USignature, int, USignatureHasher> _last_parent_method_id;

    NodeHashSet<USignature, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> _actions_in_primitive_tree;

    USignature actionOrReductionTrue;

    // END TEST ========================================================

    USigSet _axiomatic_ops;

    // All VIRTUAL facts potentially occurring at this position.
    USigSet _qfacts;
    // Maps a q-fact to the set of possibly valid decoded facts.
    NodeHashMap<USignature, USigSet, USignatureHasher> _pos_qfact_decodings;
    NodeHashMap<USignature, USigSet, USignatureHasher> _neg_qfact_decodings;

    // All facts that are definitely true at this position.
    USigSet _true_facts;
    // All facts that are definitely false at this position.
    USigSet _false_facts;

    NodeHashMap<USignature, USigSet, USignatureHasher>* _pos_fact_supports = nullptr;
    NodeHashMap<USignature, USigSet, USignatureHasher>* _neg_fact_supports = nullptr;
    IndirectFactSupportMap* _pos_indir_fact_supports = nullptr;
    IndirectFactSupportMap* _neg_indir_fact_supports = nullptr;

    // NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasher> _q_constants_type_constraints;
    // NodeHashMap<USignature, std::vector<SubstitutionConstraint>, USignatureHasher> _substitution_constraints;

    NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> _q_constants_type_constraints;
    NodeHashMap<USignature, std::vector<SubstitutionConstraint>, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> _substitution_constraints;



    size_t _max_expansion_size = 1;

    // Prop. variable for each occurring signature.
    NodeHashMap<USignature, int, USignatureHasher> _op_variables;
    NodeHashMap<USignature, int, USignatureHasher> _fact_variables;

    NodeHashMap<USignature, int, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> _op_variables_unique_id;
    // NodeHashMap<int, int> _op_variables_unique_id;



    bool _has_primitive_ops = false;
    bool _has_nonprimitive_ops = false;

public:

    Position();
    void setPos(size_t layerIdx, size_t pos);
    void setAbovePos(size_t abovePos);
    void setLtpPos(size_t ltpPos);

    void addQFact(const USignature& qfact);
    void addTrueFact(const USignature& fact);
    void addFalseFact(const USignature& fact);
    void addDefinitiveFact(const Signature& fact);

    void addFactSupport(const Signature& fact, const USignature& operation);
    void touchFactSupport(const Signature& fact);
    void touchFactSupport(const USignature& fact, bool negated);
    void addIndirectFactSupport(const USignature& fact, bool negated, const USignature& op, const std::vector<IntPair>& path);
    void setHasPrimitiveOps(bool has);
    void setHasNonprimitiveOps(bool has);
    bool hasPrimitiveOps();
    bool hasNonprimitiveOps();

    void addQConstantTypeConstraint(const USignature& op, const TypeConstraint& c);
    void addSubstitutionConstraint(const USignature& op, SubstitutionConstraint&& constr);

    bool hasQFactDecodings(const USignature& qFact, bool negated);
    void addQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated);
    void removeQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated);
    const USigSet& getQFactDecodings(const USignature& qfact, bool negated);

    // void addAction(const USignature& action);
    void addAction(USignature& action);
    void addAction(USignature&& action);
    void addReduction(const USignature& reduction);
    void addExpansion(const USignature& parent, const USignature& child);
    void addExpansionSubstitution(const USignature& parent, const USignature& child, const Substitution& s);
    void addExpansionSubstitution(const USignature& parent, const USignature& child, Substitution&& s);
    void addAxiomaticOp(const USignature& op);
    void addExpansionSize(size_t size);

    // TEST ===========================================================
    void addPrevious(const USignature& current, const USignature& previous);
    void addNexts(const USignature& current, const USignature& next);


    void addPreviousPrimitiveTree(const USignature& current, const PositionedUSig& previous);
    void addNextsPrimitiveTree(const USignature& current, const PositionedUSig& next);

    void addNewPreviousPrimitiveTree(const USignature& current, const PositionedUSig& previous);
    void addNewNextsPrimitiveTree(const USignature& current, const PositionedUSig& next);

    // void addLastParentMethodId(const USignature& current, int lastParentMethodId);
    void addActionInPrimitiveTree(const USignature& action);
    void removeActionInPrimitiveTree(const USignature& action);
    // END TEST ========================================================
    
    void removeActionOccurrence(const USignature& action);
    void removeReductionOccurrence(const USignature& reduction);
    void replaceOperation(const USignature& from, const USignature& to, Substitution&& s);

    const NodeHashMap<USignature, int, USignatureHasher>& getVariableTable(VarType type) const;
    const NodeHashMap<USignature, int, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& getVariableTableOPUniqueID() const;
    void setVariableTable(VarType type, const NodeHashMap<USignature, int, USignatureHasher>& table);
    void moveVariableTable(VarType type, Position& destination);

    bool hasQFact(const USignature& fact) const;
    bool hasAction(const USignature& action) const;
    bool hasActionWithUniqueID(const USignature& action) const;
    bool hasReduction(const USignature& red) const;
    bool hasReductionWithUniqueID(const USignature& red) const;

    const USigSet& getQFacts() const;
    int getNumQFacts() const;
    const USigSet& getTrueFacts() const;
    const USigSet& getFalseFacts() const;
    NodeHashMap<USignature, USigSet, USignatureHasher>& getPosFactSupports();
    NodeHashMap<USignature, USigSet, USignatureHasher>& getNegFactSupports();
    IndirectFactSupportMap& getPosIndirectFactSupports();
    IndirectFactSupportMap& getNegIndirectFactSupports();
    const NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& getQConstantsTypeConstraints() const;
    NodeHashMap<USignature, std::vector<SubstitutionConstraint>, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& getSubstitutionConstraints() {
        return _substitution_constraints;
    }

    USigSet& getActions();
    USigSetUniqueID& getActionsWithUniqueID();
    USigSet& getReductions();
    USigSetUniqueID& getReductionsWithUniqueID();
    NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& getExpansions();
    NodeHashMap<USignature, USigSet, USignatureHasher>& getPredecessors();
    // NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID>& getPredecessorsWithUniqueID();
    NodeHashMap<int, USigSetUniqueID>& getPredecessorsWithUniqueID();
    const NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher>& getExpansionSubstitutions() const;
    const USigSet& getAxiomaticOps() const;
    size_t getMaxExpansionSize() const;

    // TEST 
    NodeHashMap<int, USigSetUniqueID>& getPrevious();
    NodeHashMap<int, USigSetUniqueID>& getNexts();
    NodeHashMap<USignature, int, USignatureHasher>& getLastParentMethodId();
    NodeHashSet<USignature, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& getActionsInPrimitiveTree();

    NodeHashMap<int, PositionUSigSetUniqueID>& getNextsPrimitiveTree();
    NodeHashMap<int, PositionUSigSetUniqueID>& getNewNextsPrimitiveTree();
    NodeHashMap<int, PositionUSigSetUniqueID>& getPreviousesPrimitiveTree();
    NodeHashMap<int, PositionUSigSetUniqueID>& getNewPreviousesPrimitiveTree();


    void setActionOrReductionTrue(USignature& actionOrReduction);
    USignature& getActionOrReductionTrue();
    // END TEST

    size_t getLayerIndex() const;
    size_t getPositionIndex() const;
    size_t getAbovePositionIndex() const;

    size_t getLtpPos() const;
    
    void clearAfterInstantiation();
    void clearAtPastPosition();
    void clearAtPastLayer();
    void clearSubstitutions() {
        _substitution_constraints.clear();
        _substitution_constraints.reserve(0);
    }

    inline int encode(VarType type, const USignature& sig) {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        auto it = vars.find(sig);
        if (it == vars.end()) {
            // introduce a new variable
            assert(!VariableDomain::isLocked() || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
            int var = VariableDomain::nextVar();
            vars[sig] = var;
            VariableDomain::printVar(var, _layer_idx, _pos, sig);
            return var;
        } else return it->second;
    }

    inline int setVariable(VarType type, const USignature& sig, int var) {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        assert(!vars.count(sig));
        vars[sig] = var;
        return var;
    }

    inline bool hasVariable(VarType type, const USignature& sig) const {
        return (type == OP ? _op_variables : _fact_variables).count(sig);
    }

    inline int getVariable(VarType type, const USignature& sig) const {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        assert(vars.count(sig) || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
        return vars.at(sig);
    }

    inline int getVariableOrZero(VarType type, const USignature& sig) const {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        const auto& it = vars.find(sig);
        if (it == vars.end()) return 0;
        return it->second;
    }

    inline void removeVariable(VarType type, const USignature& sig) {
        auto& vars = type == OP ? _op_variables : _fact_variables;
        vars.erase(sig);
    }





    // TEST
    inline int encodeUniqueID(VarType type, const USignature& sig) {
        if (type == OP) {
            auto& vars = _op_variables_unique_id;
            auto it = vars.find(sig);
            if (it == vars.end()) {
                // introduce a new variable
                assert(!VariableDomain::isLocked() || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
                int var = VariableDomain::nextVar();
                vars[sig] = var;
                VariableDomain::printVar(var, _layer_idx, _pos, sig);
                return var;
            } else return it->second;
        } else {
            auto& vars = _fact_variables;
            auto it = vars.find(sig);
            if (it == vars.end()) {
                // introduce a new variable
                assert(!VariableDomain::isLocked() || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
                int var = VariableDomain::nextVar();
                vars[sig] = var;
                VariableDomain::printVar(var, _layer_idx, _pos, sig);
                return var;
            } else return it->second;
        }
    }

    inline int setVariableUniqueID(VarType type, const USignature& sig, int var) {
        if (type == OP) {
            auto& vars = _op_variables_unique_id;
            assert(!vars.count(sig));
            vars[sig] = var;
            return var;
        } else {
            auto& vars = _fact_variables;
            assert(!vars.count(sig));
            vars[sig] = var;
            return var;
        }
    }

    inline bool hasVariableUniqueID(VarType type, const USignature& sig) const {
        if (type == OP) {
            return _op_variables_unique_id.count(sig);
        } else {
            return _fact_variables.count(sig);
        }
    }

    inline int getVariableUniqueID(VarType type, const USignature& sig) const {
        if (type == OP) {
            assert(_op_variables_unique_id.count(sig) || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
            return _op_variables_unique_id.at(sig);
        } else {
            assert(_fact_variables.count(sig) || Log::e("Unknown variable %s queried!\n", VariableDomain::varName(_layer_idx, _pos, sig).c_str()));
            return _fact_variables.at(sig);
        }
    }

    inline int getVariableOrZeroUniqueID(VarType type, const USignature& sig) const {
        if (type == OP) {
            const auto& it = _op_variables_unique_id.find(sig);
            if (it == _op_variables_unique_id.end()) return 0;
            return it->second;
        } else {
            const auto& it = _fact_variables.find(sig);
            if (it == _fact_variables.end()) return 0;
            return it->second;
        }
    }

    inline void removeVariableUniqueID(VarType type, const USignature& sig) {
        if (type == OP) {
            _op_variables_unique_id.erase(sig);
        } else {
            _fact_variables.erase(sig);
        }
    }
};


#endif