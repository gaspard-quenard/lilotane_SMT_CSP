
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

    USigSet _actions;
    USigSet _reductions;

    USigSetUniqueID _actionsWithUniqueID;

    NodeHashMap<USignature, USigSet, USignatureHasherWithUniqueID> _expansions;
    NodeHashMap<USignature, USigSet, USignatureHasher> _predecessors; // FOR STRANGE REASON, I CANNOT PUT USignatureHasherWithUniqueID AS HASH HERE ???
    // NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID> _predecessors_with_unique_id; 
    NodeHashMap<int, USigSetUniqueID> _predecessors_with_unique_id; 
    NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher> _expansion_substitutions;

    // TEST ===========================================================

    NodeHashMap<USignature, USigSet, USignatureHasher> _previous;
    NodeHashMap<USignature, USigSet, USignatureHasher> _nexts;
    // Indicate for each Usignature its last parent method (only one parent method is allowed)
    NodeHashMap<USignature, int, USignatureHasher> _last_parent_method_id;

    NodeHashSet<USignature, USignatureHasher> _actions_in_primitive_tree;

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

    NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasher> _q_constants_type_constraints;
    NodeHashMap<USignature, std::vector<SubstitutionConstraint>, USignatureHasher> _substitution_constraints;

    size_t _max_expansion_size = 1;

    // Prop. variable for each occurring signature.
    NodeHashMap<USignature, int, USignatureHasher> _op_variables;
    NodeHashMap<USignature, int, USignatureHasher> _fact_variables;

    NodeHashMap<int, int> _op_variables_unique_id;



    bool _has_primitive_ops = false;
    bool _has_nonprimitive_ops = false;

public:

    Position();
    void setPos(size_t layerIdx, size_t pos);

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
    void addLastParentMethodId(const USignature& current, int lastParentMethodId);
    void addActionInPrimitiveTree(const USignature& action);
    void removeActionInPrimitiveTree(const USignature& action);
    // END TEST ========================================================
    
    void removeActionOccurrence(const USignature& action);
    void removeReductionOccurrence(const USignature& reduction);
    void replaceOperation(const USignature& from, const USignature& to, Substitution&& s);

    const NodeHashMap<USignature, int, USignatureHasher>& getVariableTable(VarType type) const;
    void setVariableTable(VarType type, const NodeHashMap<USignature, int, USignatureHasher>& table);
    void moveVariableTable(VarType type, Position& destination);

    bool hasQFact(const USignature& fact) const;
    bool hasAction(const USignature& action) const;
    bool hasReduction(const USignature& red) const;

    const USigSet& getQFacts() const;
    int getNumQFacts() const;
    const USigSet& getTrueFacts() const;
    const USigSet& getFalseFacts() const;
    NodeHashMap<USignature, USigSet, USignatureHasher>& getPosFactSupports();
    NodeHashMap<USignature, USigSet, USignatureHasher>& getNegFactSupports();
    IndirectFactSupportMap& getPosIndirectFactSupports();
    IndirectFactSupportMap& getNegIndirectFactSupports();
    const NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasher>& getQConstantsTypeConstraints() const;
    NodeHashMap<USignature, std::vector<SubstitutionConstraint>, USignatureHasher>& getSubstitutionConstraints() {
        return _substitution_constraints;
    }

    USigSet& getActions();
    USigSetUniqueID& getActionsWithUniqueID();
    USigSet& getReductions();
    NodeHashMap<USignature, USigSet, USignatureHasherWithUniqueID>& getExpansions();
    NodeHashMap<USignature, USigSet, USignatureHasher>& getPredecessors();
    // NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID>& getPredecessorsWithUniqueID();
    NodeHashMap<int, USigSetUniqueID>& getPredecessorsWithUniqueID();
    const NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher>& getExpansionSubstitutions() const;
    const USigSet& getAxiomaticOps() const;
    size_t getMaxExpansionSize() const;

    // TEST 
    NodeHashMap<USignature, USigSet, USignatureHasher>& getPrevious();
    NodeHashMap<USignature, USigSet, USignatureHasher>& getNexts();
    NodeHashMap<USignature, int, USignatureHasher>& getLastParentMethodId();
    NodeHashSet<USignature, USignatureHasher>& getActionsInPrimitiveTree();
    // END TEST

    size_t getLayerIndex() const;
    size_t getPositionIndex() const;
    
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
};


#endif