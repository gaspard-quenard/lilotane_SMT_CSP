
#include "position.h"

#include "sat/variable_domain.h"
#include "util/log.h"

NodeHashMap<USignature, USigSet, USignatureHasher> Position::EMPTY_USIG_TO_USIG_SET_MAP;
IndirectFactSupportMap Position::EMPTY_INDIRECT_FACT_SUPPORT_MAP;

Position::Position() : _layer_idx(-1), _pos(-1) {}
void Position::setPos(size_t layerIdx, size_t pos) {_layer_idx = layerIdx; _pos = pos;}
void Position::setAbovePos(size_t abovePos) {_above_pos = abovePos;}

void Position::addQFact(const USignature& qfact) {
    _qfacts.insert(qfact);
}
void Position::addTrueFact(const USignature& fact) {_true_facts.insert(fact);}
void Position::addFalseFact(const USignature& fact) {_false_facts.insert(fact);}
void Position::addDefinitiveFact(const Signature& fact) {(fact._negated ? _false_facts : _true_facts).insert(fact._usig);}

void Position::addFactSupport(const Signature& fact, const USignature& operation) {
    auto& supp = fact._negated ? _neg_fact_supports : _pos_fact_supports;
    if (supp == nullptr) supp = new NodeHashMap<USignature, USigSet, USignatureHasher>();
    auto& set = (*supp)[fact._usig];
    set.insert(operation);
}
void Position::touchFactSupport(const Signature& fact) {
    auto& supp = fact._negated ? _neg_fact_supports : _pos_fact_supports;
    if (supp == nullptr) supp = new NodeHashMap<USignature, USigSet, USignatureHasher>();
    (*supp)[fact._usig];
}
void Position::touchFactSupport(const USignature& fact, bool negated) {
    auto& supp = negated ? _neg_fact_supports : _pos_fact_supports;
    if (supp == nullptr) supp = new NodeHashMap<USignature, USigSet, USignatureHasher>();
    (*supp)[fact];
}
void Position::addIndirectFactSupport(const USignature& fact, bool negated, const USignature& op, const std::vector<IntPair>& path) {
    auto& supp = negated ? _neg_indir_fact_supports : _pos_indir_fact_supports;
    if (supp == nullptr) supp = new IndirectFactSupportMap();
    auto& tree = (*supp)[fact][op];
    tree.insert(path);
}
void Position::setHasPrimitiveOps(bool has) {
    _has_primitive_ops = has;
}
void Position::setHasNonprimitiveOps(bool has) {
    _has_nonprimitive_ops = has;
}
bool Position::hasPrimitiveOps() {
    return _has_primitive_ops;
}
bool Position::hasNonprimitiveOps() {
    return _has_nonprimitive_ops;
}

void Position::addQConstantTypeConstraint(const USignature& op, const TypeConstraint& c) {
    auto& vec = _q_constants_type_constraints[op];
    vec.push_back(c);
}

void Position::addSubstitutionConstraint(const USignature& op, SubstitutionConstraint&& constr) {
    _substitution_constraints[op].emplace_back(std::move(constr));
}

void Position::addQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated) {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    set[qFact].insert(decFact);
    //Log::v("QFACTDEC %s -> %s (%s)\n", TOSTR(qFact), TOSTR(decFact), negated?"false":"true");
}

void Position::removeQFactDecoding(const USignature& qFact, const USignature& decFact, bool negated) {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    set[qFact].erase(decFact);
}

bool Position::hasQFactDecodings(const USignature& qFact, bool negated) {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    return set.count(qFact);
}

const USigSet& Position::getQFactDecodings(const USignature& qFact, bool negated) {
    auto& set = negated ? _neg_qfact_decodings : _pos_qfact_decodings;
    assert(set.count(qFact) || Log::e("No qfact decodings for %s!\n", TOSTR(qFact)));
    return set.at(qFact);
}

// void Position::addAction(const USignature& action) {
//     _actions.insert(action);
//     Log::d("+ACTION@(%i,%i) %s\n", _layer_idx, _pos, TOSTR(action));
// }
void Position::addAction(USignature& action) {
    // action.setRepetition(10);
    _actions.insert(action);
    // Forced to do that because of the way the hash is computed
    _actionsWithUniqueID.insert(action);
    Log::d("+ACTION@(%i,%i) %s\n", _layer_idx, _pos, TOSTR(action));
}
void Position::addAction(USignature&& action) {
    Log::d("+ACTION@(%i,%i) %s\n", _layer_idx, _pos, TOSTR(action));
    _actions.insert(std::move(action));

    // Forced to do that because of the way the hash is computed
    _actionsWithUniqueID.insert(action);
}
void Position::addReduction(const USignature& reduction) {
    _reductions.insert(reduction);
    Log::d("+REDUCTION@(%i,%i) %s\n", _layer_idx, _pos, TOSTR(reduction));
}
void Position::addExpansion(const USignature& parent, const USignature& child) {

    // if (child._unique_id == 366) {
    //     int dbg = 0;
    //     // USignature copy = child;
    //     // copy._unique_id = 366;
    //     // Check if it is in the set
    //     // auto& predUniqueId = _predecessors_with_unique_id[copy];
    //     // if (predUniqueId.size() > 0) {
    //     //     int dbg = 0;
    //     // }
    // }

    auto& set = _expansions[parent];
    set.insert(child);
    auto& pred = _predecessors[child];
    pred.insert(parent);

    auto& predUniqueId = _predecessors_with_unique_id[child._unique_id];
    if (predUniqueId.size() > 0) {
        Log::i("Size superior for %s (%i)\n", Names::to_SMT_string(child).c_str(), child._unique_id);
        Log::i("All predecessors:\n");
        for (const auto& p : predUniqueId) {
            Log::i("    %s (%i)\n", Names::to_SMT_string(p).c_str(), p._unique_id);
            // Write all of its children
            auto& children = _expansions[p];
            Log::i("        Children:\n");
            for (const auto& c : children) {
                Log::i("            %s (%i)\n", Names::to_SMT_string(c).c_str(), c._unique_id);
            }
        }
        Log::i("    %s (%i)\n", Names::to_SMT_string(parent).c_str(), parent._unique_id);
        Log::i("        Children:\n");
        for (const auto& c : set) {
            Log::i("            %s (%i)\n", Names::to_SMT_string(c).c_str(), c._unique_id);
        }
        int dbg = 0;
    }
    predUniqueId.insert(parent);

    // if (child._unique_id == 364) {
    //     // Make a test, do a copy and change the unique_id
    //     USignature copy = child;
    //     copy._unique_id = 366;
    //     // Check if it is in the set
    //     auto& predUniqueId = _predecessors_with_unique_id[copy];
    //     if (predUniqueId.size() > 0) {
    //         int dbg = 0;
    //     }
    // }
}



// TEST  ================================================
void Position::addPrevious(const USignature& current, const USignature& previous) {
    if (previous._unique_id == 130) {
        int dbg = 0;
    }
    auto& set = _previous[current._unique_id];
    set.insert(previous);
}

void Position::addNexts(const USignature& current, const USignature& next) {
    auto& set = _nexts[current._unique_id];
    set.insert(next);
}

// void Position::addLastParentMethodId(const USignature& current, int lastParentMethodId) {
//     _last_parent_method_id[current] = lastParentMethodId;
// }

void Position::addActionInPrimitiveTree(const USignature& action) {
    _actions_in_primitive_tree.insert(action);
}

void Position::removeActionInPrimitiveTree(const USignature& action) {
    // Remove action in primitive tree if exist
    if (_actions_in_primitive_tree.count(action)) {
        _actions_in_primitive_tree.erase(action);
    }
}

void Position::setActionOrReductionTrue(USignature& actionOrReduction) {
    actionOrReductionTrue = actionOrReduction;
}

USignature& Position::getActionOrReductionTrue() {
    return actionOrReductionTrue;
}
// END TEST ================================================



void Position::addExpansionSubstitution(const USignature& parent, const USignature& child, Substitution&& s) {
    _expansion_substitutions[parent][child] = std::move(s);
}
void Position::addExpansionSubstitution(const USignature& parent, const USignature& child, const Substitution& s) {
    _expansion_substitutions[parent][child] = s;
}
void Position::addAxiomaticOp(const USignature& op) {
    _axiomatic_ops.insert(op);
}
void Position::addExpansionSize(size_t size) {_max_expansion_size = std::max(_max_expansion_size, size);}

void Position::removeActionOccurrence(const USignature& action) {
    _actions.erase(action);
    _actionsWithUniqueID.erase(action);
    for (auto& [parent, children] : _expansions) {
        children.erase(action);
    }
    _predecessors.erase(action);
}
void Position::removeReductionOccurrence(const USignature& reduction) {
    _reductions.erase(reduction);
    for (auto& [parent, children] : _expansions) {
        children.erase(reduction);
    }
    _predecessors.erase(reduction);
}
void Position::replaceOperation(const USignature& from, const USignature& to, Substitution&& s) {
    auto predecessors = getPredecessors().at(from);
    removeActionOccurrence(from);
    removeReductionOccurrence(from);
    for (const auto& parent : predecessors) {
        addExpansion(parent, to);
        addExpansionSubstitution(parent, to, s);
    }
}

const NodeHashMap<USignature, int, USignatureHasher>& Position::getVariableTable(VarType type) const {
    return type == OP ? _op_variables : _fact_variables;
}

const NodeHashMap<USignature, int, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& Position::getVariableTableOPUniqueID() const {
    return _op_variables_unique_id;
}

void Position::setVariableTable(VarType type, const NodeHashMap<USignature, int, USignatureHasher>& table) {
    if (type == OP) {
        _op_variables = table;
    } else {
        _fact_variables = table;
    }
}
void Position::moveVariableTable(VarType type, Position& destination) {
    auto& src = type == OP ? _op_variables : _fact_variables;
    auto& dest = type == OP ? destination._op_variables : destination._fact_variables;
    dest = std::move(src);
    src.clear();
    src.reserve(0);
}

bool Position::hasQFact(const USignature& fact) const {return _qfacts.count(fact);}
bool Position::hasAction(const USignature& action) const {return _actions.count(action);}
bool Position::hasReduction(const USignature& red) const {return _reductions.count(red);}

size_t Position::getLayerIndex() const {return _layer_idx;}
size_t Position::getPositionIndex() const {return _pos;}
size_t Position::getAbovePositionIndex() const {return _above_pos;}

const USigSet& Position::getQFacts() const {return _qfacts;}
const USigSet& Position::getTrueFacts() const {return _true_facts;}
const USigSet& Position::getFalseFacts() const {return _false_facts;}
NodeHashMap<USignature, USigSet, USignatureHasher>& Position::getPosFactSupports() {
    if (_pos_fact_supports == nullptr) return EMPTY_USIG_TO_USIG_SET_MAP;
    return *_pos_fact_supports;
}
NodeHashMap<USignature, USigSet, USignatureHasher>& Position::getNegFactSupports() {
    if (_neg_fact_supports == nullptr) return EMPTY_USIG_TO_USIG_SET_MAP;
    return *_neg_fact_supports;
}
IndirectFactSupportMap& Position::getPosIndirectFactSupports() {
    if (_pos_indir_fact_supports == nullptr) return EMPTY_INDIRECT_FACT_SUPPORT_MAP;
    return *_pos_indir_fact_supports;
}
IndirectFactSupportMap& Position::getNegIndirectFactSupports() {
    if (_neg_indir_fact_supports == nullptr) return EMPTY_INDIRECT_FACT_SUPPORT_MAP;
    return *_neg_indir_fact_supports;
}
const NodeHashMap<USignature, std::vector<TypeConstraint>, USignatureHasher>& Position::getQConstantsTypeConstraints() const {
    return _q_constants_type_constraints;
}

USigSet& Position::getActions() {return _actions;}
USigSetUniqueID& Position::getActionsWithUniqueID() {return _actionsWithUniqueID;}
USigSet& Position::getReductions() {return _reductions;}
NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& Position::getExpansions() {return _expansions;}
NodeHashMap<USignature, USigSet, USignatureHasher>& Position::getPredecessors() {return _predecessors;}
// NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID>& Position::getPredecessorsWithUniqueID() {return _predecessors_with_unique_id;}
NodeHashMap<int, USigSetUniqueID>& Position::getPredecessorsWithUniqueID() {return _predecessors_with_unique_id;}
const NodeHashMap<USignature, USigSubstitutionMap, USignatureHasher>& Position::getExpansionSubstitutions() const {return _expansion_substitutions;}
const USigSet& Position::getAxiomaticOps() const {return _axiomatic_ops;}
size_t Position::getMaxExpansionSize() const {return _max_expansion_size;}

// TEST
NodeHashMap<int, USigSetUniqueID>& Position::getPrevious() {return _previous;}
NodeHashMap<int, USigSetUniqueID>& Position::getNexts() {return _nexts;}
// NodeHashMap<USignature, int, USignatureHasher>& Position::getLastParentMethodId() {return _last_parent_method_id;}
NodeHashSet<USignature, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID>& Position::getActionsInPrimitiveTree() {return _actions_in_primitive_tree;}
// END TEST

void Position::clearAfterInstantiation() {
}

void Position::clearAtPastPosition() {
    _qfacts.clear();
    _qfacts.reserve(0);
    /*
    _expansions.clear();
    _expansions.reserve(0);
    _predecessors.clear();
    _predecessors.reserve(0);
    */
   _expansion_substitutions.clear();
   _expansion_substitutions.reserve(0);
    _axiomatic_ops.clear();
    _axiomatic_ops.reserve(0);
    _q_constants_type_constraints.clear();
    _q_constants_type_constraints.reserve(0);
    clearSubstitutions();
    if (_pos_fact_supports != nullptr) delete _pos_fact_supports;
    if (_neg_fact_supports != nullptr) delete _neg_fact_supports;
    if (_pos_indir_fact_supports != nullptr) delete _pos_indir_fact_supports;
    if (_neg_indir_fact_supports != nullptr) delete _neg_indir_fact_supports;
}

void Position::clearAtPastLayer() {
    _pos_qfact_decodings.clear();
    _pos_qfact_decodings.reserve(0);
    _neg_qfact_decodings.clear();
    _neg_qfact_decodings.reserve(0);
    _true_facts.clear();
    _true_facts.reserve(0);
    _false_facts.clear();
    _false_facts.reserve(0);
    _fact_variables.clear();
    _fact_variables.reserve(0);
    /*
    _actions.clear();
    _actions.reserve(0);
    _reductions.clear();
    _reductions.reserve(0);
    */
}