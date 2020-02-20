
#include "sat/encoding.h"
#include "util/log.h"

/*
encodePosition ()
*/

Encoding::Encoding(HtnInstance& htn, std::vector<Layer>& layers) : _htn(htn), 
            _layers(&layers) {
    _solver = ipasir_init();
    _sig_primitive = Signature(_htn.getNameId("__PRIMITIVE___"), std::vector<int>());
    _substitute_name_id = _htn.getNameId("__SUBSTITUTE___");
    _out.open("formula.cnf");
}

void Encoding::encode(int layerIdx, int pos) {
    
    printf("[ENC] position (%i,%i) ...\n", layerIdx, pos);

    // Calculate relevant environment of the position
    Position NULL_POS;
    NULL_POS.setPos(-1, -1);
    Layer& newLayer = _layers->at(layerIdx);
    Position& newPos = newLayer[pos];
    bool hasLeft = pos > 0;
    Position& left = (hasLeft ? newLayer[pos-1] : NULL_POS);
    int oldPos = 0, offset = 0;
    bool hasAbove = layerIdx > 0;
    if (hasAbove) {
        const Layer& oldLayer = _layers->at(layerIdx-1);
        while (oldPos+1 < oldLayer.size() && oldLayer.getSuccessorPos(oldPos+1) <= pos) 
            oldPos++;
        offset = pos - oldLayer.getSuccessorPos(oldPos);
    }
    Position& above = (hasAbove ? _layers->at(layerIdx-1)[oldPos] : NULL_POS);

    // Important variables for this position
    int varPrim = varPrimitive(layerIdx, pos);
    
    // Facts that must hold at this position
    for (auto pair : newPos.getTrueFacts()) {
        const Signature& factSig = pair.first;
        int factVar = newPos.encode(factSig);
        addClause({factVar});
    }

    // Link qfacts to their possible decodings
    for (auto pair : newPos.getQFactDecodings()) {
        const Signature& qfactSig = pair.first;
        assert(!qfactSig._negated);
        int qfactVar = newPos.encode(qfactSig);

        // initialize substitution logic where necessary
        initSubstitutionVars(qfactSig, newPos);

        // For each possible fact decoding:
        for (const auto& decFactSig : pair.second) {
            assert(!decFactSig._negated);
            int decFactVar = newPos.encode(decFactSig);

            // Get substitution from qfact to its decoded fact
            substitution_t s = Substitution::get(qfactSig._args, decFactSig._args);
            std::vector<int> substitutionVars;
            for (auto sPair : s) {
                Signature sigSubst = sigSubstitute(sPair.first, sPair.second);
                substitutionVars.push_back(varSubstitution(sigSubst));
            }
            
            // If the substitution is chosen,
            // the q-fact and the corresponding actual fact are equivalent
            for (int sign = -1; sign <= 1; sign += 2) {
                for (int varSubst : substitutionVars) {
                    appendClause({-varSubst});
                }
                appendClause({sign*qfactVar, -sign*decFactVar});
                endClause();
            }
        }
    }

    // Propagate fact assignments from above
    for (auto pair : newPos.getFacts()) {
        const Signature& factSig = pair.first;
        int factVar = newPos.encode(factSig);

        if (hasAbove && offset == 0 && above.getFacts().count(factSig)) {
            // Fact comes from above: propagate meaning
            int oldFactVar = above.getVariable(factSig);
            addClause({-oldFactVar, factVar});
            addClause({oldFactVar, -factVar});
        }
    }

    // Fact supports, frame axioms (only for non-new facts free of q-constants)
    if (pos > 0)
    for (auto pair : newPos.getFacts()) {
        assert(!pair.first._negated);

        Signature factSig = pair.first;
        if (_htn.hasQConstants(factSig)) continue;

        bool firstOccurrence = !left.getFacts().count(factSig);
        if (firstOccurrence) {
            // First time the fact occurs must be as a "false fact"
            assert(newPos.getTrueFacts().count(factSig.opposite()));
            continue;
        }

        for (int sign = -1; sign <= 1; sign += 2) {

            factSig._negated = sign < 0;
            int oldFactVar = left.getVariable(factSig);
            int factVar = newPos.encode(factSig);

            // Calculate indirect support through qfact abstractions
            std::unordered_set<int> indirectSupport;
            if (newPos.getQFactAbstractions().count(factSig.abs())) {
                for (Signature sig : newPos.getQFactAbstractions().at(factSig.abs())) {
                    const Signature qfactSig = (factSig._negated ? sig.opposite() : sig);

                    // For each operation that supports some qfact abstraction of the fact:
                    if (newPos.getFactSupports().count(qfactSig))
                    for (Signature opSig : newPos.getFactSupports().at(qfactSig)) {
                        int opVar = left.getVariable(opSig);
                        assert(opVar > 0);
                        
                        // Calculate and encode prerequisites for indirect support

                        // Find valid sets of substitutions for this operation causing the desired effect
                        SigSet opSet; opSet.insert(opSig);
                        auto subMap = _htn._instantiator->getOperationSubstitutionsCausingEffect(opSet, factSig);
                        assert(subMap.count(opSig));
                        if (subMap[opSig].empty()) {
                            // No valid instantiations!
                            continue;
                        }

                        // Assemble possible substitution options to get the desired fact support
                        std::set<std::set<int>> substOptions;
                        bool unconditionalEffect = false;
                        for (substitution_t s : subMap[opSig]) {
                            if (s.empty()) {
                                // Empty substitution does the job
                                unconditionalEffect = true;
                                break;
                            }
                            // An actual substitution is necessary
                            std::set<int> substOpt;
                            for (std::pair<int,int> entry : s) {
                                int substVar = varSubstitution(sigSubstitute(entry.first, entry.second));
                                substOpt.insert(substVar);
                            }
                            substOptions.insert(substOpt);
                        }

                        if (!unconditionalEffect) {
                            // Bring the found substitution sets to CNF and encode them
                            std::vector<std::vector<int>> dnfSubs;
                            for (auto set : substOptions) {
                                std::vector<int> vec;
                                vec.insert(vec.end(), set.begin(), set.end());
                                dnfSubs.push_back(vec);
                            }
                            std::set<std::set<int>> cnfSubs = getCnf(dnfSubs);
                            for (std::set<int> subsCls : cnfSubs) {
                                // IF fact change AND the operation is applied,
                                if (oldFactVar != 0) appendClause({oldFactVar});
                                #ifndef NONPRIMITIVE_SUPPORT
                                appendClause({-varPrimitive(layerIdx, pos-1)});
                                #endif
                                appendClause({-factVar, -opVar});
                                //printf("FRAME AXIOMS %i %i %i ", oldFactVar, -factVar, -opVar);
                                // THEN either of the valid substitution combinations
                                for (int subVar : subsCls) {
                                    appendClause({subVar});
                                    //printf("%i ", subVar);  
                                } 
                                endClause();
                                //printf("\n");
                            }
                        }

                        // Add operation to indirect support
                        indirectSupport.insert(opVar); 
                    }
                }
            }

            // Fact change:
            //printf("FRAME AXIOMS %i %i ", oldFactVar, -factVar);
            if (oldFactVar != 0) appendClause({oldFactVar});
            appendClause({-factVar});
            #ifndef NONPRIMITIVE_SUPPORT
            // Non-primitiveness wildcard
            appendClause({-varPrimitive(layerIdx, pos-1)});
            #endif
            // DIRECT support
            if (newPos.getFactSupports().count(factSig)) {
                for (Signature opSig : newPos.getFactSupports().at(factSig)) {
                    int opVar = left.getVariable(opSig);
                    assert(opVar > 0);
                    appendClause({opVar});
                    //printf("%i ", opVar);
                }
            }
            // INDIRECT support
            for (int opVar : indirectSupport) {
                appendClause({opVar});
                //printf("%i ", opVar);
            }
            endClause();
            //printf("\n");
        }
    }

    std::unordered_map<int, std::vector<int>> expansions;
    std::vector<int> axiomaticOps;

    // Effects of "old" actions to the left
    for (auto pair : left.getActions()) {
        const Signature& aSig = pair.first;
        if (aSig == Position::NONE_SIG) continue;
        int aVar = left.encode(aSig);

        for (Signature eff : _htn._actions_by_sig[aSig].getEffects()) {
            
            // Check that the action is contained in the effect's support
            assert(!newPos.getFactSupports().empty());
            assert(newPos.getFactSupports().count(eff));
            assert(newPos.getFactSupports().at(eff).count(aSig));

            addClause({-aVar, newPos.encode(eff)});
        }
    }

    // New actions
    int numOccurringOps = 0;
    for (auto pair : newPos.getActions()) {
        const Signature& aSig = pair.first;

        if (aSig == Position::NONE_SIG) {
            for (Reason why : pair.second) {
                //printf("FORBID %s\n", Names::to_string(why.sig).c_str());
                int oldAVar = above.getVariable(why.sig.abs());
                addClause({-oldAVar});
            }
            continue;
        }

        numOccurringOps++;
        int aVar = newPos.encode(aSig);
        //printVar(layerIdx, pos, aSig);
        addClause({-aVar, varPrim});

        // Preconditions
        for (Signature pre : _htn._actions_by_sig[aSig].getPreconditions()) {
            addClause({-aVar, newPos.encode(pre)});
        }

        // Examine reason for the action
        for (Reason why : pair.second) {
            assert(!why.sig._negated);

            if (why.axiomatic) {
                axiomaticOps.push_back(aVar);
            } else if (why.getOriginPos() == above.getPos()) {
                // Action is result of a propagation or expansion
                // from the layer above
                int oldOpVar = above.getVariable(why.sig.abs());
                expansions[oldOpVar];
                expansions[oldOpVar].push_back(aVar);
            } else abort();
        }

        // At-most-one action
        for (auto otherPair : newPos.getActions()) {
            const Signature& otherSig = otherPair.first;
            int otherVar = newPos.encode(otherSig);
            if (aVar < otherVar) {
                addClause({-aVar, -otherVar});
            }
        }
    }

    // reductions
    for (auto pair : newPos.getReductions()) {
        const Signature& rSig = pair.first;

        // "Virtual children" forbidding parent reductions
        if (rSig == Position::NONE_SIG) {
            for (Reason why : pair.second) {
                //printf("FORBID %s\n", Names::to_string(why.sig).c_str());
                int oldRVar = above.getVariable(why.sig.abs());
                addClause({-oldRVar});
            }
            continue;
        }

        numOccurringOps++;
        int rVar = newPos.encode(rSig);
        addClause({-rVar, -varPrim});

        // Preconditions
        for (Signature pre : _htn._reductions_by_sig[rSig].getPreconditions()) {
            assert(newPos.getFacts().count(pre.abs()));
            addClause({-rVar, newPos.encode(pre)});
        }

        // Actual children
        for (Reason why : pair.second) {
            assert(!why.sig._negated);
            if (why.axiomatic) {
                // axiomatic reduction
                axiomaticOps.push_back(rVar);
            } else if (why.getOriginPos() == above.getPos()) {
                // expansion
                int oldRVar = above.getVariable(why.sig.abs());
                expansions[oldRVar];
                expansions[oldRVar].push_back(rVar);
            } else abort();
        }

        // At-most-one reduction
        for (auto otherPair : newPos.getReductions()) {
            const Signature& otherSig = otherPair.first;
            if (otherSig == Position::NONE_SIG) continue;
            int otherVar = newPos.encode(otherSig);
            if (rVar < otherVar) {
                addClause({-rVar, -otherVar});
            }
        }
    }

    if (numOccurringOps == 0) {
        assert(pos+1 == newLayer.size() 
            || fail("No operations to encode at (" + std::to_string(layerIdx) + "," + std::to_string(pos) + ")!\n"));
    }

    // expansions
    for (auto pair : expansions) {
        int parent = pair.first;
        appendClause({-parent});
        for (int child : pair.second) {
            appendClause({child});
        }
        endClause();
    }
    // choice of axiomatic ops
    if (!axiomaticOps.empty()) {
        for (int var : axiomaticOps) {
            appendClause({var});
        }
        endClause();
    }

    // assume primitiveness
    assume(varPrim);

    printf("[ENC] position (%i,%i) done.\n", layerIdx, pos);
}

void Encoding::initSubstitutionVars(const Signature& qfactSig, Position& pos) {

    for (int argPos = 0; argPos < qfactSig._args.size(); argPos++) {
        int arg = qfactSig._args[argPos];
        if (!_htn._q_constants.count(arg)) continue;
        if (_q_constants.count(arg)) continue;

        // arg is a *new* q-constant: initialize substitution logic

        _q_constants.insert(arg);

        std::vector<int> substitutionVars;
        for (int c : _htn._domains_of_q_constants[arg]) {

            // either of the possible substitutions must be chosen
            Signature sigSubst = sigSubstitute(arg, c);
            int varSubst = varSubstitution(sigSubst);
            substitutionVars.push_back(varSubst);
            
            _q_constants_per_arg[c];
            _q_constants_per_arg[c].push_back(arg);
        }

        // AT LEAST ONE substitution
        for (int vSub : substitutionVars) appendClause({vSub});
        endClause();

        // AT MOST ONE substitution
        for (int vSub1 : substitutionVars) {
            for (int vSub2 : substitutionVars) {
                if (vSub1 < vSub2) addClause({-vSub1, -vSub2});
            }
        } 
    }
}

std::set<std::set<int>> Encoding::getCnf(const std::vector<std::vector<int>>& dnf) {
    std::set<std::set<int>> cnf;

    if (dnf.empty()) return cnf;

    // Iterate over all possible combinations
    std::vector<int> counter(dnf.size(), 0);
    while (true) {
        // Assemble the combination
        std::set<int> newCls;
        for (int pos = 0; pos < counter.size(); pos++) {
            
            assert(pos < dnf.size());
            assert(counter[pos] < dnf[pos].size());

            newCls.insert(dnf[pos][counter[pos]]);
        }
        cnf.insert(newCls);            

        // Increment exponential counter
        int x = 0;
        while (x < counter.size()) {
            if (counter[x]+1 == dnf[x].size()) {
                // max value reached
                counter[x] = 0;
                if (x+1 == counter.size()) break;
            } else {
                // increment
                counter[x]++;
                break;
            }
            x++;
        }

        // Counter finished?
        if (counter[x] == 0 && x+1 == counter.size()) break;
    }

    if (cnf.size() > 1000) printf("CNF of size %i generated\n", cnf.size());

    return cnf;
}

int numLits = 0;
int numClauses = 0;
int numAssumptions = 0;
bool beganLine = false;

void Encoding::addClause(std::initializer_list<int> lits) {
    //printf("CNF ");
    for (int lit : lits) {
        ipasir_add(_solver, lit);
        _out << lit << " ";
        //printf("%i ", lit);
    } 
    ipasir_add(_solver, 0);
    _out << "0\n";
    //printf("0\n");

    numClauses++;
    numLits += lits.size();
}
void Encoding::appendClause(std::initializer_list<int> lits) {
    if (!beganLine) {
        //printf("CNF ");
        beganLine = true;
    }
    for (int lit : lits) {
        ipasir_add(_solver, lit);
        _out << lit << " ";
        //printf("%i ", lit);
    } 

    numLits += lits.size();
}
void Encoding::endClause() {
    assert(beganLine);
    ipasir_add(_solver, 0);
    _out << "0\n";
    //printf("0\n");
    beganLine = false;

    numClauses++;
}
void Encoding::assume(int lit) {
    if (numAssumptions == 0) _last_assumptions.clear();
    ipasir_assume(_solver, lit);
    //printf("CNF !%i\n", lit);
    _last_assumptions.push_back(lit);
    numAssumptions++;
}

bool Encoding::solve() {
    printf("Attempting to solve formula with %i clauses (%i literals) and %i assumptions\n", 
                numClauses, numLits, numAssumptions);
    bool solved = ipasir_solve(_solver) == 10;
    if (numAssumptions == 0) _last_assumptions.clear();
    numAssumptions = 0;
    return solved;
}

bool Encoding::isEncoded(int layer, int pos, const Signature& sig) {
    return _layers->at(layer)[pos].hasVariable(sig);
}

bool Encoding::isEncodedSubstitution(Signature& sig) {
    return _substitution_variables.count(sig.abs());
}

int Encoding::varSubstitution(Signature sigSubst) {
    bool neg = sigSubst._negated;
    Signature sigAbs = neg ? sigSubst.abs() : sigSubst;
    if (!_substitution_variables.count(sigSubst)) {
        assert(!VariableDomain::isLocked() || fail("Unknown substitution variable " 
                    + Names::to_string(sigSubst) + " queried!\n"));
        _substitution_variables[sigAbs] = VariableDomain::nextVar();
        //printf("VARMAP %i %s\n", _substitution_variables[sigAbs], Names::to_string(sigSubst).c_str());
    }
    return _substitution_variables[sigAbs];
}

std::string Encoding::varName(int layer, int pos, const Signature& sig) {
    return _layers->at(layer)[pos].varName(sig);
}

void Encoding::printVar(int layer, int pos, const Signature& sig) {
    printf("%s\n", varName(layer, pos, sig).c_str());
}

int Encoding::varPrimitive(int layer, int pos) {
    return _layers->at(layer)[pos].encode(_sig_primitive);
}

void Encoding::printFailedVars(Layer& layer) {
    printf("FAILED ");
    for (int pos = 0; pos < layer.size(); pos++) {
        int v = varPrimitive(layer.index(), pos);
        if (ipasir_failed(_solver, v)) printf("%i ", v);
    }
    printf("\n");
}

std::vector<PlanItem> Encoding::extractClassicalPlan() {

    Layer& finalLayer = _layers->back();
    int li = finalLayer.index();
    VariableDomain::lock();

    State state = finalLayer[0].getState();
    for (auto pair : state) {
        for (const Signature& fact : pair.second) {
            if (!fact._negated) assert((isEncoded(0, 0, fact) && value(0, 0, fact)) || fail(Names::to_string(fact) + " does not hold initially!\n"));
            if (fact._negated) assert(!isEncoded(0, 0, fact) || value(0, 0, fact) || fail(Names::to_string(fact) + " does not hold initially!\n"));
        } 
    }

    std::vector<PlanItem> plan;
    printf("(actions at layer %i)\n", li);
    for (int pos = 0; pos+1 < finalLayer.size(); pos++) {
        //printf("%i\n", pos);
        assert(value(li, pos, _sig_primitive) || fail("Position " + std::to_string(pos) + " is not primitive!\n"));

        int chosenActions = 0;
        State newState = state;
        SigSet effects;
        for (auto pair : finalLayer[pos].getActions()) {
            const Signature& aSig = pair.first;

            if (!isEncoded(li, pos, aSig)) continue;
            //printf("  %s ?\n", Names::to_string(aSig).c_str());

            if (value(li, pos, aSig)) {
                chosenActions++;
                int aVar = finalLayer[pos].getVariable(aSig);

                // Check fact consistency
                checkAndApply(_htn._actions_by_sig[aSig], state, newState, li, pos);

                //if (aSig == _htn._action_blank.getSignature()) continue;

                // Decode q constants
                Action& a = _htn._actions_by_sig[aSig];
                Signature aDec = getDecodedQOp(li, pos, aSig);
                if (aDec != aSig) {

                    HtnOp opDecoded = a.substitute(Substitution::get(a.getArguments(), aDec._args));
                    Action aDecoded = (Action) opDecoded;

                    // Check fact consistency w.r.t. "actual" decoded action
                    checkAndApply(aDecoded, state, newState, li, pos);
                }

                printf("* %s @ %i\n", Names::to_string(aDec).c_str(), pos);
                plan.push_back({aVar, aDec, aDec, std::vector<int>()});
            }
        }

        //for (Signature sig : newState) {
        //    assert(value(li, pos+1, sig));
        //}
        state = newState;

        assert(chosenActions == 1 || fail("Added " + std::to_string(chosenActions) + " actions at step " + std::to_string(pos) + "!\n"));
    }

    printf("%i actions at final layer of size %i\n", plan.size(), _layers->back().size());
    return plan;
}

bool holds(State& state, const Signature& fact) {
    // Positive fact
    if (!fact._negated)
        return state.count(fact._name_id) && state[fact._name_id].count(fact);
    
    // Negative fact
    return !state.count(fact._name_id) || !state[fact._name_id].count(fact);
}

void Encoding::checkAndApply(const Action& a, State& state, State& newState, int layer, int pos) {
    //printf("%s\n", Names::to_string(a).c_str());
    for (Signature pre : a.getPreconditions()) {

        // Check assignment
        assert((isEncoded(layer, pos, pre) && value(layer, pos, pre)) 
            || fail("Precondition " + Names::to_string(pre) + " of action "
        + Names::to_string(a) + " does not hold in assignment at step " + std::to_string(pos) + "!\n"));

        // Check state
        assert(_htn.hasQConstants(pre) || holds(state, pre) || fail("Precondition " + Names::to_string(pre) + " of action "
            + Names::to_string(a) + " does not hold in inferred state at step " + std::to_string(pos) + "!\n"));
        
        //printf("Pre %s of action %s holds @(%i,%i)\n", Names::to_string(pre).c_str(), Names::to_string(a.getSignature()).c_str(), 
        //        layer, pos);
    }

    for (Signature eff : a.getEffects()) {
        assert((isEncoded(layer, pos+1, eff) && value(layer, pos+1, eff)) 
            || fail("Effect " + Names::to_string(eff) + " of action "
        + Names::to_string(a) + " does not hold in assignment at step " + std::to_string(pos+1) + "!\n"));

        // Apply effect
        if (holds(state, eff.opposite())) newState[eff._name_id].erase(eff.opposite());
        newState[eff._name_id];
        newState[eff._name_id].insert(eff);

        //printf("Eff %s of action %s holds @(%i,%i)\n", Names::to_string(eff).c_str(), Names::to_string(a.getSignature()).c_str(), 
        //        layer, pos);
    }
}

std::vector<PlanItem> Encoding::extractDecompositionPlan() {

    std::vector<PlanItem> plan;
    std::vector<PlanItem> classicalPlan = extractClassicalPlan();

    PlanItem root({0, 
                Signature(_htn.getNameId("root"), std::vector<int>()), 
                Signature(_htn.getNameId("root"), std::vector<int>()), 
                std::vector<int>()});
    
    std::vector<PlanItem> itemsOldLayer, itemsNewLayer;
    itemsOldLayer.push_back(root);

    for (int i = 0; i < _layers->size(); i++) {
        Layer& l = _layers->at(i);
        printf("(decomps at layer %i)\n", l.index());

        itemsNewLayer.resize(l.size());
        
        for (int pos = 0; pos < l.size(); pos++) {

            int predPos = 0;
            if (i > 0) {
                Layer& lastLayer = _layers->at(i-1);
                while (predPos+1 < lastLayer.size() && lastLayer.getSuccessorPos(predPos+1) <= pos) 
                    predPos++;
            } 
            //printf("%i -> %i\n", predPos, pos);

            int itemsThisPos = 0;

            for (auto pair : l[pos].getReductions()) {
                Signature rSig = pair.first;
                if (!isEncoded(i, pos, rSig) || rSig == Position::NONE_SIG) continue;

                if (value(i, pos, rSig)) {
                    itemsThisPos++;

                    int v = _layers->at(i)[pos].getVariable(rSig);
                    Reduction& r = _htn._reductions_by_sig[rSig];

                    // Check preconditions
                    for (Signature pre : r.getPreconditions()) {
                        assert(value(i, pos, pre) || fail("Precondition " + Names::to_string(pre) + " of reduction "
                        + Names::to_string(r) + " does not hold at step " + std::to_string(pos) + "!\n"));
                    }

                    rSig = getDecodedQOp(i, pos, rSig);
                    Reduction rDecoded = r.substituteRed(Substitution::get(r.getArguments(), rSig._args));
                    itemsNewLayer[pos] = PlanItem({v, rDecoded.getTaskSignature(), rSig, std::vector<int>()});

                    // TODO check this is a valid subtask relationship
                    itemsOldLayer[predPos].subtaskIds.push_back(v);
                }
            }

            for (auto pair : l[pos].getActions()) {
                Signature aSig = pair.first;
                if (!isEncoded(i, pos, aSig)) continue;

                if (value(i, pos, aSig)) {
                    itemsThisPos++;

                    if (aSig == _htn._action_blank.getSignature()) continue;
                    
                    int v = _layers->at(i)[pos].getVariable(aSig);
                    Action a = _htn._actions_by_sig[aSig];

                    // Check preconditions, effects
                    for (Signature pre : a.getPreconditions()) {
                        assert(value(i, pos, pre) || fail("Precondition " + Names::to_string(pre) + " of action "
                        + Names::to_string(aSig) + " does not hold at step " + std::to_string(pos) + "!\n"));
                    }
                    for (Signature eff : a.getEffects()) {
                        assert(value(i, pos+1, eff) || fail("Effect " + Names::to_string(eff) + " of action "
                        + Names::to_string(aSig) + " does not hold at step " + std::to_string(pos+1) + "!\n"));
                    }

                    // TODO check this is a valid subtask relationship

                    // Find the actual action variable at the final layer, not at this (inner) layer
                    int l = i;
                    int aPos = pos;
                    while (l+1 < _layers->size()) {
                        //printf("(%i,%i) => ", l, aPos);
                        aPos = _layers->at(l).getSuccessorPos(aPos);
                        l++;
                        //printf("(%i,%i)\n", l, aPos);
                    }
                    v = classicalPlan[aPos].id; // _layers->at(l-1)[aPos].getVariable(aSig);

                    //itemsNewLayer[pos] = PlanItem({v, aSig, aSig, std::vector<int>()});
                    itemsOldLayer[predPos].subtaskIds.push_back(v);
                }
            }

            assert( ((itemsThisPos == 1) ^ (pos+1 == l.size()))
            || fail(std::to_string(itemsThisPos) 
                + " items at (" + std::to_string(i) + "," + std::to_string(pos) + ") !\n"));
        }

        plan.insert(plan.end(), itemsOldLayer.begin(), itemsOldLayer.end());

        itemsOldLayer = itemsNewLayer;
        itemsNewLayer.clear();
    }

    plan.insert(plan.end(), itemsOldLayer.begin(), itemsOldLayer.end());
    return plan;
}

bool Encoding::value(int layer, int pos, const Signature& sig) {
    int v = _layers->at(layer)[pos].getVariable(sig);
    int vAbs = std::abs(v);
    return (v < 0) ^ (ipasir_val(_solver, vAbs) > 0);
}

void Encoding::printSatisfyingAssignment() {
    printf("SOLUTION_VALS ");
    for (int v = 1; v <= VariableDomain::getMaxVar(); v++) {
        printf("%i ", ipasir_val(_solver, v));
    }
    printf("\n");
}

Signature Encoding::getDecodedQOp(int layer, int pos, Signature sig) {
    assert(isEncoded(layer, pos, sig));
    assert(value(layer, pos, sig));

    Signature origSig = sig;
    while (true) {
        bool containsQConstants = false;
        for (int arg : sig._args) if (_q_constants.count(arg)) {
            // q constant found
            containsQConstants = true;

            int numSubstitutions = 0;
            for (int argSubst : _htn._domains_of_q_constants[arg]) {
                Signature sigSubst = sigSubstitute(arg, argSubst);
                if (isEncodedSubstitution(sigSubst) && ipasir_val(_solver, varSubstitution(sigSubst)) > 0) {
                    //printf("%i TRUE\n", varSubstitution(sigSubst));
                    printf("%s/%s => %s ~~> ", Names::to_string(arg).c_str(), 
                            Names::to_string(argSubst).c_str(), Names::to_string(sig).c_str());
                    numSubstitutions++;
                    substitution_t sub;
                    sub[arg] = argSubst;
                    sig = sig.substitute(sub);
                    printf("%s\n", Names::to_string(sig).c_str());
                } else {
                    //printf("%i FALSE\n", varSubstitution(sigSubst));
                }
            }

            assert(numSubstitutions == 1);
        }

        if (!containsQConstants) break; // done
    }

    if (origSig != sig)
        printf("%s ~~> %s\n", Names::to_string(origSig).c_str(), Names::to_string(sig).c_str());
    return sig;
}

Encoding::~Encoding() {
    for (int asmpt : _last_assumptions) {
        _out << asmpt << " 0\n";
    }
    _out.flush();
    _out.close();

    std::ofstream headerfile;
    headerfile.open("header.cnf");
    VariableDomain::unlock();
    headerfile << "p cnf " << VariableDomain::getMaxVar() << " " << (numClauses+_last_assumptions.size()) << "\n";
    headerfile.flush();
    headerfile.close();

    ipasir_release(_solver);
}