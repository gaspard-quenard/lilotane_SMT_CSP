
#include "sat/encoding.h"
#include "util/log.h"

/*
encodePosition ()
*/

bool beganLine = false;

Encoding::Encoding(Parameters& params, HtnInstance& htn, std::vector<Layer>& layers) : 
            _params(params), _htn(htn), _layers(&layers), _print_formula(params.isSet("of")) {
    _solver = ipasir_init();
    _sig_primitive = USignature(_htn.getNameId("__PRIMITIVE___"), std::vector<int>());
    _substitute_name_id = _htn.getNameId("__SUBSTITUTE___");
    _sig_substitution = USignature(_substitute_name_id, std::vector<int>(2));
    if (_print_formula) _out.open("formula.cnf");
    VariableDomain::init(params);
    _num_cls = 0;
    _num_lits = 0;
    _num_asmpts = 0;
}

void Encoding::encode(int layerIdx, int pos) {
    
    Log::v("  Encoding ...\n");
    int priorNumClauses = _num_cls;
    int priorNumLits = _num_lits;

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
    int prevVarPrim = hasLeft ? varPrimitive(layerIdx, pos-1) : 0;
    
    // Encode true facts at this position and decide for each fact
    // whether to encode it or to reuse the previous variable
    encodeFactVariables(newPos, left);

    // Init substitution vars where necessary
    stage("initsubstitutions");
    for (const auto& a : newPos.getActions()) {
        for (int arg : a.first._args) initSubstitutionVars(newPos.encode(a.first), arg, newPos);
    }
    for (const auto& r : newPos.getReductions()) {
        for (int arg : r.first._args) initSubstitutionVars(newPos.encode(r.first), arg, newPos);
    }
    stage("initsubstitutions");

    // Link qfacts to their possible decodings
    stage("qfactsemantics");
    std::vector<int> substitutionVars; substitutionVars.reserve(128);
    for (const auto& entry : newPos.getQFacts()) for (const auto& qfactSig : entry.second) {
        assert(_htn.hasQConstants(qfactSig));
        assert(!_htn.isRigidPredicate(qfactSig._name_id));

        // Already encoded earlier?
        bool qVarReused = newPos.getPriorPosOfVariable(qfactSig) < pos;
        if (qVarReused) continue;
        
        int qfactVar = newPos.getVariable(qfactSig);

        std::vector<int> qargs, qargIndices; 
        for (int aIdx = 0; aIdx < qfactSig._args.size(); aIdx++) if (_htn._q_constants.count(qfactSig._args[aIdx])) {
            qargs.push_back(qfactSig._args[aIdx]);
            qargIndices.push_back(aIdx);
        } 

        // For each possible fact decoding:
        for (const auto& decFactSig : _htn.getQFactDecodings(qfactSig)) {
            if (!newPos.hasFact(decFactSig)) continue;

            // Check if this decoding is valid
            std::vector<int> decArgs; for (int idx : qargIndices) decArgs.push_back(decFactSig._args[idx]);
            if (!_htn._q_db.test(qargs, decArgs)) continue;

            // Already encoded earlier?
            //if (qVarReused && newPos.getPriorPosOfVariable(decFactSig) < pos) continue;
            
            int decFactVar = newPos.getVariable(decFactSig);

            // Encode substitution from qfact to its decoded fact
            /*
            for (int i = 0; i < qfactSig._args.size(); i++) {
                const int& first = qfactSig._args[i];
                const int& second = decFactSig._args[i];
                if (first != second)
                    substitutionVars.insert(varSubstitution(sigSubstitute(first, second)));
            }*/
            for (const auto& pair : Substitution(qfactSig._args, decFactSig._args)) {
                substitutionVars.push_back(varSubstitution(sigSubstitute(pair.first, pair.second)));
            }
            
            // If the substitution is chosen,
            // the q-fact and the corresponding actual fact are equivalent
            for (int sign = -1; sign <= 1; sign += 2) {
                for (const int& varSubst : substitutionVars) {
                    appendClause(-varSubst);
                }
                appendClause(sign*qfactVar, -sign*decFactVar);
                endClause();
            }
            substitutionVars.clear();
        }
    }
    stage("qfactsemantics");

    // Propagate fact assignments from above
    stage("propagatefacts");
    for (const USignature& factSig : newPos.getFacts())
        propagateFact(newPos, above, oldPos, offset, factSig);
    //for (const auto& entry : newPos.getQFacts()) for (const auto& factSig : entry.second)
    //    propagateFact(newPos, above, oldPos, offset, factSig);
    stage("propagatefacts");

    encodeFrameAxioms(newPos, left);

    // Effects of "old" actions to the left
    stage("actioneffects");
    for (const auto& entry : left.getActions()) {
        const USignature& aSig = entry.first;
        if (aSig == Position::NONE_SIG) continue;
        int aVar = left.encode(aSig);

        for (const Signature& eff : _htn._actions_by_sig[aSig].getEffects()) {
            
            // Check that the action is contained in the effect's support
            const auto& supports = eff._negated ? newPos.getNegFactSupports() : newPos.getPosFactSupports();

            assert(supports.count(eff._usig));
            assert(supports.at(eff._usig).count(aSig));

            // If the action is not contained, it is invalid -- forbid and skip
            if (!supports.count(eff._usig) || !supports.at(eff._usig).count(aSig)) {
                addClause(-aVar);
                break;
            }
            
            // Predicate must not be rigid
            assert(!_htn.isRigidPredicate(eff._usig._name_id));

            std::vector<int> unifiersDnf;
            bool unifiedUnconditionally = false;
            if (eff._negated) {
                for (const auto& posEff : _htn._actions_by_sig[aSig].getEffects()) {
                    if (posEff._negated) continue;
                    if (posEff._usig._name_id != eff._usig._name_id) continue;
                    bool fits = true;
                    std::vector<int> s;
                    for (int i = 0; i < eff._usig._args.size(); i++) {
                        const int& effArg = eff._usig._args[i];
                        const int& posEffArg = posEff._usig._args[i];
                        if (effArg != posEffArg) {
                            bool effIsQ = _q_constants.count(effArg);
                            bool posEffIsQ = _q_constants.count(posEffArg);
                            if (effIsQ && posEffIsQ) {
                                s.push_back(varQConstEquality(effArg, posEffArg));
                            } else if (effIsQ) {
                                if (!_htn.getDomainOfQConstant(effArg).count(posEffArg)) fits = false;
                                else s.push_back(varSubstitution(sigSubstitute(effArg, posEffArg)));
                            } else if (posEffIsQ) {
                                if (!_htn.getDomainOfQConstant(posEffArg).count(effArg)) fits = false;
                                else s.push_back(varSubstitution(sigSubstitute(posEffArg, effArg)));
                            } else fits = false;
                        }
                    }
                    if (fits && s.empty()) {
                        // Empty substitution does the job
                        unifiedUnconditionally = true;
                        break;
                    }
                    s.push_back(0);
                    if (fits) unifiersDnf.insert(unifiersDnf.end(), s.begin(), s.end());
                }
            }
            if (unifiedUnconditionally) {
                //addClause(-aVar, -getVariable(newPos, eff._usig));
            } else if (unifiersDnf.empty()) {
                addClause(-aVar, (eff._negated?-1:1)*getVariable(newPos, eff._usig));
            } else {
                auto cnf = getCnf(unifiersDnf);
                for (const auto& clause : cnf) {
                    appendClause(-aVar, -getVariable(newPos, eff._usig));
                    for (int lit : clause) appendClause(lit);
                    endClause();
                }
            }
        }
    }
    stage("actioneffects");

    // New actions
    stage("actionconstraints");
    int numOccurringOps = 0;
    for (const auto& entry : newPos.getActions()) {
        const USignature& aSig = entry.first;
        if (aSig == Position::NONE_SIG) continue;

        numOccurringOps++;
        int aVar = newPos.encode(aSig);
        //printVar(layerIdx, pos, aSig);

        // If the action occurs, the position is primitive
        addClause(-aVar, varPrim);

        // Preconditions
        for (const Signature& pre : _htn._actions_by_sig[aSig].getPreconditions()) {
            assert(!_htn.isRigidPredicate(pre._usig._name_id));
            addClause(-aVar, (pre._negated?-1:1)*newPos.encode(pre._usig));
        }

        // At-most-one action
        for (const auto& otherEntry : newPos.getActions()) {
            const USignature& otherSig = otherEntry.first;
            int otherVar = newPos.encode(otherSig);
            if (aVar < otherVar) {
                addClause(-aVar, -otherVar);
            }
        }
    }
    stage("actionconstraints");

    // reductions
    stage("reductionconstraints");
    for (const auto& entry : newPos.getReductions()) {
        const USignature& rSig = entry.first;
        if (rSig == Position::NONE_SIG) continue;

        numOccurringOps++;
        int rVar = newPos.encode(rSig);

        bool trivialReduction = _htn._reductions_by_sig[rSig].getSubtasks().size() == 0;
        if (trivialReduction) {
            // If a trivial reduction occurs, the position is primitive
            addClause(-rVar, varPrim);

            // TODO At-most-one constraints to other trivial reductions?

            // Add At-most-one constraints to "proper" actions
            for (const auto& otherEntry : newPos.getActions()) {
                int otherVar = newPos.encode(otherEntry.first);
                addClause(-rVar, -otherVar);
            }
        } else {
            // If a non-trivial reduction occurs, the position is non-primitive
            addClause(-rVar, -varPrim);
        }

        // Preconditions
        for (const Signature& pre : _htn._reductions_by_sig[rSig].getPreconditions()) {
            //assert(newPos.hasFact(pre._usig));
            assert(!_htn.isRigidPredicate(pre._usig._name_id));
            addClause(-rVar, (pre._negated?-1:1)*newPos.encode(pre._usig));
        }

        // At-most-one reduction
        if (newPos.getReductions().size() > _params.getIntParam("amor")) continue;
        for (const auto& otherEntry : newPos.getReductions()) {
            const USignature& otherSig = otherEntry.first;
            if (otherSig == Position::NONE_SIG) continue;
            int otherVar = newPos.encode(otherSig);
            if (rVar < otherVar) {
                addClause(-rVar, -otherVar);
            }
        }
    }
    stage("reductionconstraints");
    
    if (numOccurringOps == 0) {
        //addClause(varPrim);
        //assert(pos+1 == newLayer.size() || fail("No operations to encode at (" + std::to_string(layerIdx) + "," + std::to_string(pos) + ")!\n"));
    }

    // Q-constants type constraints
    stage("qtypeconstraints");
    const auto& constraints = newPos.getQConstantsTypeConstraints();
    for (const auto& pair : constraints) {
        const USignature& opSig = pair.first;
        if (isEncoded(layerIdx, pos, opSig)) {
            for (const TypeConstraint& c : pair.second) {
                int qconst = c.qconstant;
                bool positiveConstraint = c.sign;
                assert(_q_constants.count(qconst));

                if (positiveConstraint) {
                    // EITHER of the GOOD constants - one big clause
                    appendClause(-newPos.getVariable(opSig));
                    for (int cnst : c.constants) {
                        appendClause(varSubstitution(sigSubstitute(qconst, cnst)));
                    }
                    endClause();
                } else {
                    // NEITHER of the BAD constants - many 2-clauses
                    for (int cnst : c.constants) {
                        addClause(-newPos.getVariable(opSig), -varSubstitution(sigSubstitute(qconst, cnst)));
                    }
                }
            }
        }
    }
    stage("qtypeconstraints");

    // Forbidden substitutions per operator
    stage("forbiddensubstitutions");
    for (const auto& opPair : newPos.getForbiddenSubstitutions()) {
        const USignature& opSig = opPair.first;
        for (const Substitution& s : opPair.second) {
            appendClause(-newPos.getVariable(opSig));
            for (const auto& entry : s) {
                appendClause(-varSubstitution(sigSubstitute(entry.first, entry.second)));
            }
            endClause();
        }
    }
    for (const auto& sub : _htn._forbidden_substitutions) {
        assert(!sub.empty());
        if (_forbidden_substitutions.count(sub)) continue;
        for (const auto& entry : sub) {
            appendClause(-varSubstitution(sigSubstitute(entry.first, entry.second)));
        }
        endClause();
        _forbidden_substitutions.insert(sub);
    }
    _htn._forbidden_substitutions.clear();
    stage("forbiddensubstitutions");

    // Forbid impossible parent ops
    stage("forbiddenparents");
    for (const auto& pair : newPos.getExpansions()) {
        const USignature& parent = pair.first;
        for (const USignature& child : pair.second) {
            if (child == Position::NONE_SIG) {
                // Forbid parent op that turned out to be impossible
                int oldOpVar = above.getVariable(parent);
                addClause(-oldOpVar);
                break;
            }
        }
    }
    stage("forbiddenparents");

    // expansions
    stage("expansions");
    for (const auto& pair : newPos.getExpansions()) {
        const USignature& parent = pair.first;

        appendClause(-above.getVariable(parent));
        for (const USignature& child : pair.second) {
            if (child == Position::NONE_SIG) continue;
            appendClause(newPos.getVariable(child));
        }
        endClause();
    }
    stage("expansions");

    // choice of axiomatic ops
    stage("axiomaticops");
    const USigSet& axiomaticOps = newPos.getAxiomaticOps();
    if (!axiomaticOps.empty()) {
        for (const USignature& op : axiomaticOps) {
            appendClause(newPos.getVariable(op));
        }
        endClause();
    }
    stage("axiomaticops");

    Log::i("Encoding done. (%i clauses, total of %i literals)\n", (_num_cls-priorNumClauses), (_num_lits-priorNumLits));

    left.clearFactChanges();

    if (layerIdx == 0 || offset != 0) return;
    
    Position* positionToClear = nullptr;
    if (oldPos == 0) {
        // Clear rightmost position of "above above" layer
        if (layerIdx > 1) positionToClear = &_layers->at(layerIdx-2)[_layers->at(layerIdx-2).size()-1];
    } else {
        // Clear previous parent position of "above" layer
        positionToClear = &_layers->at(layerIdx-1)[oldPos-1];
    }
    if (positionToClear != nullptr) {
        Log::v("  Freeing memory of (%i,%i) ...\n", positionToClear->getPos().first, positionToClear->getPos().second);
        positionToClear->clearUnneeded();
    }
    /*
    if (layerIdx > 1 && pos == 0) {
        // delete data from "above above" layer
        // except for necessary structures for decoding a plan
        Layer& layerToClear = _layers->at(layerIdx-2);
        log("  Freeing memory of (%i,{%i..%i}) ...\n", layerIdx-2, 0, layerToClear.size());
        for (int p = 0; p < layerToClear.size(); p++) {
            layerToClear[p].clearUnneeded();
        }
    }*/
}

void Encoding::propagateFact(Position& newPos, Position& above, int oldPos, int offset, const USignature& factSig) {
    
    if (_htn.isRigidPredicate(factSig._name_id)) return;
        
    // Do not propagate fact if a q-fact 
    // TODO include this or not?
    //if (_htn.hasQConstants(factSig)) continue;

    int factVar = newPos.getVariable(factSig);
    if (offset > 0 || !above.hasVariable(factSig)) return;
    int oldFactVar = above.getVariable(factSig);

    // Find out whether the variables already occurred in an earlier propagation
    if (oldPos > 0) {
        int oldPriorPos = oldPos-1;
        int newPriorPos = _layers->at(above.getPos().first).getSuccessorPos(oldPos-1);
        
        bool oldReused = above.getPriorPosOfVariable(factSig) <= oldPriorPos;
        bool reused = newPos.getPriorPosOfVariable(factSig) <= newPriorPos;

        // Do not re-encode the propagation if both variables have already been reused
        //if (reused) log("NEW_REUSED\n");
        //if (oldReused) log("OLD_REUSED\n");
        if (reused && oldReused) {
            //log("AVOID_REENCODE\n");
            return;
        } 
    }

    // Fact comes from above: propagate meaning
    addClause(-oldFactVar, factVar);
    addClause(oldFactVar, -factVar);
}

void Encoding::addAssumptions(int layerIdx) {
    Layer& l = _layers->at(layerIdx);
    for (int pos = 0; pos < l.size(); pos++) {
        assume(varPrimitive(layerIdx, pos));
    }
}

void Encoding::encodeFactVariables(Position& newPos, const Position& left) {

    // Facts that must hold at this position
    stage("truefacts");
    for (const USignature& factSig : newPos.getTrueFacts()) {
        if (_htn.isRigidPredicate(factSig._name_id)) continue;
        int factVar = newPos.encode(factSig);
        addClause(factVar);
    }
    for (const USignature& factSig : newPos.getFalseFacts()) {
        if (_htn.isRigidPredicate(factSig._name_id)) continue;
        int factVar = -newPos.encode(factSig);
        addClause(factVar);
    }
    stage("truefacts");

    stage("factvarreusage");
    // Re-use all other fact variables where possible
    int leftPos = left.getPos().second;
    int thisPos = newPos.getPos().second;
    LayerState& state = _layers->back().getState();

    // a) first check normal facts
    FlatHashSet<int> unchangedFactVars;
    int reusedFacts = 0;
    for (const USignature& factSig : newPos.getFacts()) {
        
        // Fact must be contained to the left
        bool reuse = left.getFacts().count(factSig);

        // Fact must not have any support to change
        if (reuse) reuse = !newPos.getPosFactSupports().count(factSig)
                        && !newPos.getNegFactSupports().count(factSig);

        // None of its linked q-facts must have a support
        //log("     %i abstractions\n", _htn.getQFactDecodings(factSig).size());
        for (const USignature& qSig : newPos.getQFacts(factSig._name_id)) {
            if (!_htn.isAbstraction(factSig, qSig)) continue;  
            reuse &= !newPos.getPosFactSupports().count(qSig)
                    && !newPos.getNegFactSupports().count(qSig);
            if (!reuse) break;
        }
        
        if (reuse) {
            int var = left.getVariable(factSig);
            newPos.setVariable(factSig, var, left.getPriorPosOfVariable(factSig));
            //log("REUSE %s (%i,%i) ~> (%i,%i)\n", TOSTR(factSig), layerIdx, pos-1, layerIdx, pos);
            reusedFacts++;

            //if (state.contains(leftPos, factSig, true) == state.contains(thisPos, factSig, true) 
            //    && state.contains(leftPos, factSig, false) == state.contains(thisPos, factSig, false)) {
                unchangedFactVars.insert(var);
            //}
        } else {
            newPos.encode(factSig);
        }
    }

    // b) now check q-facts
    int reusedQFacts = 0;
    int totalQFacts = 0;
    for (const auto& entry : newPos.getQFacts()) for (const USignature& factSig : entry.second) {
        totalQFacts++;

        // Fact must be contained to the left
        bool reuse = left.getQFacts().count(factSig._name_id) && left.getQFacts().at(factSig._name_id).count(factSig);

        // Fact must not have any support to change
        if (reuse) reuse = !newPos.getPosFactSupports().count(factSig)
                        && !newPos.getNegFactSupports().count(factSig);
        
        std::vector<int> qargs, qargIndices; 
        for (int aIdx = 0; aIdx < factSig._args.size(); aIdx++) if (_htn._q_constants.count(factSig._args[aIdx])) {
            qargs.push_back(factSig._args[aIdx]);
            qargIndices.push_back(aIdx);
        } 

        // None of the (valid) decoded facts may have changed
        //log("     %i decodings\n", _htn.getQFactDecodings(factSig).size());
        if (reuse) for (const USignature& decSig : _htn.getQFactDecodings(factSig)) {
            if (!newPos.getFacts().count(decSig)) continue;
            
            // Check if this decoding is valid
            std::vector<int> decArgs; for (int idx : qargIndices) decArgs.push_back(decSig._args[idx]);
            if (!_htn._q_db.test(qargs, decArgs)) continue;

            // Decoded fact must be completely unchanged
            reuse &= unchangedFactVars.count(newPos.getVariable(decSig));
            if (!reuse) break;
            
            /*
            LayerState& state = _layers->back().getState();
            reuse &= state.contains(leftPos, factSig, true) == state.contains(thisPos, factSig, true);
            reuse &= state.contains(leftPos, factSig, false) == state.contains(thisPos, factSig, false);
            */
        }

        if (reuse) {
            newPos.setVariable(factSig, left.getVariable(factSig), left.getPriorPosOfVariable(factSig));
            //log("  REUSE %s\n", TOSTR(factSig));
            reusedQFacts++;
        } else {
            //log("  NO_REUSE %s\n", TOSTR(factSig));
            newPos.encode(factSig);
        }
    }
    stage("factvarreusage");
    Log::d("%.2f%% (%.2f%%) of fact (qfact) variables reused from previous position\n", 
                ((float)100*reusedFacts/newPos.getFacts().size()), 
                totalQFacts == 0 ? 100 : ((float)100*reusedQFacts/totalQFacts));
}

void Encoding::encodeFrameAxioms(Position& newPos, const Position& left) {

    // Fact supports, frame axioms (only for non-new facts free of q-constants)
    stage("frameaxioms");

    int layerIdx = newPos.getPos().first;
    int pos = newPos.getPos().second;
    int prevVarPrim = pos>0 ? varPrimitive(layerIdx, pos-1) : 0;

    std::vector<int> dnfSubs; dnfSubs.reserve(8192);
    if (pos > 0)
    for (const USignature& fact : newPos.getFacts()) {
        if (_htn.isRigidPredicate(fact._name_id)) continue;

        bool firstOccurrence = !left.hasFact(fact);
        if (firstOccurrence) {
            // First time the fact occurs must be as a "false fact"
            assert(newPos.getFalseFacts().count(fact));
            continue;
        }

        // Do not re-encode frame axioms if the fact has a reused variable
        if (newPos.getPriorPosOfVariable(fact) < pos) continue;

        for (int sign = -1; sign <= 1; sign += 2) {
            //Signature factSig(fact, sign < 0);
            int oldFactVar = sign*left.getVariable(fact);
            int factVar = sign*newPos.getVariable(fact);
            const auto& supports = sign > 0 ? newPos.getPosFactSupports() : newPos.getNegFactSupports();

            // Calculate indirect support through qfact abstractions
            FlatHashSet<int> indirectSupport;
            for (const USignature& qsig : newPos.getQFacts(fact._name_id)) {
                if (!_htn.isAbstraction(fact, qsig)) continue;
                //const Signature qfactSig(sig, sign < 0);

                // For each operation that supports some qfact abstraction of the fact:
                if (supports.count(qsig))
                for (const USignature& opSig : supports.at(qsig)) {
                    int opVar = left.getVariable(opSig);
                    assert(opVar > 0);
                    
                    // Calculate and encode prerequisites for indirect support

                    // Find valid sets of substitutions for this operation causing the desired effect
                    auto subs = _htn._instantiator->getOperationSubstitutionsCausingEffect(
                        left.getFactChanges(opSig), fact, sign<0);
                    //assert(subMap.count(opSig));
                    if (subs.empty()) {
                        // No valid instantiations!
                        continue;
                    }

                    // Assemble possible substitution options to get the desired fact support
                    std::set<std::set<int>> substOptions;
                    bool unconditionalEffect = false;
                    for (const Substitution& s : subs) {
                        if (s.empty()) {
                            // Empty substitution does the job
                            unconditionalEffect = true;
                            break;
                        }
                        // An actual substitution is necessary
                        std::set<int> substOpt;
                        for (const auto& entry : s) {
                            int substVar = varSubstitution(sigSubstitute(entry.first, entry.second));
                            substOpt.insert(substVar);
                        }
                        substOptions.insert(substOpt);
                    }

                    if (!unconditionalEffect) {
                        // Bring the found substitution sets to CNF and encode them
                        for (const auto& set : substOptions) {
                            dnfSubs.insert(dnfSubs.end(), set.begin(), set.end());
                            dnfSubs.push_back(0);
                        }
                        std::set<std::set<int>> cnfSubs = getCnf(dnfSubs);
                        dnfSubs.clear();
                        for (const std::set<int>& subsCls : cnfSubs) {
                            // IF fact change AND the operation is applied,
                            if (oldFactVar != 0) appendClause(oldFactVar);
                            #ifndef NONPRIMITIVE_SUPPORT
                            appendClause(-prevVarPrim);
                            #endif
                            appendClause(-factVar, -opVar);
                            //log("FRAME AXIOMS %i %i %i ", oldFactVar, -factVar, -opVar);
                            // THEN either of the valid substitution combinations
                            for (int subVar : subsCls) {
                                appendClause(subVar);
                                //log("%i ", subVar);  
                            } 
                            endClause();
                            //log("\n");
                        }
                    }

                    // Add operation to indirect support
                    indirectSupport.insert(opVar); 
                }
            }

            // Fact change:
            //log("FRAME AXIOMS %i %i ", oldFactVar, -factVar);
            if (oldFactVar != 0) appendClause(oldFactVar);
            appendClause(-factVar);
            #ifndef NONPRIMITIVE_SUPPORT
            // Non-primitiveness wildcard
            appendClause(-prevVarPrim);
            #endif
            // DIRECT support
            if (supports.count(fact)) {
                for (const USignature& opSig : supports.at(fact)) {
                    int opVar = left.getVariable(opSig);
                    assert(opVar > 0);
                    appendClause(opVar);
                    //log("%i ", opVar);
                }
            }
            // INDIRECT support
            for (int opVar : indirectSupport) {
                appendClause(opVar);
                //log("%i ", opVar);
            }
            endClause();
            //log("\n");
        }
    }
    stage("frameaxioms");
}

void Encoding::initSubstitutionVars(int opVar, int arg, Position& pos) {

    if (_q_constants.count(arg)) return;
    if (!_htn._q_constants.count(arg)) return;
    // arg is a *new* q-constant: initialize substitution logic

    _q_constants.insert(arg);

    std::vector<int> substitutionVars;
    for (int c : _htn.getDomainOfQConstant(arg)) {

        assert(!_htn._var_ids.count(c));

        // either of the possible substitutions must be chosen
        int varSubst = varSubstitution(sigSubstitute(arg, c));
        substitutionVars.push_back(varSubst);
    }
    assert(!substitutionVars.empty());

    // AT LEAST ONE substitution, or the parent op does NOT occur
    Log::d("INITSUBVARS @(%i,%i) op=%i qc=%s\n", pos.getPos().first, pos.getPos().second, opVar, TOSTR(arg));
    appendClause(-opVar);
    for (int vSub : substitutionVars) appendClause(vSub);
    endClause();

    // AT MOST ONE substitution
    for (int vSub1 : substitutionVars) {
        for (int vSub2 : substitutionVars) {
            if (vSub1 < vSub2) addClause(-vSub1, -vSub2);
        }
    } 
}

std::set<std::set<int>> Encoding::getCnf(const std::vector<int>& dnf) {
    std::set<std::set<int>> cnf;

    if (dnf.empty()) return cnf;

    int size = 1;
    int clsSize = 0;
    std::vector<int> clsStarts;
    for (int i = 0; i < dnf.size(); i++) {
        if (dnf[i] == 0) {
            size *= clsSize;
            clsSize = 0;
        } else {
            if (clsSize == 0) clsStarts.push_back(i);
            clsSize++;
        }
    }
    assert(size > 0);

    // Iterate over all possible combinations
    std::vector<int> counter(clsStarts.size(), 0);
    while (true) {
        // Assemble the combination
        std::set<int> newCls;
        for (int pos = 0; pos < counter.size(); pos++) {
            const int& lit = dnf[clsStarts[pos]+counter[pos]];
            assert(lit != 0);
            newCls.insert(lit);
        }
        cnf.insert(newCls);            

        // Increment exponential counter
        int x = 0;
        while (x < counter.size()) {
            if (dnf[clsStarts[x]+counter[x]+1] == 0) {
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

    if (cnf.size() > 1000) Log::w("CNF of size %i generated\n", cnf.size());

    return cnf;
}

void Encoding::addClause(int lit) {
    ipasir_add(_solver, lit); ipasir_add(_solver, 0);
    if (_print_formula) _out << lit << " 0\n";
    _num_lits++; _num_cls++;
}
void Encoding::addClause(int lit1, int lit2) {
    ipasir_add(_solver, lit1); ipasir_add(_solver, lit2); ipasir_add(_solver, 0);
    if (_print_formula) _out << lit1 << " " << lit2 << " 0\n";
    _num_lits += 2; _num_cls++;
}
void Encoding::addClause(int lit1, int lit2, int lit3) {
    ipasir_add(_solver, lit1); ipasir_add(_solver, lit2); ipasir_add(_solver, lit3); ipasir_add(_solver, 0);
    if (_print_formula) _out << lit1 << " " << lit2 << " " << lit3 << " 0\n";
    _num_lits += 3; _num_cls++;
}
void Encoding::addClause(const std::initializer_list<int>& lits) {
    //log("CNF ");
    for (int lit : lits) {
        ipasir_add(_solver, lit);
        if (_print_formula) _out << lit << " ";
        //log("%i ", lit);
    } 
    ipasir_add(_solver, 0);
    if (_print_formula) _out << "0\n";
    //log("0\n");

    _num_cls++;
    _num_lits += lits.size();
}
void Encoding::appendClause(int lit) {
    if (!beganLine) beganLine = true;
    ipasir_add(_solver, lit);
    if (_print_formula) _out << lit << " ";
    _num_lits++;
}
void Encoding::appendClause(int lit1, int lit2) {
    if (!beganLine) beganLine = true;
    ipasir_add(_solver, lit1); ipasir_add(_solver, lit2);
    if (_print_formula) _out << lit1 << " " << lit2 << " ";
    _num_lits += 2;
}
void Encoding::appendClause(const std::initializer_list<int>& lits) {
    if (!beganLine) {
        //log("CNF ");
        beganLine = true;
    }
    for (int lit : lits) {
        ipasir_add(_solver, lit);
        if (_print_formula) _out << lit << " ";
        //log("%i ", lit);
    } 

    _num_lits += lits.size();
}
void Encoding::endClause() {
    assert(beganLine);
    ipasir_add(_solver, 0);
    if (_print_formula) _out << "0\n";
    //log("0\n");
    beganLine = false;

    _num_cls++;
}
void Encoding::assume(int lit) {
    if (_num_asmpts == 0) _last_assumptions.clear();
    ipasir_assume(_solver, lit);
    //log("CNF !%i\n", lit);
    _last_assumptions.push_back(lit);
    _num_asmpts++;
}

bool Encoding::solve() {
    Log::i("Attempting to solve formula with %i clauses (%i literals) and %i assumptions\n", 
                _num_cls, _num_lits, _num_asmpts);
    bool solved = ipasir_solve(_solver) == 10;
    if (_num_asmpts == 0) _last_assumptions.clear();
    _num_asmpts = 0;
    return solved;
}

bool Encoding::isEncoded(int layer, int pos, const USignature& sig) {
    return _layers->at(layer)[pos].hasVariable(sig);
}

bool Encoding::isEncodedSubstitution(const USignature& sig) {
    return _substitution_variables.count(sig);
}

int Encoding::varSubstitution(const USignature& sigSubst) {

    if (!_substitution_variables.count(sigSubst)) {
        assert(!VariableDomain::isLocked() || Log::e("Unknown substitution variable %s queried!\n", TOSTR(sigSubst)));
        int var = VariableDomain::nextVar();
        _substitution_variables[sigSubst] = var;
        VariableDomain::printVar(var, -1, -1, sigSubst);
        return var;
    } 
    return _substitution_variables[sigSubst];
}

int Encoding::varQConstEquality(int q1, int q2) {
    std::pair<int, int> qPair(std::min(q1, q2), std::max(q1, q2));
    if (!_q_equality_variables.count(qPair)) {
        
        stage("qconstequality");
        FlatHashSet<int> good, bad1, bad2;
        for (int c : _htn.getDomainOfQConstant(q1)) {
            if (!_htn.getDomainOfQConstant(q2).count(c)) bad1.insert(c);
            else good.insert(c);
        }
        for (int c : _htn.getDomainOfQConstant(q2)) {
            if (_htn.getDomainOfQConstant(q1).count(c)) continue;
            bad2.insert(c);
        }
        int varEq = VariableDomain::nextVar();
        if (good.empty()) {
            // Domains are incompatible -- equality never holds
            addClause(-varEq);
        } else {
            // If equality, then all "good" substitution vars are equivalent
            for (int c : good) {
                addClause(-varEq, varSubstitution(sigSubstitute(q1, c)), -varSubstitution(sigSubstitute(q2, c)));
                addClause(-varEq, -varSubstitution(sigSubstitute(q1, c)), varSubstitution(sigSubstitute(q2, c)));
            }
            // Any of the GOOD ones
            for (int c : good) addClause(-varSubstitution(sigSubstitute(q1, c)), -varSubstitution(sigSubstitute(q2, c)), varEq);
            // None of the BAD ones
            for (int c : bad1) addClause(-varSubstitution(sigSubstitute(q1, c)), -varEq);
            for (int c : bad2) addClause(-varSubstitution(sigSubstitute(q2, c)), -varEq);
        }
        stage("qconstequality");

        _q_equality_variables[qPair] = varEq;
    }
    return _q_equality_variables[qPair];
}

std::string Encoding::varName(int layer, int pos, const USignature& sig) {
    return VariableDomain::varName(layer, pos, sig);
}

void Encoding::printVar(int layer, int pos, const USignature& sig) {
    Log::d("%s\n", VariableDomain::varName(layer, pos, sig).c_str());
}

int Encoding::varPrimitive(int layer, int pos) {
    return _layers->at(layer)[pos].encode(_sig_primitive);
}

void Encoding::printFailedVars(Layer& layer) {
    Log::d("FAILED ");
    for (int pos = 0; pos < layer.size(); pos++) {
        int v = varPrimitive(layer.index(), pos);
        if (ipasir_failed(_solver, v)) Log::d("%i ", v);
    }
    Log::d("\n");
}

std::vector<PlanItem> Encoding::extractClassicalPlan() {

    Layer& finalLayer = _layers->back();
    int li = finalLayer.index();
    VariableDomain::lock();

    /*
    State state = finalLayer[0].getState();
    for (const auto& pair : state) {
        for (const Signature& fact : pair.second) {
            if (_htn.isRigidPredicate(fact._name_id)) assert(!isEncoded(0, 0, fact));
            else if (!fact._negated) assert((isEncoded(0, 0, fact) && value(0, 0, fact)) || fail(Names::to_string(fact) + " does not hold initially!\n"));
            else if (fact._negated) assert(!isEncoded(0, 0, fact) || value(0, 0, fact) || fail(Names::to_string(fact) + " does not hold initially!\n"));
        } 
    }*/

    std::vector<PlanItem> plan;
    //log("(actions at layer %i)\n", li);
    for (int pos = 0; pos < finalLayer.size(); pos++) {
        //log("%i\n", pos);
        assert(value(li, pos, _sig_primitive) || Log::e("Plan error: Position %i is not primitive!\n", pos));

        int chosenActions = 0;
        //State newState = state;
        SigSet effects;
        for (const auto& entry : finalLayer[pos].getActions()) {
            const USignature& aSig = entry.first;

            if (!isEncoded(li, pos, aSig)) continue;
            //log("  %s ?\n", TOSTR(aSig));

            if (value(li, pos, aSig)) {
                chosenActions++;
                int aVar = finalLayer[pos].getVariable(aSig);

                // Check fact consistency
                //checkAndApply(_htn._actions_by_sig[aSig], state, newState, li, pos);

                //if (aSig == _htn._action_blank.getSignature()) continue;

                // Decode q constants
                Action& a = _htn._actions_by_sig[aSig];
                USignature aDec = getDecodedQOp(li, pos, aSig);
                if (aDec == Position::NONE_SIG) continue;

                if (aDec != aSig) {

                    HtnOp opDecoded = a.substitute(Substitution(a.getArguments(), aDec._args));
                    Action aDecoded = (Action) opDecoded;

                    // Check fact consistency w.r.t. "actual" decoded action
                    //checkAndApply(aDecoded, state, newState, li, pos);
                }

                //log("* %s @ %i\n", TOSTR(aDec), pos);
                plan.push_back({aVar, aDec, aDec, std::vector<int>()});
            }
        }

        //for (Signature sig : newState) {
        //    assert(value(li, pos+1, sig));
        //}
        //state = newState;

        assert(chosenActions <= 1 || Log::e("Plan error: Added %i actions at step %i!\n", chosenActions, pos));
        if (chosenActions == 0) {
            plan.emplace_back(-1, USignature(), USignature(), std::vector<int>());
        }
    }

    //log("%i actions at final layer of size %i\n", plan.size(), _layers->back().size());
    return plan;
}

bool holds(State& state, const Signature& fact) {

    // Positive fact
    if (!fact._negated) return state[fact._usig._name_id].count(fact);
    
    // Negative fact: fact is contained, OR counterpart is NOT contained
    return state[fact._usig._name_id].count(fact) || !state[fact._usig._name_id].count(fact.opposite());
}

void Encoding::checkAndApply(const Action& a, State& state, State& newState, int layer, int pos) {
    //log("%s\n", TOSTR(a));
    for (const Signature& pre : a.getPreconditions()) {

        // Check assignment
        if (!_htn.isRigidPredicate(pre._usig._name_id))
            assert((isEncoded(layer, pos, pre._usig) && value(layer, pos, pre._usig) == !pre._negated) 
            || Log::e("Plan error: Precondition %s of action %s does not hold in assignment at step %i!\n", TOSTR(pre), TOSTR(a), pos));

        // Check state
        assert(_htn.hasQConstants(pre._usig) || holds(state, pre) 
            || Log::e("Plan error: Precondition %s of action %s does not hold in inferred state at step %i!\n", TOSTR(pre), TOSTR(a), pos));
        
        //log("Pre %s of action %s holds @(%i,%i)\n", TOSTR(pre), TOSTR(a.getSignature()), 
        //        layer, pos);
    }

    for (const Signature& eff : a.getEffects()) {
        assert((isEncoded(layer, pos+1, eff._usig) && value(layer, pos+1, eff._usig) == !eff._negated) 
            || Log::e("Plan error: Effect %s of action %s does not hold in assignment at step %i!\n", TOSTR(eff), TOSTR(a), pos+1));

        // Apply effect
        if (holds(state, eff.opposite())) newState[eff._usig._name_id].erase(eff.opposite());
        newState[eff._usig._name_id];
        newState[eff._usig._name_id].insert(eff);

        //log("Eff %s of action %s holds @(%i,%i)\n", TOSTR(eff), TOSTR(a.getSignature()), 
        //        layer, pos);
    }
}

std::pair<std::vector<PlanItem>, std::vector<PlanItem>> Encoding::extractPlan() {

    auto result = std::pair<std::vector<PlanItem>, std::vector<PlanItem>>();
    std::vector<PlanItem>& classicalPlan = result.first;
    std::vector<PlanItem>& plan = result.second;

    result.first = extractClassicalPlan();
    
    std::vector<PlanItem> itemsOldLayer, itemsNewLayer;

    for (int layerIdx = 0; layerIdx < _layers->size(); layerIdx++) {
        Layer& l = _layers->at(layerIdx);
        //log("(decomps at layer %i)\n", l.index());

        itemsNewLayer.resize(l.size());
        
        for (int pos = 0; pos < l.size(); pos++) {

            int predPos = 0;
            if (layerIdx > 0) {
                Layer& lastLayer = _layers->at(layerIdx-1);
                while (predPos+1 < lastLayer.size() && lastLayer.getSuccessorPos(predPos+1) <= pos) 
                    predPos++;
            } 
            //log("%i -> %i\n", predPos, pos);

            int actionsThisPos = 0;
            int reductionsThisPos = 0;

            for (const auto& entry : l[pos].getReductions()) {
                const USignature& rSig = entry.first;
                if (!isEncoded(layerIdx, pos, rSig) || rSig == Position::NONE_SIG) continue;

                //log("? %s @ (%i,%i)\n", TOSTR(rSig), i, pos);

                if (value(layerIdx, pos, rSig)) {

                    int v = _layers->at(layerIdx)[pos].getVariable(rSig);
                    const Reduction& r = _htn._reductions_by_sig[rSig];

                    // Check preconditions
                    /*
                    for (const Signature& pre : r.getPreconditions()) {
                        assert(value(layerIdx, pos, pre) || fail("Precondition " + Names::to_string(pre) + " of reduction "
                        + Names::to_string(r.getSignature()) + " does not hold at step " + std::to_string(pos) + "!\n"));
                    }*/

                    //log("%s:%s @ (%i,%i)\n", TOSTR(r.getTaskSignature()), TOSTR(rSig), layerIdx, pos);
                    USignature decRSig = getDecodedQOp(layerIdx, pos, rSig);
                    if (decRSig == Position::NONE_SIG) continue;

                    Reduction rDecoded = r.substituteRed(Substitution(r.getArguments(), decRSig._args));
                    Log::d("[%i] %s:%s @ (%i,%i)\n", v, TOSTR(rDecoded.getTaskSignature()), TOSTR(decRSig), layerIdx, pos);

                    if (layerIdx == 0) {
                        // Initial reduction
                        PlanItem root(0, 
                            USignature(_htn.getNameId("root"), std::vector<int>()), 
                            decRSig, std::vector<int>());
                        itemsNewLayer[0] = root;
                        reductionsThisPos++;
                        continue;
                    }

                    // Lookup parent reduction
                    Reduction parentRed;
                    int offset = pos - _layers->at(layerIdx-1).getSuccessorPos(predPos);
                    PlanItem& parent = itemsOldLayer[predPos];
                    assert(parent.id >= 0 || Log::e("Plan error: No parent at %i,%i!\n", layerIdx-1, predPos));
                    assert(_htn._reductions.count(parent.reduction._name_id) || 
                        Log::e("Plan error: Invalid reduction id=%i at %i,%i!\n", parent.reduction._name_id, layerIdx-1, predPos));

                    parentRed = _htn._reductions[parent.reduction._name_id];
                    parentRed = parentRed.substituteRed(Substitution(parentRed.getArguments(), parent.reduction._args));

                    // Is the current reduction a proper subtask?
                    assert(offset < parentRed.getSubtasks().size());
                    if (parentRed.getSubtasks()[offset] == rDecoded.getTaskSignature()) {
                        if (itemsOldLayer[predPos].subtaskIds.size() > offset) {
                            // This subtask has already been written!
                            Log::d(" -- is a redundant child -> dismiss\n");
                            continue;
                        }
                        itemsNewLayer[pos] = PlanItem(v, rDecoded.getTaskSignature(), decRSig, std::vector<int>());
                        itemsOldLayer[predPos].subtaskIds.push_back(v);
                        reductionsThisPos++;
                    } else {
                        Log::d(" -- invalid : %s != %s\n", TOSTR(parentRed.getSubtasks()[offset]), TOSTR(rDecoded.getTaskSignature()));
                    } 
                }
            }

            for (const auto& entry : l[pos].getActions()) {
                const USignature& aSig = entry.first;
                if (!isEncoded(layerIdx, pos, aSig)) continue;

                if (value(layerIdx, pos, aSig)) {
                    actionsThisPos++;

                    if (aSig == _htn._action_blank.getSignature()) continue;
                    
                    int v = _layers->at(layerIdx)[pos].getVariable(aSig);
                    Action a = _htn._actions_by_sig[aSig];

                    /*
                    // Check preconditions, effects
                    for (const Signature& pre : a.getPreconditions()) {
                        assert(value(layerIdx, pos, pre) || fail("Precondition " + Names::to_string(pre) + " of action "
                        + Names::to_string(aSig) + " does not hold at step " + std::to_string(pos) + "!\n"));
                    }
                    for (const Signature& eff : a.getEffects()) {
                        assert(value(layerIdx, pos+1, eff) || fail("Effect " + Names::to_string(eff) + " of action "
                        + Names::to_string(aSig) + " does not hold at step " + std::to_string(pos+1) + "!\n"));
                    }*/

                    // TODO check this is a valid subtask relationship

                    Log::d("[%i] %s @ (%i,%i)\n", v, TOSTR(aSig), layerIdx, pos);                    

                    // Find the actual action variable at the final layer, not at this (inner) layer
                    int l = layerIdx;
                    int aPos = pos;
                    while (l+1 < _layers->size()) {
                        //log("(%i,%i) => ", l, aPos);
                        aPos = _layers->at(l).getSuccessorPos(aPos);
                        l++;
                        //log("(%i,%i)\n", l, aPos);
                    }
                    v = classicalPlan[aPos].id; // _layers->at(l-1)[aPos].getVariable(aSig);
                    assert(v > 0);

                    //itemsNewLayer[pos] = PlanItem({v, aSig, aSig, std::vector<int>()});
                    if (layerIdx > 0) itemsOldLayer[predPos].subtaskIds.push_back(v);
                }
            }

            // At least an item per position 
            assert( (actionsThisPos+reductionsThisPos >= 1)
            || Log::e("Plan error: %i ops at (%i,%i)!\n", actionsThisPos+reductionsThisPos, layerIdx, pos));
            
            // At most one action per position
            assert(actionsThisPos <= 1 || Log::e("Plan error: %i actions at (%i,%i)!\n", actionsThisPos, layerIdx, pos));

            // Either actions OR reductions per position (not both)
            assert(actionsThisPos == 0 || reductionsThisPos == 0 
            || Log::e("Plan error: %i actions and %i reductions at (%i,%i)!\n", actionsThisPos, reductionsThisPos, layerIdx, pos));
        }

        plan.insert(plan.end(), itemsOldLayer.begin(), itemsOldLayer.end());

        itemsOldLayer = itemsNewLayer;
        itemsNewLayer.clear();
    }
    plan.insert(plan.end(), itemsOldLayer.begin(), itemsOldLayer.end());

    return result;
}

bool Encoding::value(int layer, int pos, const USignature& sig) {
    int v = _layers->at(layer)[pos].getVariable(sig);
    return (ipasir_val(_solver, v) > 0);
}

void Encoding::printSatisfyingAssignment() {
    Log::d("SOLUTION_VALS ");
    for (int v = 1; v <= VariableDomain::getMaxVar(); v++) {
        Log::d("%i ", ipasir_val(_solver, v));
    }
    Log::d("\n");
}

USignature Encoding::getDecodedQOp(int layer, int pos, const USignature& origSig) {
    assert(isEncoded(layer, pos, origSig));
    assert(value(layer, pos, origSig));

    USignature sig = origSig;
    while (true) {
        bool containsQConstants = false;
        for (int arg : sig._args) if (_htn._q_constants.count(arg)) {
            // q constant found
            containsQConstants = true;

            int numSubstitutions = 0;
            for (int argSubst : _htn.getDomainOfQConstant(arg)) {
                const USignature& sigSubst = sigSubstitute(arg, argSubst);
                if (isEncodedSubstitution(sigSubst) && ipasir_val(_solver, varSubstitution(sigSubst)) > 0) {
                    //log("%i TRUE\n", varSubstitution(sigSubst));
                    //log("%s/%s => %s ~~> ", TOSTR(arg), 
                    //        TOSTR(argSubst), TOSTR(sig));
                    numSubstitutions++;
                    Substitution sub;
                    sub[arg] = argSubst;
                    sig.apply(sub);
                    //log("%s\n", TOSTR(sig));
                } else {
                    //log("%i FALSE\n", varSubstitution(sigSubst));
                }
            }

            int opVar = _layers->at(layer)[pos].getVariable(origSig);
            if (numSubstitutions == 0) {
                return Position::NONE_SIG;
            }
            assert(numSubstitutions == 1 || Log::e("%i substitutions for arg %s of %s (op=%i)\n", numSubstitutions, TOSTR(arg), TOSTR(origSig), opVar));
        }

        if (!containsQConstants) break; // done
    }

    /*
    if (origSig != sig)
        log("%s ~~> %s\n", TOSTR(origSig), TOSTR(sig));
    */
    return sig;
}

void Encoding::stage(std::string name) {
    if (!_num_cls_per_stage.count(name)) {
        _num_cls_per_stage[name] = _num_cls;
        //log("    %s ...\n", name.c_str());
    } else {
        if (!_total_num_cls_per_stage.count(name)) _total_num_cls_per_stage[name] = 0;
        _total_num_cls_per_stage[name] += _num_cls - _num_cls_per_stage[name];
        _num_cls_per_stage.erase(name);
    }
}

void Encoding::printStages() {
    Log::i("Total amount of clauses encoded: %i\n", _num_cls);
    for (const auto& entry : _total_num_cls_per_stage) {
        Log::i(" %s : %i cls\n", entry.first.c_str(), entry.second);
    }
    _total_num_cls_per_stage.clear();
}

Encoding::~Encoding() {

    if (_params.isSet("of")) {

        // Append assumptions to written formula, close stream
        for (int asmpt : _last_assumptions) {
            _out << asmpt << " 0\n";
        }
        _out.flush();
        _out.close();

        // Create final formula file
        std::ofstream ffile;
        ffile.open("f.cnf");
        
        // Append header to formula file
        ffile << "p cnf " << VariableDomain::getMaxVar() << " " << (_num_cls+_last_assumptions.size()) << "\n";

        // Append main content to formula file (reading from "old" file)
        std::ifstream oldfile;
        oldfile.open("formula.cnf");
        std::string line;
        while (std::getline(oldfile, line)) {
            line = line + "\n";
            ffile.write(line.c_str(), line.size());
        }
        oldfile.close();
        remove("formula.cnf");

        // Finish
        ffile.flush();
        ffile.close();
    }

    // Release SAT solver
    ipasir_release(_solver);
}