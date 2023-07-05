
#ifndef DOMPASCH_LILOTANE_DECODER_H
#define DOMPASCH_LILOTANE_DECODER_H

#include "data/htn_instance.h"
#include "data/layer.h"
#include "sat/sat_interface.h"
#include "sat/smt_interface.h"
#include "sat/variable_provider.h"
#include "data/plan.h"

class Decoder {

private:
    HtnInstance& _htn;
    std::vector<Layer*>& _layers;
    SatInterface& _sat;
    SmtInterface& _smt;
    VariableProvider& _vars;
    bool _useSmt;

public:
    Decoder(HtnInstance& htn, std::vector<Layer*>& layers, SatInterface& sat, SmtInterface& smt, VariableProvider& vars, bool useSmt) :
        _htn(htn), _layers(layers), _sat(sat), _smt(smt), _vars(vars), _useSmt(useSmt) {}

    enum PlanExtraction {ALL, PRIMITIVE_ONLY};
    std::vector<PlanItem> extractClassicalPlan(PlanExtraction mode = PRIMITIVE_ONLY) {

        Layer& finalLayer = *_layers.back();
        int li = finalLayer.index();
        //VariableDomain::lock();

        std::vector<PlanItem> plan(finalLayer.size());
        //log("(actions at layer %i)\n", li);
        for (size_t pos = 0; pos < finalLayer.size(); pos++) {
            //log("%i\n", pos);

            // Print out the state
            Log::d("PLANDBG %i,%i S ", li, pos);
            for (const auto& [sig, fVar] : finalLayer[pos].getVariableTable(VarType::FACT)) {
                if (_useSmt &&_smt.holds(fVar)) Log::log_notime(Log::V4_DEBUG, "%s ", TOSTR(sig));
                else if (!_useSmt && _sat.holds(fVar)) Log::log_notime(Log::V4_DEBUG, "%s ", TOSTR(sig));
                
            }
            Log::log_notime(Log::V4_DEBUG, "\n");

            int chosenActions = 0;
            //State newState = state;
            for (const auto& [sig, aVar] : finalLayer[pos].getVariableTable(VarType::OP)) {
                if (_useSmt && !_smt.holds(aVar)) continue;
                else if (!_useSmt && !_sat.holds(aVar)) continue;
                
                USignature aSig = sig;
                if (mode == PRIMITIVE_ONLY && !_htn.isAction(aSig)) continue;

                if (_htn.isActionRepetition(aSig._name_id)) {
                    aSig._name_id = _htn.getActionNameFromRepetition(sig._name_id);
                }

                Log::i("  %s ?\n", TOSTR(aSig));

                chosenActions++;
                
                Log::d("PLANDBG %i,%i A %s\n", li, pos, TOSTR(aSig));

                // Decode q constants
                USignature aDec = getDecodedQOp(li, pos, aSig);
                if (aDec == Sig::NONE_SIG) continue;
                plan[pos] = {aVar, aDec, aDec, std::vector<int>()};
            }

            assert(chosenActions <= 1 || Log::e("Plan error: Added %i actions at step %i!\n", chosenActions, pos));
            if (chosenActions == 0) {
                plan[pos] = {-1, USignature(), USignature(), std::vector<int>()};
            }
        }

        // Log::i("%i actions at final layer of size %i\n", plan.size(), _layers->back().size());
        return plan;
    }


std::vector<PlanItem> extractClassicalPlanLiftedTreePath(PlanExtraction mode = PRIMITIVE_ONLY) {

        Layer& finalLayer = *_layers.back();
        int li = finalLayer.index();
        //VariableDomain::lock();

        std::vector<PlanItem> plan(finalLayer.size());
        //log("(actions at layer %i)\n", li);
        for (size_t pos = 0; pos < finalLayer.size(); pos++) {
            //log("%i\n", pos);

            // Print out the state
            Log::d("PLANDBG %i,%i S ", li, pos);
            for (const auto& [sig, fVar] : finalLayer[pos].getVariableTable(VarType::FACT)) {
                if (_useSmt &&_smt.holds(fVar)) Log::log_notime(Log::V4_DEBUG, "%s ", TOSTR(sig));
                else if (!_useSmt && _sat.holds(fVar)) Log::log_notime(Log::V4_DEBUG, "%s ", TOSTR(sig));
                
            }
            Log::log_notime(Log::V4_DEBUG, "\n");

            int chosenActions = 0;
            bool isMethodPrecond = false;
            //State newState = state;
            for (const auto& [sig, aVar] : finalLayer[pos].getVariableTableOPUniqueID()) {
                if (_useSmt && !_smt.holds(aVar)) continue;
                else if (!_useSmt && !_sat.holds(aVar)) continue;

                // Do debug print the sig
                Log::i("%i -> %s (%i)\n", pos, TOSTR(sig), sig._unique_id);
                
                USignature aSig = sig;

                if (_htn.isActionRepetition(aSig._name_id)) {
                    aSig._name_id = _htn.getActionNameFromRepetition(sig._name_id);
                }

                // Log::i("  %s ?\n", TOSTR(aSig));

                chosenActions++;
                
                Log::d("PLANDBG %i,%i A %s\n", li, pos, TOSTR(aSig));

                isMethodPrecond = false;
                // If this is a method precondition (start with <method_prec>), then do not add it to the plan
                std::string name = TOSTR(aSig);
                // Carefull, must be find that <method_prec> is at the start of the string
                if (name.find("(<method_prec>") == 0) {
                    isMethodPrecond = true;
                }

                // aVar = aSig._unique_id;

                int v = aSig._unique_id;

                assert(v != -1);

                // Decode q constants
                USignature aDec = getDecodedQOp(li, pos, aSig);
                if (aDec == Sig::NONE_SIG) continue;
                plan[pos] = {v, aDec, aDec, std::vector<int>()};

                // Log::i("Sig2: %s\n", TOSTR(aDec));
            }

            assert(chosenActions <= 1 || Log::e("Plan error: Added %i actions at step %i!\n", chosenActions, pos));
            
            if (chosenActions == 0) {//  || isMethodPrecond) {
                plan[pos] = {-1, USignature(), USignature(), std::vector<int>()};
            }
        }

        // Log::i("%i actions at final layer of size %i\n", plan.size(), _layers->back().size());
        return plan;
    }

    Plan extractPlan() {

        auto result = Plan();
        auto& [classicalPlan, plan] = result;
        classicalPlan = extractClassicalPlan();
        
        std::vector<PlanItem> itemsOldLayer, itemsNewLayer;

        for (size_t layerIdx = 0; layerIdx < _layers.size(); layerIdx++) {
            Layer& l = *_layers.at(layerIdx);
            //log("(decomps at layer %i)\n", l.index());

            itemsNewLayer.resize(l.size());
            
            for (size_t pos = 0; pos < l.size(); pos++) {

                size_t predPos = 0;
                if (layerIdx > 0) {
                    Layer& lastLayer = *_layers.at(layerIdx-1);
                    while (predPos+1 < lastLayer.size() && lastLayer.getSuccessorPos(predPos+1) <= pos) 
                        predPos++;
                } 
                //log("%i -> %i\n", predPos, pos);

                int actionsThisPos = 0;
                int reductionsThisPos = 0;

                for (const auto& [opSig, v] : l[pos].getVariableTable(VarType::OP)) {

                    if ((_useSmt && _smt.holds(v)) || (!_useSmt && _sat.holds(v))) {

                        if (_htn.isAction(opSig)) {
                            // Action
                            actionsThisPos++;
                            const USignature& aSig = opSig;

                            if (aSig == _htn.getBlankActionSig()) continue;
                            if (_htn.isActionRepetition(aSig._name_id)) {
                                continue;
                            }
                            
                            int v = _vars.getVariable(VarType::OP, layerIdx, pos, aSig);
                            Action a = _htn.getOpTable().getAction(aSig);

                            // TODO check this is a valid subtask relationship

                            Log::d("[%i] %s @ (%i,%i)\n", v, TOSTR(aSig), layerIdx, pos);                    

                            // Find the actual action variable at the final layer, not at this (inner) layer
                            size_t l = layerIdx;
                            int aPos = pos;
                            while (l+1 < _layers.size()) {
                                //log("(%i,%i) => ", l, aPos);
                                aPos = _layers.at(l)->getSuccessorPos(aPos);
                                l++;
                                //log("(%i,%i)\n", l, aPos);
                            }
                            v = classicalPlan[aPos].id; // *_layers.at(l-1)[aPos]._vars.getVariable(aSig);
                            //assert(v > 0 || Log::e("%s : v=%i\n", TOSTR(aSig), v));
                            if (v > 0 && layerIdx > 0) {
                                itemsOldLayer[predPos].subtaskIds.push_back(v);
                            } else if (v <= 0) {
                                Log::d(" -- invalid: not part of classical plan\n");
                            }

                            //itemsNewLayer[pos] = PlanItem({v, aSig, aSig, std::vector<int>()});

                        } else if (_htn.isReduction(opSig)) {
                            // Reduction
                            const USignature& rSig = opSig;
                            const Reduction& r = _htn.getOpTable().getReduction(rSig);

                            //log("%s:%s @ (%i,%i)\n", TOSTR(r.getTaskSignature()), TOSTR(rSig), layerIdx, pos);
                            USignature decRSig = getDecodedQOp(layerIdx, pos, rSig);
                            if (decRSig == Sig::NONE_SIG) continue;

                            Reduction rDecoded = r.substituteRed(Substitution(r.getArguments(), decRSig._args));
                            Log::d("[%i] %s:%s @ (%i,%i)\n", v, TOSTR(rDecoded.getTaskSignature()), TOSTR(decRSig), layerIdx, pos);

                            if (layerIdx == 0) {
                                // Initial reduction
                                PlanItem root(0, 
                                    USignature(_htn.nameId("root"), std::vector<int>()), 
                                    decRSig, std::vector<int>());
                                itemsNewLayer[0] = root;
                                reductionsThisPos++;
                                continue;
                            }

                            // Lookup parent reduction
                            Reduction parentRed;
                            size_t offset = pos - _layers.at(layerIdx-1)->getSuccessorPos(predPos);
                            PlanItem& parent = itemsOldLayer[predPos];
                            assert(parent.id >= 0 || Log::e("Plan error: No parent at %i,%i!\n", layerIdx-1, predPos));
                            assert(_htn.isReduction(parent.reduction) || 
                                Log::e("Plan error: Invalid reduction id=%i at %i,%i!\n", parent.reduction._name_id, layerIdx-1, predPos));

                            parentRed = _htn.toReduction(parent.reduction._name_id, parent.reduction._args);

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
                }

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



    Plan extractPlanLiftedTreePath() {

        auto result = Plan();
        auto& [classicalPlan, plan] = result;
        classicalPlan = extractClassicalPlanLiftedTreePath();

        // Print the classical plan
        Log::i("Classical plan:\n");
        int idx = 0;
        for (auto& a: classicalPlan) {
            if (a.reduction._name_id != 1 && a.reduction._name_id != -1) { // Do not print blank action and special precondition action
                std::string name = TOSTR(a.reduction);
                // If the name does not contains the substring <method_prec>, then print it
                if (name.find("<method_prec>") == std::string::npos) {
                    Log::i(" (%i)-> %s\n", idx, TOSTR(a.reduction));
                }
            }
            idx++;
        }


        // Make a first pass to set all the reduction/action which is true in each layer position
        // Create a loopup table which indicate the id already seen
        std::set<std::pair<int, int>> seenLayerPositions;

        Layer& lastLayer = *_layers.at(_layers.size()-1);

        // Now, iterate over each action of the classical plan, and get its last method parent id, indicate that it is true, and recurse
        for (int i = 0; i < classicalPlan.size(); i++) {
            auto& aSig = classicalPlan[i].reduction;

            if (aSig._name_id == -1) {
                continue;
            }

            // Get its position objects
            Position& pos = lastLayer[i];

            Log::d("Action: %s\n", TOSTR(aSig));

            // Find the action with the same ID as aSig in this position
            bool found = false;
            for (auto& a: pos.getActionsWithUniqueID()) {
                // Display the action
                if (a._unique_id == aSig._unique_id) {
                    // This is the action
                    Log::i("  === %s\n", TOSTR(a));
                    pos.setActionOrReductionTrue(a);
                    found = true;
                    break;
                }
            }

            if (!found) {
                Log::e("Plan error: Action %s not found in position (%i,%i)!\n", TOSTR(aSig), _layers.size()-1, i);
                assert(false);
            }


            // pos.setActionOrReductionTrue(aSig);

            int currentLayer = _layers.size()-2;
            size_t currentPos = pos.getAbovePositionIndex();

            // Get the id of the predecessor of this action
            USigSetUniqueID preds = pos.getPredecessorsWithUniqueID().at(aSig._unique_id);
            assert(preds.size() == 1);

            while (currentLayer >= 0) {

                // Log::i("  %i,%i\n", currentLayer, currentPos);

                USignature actionOrReductionTrue = *preds.begin();

                // Log::i("  %s\n", TOSTR(actionOrReductionTrue));

                if (seenLayerPositions.find(std::pair(currentLayer, currentPos)) != seenLayerPositions.end()) {
                    // This action or reduction has already been seen
                    break;
                }

                // Get the position object
                Position& pos = (*_layers.at(currentLayer))[currentPos];

                // Verify that this action or reduction is in the current position
                if (_htn.isAction(actionOrReductionTrue)) {
                    // Action
                    assert(pos.getActionsWithUniqueID().contains(actionOrReductionTrue));
                } else if (_htn.isReduction(actionOrReductionTrue)) {
                    // Reduction
                    if (!pos.getReductions().contains(actionOrReductionTrue)) {
                        // Display all the reductions
                        Log::i("  -> reductions: ");
                        for (const auto& r : pos.getReductions()) {
                            Log::i("%s ", TOSTR(r));
                        }
                    }

                    assert(pos.getReductions().contains(actionOrReductionTrue));
                }

                pos.setActionOrReductionTrue(actionOrReductionTrue);

                // Set this id as seen
                // Log::i("  -> set true at (%i,%i)\n", currentLayer, currentPos);
                seenLayerPositions.insert(std::pair(currentLayer, currentPos));

                // Get the above layer
                currentLayer--;

                if (currentLayer < 0) {
                    // We are at the root layer, we are done
                    break;
                }

                // Get the above position
                currentPos = pos.getAbovePositionIndex();
                assert(currentPos != -1);

                // Get the id of the predecessor of this action
                preds = pos.getPredecessorsWithUniqueID().at(actionOrReductionTrue._unique_id);
                assert(preds.size() == 1);
            }
        }

        
        std::vector<PlanItem> itemsOldLayer, itemsNewLayer;

        for (size_t layerIdx = 0; layerIdx < _layers.size(); layerIdx++) {
            Layer& l = *_layers.at(layerIdx);
            //log("(decomps at layer %i)\n", l.index());

            itemsNewLayer.resize(l.size());
            
            for (size_t pos = 0; pos < l.size(); pos++) {

                Log::i("Layer %i, pos %i\n", layerIdx, pos);

                size_t predPos = 0;
                if (layerIdx > 0) {
                    Layer& lastLayer = *_layers.at(layerIdx-1);
                    while (predPos+1 < lastLayer.size() && lastLayer.getSuccessorPos(predPos+1) <= pos) 
                        predPos++;
                } 
                //log("%i -> %i\n", predPos, pos);

                int actionsThisPos = 0;
                int reductionsThisPos = 0;

                // for (const auto& [opSig, v] : l[pos].getVariableTable(VarType::OP)) {
                // Get the action/reduction true for this layer position
                const USignature& actionOrReductionTrue = l[pos].getActionOrReductionTrue(); 

                if (actionOrReductionTrue._name_id == -1) {
                    Log::i("No action or reduction true at this position\n");
                    continue;
                }

                // Display the action or reduction true
                Log::i("  %s\n", TOSTR(actionOrReductionTrue));

                    // if ((_useSmt && _smt.holds(v)) || (!_useSmt && _sat.holds(v))) {

                        if (_htn.isAction(actionOrReductionTrue)) {
                            // Action
                            actionsThisPos++;
                            const USignature& aSig = actionOrReductionTrue;

                            if (aSig == _htn.getBlankActionSig()) continue;
                            if (_htn.isActionRepetition(aSig._name_id)) {
                                continue;
                            }
                            
                            // int v = _vars.getVariable(VarType::OP, layerIdx, pos, aSig);
                            int v = aSig._unique_id;
                            if (!_htn.getOpTable().hasAction(aSig)) {
                                // Strange thing here !! Display all the actions to understand
                                Log::i("  -> actions: \n");
                                for (const auto& [aSig, a] : _htn.getOpTable().getActions()) {
                                    Log::i("%s \n", TOSTR(aSig));
                                }
                            }
                            Action a = _htn.getOpTable().getAction(aSig);

                            // TODO check this is a valid subtask relationship

                            Log::i("[%i] %s @ (%i,%i)\n", v, TOSTR(aSig), layerIdx, pos);                    

                            // Find the actual action variable at the final layer, not at this (inner) layer
                            size_t l = layerIdx;
                            int aPos = pos;
                            while (l+1 < _layers.size()) {
                                //log("(%i,%i) => ", l, aPos);
                                aPos = _layers.at(l)->getSuccessorPos(aPos);
                                l++;
                                //log("(%i,%i)\n", l, aPos);
                            }
                            v = classicalPlan[aPos].id; // *_layers.at(l-1)[aPos]._vars.getVariable(aSig);
                            //assert(v > 0 || Log::e("%s : v=%i\n", TOSTR(aSig), v));
                            if (v > 0 && layerIdx > 0) {
                                itemsOldLayer[predPos].subtaskIds.push_back(v);
                            } else if (v <= 0) {
                                Log::d(" -- invalid: not part of classical plan\n");
                            }

                            //itemsNewLayer[pos] = PlanItem({v, aSig, aSig, std::vector<int>()});

                        } else if (_htn.isReduction(actionOrReductionTrue)) {
                            // Reduction
                            const USignature& rSig = actionOrReductionTrue;
                            const Reduction& r = _htn.getOpTable().getReduction(rSig);

                            int v = rSig._unique_id;

                            Log::i("%s:%s @ (%i,%i)\n", TOSTR(r.getTaskSignature()), TOSTR(rSig), layerIdx, pos);
                            USignature decRSig = getDecodedQOp(layerIdx, pos, rSig);
                            if (decRSig == Sig::NONE_SIG)  {
                                continue;
                            }

                            Reduction rDecoded = r.substituteRed(Substitution(r.getArguments(), decRSig._args));
                            Log::d("[%i] %s:%s @ (%i,%i)\n", v, TOSTR(rDecoded.getTaskSignature()), TOSTR(decRSig), layerIdx, pos);

                            if (layerIdx == 0) {
                                // Initial reduction
                                PlanItem root(0, 
                                    USignature(_htn.nameId("root"), std::vector<int>()), 
                                    decRSig, std::vector<int>());
                                itemsNewLayer[0] = root;
                                reductionsThisPos++;
                                continue;
                            }

                            // Lookup parent reduction
                            Reduction parentRed;
                            size_t offset = pos - _layers.at(layerIdx-1)->getSuccessorPos(predPos);
                            PlanItem& parent = itemsOldLayer[predPos];
                            assert(parent.id >= 0 || Log::e("Plan error: No parent at %i,%i!\n", layerIdx-1, predPos));
                            assert(_htn.isReduction(parent.reduction) || 
                                Log::e("Plan error: Invalid reduction id=%i at %i,%i!\n", parent.reduction._name_id, layerIdx-1, predPos));

                            parentRed = _htn.toReduction(parent.reduction._name_id, parent.reduction._args);

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
                        } else {
                            Log::e("Plan error: Invalid action/reduction id=%i at %i,%i!\n", actionOrReductionTrue._name_id, layerIdx, pos);
                            assert(actionOrReductionTrue._name_id != -1);
                        }
                    // }
                // }

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

    bool value(VarType type, int layer, int pos, const USignature& sig) {
        int v = _vars.getVariable(type, layer, pos, sig);
        if (_useSmt) {
            Log::d("VAL %s@(%i,%i)=%i %i\n", TOSTR(sig), layer, pos, v, _smt.holds(v));
            return _smt.holds(v);
        }
        else {
            Log::d("VAL %s@(%i,%i)=%i %i\n", TOSTR(sig), layer, pos, v, _sat.holds(v));
            return _sat.holds(v);
        }
    }


    USignature getDecodedQOp(int layer, int pos, const USignature& origSig) {
        //assert(isEncoded(VarType::OP, layer, pos, origSig));
        //assert(value(VarType::OP, layer, pos, origSig));

        USignature sig = origSig;
        while (true) {
            bool containsQConstants = false;
            for (int arg : sig._args) if (_htn.isQConstant(arg)) {
                // q constant found
                containsQConstants = true;

                int numSubstitutions = 0;
                for (int argSubst : _htn.getDomainOfQConstant(arg)) {
                    const USignature& sigSubst = _vars.sigSubstitute(arg, argSubst);
                    if (_vars.isEncodedSubstitution(sigSubst) && (_useSmt && _smt.holds(_vars.varSubstitution(arg, argSubst))) || (!_useSmt && _sat.holds(_vars.varSubstitution(arg, argSubst))) ) {
                        Log::d("SUBSTVAR [%s/%s] TRUE => %s ~~> ", TOSTR(arg), TOSTR(argSubst), TOSTR(sig));
                        numSubstitutions++;
                        Substitution sub;
                        sub[arg] = argSubst;
                        sig.apply(sub);
                        Log::d("%s\n", TOSTR(sig));
                    } else {
                        //Log::d("%i FALSE\n", varSubstitution(sigSubst));
                    }
                }

                if (numSubstitutions == 0) {
                    Log::e("(%i,%i) No substitutions for arg %s of %s\n", layer, pos, TOSTR(arg), TOSTR(origSig));
                    return Sig::NONE_SIG;
                }
                assert(numSubstitutions == 1 || Log::e("%i substitutions for arg %s of %s\n", numSubstitutions, TOSTR(arg), TOSTR(origSig)));
            }

            if (!containsQConstants) break; // done
        }

        //if (origSig != sig) Log::d("%s ~~> %s\n", TOSTR(origSig), TOSTR(sig));
        
        return sig;
    }
};

#endif
