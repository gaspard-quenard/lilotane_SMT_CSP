
#include <assert.h> 

#include "planner.h"
#include "util/log.h"
#include "util/signal_manager.h"
#include "util/timer.h"
#include "sat/plan_optimizer.h"
#include "data/primitive_tree.h"
#include "data/signature.h"
#include "sat/variable_position.h"

int terminateSatCall(void* state) {return ((Planner*) state)->getTerminateSatCall();}

int Planner::findPlan() {
    
    int iteration = 0;
    Log::i("Iteration %i.\n", iteration);

    createFirstLayer();

    // Bounds on depth to solve / explore
    int firstSatCallIteration = _params.getIntParam("d");
    int maxIterations = _params.getIntParam("D");
    _sat_time_limit = _params.getFloatParam("stl");

    bool solved = false;
    _enc.setTerminateCallback(this, terminateSatCall);
    if (!USE_LIFTED_TREE_PATH && iteration >= firstSatCallIteration) {
        _enc.addAssumptions(_layer_idx);
        int result = _enc.solve();
        if (result == 0) {
            Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
            _sat_time_limit = 0;
        }
        solved = result == 10;
    } 
    
    // Next layers
    while (!solved && (maxIterations == 0 || iteration < maxIterations)) {

        if (iteration >= firstSatCallIteration) {

            _enc.printFailedVars(*_layers.back());

            if (_params.isNonzero("cs")) { // check solvability
                Log::i("Not solved at layer %i with assumptions\n", _layer_idx);

                // Attempt to solve formula again, now without assumptions
                // (is usually simple; if it fails, we know the entire problem is unsolvable)
                int result = _enc.solve();
                if (result == 20) {
                    Log::w("Unsolvable at layer %i even without assumptions!\n", _layer_idx);
                    break;
                } else {
                    Log::i("Not proven unsolvable - expanding by another layer\n");
                }
            } else {
                Log::i("Unsolvable at layer %i -- expanding.\n", _layer_idx);
            }
        }

        iteration++;      
        Log::i("Iteration %i.\n", iteration);
        
        bool isOk = createNextLayer();

        // TEST LIFTED TREE PATH
        if (USE_LIFTED_TREE_PATH && (iteration < 1 || !isOk)) {
            continue;
        }
        // END TEST LIFTED TREE PATH

        if (iteration >= firstSatCallIteration) {
            _enc.addAssumptions(_layer_idx);
            int result = _enc.solve();
            if (result == 0) {
                Log::w("Solver was interrupted. Discarding time limit for next solving attempts.\n");
                _sat_time_limit = 0;
            }
            solved = result == 10;
        } 
    }

    if (!solved) {
        if (iteration >= firstSatCallIteration) _enc.printFailedVars(*_layers.back());
        Log::w("No success. Exiting.\n");
        return 1;
    }

    Log::i("Found a solution at layer %i.\n", _layers.size()-1);
    _time_at_first_plan = Timer::elapsedSeconds();

    improvePlan(iteration);

    _plan_writer.outputPlan(_plan);
    printStatistics();    
    return 0;
}

void Planner::improvePlan(int& iteration) {

    // Compute extra layers after initial solution as desired
    PlanOptimizer optimizer(_htn, _layers, _enc);
    int maxIterations = _params.getIntParam("D");
    int extraLayers = _params.getIntParam("el");
    int upperBound = _layers.back()->size()-1;
    if (extraLayers != 0) {

        // Extract initial plan (for anytime purposes)
        _plan = _enc.extractPlan();
        _has_plan = true;
        upperBound = optimizer.getPlanLength(std::get<0>(_plan));
        Log::i("Initial plan at most shallow layer has length %i\n", upperBound);
        
        if (extraLayers == -1) {

            // Indefinitely increase bound and solve until program is interrupted or max depth reached
            size_t el = 1;
            do {
                // Extra layers without solving
                for (size_t x = 0; x < el && (maxIterations == 0 || iteration < maxIterations); x++) {
                    iteration++;      
                    Log::i("Iteration %i. (extra)\n", iteration);
                    createNextLayer();
                }
                // Solve again (to get another plan)
                _enc.addAssumptions(_layer_idx);
                int result = _enc.solve();
                if (result != 10) break;
                // Extract plan at layer, update bound
                auto thisLayerPlan = _enc.extractPlan();
                int newLength = optimizer.getPlanLength(std::get<0>(thisLayerPlan));
                // Update plan only if it is better than any previous plan
                if (newLength < upperBound || !_has_plan) {
                    upperBound = newLength;
                    _plan = thisLayerPlan;
                    _has_plan = true;
                }
                Log::i("Initial plan at layer %i has length %i\n", iteration, newLength);
                // Optimize
                optimizer.optimizePlan(upperBound, _plan, PlanOptimizer::ConstraintAddition::TRANSIENT);
                // Double number of extra layers in next iteration
                el *= 2;
            } while (maxIterations == 0 || iteration < maxIterations);

        } else {
            // Extra layers without solving
            for (int x = 0; x < extraLayers; x++) {
                iteration++;      
                Log::i("Iteration %i. (extra)\n", iteration);
                createNextLayer();
            }

            // Solve again (to get another plan)
            _enc.addAssumptions(_layer_idx);
            _enc.solve();
        }
    }

    if (extraLayers != -1) {
        if (_optimization_factor != 0) {

            // Extract plan at final layer, update bound
            auto finalLayerPlan = _enc.extractPlan();
            int newLength = optimizer.getPlanLength(std::get<0>(finalLayerPlan));
            // Update plan only if it is better than any previous plan
            if (newLength < upperBound || !_has_plan) {
                upperBound = newLength;
                _plan = finalLayerPlan;
                _has_plan = true;
            }
            Log::i("Initial plan at final layer has length %i\n", newLength);
            // Optimize
            optimizer.optimizePlan(upperBound, _plan, PlanOptimizer::ConstraintAddition::PERMANENT);

        } else {
            // Just extract plan
            _plan = _enc.extractPlan();
            _has_plan = true;
        }
    }
}

void Planner::incrementPosition() {
    _num_instantiated_actions += _layers[_layer_idx]->at(_pos).getActions().size();
    _num_instantiated_reductions += _layers[_layer_idx]->at(_pos).getReductions().size();
    _pos++; _num_instantiated_positions++;
}

void Planner::createFirstLayer() {

    // Initial layer of size 2 (top level reduction + goal action)
    int initSize = 2;
    Log::i("Creating initial layer of size %i\n", initSize);
    _layer_idx = 0;
    _pos = 0;
    _layers.push_back(new Layer(0, initSize));
    Layer& initLayer = (*_layers[0]);
    initLayer[_pos].setPos(_layer_idx, _pos);

    initLayer[_pos].setLtpPos(VariablePosition::nextVar());
    
    /***** LAYER 0, POSITION 0 ******/

    // Instantiate all possible init. reductions
    for (USignature& rSig : _instantiator.getApplicableInstantiations(_htn.getInitReduction())) {
        auto rOpt = createValidReduction(rSig, USignature());
        if (rOpt) {
            auto& r = rOpt.value();
            USignature sig = r.getSignature();
            sig.setNextId();
            initLayer[_pos].addReduction(sig);
            initLayer[_pos].addAxiomaticOp(sig);
            initLayer[_pos].addExpansionSize(r.getSubtasks().size());
        }
    }
    addPreconditionConstraints();
    initializeNextEffects();
    
    incrementPosition();

    /***** LAYER 0, POSITION 1 ******/

    createNextPosition(); // position 1

    initLayer[_pos].setLtpPos(VariablePosition::nextVar());

    // Create virtual goal action
    Action goalAction = _htn.getGoalAction();
    USignature goalSig = goalAction.getSignature();
    goalSig.setNextId();
    initLayer[_pos].addAction(goalSig);
    initLayer[_pos].addAxiomaticOp(goalSig);
    addPreconditionConstraints();
    
    /***** LAYER 0 END ******/

    initLayer[0].clearAfterInstantiation();
    initLayer[1].clearAfterInstantiation();

    _pos = 0;
    if (!USE_LIFTED_TREE_PATH) {
        _enc.encode(_layer_idx, _pos++);
        _enc.encode(_layer_idx, _pos++);
    }

    initLayer.consolidate();
}

bool Planner::createNextLayer() {

    _layers.push_back(new Layer(_layers.size(), _layers.back()->getNextLayerSize()));
    Layer& newLayer = *_layers.back();
    Log::i("New layer size: %i\n", newLayer.size());
    Layer& oldLayer = (*_layers[_layer_idx]);
    _layer_idx++;
    _pos = 0;

    // Instantiate new layer
    Log::i("Instantiating ...\n");
    for (_old_pos = 0; _old_pos < oldLayer.size(); _old_pos++) {
        size_t newPos = oldLayer.getSuccessorPos(_old_pos);
        size_t maxOffset = oldLayer[_old_pos].getMaxExpansionSize();

        // Instantiate each new position induced by the old position
        for (size_t offset = 0; offset < maxOffset; offset++) {
            //Log::d("%i,%i,%i,%i\n", _old_pos, newPos, offset, newLayer.size());
            assert(_pos == newPos + offset);
            Log::v("- Position (%i,%i)\n", _layer_idx, _pos);

            assert(newPos+offset < newLayer.size());

            createNextPosition();
            Log::v("  Instantiation done. (r=%i a=%i qf=%i supp=%i)\n", 
                    (*_layers[_layer_idx])[_pos].getReductions().size(),
                    (*_layers[_layer_idx])[_pos].getActions().size(),
                    (*_layers[_layer_idx])[_pos].getQFacts().size(),
                    (*_layers[_layer_idx])[_pos].getPosFactSupports().size() + (*_layers[_layer_idx])[_pos].getNegFactSupports().size()
            );
            if (_pos > 0) _layers[_layer_idx]->at(_pos-1).clearAfterInstantiation();

            incrementPosition();
            checkTermination();
        }
    }
    if (_pos > 0) _layers[_layer_idx]->at(_pos-1).clearAfterInstantiation();

    Log::i("Collected %i relevant facts at this layer\n", _analysis.getRelevantFacts().size());
    
    // Get the size of the new layer
    Log::i("New layer size: %i\n", newLayer.size());

    if (USE_LIFTED_TREE_PATH) {
        
        computePreviousesAndNextsFlows(newLayer, _layer_idx);

        // Compute the time of the following function
        std::vector<PositionedUSig> intialActionsInPrimitiveTree;
        auto start = std::chrono::high_resolution_clock::now();
        bool primitiveTreeIsNotEmpty = constructPrimitiveTree(newLayer, _layer_idx, intialActionsInPrimitiveTree);
        auto stop = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
        long long int time_ms = duration.count();

        Log::i("Primitive tree construction took %lld ms\n", time_ms);

        debug_write_all_paths_in_file(newLayer, _layer_idx);


        if (LTP_INCREMENTAL_SAT) {
            // Remove all blank actions in the primitive tree + indicate all the new successors and predecessors of each action for this layer
            cleanPrimitiveTree(newLayer, _layer_idx);
            debug_write_primitive_tree(newLayer, _layer_idx);
        }        

        _enc.__interfaceSolver__reset();

        // if (primitiveTree.size() == 0) {
        //     return false;
        // }

        // TEST
        // Re compute the true and false facts with only the primitive tree (Difficult, since we must recompute the preconditions and effects of all actions of the primitive tree)
        // propagateInitialState();
        // for (int posIdx = 0; posIdx < newLayer.size(); posIdx++) {
        //     Position& pos = newLayer[posIdx];
        //     initializeNextEffectsPrimitiveTree(pos);
        // }

        // END TEST

        // Encode new layer
        // Print the current layer
        Log::i("Encoding for lifted tree path ...\n");
        for (_old_pos = 0; _old_pos < oldLayer.size(); _old_pos++) {
            size_t newPos = oldLayer.getSuccessorPos(_old_pos);
            size_t maxOffset = oldLayer[_old_pos].getMaxExpansionSize();
            for (size_t offset = 0; offset < maxOffset; offset++) {
                _pos = newPos + offset;
                Log::v("- Position (%i,%i)\n", _layer_idx, _pos);
                _enc.encode_for_lifted_tree_path(_layer_idx, _pos);
                clearDonePositions(offset);
            }
        }

        // _enc.encode_for_lifted_tree_path_ensure_one_init_action_is_true(_layer_idx);
        _enc.encode_for_lifted_tree_path_ensure_one_init_action_is_true(intialActionsInPrimitiveTree);

        // std::string filename = "smt_file_layer_" + std::to_string(_layer_idx) + ".SMT";
        // _enc.__interfaceSolver__printFormula(filename);        

        newLayer.consolidate();

        return primitiveTreeIsNotEmpty;
    
    }
    else {
        // Encode new layer
        Log::i("Encoding ...\n");
        for (_old_pos = 0; _old_pos < oldLayer.size(); _old_pos++) {
            size_t newPos = oldLayer.getSuccessorPos(_old_pos);
            size_t maxOffset = oldLayer[_old_pos].getMaxExpansionSize();
            for (size_t offset = 0; offset < maxOffset; offset++) {
                _pos = newPos + offset;
                Log::v("- Position (%i,%i)\n", _layer_idx, _pos);
                _enc.encode(_layer_idx, _pos);
                clearDonePositions(offset);
            }
        }

        // _enc.__interfaceSolver__printFormula();        

        newLayer.consolidate();
    }


    return true;
}


void Planner::computePreviousesAndNextsFlows(Layer& layer, int layerIdx) {

    robin_hood::unordered_set<int> methodsIdAlreadySeen;
    NodeHashMap<int, USigSetUniqueID> childrenIsPreviousesPosition;

    // Iterate over all positions
    for (int posIdx = 0; posIdx < layer.size(); posIdx++) {
        Log::d("At pos: %i/%i\n", posIdx, layer.size());
        Position& newPos = layer[posIdx]; 

        bool hasAbove = layerIdx > 0;
        Position NULL_POS;
        size_t _old_pos = 0;
        if (hasAbove) {
            const Layer& oldLayer = *_layers.at(layerIdx-1);
            while (_old_pos+1 < oldLayer.size() && oldLayer.getSuccessorPos(_old_pos+1) <= posIdx) 
                _old_pos++;
        }
        Position& above = (hasAbove ? (*_layers.at(layerIdx-1))[_old_pos] : NULL_POS);


            // Print all the expansions
        // if (newPos.getPositionIndex() == 0 && newPos.getLayerIndex() == 4) {
        //     for (auto& [rSig, exps] : newPos.getExpansions()) {
        //         for (USignature aSig : exps) {
        //             Log::i("Expansion of (%i): (%i)\n", rSig._unique_id, aSig._unique_id);
        //         }
        //     }

        //     int ebg = 0;
        // }

        //// TEST
        // Check if there is an action with a repetition somewhere
        // for (USignature& aSig : newPos.getActions()) {
        //     assert(aSig._unique_id >= 0);
        //     if (aSig.repetition > 0) {
        //         int a = 0;
        //     }
        // }

        // Print the above position and all the action in this position
        // Log::i("Current pos: %i\n", newPos.getPositionIndex());
        // for (USignature& aSig : newPos.getActionsWithUniqueID()) {
        //     if (aSig._unique_id == 366) {
        //         int a = 0;
        //     }
        //     Log::i("  Action: %s(%i)\n", Names::to_SMT_string(aSig).c_str(), aSig._unique_id);
        //     // Check if we have the ID 130 in the previous
        //     if (newPos.getPrevious().count(aSig._unique_id) > 0) {
        //         for (USignature& aSig : newPos.getPrevious().at(aSig._unique_id)) {
        //             if (aSig._unique_id == 366) {
        //                 int a = 0;
        //             }
        //         }
        //     }  
        // }

        // if (layerIdx == 4 && posIdx == 70) {
        //     int a = 0;
        // }




        // Log::i("Above pos: %i\n", above.getPositionIndex());
        // for (USignature& aSig : above.getActionsWithUniqueID()) {
        //     if (aSig._unique_id == 366) {
        //         int a = 0;
        //         // Test something, get all the nexts of this child, then verity that in the next position, all the previous of the nexts contains this child
        //         USigSetUniqueID& nexts = above.getNexts().at(aSig._unique_id);
        //         Position& nextPosAbove = (*_layers.at(layerIdx-1))[above.getPositionIndex()+1];
        //         for (USignature& next : nexts) {
        //             USigSetUniqueID& previouses = nextPosAbove.getPrevious().at(next._unique_id);
        //             // Verify that it contains the correct id of this child
        //             bool found = false;
        //             for (USignature& previous : previouses) {
        //                 if (previous._unique_id == aSig._unique_id) {
        //                     found = true;
        //                     break;
        //                 }
        //             }
        //             assert(found);
        //         }
        //     }
        //     Log::i("  Action: %s(%i)\n", Names::to_SMT_string(aSig).c_str(), aSig._unique_id);
        // }

        

        ///// END TEST

        if (posIdx == layer.size() - 1) {
            // We are at the last position of this layer, there should be only the goal action in there
            // The goal action should follows all the actions and reductions of the previous position

            assert(newPos.getActionsWithUniqueID().size() == 1);
            assert(newPos.getReductions().size() == 0);

            USignature& goalAction = *newPos.getActions().begin();

            // Get the last position 
            int lastPosIdx = posIdx-1;
            Position& lastPos = layer[lastPosIdx];

            // Iterate over all the actions of the last position
            for (USignature& aSig : lastPos.getActionsWithUniqueID()) {

                // Add the nexts and previouses
                lastPos.addNexts(aSig, goalAction);
                newPos.addPrevious(goalAction, aSig);

            }
            // Do the same for the reductions
            for (USignature& rSig : lastPos.getReductions()) {

                // Add the nexts and previouses
                lastPos.addNexts(rSig, goalAction);
                newPos.addPrevious(goalAction, rSig);

            }

            continue;
        }

        for (auto& [parent, children] : newPos.getExpansions()) {

            if (parent._unique_id == 29) {
                int dbg = 0;
            }

            // To debug, print the parent and all the children
            std::string parentName = Names::to_SMT_string(parent, false);
            for (USignature& child : children) {
                std::string childCurrentName = Names::to_SMT_string(child, false);
                Log::d("Flow: %s(%i) (parent: %s(%i))\n", childCurrentName.c_str(), child._unique_id, parentName.c_str(), parent._unique_id);
            }

            // Get the id of the parent
            // int idParent = above.getVariable(VarType::OP, parent);
            int idParent = parent._unique_id;

            // Check if the parent has children in the previous position
            if (childrenIsPreviousesPosition.contains(idParent)) {

                // Get the last position 
                int lastPosIdx = posIdx-1;
                Position& lastPos = layer[lastPosIdx];

                // Get the children of the parent in the previous position
                USigSetUniqueID& childrenPreviouses = childrenIsPreviousesPosition.at(idParent);
                // Iterate over all the children of the parent in the previous position
                for (USignature& childPrevious : childrenPreviouses) {

                     for (USignature& childCurrent : children) {

                        if (childPrevious._unique_id == 822) {
                            int dbg = 0;
                        }

                        lastPos.addNexts(childPrevious, childCurrent);
                        newPos.addPrevious(childCurrent, childPrevious);

                        if (childPrevious._unique_id == 366) {
                            int numNexts = lastPos.getNexts().at(childPrevious._unique_id).size();
                            int dbg = 0;
                        }

                        std::string childPreviousName = Names::to_SMT_string(childPrevious, false);
                        std::string childCurrentName = Names::to_SMT_string(childCurrent, false);

                        Log::d("Next of: %s(%i) -> %s(%i)\n", childPreviousName.c_str(), childPrevious._unique_id, childCurrentName.c_str(), childCurrent._unique_id);

                     }
                    
                }
            } else {
                // It means that we are the first children of this parent
                // We need to check if this parent has previouses flows (and if so, the last children of those previouses flows)
                if (above.getPrevious().contains(parent._unique_id)) {
                    for (auto& previousParent : above.getPrevious().at(parent._unique_id)) {
                        // Check if the parent has children in the previous position

                        // We need the id of the previous parent
                        Layer& oldLayer = *_layers.at(layerIdx-1);
                        Position& aboveLastPos = oldLayer[_old_pos - 1];

                        Position& lastPos = layer[posIdx-1];

                        // Get the id of the previous parent
                        // int idPreviousParent = aboveLastPos.getVariable(VarType::OP, previousParent);
                        int idPreviousParent = previousParent._unique_id;

                        if (!childrenIsPreviousesPosition.count(idPreviousParent)) {
                            Log::e("NONONONON for %s(%i)\n", Names::to_SMT_string(previousParent, false).c_str(), previousParent._unique_id);

                            // Print all the previous of above
                            for (USignature& previous : above.getPrevious().at(parent._unique_id)) {
                                std::string previousName = Names::to_SMT_string(previous, false);
                                Log::e("Previous of %s(%i): %s(%i)\n", parentName.c_str(), parent._unique_id, previousName.c_str(), previous._unique_id);
                            }
                            int a = 0;
                        }

                        // Iterate over all the last children of the previous parent
                        for (USignature& childPrevious : childrenIsPreviousesPosition.at(idPreviousParent)) {
                            for (USignature& childCurrent : children) {

                                // if (childPrevious._unique_id == 366) {
                                //     int numNexts = lastPos.getNexts().at(childPrevious._unique_id).size();
                                //     int dbg = 0;
                                // }

                                // if (childPrevious._unique_id == 29) {
                                //     int dbg = 0;
                                //     assert(dbg != 0);
                                // }

                                // Add the nexts
                                lastPos.addNexts(childPrevious, childCurrent);
                                newPos.addPrevious(childCurrent, childPrevious);

                                if (childPrevious._unique_id == 366) {
                                    int numNexts = lastPos.getNexts().at(childPrevious._unique_id).size();
                                    int numPrevious = newPos.getPrevious().at(childCurrent._unique_id).size();
                                    int dbg = 0;
                                }

                                std::string childPreviousName = Names::to_SMT_string(childPrevious, false);
                                std::string childCurrentName = Names::to_SMT_string(childCurrent, false);

                                Log::d("Next of: %s(%i) -> %s(%i)\n", childPreviousName.c_str(), childPrevious._unique_id, childCurrentName.c_str(), childCurrent._unique_id);

                            }
                        }
                        
                        int a = 0;
                    }
                }
            }
        }

        // Now update the childrenIsPreviousesPosition
        childrenIsPreviousesPosition.clear();
        for (auto& [parent, children] : newPos.getExpansions()) {

            Log::d("Parent: %s(%i)\n", Names::to_SMT_string(parent, false).c_str(), parent._unique_id);

            if (parent._unique_id == 360) {
                int dbg = 0;

                int dbg2 = 0;
            }

            // Get the id of the parent
            // int idParent = above.getVariable(VarType::OP, parent);
            int idParent = parent._unique_id;

            if (children.size() == 0) {
                int dbg2 = 0;
            }

            // Add the children of the parent to the childrenIsPreviousesPosition
            for (USignature& child : children) {

                Log::d("Child: %s(%i)\n", Names::to_SMT_string(child, false).c_str(), child._unique_id);

                if (child.repetition > 0) {
                    int dbs = 0;
                }

                if (child._name_id == 1) {
                    int dbd = 0;
                }

                // Just confirm that this child has only one parent (for now, we will handle later for blank action with multiples parents)
                if (newPos.getPredecessorsWithUniqueID().at(child._unique_id).size() > 1) {
                    // Print all the parents
                    for (USignature& parent : newPos.getPredecessorsWithUniqueID().at(child._unique_id)) {
                        std::string parentName = Names::to_SMT_string(parent, false);
                        Log::d("=> Parent: %s(%i)\n", parentName.c_str(), parent._unique_id);
                    }
                    int dbg = 0;
                }
                assert(newPos.getPredecessorsWithUniqueID().at(child._unique_id).size() == 1);

                if (child._unique_id == 366) {
                    int dbf = 0;
                }

                childrenIsPreviousesPosition[idParent].insert(child);
            }
        }

        Log::d("\n");
    }
    int a = 0;
}

/**
 * Return all the initial action of the primitive tree if the primitive tree is not empty
*/
bool Planner::constructPrimitiveTree(Layer& layer, int layerIdx, std::vector<PositionedUSig>& initialActionsInPrimitiveTree) {

    robin_hood::unordered_set<int> flowsAlreadySeen;
    robin_hood::unordered_set<int> idActionsInPrimitiveTree;

    // Iterate over all positions
    for (int posIdx = 0; posIdx < layer.size(); posIdx++) {
        Position& newPos = layer[posIdx]; 

        // Iterate over all actions of this position
        for (USignature& aSig : newPos.getActionsWithUniqueID()) {

            // Check if this action can be the beginning of the primitive tree (no previouses flows)
            if (!newPos.getPrevious().contains(aSig._unique_id)) {

                if (aSig._unique_id == 822) {
                    int dbg = 0;
                }

                // Indicate that this action can be the beginning of the primitive tree
                std::string aSigName = Names::to_SMT_string(aSig, true);
                Log::d("Action: %s (can be the beginning of the primitive tree)\n", aSigName.c_str());

                recursiveComputePrimitiveTree(aSig, layer, posIdx, flowsAlreadySeen, idActionsInPrimitiveTree);

                if (newPos.getActionsInPrimitiveTree().contains(aSig)) {
                    // Create a copy
                    // const USignature aSigCopy = aSig;
                    initialActionsInPrimitiveTree.push_back(PositionedUSig(layerIdx, posIdx, aSig));
                }
            }
        }
    }

    // Print all the actions of the primitive tree
    bool primitiveTreeIsEmpty = true;
    for (int posIdx = 0; posIdx < layer.size(); posIdx++) {
        Position& newPos = layer[posIdx]; 

        // Iterate over all actions of this position
        for (USignature& aSig : newPos.getActionsWithUniqueID()) {

            // Check if this action is in the primitive tree
            if (newPos.getActionsInPrimitiveTree().contains(aSig)) {

                // Indicate that this action is in the primitive tree
                std::string aSigName = Names::to_SMT_string(aSig, true);
                Log::d("Action: %s__%i (is part of the primitive tree)\n", aSigName.c_str(), posIdx);
                primitiveTreeIsEmpty = false;
            }

            // if (aSig.is_primitive) {
            //     std::string aSigName = Names::to_SMT_string(aSig, true);
            //     Log::i("Action: %s (is part of the primitive tree)\n", aSigName.c_str());
            //     primitiveTreeIsEmpty = false;
            // }
        }
    }

    if (primitiveTreeIsEmpty) {
        Log::i("The primitive tree is empty\n");
    }

    // debug_write_all_paths_in_file(layer, layerIdx);


    return !primitiveTreeIsEmpty;
}


/**
 * Remove all useless blank actions in the primitive tree and indicate which succcessors are new successor for each action in the primitive tree
*/
void Planner::cleanPrimitiveTree(Layer& layer, int layerIdx) {

    NodeHashMap<int, PositionUSigSetUniqueID> mapBlankActionToAllNexts;

    // Iterate over all position in the layer and then iterate over all action which are in the primitive tree in this position
    for (int posIdx = 1; posIdx < layer.size(); posIdx++) {
        Position& left = layer[posIdx - 1]; 
        Position& pos = layer[posIdx]; 

        // Get the above position (to be able to determinate the new successors and predessors of each action (
        // predecessors and successors of an action which were not defined in the previous layer
        bool hasAbove = layerIdx > 0;
        Position NULL_POS;
        size_t _old_pos = 0;
        if (hasAbove) {
            const Layer& oldLayer = *_layers.at(layerIdx-1);
            while (_old_pos+1 < oldLayer.size() && oldLayer.getSuccessorPos(_old_pos+1) <= (posIdx - 1)) 
                _old_pos++;
        }
        Position& above = (hasAbove ? (*_layers.at(layerIdx-1))[_old_pos] : NULL_POS);
        
        NodeHashSet<USignature, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> allBlanksActionToRemove;

        for (USignature& aSig : left.getActionsInPrimitiveTree()) {

            PositionedUSig positionnedCurrent = PositionedUSig(layerIdx, posIdx - 1, aSig);

            if (aSig.shadow_action) {
                allBlanksActionToRemove.insert(aSig);
                continue;
            }

            // Iterate over all the nexts and get all the next which are not a shadow action
            // To do this, create a set of all the current action to iterate 
            FlatHashSet<PositionedUSig, PositionedUSigHasherWithUniqueID, PositionUSignatureEqualityWithUniqueID> allBlanksActionToIterate;
            // Initialize it with all the nexts blank action
            for (USignature& next : left.getNexts().at(aSig._unique_id)) {

                // If this next is not in the primitive tree, we do not care
                if (!pos.getActionsInPrimitiveTree().contains(next)) continue;

                if (next.shadow_action) {
                    // Add it as a position usig in all blanks to iterate
                    PositionedUSig blank = PositionedUSig(layerIdx, posIdx, next);
                    allBlanksActionToIterate.insert(blank);
                } else {
                    // It is a true next, add it into the next_primitive tree
                    PositionedUSig positionUSigNext = PositionedUSig(layerIdx, posIdx, next);


                    left.addNextsPrimitiveTree(aSig, positionUSigNext);

                    // Add the previous as well
                    pos.addPreviousPrimitiveTree(next, positionnedCurrent);

                    // Add it as well in new nexts if the above position does not contains the action of the above does not have this 
                    // into its nextsPrimitiveTree
                    if (!above.getActionsInPrimitiveTree().contains(aSig) || !above.getNextsPrimitiveTree().at(aSig._unique_id).contains(positionUSigNext)) {
                        left.addNewNextsPrimitiveTree(aSig, positionUSigNext);
                        pos.addNewPreviousPrimitiveTree(next, positionnedCurrent);
                    }
                }
            }

            // Now, we need to iterate over all blanks action untils our set is empty
            while (allBlanksActionToIterate.size() > 0) {
                // Get one 
                PositionedUSig psig = *allBlanksActionToIterate.begin();
                allBlanksActionToIterate.erase(psig);
                Position& position = _layers[psig.layer]->at(psig.pos);
                Position& nextPosition = _layers[psig.layer]->at(psig.pos + 1);
                for (USignature& next : position.getNexts().at(psig.usig._unique_id)) {
                    
                    // If this next is not in the primitive tree, we do not care
                    if (!nextPosition.getActionsInPrimitiveTree().contains(next)) continue;

                    if (next.shadow_action) {
                        // Add it as a position usig in all blanks to iterate
                        PositionedUSig blank = PositionedUSig(layerIdx, nextPosition.getPositionIndex(), next);
                        allBlanksActionToIterate.insert(blank);
                    } else {
                        // It is a true next, add it into the next_primitive tree
                        PositionedUSig positionUSigNext = PositionedUSig(layerIdx, nextPosition.getPositionIndex(), next);


                        left.addNextsPrimitiveTree(aSig, positionUSigNext);

                        nextPosition.addPreviousPrimitiveTree(next, positionnedCurrent);

                        // Add it as well in new nexts if the above position does not contains the action of the above does not have this 
                        // into its nextsPrimitiveTree
                        if (!above.getActionsInPrimitiveTree().contains(aSig) || !above.getNextsPrimitiveTree().at(aSig._unique_id).contains(positionUSigNext)) {
                            left.addNewNextsPrimitiveTree(aSig, positionUSigNext);
                            nextPosition.addNewPreviousPrimitiveTree(next, positionnedCurrent);
                        }
                    } 
                }
            } 
        }

        // Remove all the blank action which are in the primitive tree
        for (USignature& aSig : allBlanksActionToRemove) {
            left.getActionsInPrimitiveTree().erase(aSig);
        }
    }
}

void Planner::debug_write_all_paths_in_file(Layer& layer, int layerIdx) {
    std::ofstream file;
    std::string nameFile = "all_paths_" + std::to_string(layerIdx) + ".txt";
    file.open(nameFile);

    // Iterate over all positions
    for (int posIdx = 0; posIdx < layer.size(); posIdx++) {
        Position& newPos = layer[posIdx]; 
        std::string posString = std::to_string(posIdx);
        for (USignature& rSig : newPos.getReductionsWithUniqueID()) {
            file << Names::to_SMT_string(rSig, false) << "__" << posString << " 0 0" << std::endl;
        }
        for (USignature& aSig : newPos.getActionsWithUniqueID()) {
            if (newPos.getActionsInPrimitiveTree().contains(aSig)) {
                file << Names::to_SMT_string(aSig, true) << "__" << posString << " 1 1" << std::endl;
            } else {
                file << Names::to_SMT_string(aSig, true) << "__" << posString << " 1 0" << std::endl;
            }
        }
    }

    file << std::endl;

    // Now, make a second pass to indicate all the nexts
    for (int posIdx = 0; posIdx < layer.size(); posIdx++) {
        Position& newPos = layer[posIdx]; 
        std::string nextPosString = std::to_string(posIdx + 1);
        std::string posString = std::to_string(posIdx);
        for (auto& [aSig_unique_id, nexts] : newPos.getNexts()) {

            // Get the aSig
            USignature aSig;
            for (USignature& aSig2 : newPos.getActionsWithUniqueID()) {
                if (aSig2._unique_id == aSig_unique_id) {
                    aSig = aSig2;
                    break;
                }
            }
            for (USignature& aSig2 : newPos.getReductionsWithUniqueID()) {
                if (aSig2._unique_id == aSig_unique_id) {
                    aSig = aSig2;
                    break;
                }
            }

            // Check if it is an action
            bool isAction = false;
            if (_htn.isAction(aSig)) {
                isAction = true;
            }
            file << Names::to_SMT_string(aSig, isAction) << "__" << posString << " ";
            for (USignature& next : nexts) {
                isAction = false;
                if (_htn.isAction(next)) {
                    isAction = true;
                }
                file << Names::to_SMT_string(next, isAction) << "__" << nextPosString << " ";
            }
            file << std::endl;
        }
    }

    file.flush();
    file.close();
}

void Planner::debug_write_primitive_tree(Layer& layer, int layerIdx) {
    std::ofstream file;
    std::string nameFile = "primitive_tree_" + std::to_string(layerIdx) + ".txt";
    file.open(nameFile);

    // Iterate over all positions
    for (int posIdx = 0; posIdx < layer.size(); posIdx++) {
        Position& newPos = layer[posIdx]; 
        std::string posString = std::to_string(posIdx);
        for (USignature& aSig : newPos.getActionsInPrimitiveTree()) {
            if (!newPos.getActionsInPrimitiveTree().contains(aSig)) continue;

            file << Names::to_SMT_string(aSig, true) << "__" << posString << std::endl;
    
        }
    }

    file << std::endl;

    // Now, make a second pass to indicate all the nexts
    for (int posIdx = 0; posIdx < layer.size(); posIdx++) {
        Position& newPos = layer[posIdx]; 
        std::string posString = std::to_string(posIdx);
        for (auto& [aSig_unique_id, nexts] : newPos.getNextsPrimitiveTree()) {

            // Get the aSig
            USignature aSig;
            for (USignature& aSig2 : newPos.getActionsWithUniqueID()) {
                if (aSig2._unique_id == aSig_unique_id) {
                    aSig = aSig2;
                    break;
                }
            }

            file << Names::to_SMT_string(aSig, true) << "__" << posString << " ";
            for (PositionedUSig& next : nexts) {
                file << Names::to_SMT_string(next.usig, true) << "__" << std::to_string(next.pos) << " ";
            }
            file << std::endl;
        }
    }

    file.flush();
    file.close();
}

bool Planner::recursiveComputePrimitiveTree(USignature currentAction, Layer& layer, int posIdx, robin_hood::unordered_set<int>& idActionsAlreadyVisited, robin_hood::unordered_set<int>& idActionsInPrimitiveTree) {

    std::string currentActionName = Names::to_SMT_string(currentAction, true);
    // Log::i("Action: %s\n", currentActionName.c_str());

    // Verify that this is an action
    if (!_htn.isAction(currentAction)) {
        // currentAction.setIsPrimitive(false);
        // layer[posIdx].removeActionInPrimitiveTree(currentAction);
        // Indicate that we have already visited this action
        idActionsAlreadyVisited.insert(currentAction._unique_id);
        return false;
    }

    // If this node is an action and has no nexts flows, then is a a leaf of the primitive tree
    if (!layer[posIdx].getNexts().contains(currentAction._unique_id)) {
        // currentAction.setIsPrimitive(true);
        layer[posIdx].addActionInPrimitiveTree(currentAction);
        idActionsInPrimitiveTree.insert(currentAction._unique_id);
        // Indicate that we have already visited this action
        idActionsAlreadyVisited.insert(currentAction._unique_id);
        return true;
    }


    // If this node is an action node, then we have to iterate over all its children
    // If at least one of the children is a primitive flow, then the current node is a primitive flow as well
    // So its attribute isPrimitiveFlow is set to true and we return true
    // (If a children has already been computed, then we do not have to compute it again)


    bool currentActionIsPrimitive = false;
    
    // Iterate over all the children of the current action
    for (USignature next : layer[posIdx].getNexts().at(currentAction._unique_id)) {

        // Check if we have already visited this action
        if (idActionsAlreadyVisited.contains(next._unique_id)) {
            // If we have already visited this action, then we do not have to compute it again
            // We just have to check if it is a primitive flow
            // if (next.is_primitive) {
            if (idActionsInPrimitiveTree.contains(next._unique_id)) {
                currentActionIsPrimitive = true;
            }
                
        } else {
            // If we have not already visited this action, then we have to compute it
            // We have to check if it is a primitive flow
            if (recursiveComputePrimitiveTree(next, layer, posIdx+1, idActionsAlreadyVisited, idActionsInPrimitiveTree)) {
                currentActionIsPrimitive = true;
            }
        }
    }

    // Set the attribute isPrimitiveFlow of the current action
    // currentAction.setIsPrimitive(currentActionIsPrimitive);
    if (currentActionIsPrimitive) {
        layer[posIdx].addActionInPrimitiveTree(currentAction);
        idActionsInPrimitiveTree.insert(currentAction._unique_id);
    } else {
        // layer[posIdx].removeActionInPrimitiveTree(currentAction);
    }
    // Indicate that we have already visited this action
    idActionsAlreadyVisited.insert(currentAction._unique_id);
    return currentActionIsPrimitive;
}


void Planner::createNextPosition() {

    // Set up all facts that may hold at this position.
    if (_pos == 0) {
        propagateInitialState();
    } else {
        Position& left = (*_layers[_layer_idx])[_pos-1];
        createNextPositionFromLeft(left);
    }

    // Generate this new position's content based on the facts and the position above.
    if (_layer_idx > 0) {
        createNextPositionFromAbove();
    }

    // Eliminate operations which are dominated by another operation
    if (!USE_LIFTED_TREE_PATH && _params.isNonzero("edo")) 
        _domination_resolver.eliminateDominatedOperations(_layers[_layer_idx]->at(_pos));

    // In preparation for the upcoming position,
    // add all effects of the actions and reductions occurring HERE
    // as (initially false) facts to THIS position.  
    initializeNextEffects();
}

void Planner::createNextPositionFromAbove() {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    newPos.setPos(_layer_idx, _pos);
    newPos.setAbovePos(_old_pos);
    int offset = _pos - (*_layers[_layer_idx-1]).getSuccessorPos(_old_pos);
    //eliminateInvalidParentsAtCurrentState(offset);
    if (USE_LIFTED_TREE_PATH) {

        if (offset == 0) {
            // Take the same ltp position as parent
            Position& above = (*_layers[_layer_idx-1])[_old_pos];
            newPos.setLtpPos(above.getLtpPos());
        } else {
            // Create new ltp position
            newPos.setLtpPos(VariablePosition::nextVar());
        }


        propagateActionsWithUniqueID(offset);
        propagateReductionsWithUniqueID(offset);
        addPreconditionConstraintsUniqueID();
        // addPreconditionConstraints();
    } else {
        propagateActions(offset);
        propagateReductions(offset);
        addPreconditionConstraints();
    }
}

void Planner::createNextPositionFromLeft(Position& left) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    newPos.setPos(_layer_idx, _pos);
    assert(left.getLayerIndex() == _layer_idx);
    assert(left.getPositionIndex() == _pos-1);

    // Propagate fact changes from operations from previous position
    USigSet actionsToRemove;
    const USigSet* ops[2] = {&left.getActions(), &left.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {

            bool repeatedAction = isAction && _htn.isActionRepetition(aSig._name_id);

            for (const Signature& fact : _analysis.getPossibleFactChanges(aSig)) {
                if (isAction && !addEffect(
                        repeatedAction ? aSig.renamed(_htn.getActionNameFromRepetition(aSig._name_id)) : aSig, 
                        fact, 
                        repeatedAction ? EffectMode::DIRECT_NO_QFACT : EffectMode::DIRECT)) {
                    
                    // Impossible direct effect: forbid action retroactively.
                    Log::w("Retroactively prune action %s due to impossible effect %s\n", TOSTR(aSig), TOSTR(fact));
                    actionsToRemove.insert(aSig);

                    // Also remove any virtualized actions corresponding to this action
                    USignature repSig = aSig.renamed(_htn.getRepetitionNameOfAction(aSig._name_id));
                    if (left.hasAction(repSig)) actionsToRemove.insert(repSig);
                    
                    break;
                }
                if (!isAction && !addEffect(aSig, fact, EffectMode::INDIRECT)) {
                    // Impossible indirect effect: ignore.
                }
            }
            _analysis.eraseCachedPossibleFactChanges(aSig);
        }
        isAction = false;
    }

    for (const auto& aSig : actionsToRemove) {
        if (USE_LIFTED_TREE_PATH) {
            _pruning.pruneLiftedTreePath(aSig, _layer_idx, _pos-1);
        } else {
            _pruning.prune(aSig, _layer_idx, _pos-1);
        }
        
    }
}

void Planner::addPreconditionConstraints() {
    Position& newPos = _layers[_layer_idx]->at(_pos);

    for (const auto& aSig : newPos.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);
        // Add preconditions of action
        bool isRepetition = _htn.isActionRepetition(aSig._name_id);
        addPreconditionsAndConstraints(aSig, a.getPreconditions(), isRepetition);
    }

    for (const auto& rSig : newPos.getReductions()) {
        // Add preconditions of reduction
        addPreconditionsAndConstraints(rSig, _htn.getOpTable().getReduction(rSig).getPreconditions(), /*isRepetition=*/false);
    }
}


void Planner::addPreconditionConstraintsUniqueID() {
    Position& newPos = _layers[_layer_idx]->at(_pos);

    for (const auto& aSig : newPos.getActionsWithUniqueID()) {
        const Action& a = _htn.getOpTable().getAction(aSig);
        // Add preconditions of action
        bool isRepetition = _htn.isActionRepetition(aSig._name_id);
        addPreconditionsAndConstraints(aSig, a.getPreconditions(), isRepetition);
    }

    for (const auto& rSig : newPos.getReductionsWithUniqueID()) {
        // Add preconditions of reduction
        addPreconditionsAndConstraints(rSig, _htn.getOpTable().getReduction(rSig).getPreconditions(), /*isRepetition=*/false);
    }
}

void Planner::addPreconditionsAndConstraints(const USignature& op, const SigSet& preconditions, bool isRepetition) {
    Position& newPos = _layers[_layer_idx]->at(_pos);
    
    USignature constrOp = isRepetition ? USignature(_htn.getActionNameFromRepetition(op._name_id), op._args) : op;

    for (const Signature& fact : preconditions) {
        auto cOpt = addPrecondition(op, fact, !isRepetition);
        if (cOpt) newPos.addSubstitutionConstraint(constrOp, std::move(cOpt.value()));
    }
    if (!isRepetition) addQConstantTypeConstraints(op);

    if (!newPos.getSubstitutionConstraints().count(op)) return;

    // Merge substitution constraints as far as possible
    auto& constraints = newPos.getSubstitutionConstraints().at(op);
    //Log::d("MERGE? %i constraints\n", constraints.size());
    for (size_t i = 0; i < constraints.size(); i++) {
        for (size_t j = i+1; j < constraints.size(); j++) {
            auto& iTree = constraints[i];
            auto& jTree = constraints[j];
            if (iTree.canMerge(jTree)) {
                //Log::d("MERGE %s %i,%i sizes %i,%i\n", 
                //    iTree.getPolarity() == SubstitutionConstraint::ANY_VALID ? "ANY_VALID" : "NO_INVALID", 
                //    i, j, iTree.getEncodedSize(), jTree.getEncodedSize());
                iTree.merge(std::move(jTree));
                //Log::d("MERGED: new size %i\n", iTree.getEncodedSize());
                if (j+1 < constraints.size()) 
                    constraints[j] = std::move(constraints.back());
                constraints.erase(constraints.begin()+constraints.size()-1);
                j--;
            }
        }
    }
}

std::optional<SubstitutionConstraint> Planner::addPrecondition(const USignature& op, const Signature& fact, bool addQFact) {

    Position& pos = (*_layers[_layer_idx])[_pos];
    const USignature& factAbs = fact.getUnsigned();

    if (!_htn.hasQConstants(factAbs)) { 
        assert(_analysis.isReachable(fact) || Log::e("Precondition %s not reachable for op %s!\n", TOSTR(fact), TOSTR(op)));
                
        if (_analysis.isReachable(factAbs, !fact._negated)) {
            // Negated prec. is reachable: not statically resolvable
            initializeFact(pos, factAbs);
            _analysis.addRelevantFact(factAbs);
        }
        return std::optional<SubstitutionConstraint>();
    }
    
    std::vector<int> sorts = _htn.getOpSortsForCondition(factAbs, op);
    std::vector<int> sortedArgIndices = SubstitutionConstraint::getSortedSubstitutedArgIndices(_htn, factAbs._args, sorts);
    std::vector<int> involvedQConsts(sortedArgIndices.size());
    for (size_t i = 0; i < sortedArgIndices.size(); i++) involvedQConsts[i] = factAbs._args[sortedArgIndices[i]];
    SubstitutionConstraint c(involvedQConsts);

    bool staticallyResolvable = true;
    USigSet relevants;
    
    auto eligibleArgs = _htn.getEligibleArgs(factAbs, sorts);

    auto polarity = SubstitutionConstraint::UNDECIDED;
    size_t totalSize = 1; for (auto& args : eligibleArgs) totalSize *= args.size();
    size_t sampleSize = 25;
    bool doSample = totalSize > 2*sampleSize;
    if (doSample) {
        size_t valids = 0;
        // Check out a random sample of the possible decoded objects
        for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs, sampleSize)) {
            if (_analysis.isReachable(decFactAbs, fact._negated)) valids++;
        }
        polarity = valids < sampleSize/2 ? SubstitutionConstraint::ANY_VALID : SubstitutionConstraint::NO_INVALID;
        c.fixPolarity(polarity);
    }

    // For each fact decoded from the q-fact:
    for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, eligibleArgs)) {

        // Can the decoded fact occur as is?
        if (_analysis.isReachable(decFactAbs, fact._negated)) {
            if (polarity != SubstitutionConstraint::NO_INVALID)
                c.addValid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
        } else {
            // Fact cannot hold here
            if (polarity != SubstitutionConstraint::ANY_VALID)
                c.addInvalid(SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices));
            continue;
        }

        // If the fact is reachable, is it even invariant?
        if (_analysis.isInvariant(decFactAbs, fact._negated)) {
            // Yes! This precondition is trivially satisfied 
            // with above substitution restrictions
            continue;
        }

        staticallyResolvable = false;
        relevants.insert(decFactAbs);
    }

    if (!staticallyResolvable) {
        if (addQFact) pos.addQFact(factAbs);
        for (const USignature& decFactAbs : relevants) {
            // Decoded fact may be new - initialize as necessary
            initializeFact(pos, decFactAbs);
            if (addQFact) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFact(decFactAbs);
        }
    } // else : encoding the precondition is not necessary!

    if (!doSample) c.fixPolarity();
    return std::optional<SubstitutionConstraint>(std::move(c));
}

bool Planner::addEffect(const USignature& opSig, const Signature& fact, EffectMode mode) {
    Position& pos = (*_layers[_layer_idx])[_pos];
    assert(_pos > 0);
    Position& left = (*_layers[_layer_idx])[_pos-1];
    USignature factAbs = fact.getUnsigned();
    bool isQFact = _htn.hasQConstants(factAbs);

    if (!isQFact) {
        // Invariant fact? --> no need to encode
        if (_analysis.isInvariant(fact)) return true;

        if (mode != INDIRECT) _analysis.addRelevantFact(factAbs);

        // Depending on whether fact supports are encoded for primitive ops only,
        // add the ground fact to the op's support accordingly
        if (_nonprimitive_support || _htn.isAction(opSig)) {
            pos.addFactSupport(fact, opSig);
        } else {
            // Remember that there is some (unspecified) support for this fact
            pos.touchFactSupport(fact);
        }
        
        _analysis.addReachableFact(fact);
        return true;
    }

    // Create the full set of valid decodings for this qfact
    std::vector<int> sorts = _htn.getOpSortsForCondition(factAbs, opSig);
    std::vector<int> sortedArgIndices = SubstitutionConstraint::getSortedSubstitutedArgIndices(_htn, factAbs._args, sorts);
    const bool isConstrained = left.getSubstitutionConstraints().count(opSig);
    
    std::vector<int> involvedQConsts(sortedArgIndices.size());
    for (size_t i = 0; i < sortedArgIndices.size(); i++) involvedQConsts[i] = factAbs._args[sortedArgIndices[i]];
    std::vector<SubstitutionConstraint*> fittingConstrs, otherConstrs;
    if (isConstrained) {
        for (auto& c : left.getSubstitutionConstraints().at(opSig)) {
            if (c.getInvolvedQConstants() == involvedQConsts) fittingConstrs.push_back(&c);
            else if (c.getPolarity() == SubstitutionConstraint::NO_INVALID || c.involvesSupersetOf(involvedQConsts)) 
                otherConstrs.push_back(&c);
        }
    }
    
    bool anyGood = false;
    bool staticallyResolvable = true;
    for (const USignature& decFactAbs : _htn.decodeObjects(factAbs, _htn.getEligibleArgs(factAbs, sorts))) {

        auto path = SubstitutionConstraint::decodingToPath(factAbs._args, decFactAbs._args, sortedArgIndices);

        // Check if this decoding is known to be invalid due to some precondition
        if (isConstrained) {
            bool isValid = true;
            for (const auto& c : fittingConstrs) {
                if (!c->isValid(path, /*sameReference=*/true)) {
                    isValid = false;
                    break;
                }
            }
            if (isValid) for (const auto& c : otherConstrs) {
                if (!c->isValid(path, /*sameReference=*/false)) {
                    isValid = false;
                    break;
                }
            }
            if (!isValid) continue;
        }

        anyGood = true;
        if (_analysis.isInvariant(decFactAbs, fact._negated)) {
            // Effect holds trivially
            continue;
        }

        // Valid effect decoding
        _analysis.addReachableFact(decFactAbs, /*negated=*/fact._negated);
        if (_nonprimitive_support || _htn.isAction(opSig)) {
            pos.addIndirectFactSupport(decFactAbs, fact._negated, opSig, path);
        } else {
            pos.touchFactSupport(decFactAbs, fact._negated);
        }
        if (mode != INDIRECT) {
            if (mode == DIRECT) pos.addQFactDecoding(factAbs, decFactAbs, fact._negated);
            _analysis.addRelevantFact(decFactAbs);
        }
        staticallyResolvable = false;
    }
    // Not a single valid decoding of the effect? -> Invalid effect.
    if (!anyGood) return false;

    if (!staticallyResolvable && mode == DIRECT) pos.addQFact(factAbs);
    
    return true;
}

void Planner::propagateInitialState() {
    assert(_layer_idx > 0);
    // assert(_pos == 0);

    Position& newPos = (*_layers[_layer_idx])[0];
    Position& above = (*_layers[_layer_idx-1])[0];

    _analysis.resetReachability();

    // Propagate TRUE facts
    for (const USignature& fact : above.getTrueFacts()) {
        newPos.addTrueFact(fact);
        _analysis.addInitializedFact(fact);
    }
    for (const USignature& fact : above.getFalseFacts()) {
        newPos.addFalseFact(fact);
        _analysis.addInitializedFact(fact);
    }
}

void Planner::propagateActions(size_t offset) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    Position& above = (*_layers[_layer_idx-1])[_old_pos];

    // Check validity of actions at above position
    std::vector<USignature> actionsToPrune;
    size_t numActionsBefore = above.getActions().size();
    for (const auto& aSig : above.getActions()) {
        const Action& a = _htn.getOpTable().getAction(aSig);

        // Can the action occur here w.r.t. the current state?
        bool valid = _analysis.hasValidPreconditions(a.getPreconditions())
                && _analysis.hasValidPreconditions(a.getExtraPreconditions());

        // If not: forbid the action, i.e., its parent action
        if (!valid) {
            Log::i("Retroactively prune action %s@(%i,%i): no children at offset %i\n", TOSTR(aSig), _layer_idx-1, _old_pos, offset);
            actionsToPrune.push_back(aSig);
        }
    }

    // Prune invalid actions at above position
    for (const auto& aSig : actionsToPrune) {
        _pruning.prune(aSig, _layer_idx-1, _old_pos);
    }
    assert(above.getActions().size() == numActionsBefore - actionsToPrune.size() 
        || Log::e("%i != %i-%i\n", above.getActions().size(), numActionsBefore, actionsToPrune.size()));

    // Propagate remaining (valid) actions from above
    for (auto& aSig : above.getActions()) {
        if (offset < 1) {

            // if (aSig._unique_id == 130 || aSig._unique_id == 128) {
            //     int a = 0;
            // }
            // proper action propagation
            assert(_htn.isFullyGround(aSig));
            if (_params.isNonzero("aar") && !_htn.isActionRepetition(aSig._name_id)) {
                
                // Virtualize child of action
                USignature vChildSig = _htn.getRepetitionOfAction(aSig);

                vChildSig.setNextId();

                newPos.addAction(vChildSig);
                newPos.addExpansion(aSig, vChildSig);
            } else {
                // Treat as a normal action
                newPos.addAction(aSig);
                newPos.addExpansion(aSig, aSig);
            }
        } else {
            // action expands to "blank" at non-zero offsets
            USignature& blankSig = _htn.getBlankActionSig();

            blankSig.setNextId();
            newPos.addAction(blankSig);
            newPos.addExpansion(aSig, blankSig);
        }
    }
}


void Planner::propagateActionsWithUniqueID(size_t offset) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    Position& above = (*_layers[_layer_idx-1])[_old_pos];

    if (above.getLayerIndex() == 7 && above.getPositionIndex() == 42) {
        int dbg = 0;
    }

    // Check validity of actions at above position
    std::vector<USignature> actionsToPrune;
    size_t numActionsBefore = above.getActionsWithUniqueID().size();
    for (const auto& aSig : above.getActionsWithUniqueID()) {
        const Action& a = _htn.getOpTable().getAction(aSig);

        if (aSig._unique_id == 360) {
            int dbg = 0;
        }

        // Can the action occur here w.r.t. the current state?
        bool valid = _analysis.hasValidPreconditions(a.getPreconditions())
                && _analysis.hasValidPreconditions(a.getExtraPreconditions());

        // If not: forbid the action, i.e., its parent action
        if (!valid) {
            Log::i("Retroactively prune action %s@(%i,%i): no children at offset %i\n", TOSTR(aSig), _layer_idx-1, _old_pos, offset);
            actionsToPrune.push_back(aSig);
        }
    }

    // Prune invalid actions at above position
    for (const auto& aSig : actionsToPrune) {
        _pruning.pruneLiftedTreePath(aSig, _layer_idx-1, _old_pos);
    }
    assert(above.getActionsWithUniqueID().size() == numActionsBefore - actionsToPrune.size() 
        || Log::e("%i != %i-%i\n", above.getActionsWithUniqueID().size(), numActionsBefore, actionsToPrune.size()));

    // Propagate remaining (valid) actions from above
    for (auto& aSig : above.getActionsWithUniqueID()) {
        if (offset < 1) {

            if (aSig._unique_id == 360) {
                int a = 0;
            }
            // proper action propagation
            assert(_htn.isFullyGround(aSig));
            if (_params.isNonzero("aar") && !_htn.isActionRepetition(aSig._name_id)) {
                
                // Virtualize child of action
                USignature vChildSig = _htn.getRepetitionOfAction(aSig);

                vChildSig.setNextId();

                if (vChildSig._unique_id == 366) {
                    int a = 0;
                }

                newPos.addAction(vChildSig);
                newPos.addExpansion(aSig, vChildSig);
            } else {
                // Treat as a normal action
                newPos.addAction(aSig);
                newPos.addExpansion(aSig, aSig);
            }
        } else {

            if (aSig._unique_id == 360) {
                int a = 0;
            }
            // action expands to "blank" at non-zero offsets
            USignature& blankSig = _htn.getBlankActionSig();

            blankSig.setNextId();
            blankSig.setShadowAction(true);

            newPos.addAction(blankSig);
            newPos.addExpansion(aSig, blankSig);

        }
    }
}

void Planner::propagateReductions(size_t offset) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    Position& above = (*_layers[_layer_idx-1])[_old_pos];

    NodeHashMap<USignature, USigSetUniqueID, USignatureHasher> subtaskToParents;
    NodeHashSet<USignature, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> reductionsWithChildren;

    // Collect all possible subtasks and remember their possible parents
    for (const auto& rSig : above.getReductions()) {

        const Reduction r = _htn.getOpTable().getReduction(rSig);
        
        if (offset < r.getSubtasks().size()) {
            // Proper expansion
            const USignature& subtask = r.getSubtasks()[offset];
            subtaskToParents[subtask].insert(rSig);
        } else {
            // Blank
            reductionsWithChildren.insert(rSig);
            // const USignature& blankSig = _htn.getBlankActionSig();
            USignature& blankSig = _htn.getBlankActionSig();

            blankSig.setNextId();
            if (offset > 0) {
                blankSig.setShadowAction(true);
            } else {
                blankSig.setFirstChildOfReduction(true);
            }

            // Get the number of blank actions already in the position
            // int numBlankActions = 0;
            // for (const auto& aSig: newPos.getActions()) {
            //     if (aSig._name_id == 1) {
            //         numBlankActions++;
            //     }
            // }
            // // Create a copy of the blank action
            // USignature blankSigWithRepetition = USignature(blankSig._name_id, blankSig._args);
            // // Set the number of repetition 
            // blankSigWithRepetition.setRepetition(numBlankActions);
            // newPos.addAction(blankSigWithRepetition);
            // newPos.addExpansion(rSig, blankSigWithRepetition);

            newPos.addAction(blankSig);
            newPos.addExpansion(rSig, blankSig);
        }
    }

    // Iterate over all possible subtasks
    for (const auto& [subtask, parents] : subtaskToParents) {

        // Calculate all possible actions fitting the subtask.
        auto allActions = instantiateAllActionsOfTask(subtask);

        // Any reduction(s) fitting the subtask?
        for (USignature& subRSig : instantiateAllReductionsOfTask(subtask)) {

            if (_htn.isAction(subRSig)) {
                // Actually an action, not a reduction: remember for later
                allActions.push_back(subRSig);
                continue;
            }

            // TEST
            subRSig.setNextId();
            if (offset == 0) {
                subRSig.setFirstChildOfReduction(true);
            }
            // END TEST

            const Reduction& subR = _htn.getOpTable().getReduction(subRSig);
            
            assert(_htn.isReduction(subRSig) && subRSig == subR.getSignature() && _htn.isFullyGround(subRSig));
            
            newPos.addReduction(subRSig);
            newPos.addExpansionSize(subR.getSubtasks().size());

            for (const auto& rSig : parents) {

                if (rSig._unique_id == 29) {
                    int dbg = 0;
                }

                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, subRSig);

                if (newPos.getPositionIndex() == 0 && newPos.getLayerIndex() == 4) {

                    // Print all the expansions
                    for (auto& [rSig, exps] : newPos.getExpansions()) {
                        for (USignature aSig : exps) {
                            Log::i("Expansion of %s(%i): %s(%i)\n", Names::to_SMT_string(rSig, false).c_str(), rSig._unique_id, Names::to_SMT_string(aSig, false).c_str(), aSig._unique_id);
                        }
                    }

                    // if (newPos.getExpansions().count(rSig) == 0) {
                    //     int a = 0;
                    // }
                    // // Print all the expansion of 29
                    // for (USignature aSig : newPos.getExpansions().at(rSig)) {
                    //     Log::i("Expansion of 29: %s\n", Names::to_SMT_string(aSig, true).c_str());
                    // }
                    int c = 0;
                }


                // if (rSig._unique_id == 1) {
                //     int dbg = 0;
                //     // Display the parent to check something
                //     for (USignature aSig : newPos.getPredecessorsWithUniqueID().at(subRSig._unique_id)) {
                //         if (aSig._unique_id == 1) {
                //             Log::i("Parent: %s\n", Names::to_SMT_string(aSig, true).c_str());
                //         }
                //     }
                // }

                // if (USE_LIFTED_TREE_PATH) {
                //     // Needs to inherit the domain from the parent
                //     _htn.inheritQConstFromParent(subRSig, rSig);
                //     if (offset == 0) {
                //         // Inherit the substitution constrains from the parent
                //                         // Inherit as well all the substitution constains from the parent reduction
                //         if (above.getSubstitutionConstraints().count(rSig) > 0) {
                //             for (SubstitutionConstraint constraint : above.getSubstitutionConstraints().at(rSig)) {
                //                 newPos.addSubstitutionConstraint(subRSig, std::move(constraint));
                //             }
                //         }
                //     }
                // }
            }
        }

        // Any action(s) fitting the subtask?
        for (USignature& aSig : allActions) {

            // TEST
            aSig.setNextId();
            if (offset == 0) {
                aSig.setFirstChildOfReduction(true);
            }
            // END TEST

            assert(_htn.isFullyGround(aSig));
            newPos.addAction(aSig);

            if (newPos.getLayerIndex() == 4 && newPos.getPositionIndex() == 17) {
                Log::i("Flow: %s\n", Names::to_SMT_string(aSig, true).c_str());
                // ACTION__drive-truck_0-Q_3-12_location%0_4e6d4ef15ccc6897-Q_2-8_location%0_e4354a9774db1231
                int dbg = 0;
            }

            for (const auto& rSig : parents) {
                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, aSig);

                if (USE_LIFTED_TREE_PATH) {
                    // Needs to inherit the domain from the parent
                    _htn.inheritQConstFromParent(aSig, rSig);

                    // if (above.getSubstitutionConstraints().count(rSig) > 0) {
                    //     for (SubstitutionConstraint constraint : above.getSubstitutionConstraints().at(rSig)) {
                    //         newPos.addSubstitutionConstraint(aSig, std::move(constraint));
                    //     }
                    // }
                }
            }

            // TESTETSTEST Iterate over all actions
            // for (USignature& aSig : newPos.getActions()) {
            //     int dbg = 0;
            // }

            // for (USignature& aSig : allActions) {
            //     int dbg = 0;
            // }

            // // Try a test here
            // for (auto& [parent, children] : newPos.getExpansions()) {
            //     // Iterate over all childre
            //     for (USignature& child : children) {
            //         std::string childCurrentName = Names::to_SMT_string(child, false);
            //         Log::i("Flow: %s\n", childCurrentName.c_str());
            //     }
            // }
        }
    }


    // Print all the expansions
    if (newPos.getPositionIndex() == 0 && newPos.getLayerIndex() == 4) {
        for (auto& [rSig, exps] : newPos.getExpansions()) {
            for (USignature aSig : exps) {
                Log::i("Expansion of (%i): (%i)\n", rSig._unique_id, aSig._unique_id);
            }
        }

        int ebg = 0;
    }

    // Check if any reduction has no valid children at all
    for (const auto& rSig : above.getReductions()) {
        if (!reductionsWithChildren.count(rSig)) {
            Log::i("Retroactively prune reduction %s@(%i,%i): no children at offset %i\n", 
                    TOSTR(rSig), _layer_idx-1, _old_pos, offset);
            if (USE_LIFTED_TREE_PATH) {
                _pruning.pruneLiftedTreePath(rSig, _layer_idx-1, _old_pos);
            } else {
                _pruning.prune(rSig, _layer_idx-1, _old_pos);
            }
        }
    }
}


void Planner::propagateReductionsWithUniqueID(size_t offset) {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    Position& above = (*_layers[_layer_idx-1])[_old_pos];

    NodeHashMap<USignature, USigSetUniqueID, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> subtaskToParents;
    NodeHashSet<USignature, USignatureHasherWithUniqueID, USignatureEqualityWithUniqueID> reductionsWithChildren;

    // Collect all possible subtasks and remember their possible parents
    for (const auto& rSig : above.getReductionsWithUniqueID()) {

        const Reduction r = _htn.getOpTable().getReduction(rSig);
        
        if (offset < r.getSubtasks().size()) {
            // Proper expansion
            USignature subtask = r.getSubtasks()[offset];
            subtask.setNextId();
            subtaskToParents[subtask].insert(rSig);
        } else {
            // Blank
            reductionsWithChildren.insert(rSig);
            // const USignature& blankSig = _htn.getBlankActionSig();
            USignature& blankSig = _htn.getBlankActionSig();

            blankSig.setNextId();
            if (offset > 0) {
                blankSig.setShadowAction(true);
            } else {
                blankSig.setFirstChildOfReduction(true);
            }

            // Get the number of blank actions already in the position
            // int numBlankActions = 0;
            // for (const auto& aSig: newPos.getActions()) {
            //     if (aSig._name_id == 1) {
            //         numBlankActions++;
            //     }
            // }
            // // Create a copy of the blank action
            // USignature blankSigWithRepetition = USignature(blankSig._name_id, blankSig._args);
            // // Set the number of repetition 
            // blankSigWithRepetition.setRepetition(numBlankActions);
            // newPos.addAction(blankSigWithRepetition);
            // newPos.addExpansion(rSig, blankSigWithRepetition);

            newPos.addAction(blankSig);
            newPos.addExpansion(rSig, blankSig);
        }
    }

    // Iterate over all possible subtasks
    for (const auto& [subtask, parents] : subtaskToParents) {

        // Calculate all possible actions fitting the subtask.
        auto allActions = instantiateAllActionsOfTask(subtask);

        // Any reduction(s) fitting the subtask?
        for (USignature& subRSig : instantiateAllReductionsOfTask(subtask)) {

            if (_htn.isAction(subRSig)) {
                // Actually an action, not a reduction: remember for later
                allActions.push_back(subRSig);
                continue;
            }

            // TEST
            subRSig.setNextId();
            if (offset == 0) {
                subRSig.setFirstChildOfReduction(true);
            }
            // END TEST

            const Reduction& subR = _htn.getOpTable().getReduction(subRSig);
            
            assert(_htn.isReduction(subRSig) && subRSig == subR.getSignature() && _htn.isFullyGround(subRSig));
            
            newPos.addReduction(subRSig);
            newPos.addExpansionSize(subR.getSubtasks().size());

            for (const auto& rSig : parents) {

                if (rSig._unique_id == 29) {
                    int dbg = 0;
                }

                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, subRSig);

                if (newPos.getPositionIndex() == 0 && newPos.getLayerIndex() == 4) {

                    // Print all the expansions
                    for (auto& [rSig, exps] : newPos.getExpansions()) {
                        for (USignature aSig : exps) {
                            Log::i("Expansion of %s(%i): %s(%i)\n", Names::to_SMT_string(rSig, false).c_str(), rSig._unique_id, Names::to_SMT_string(aSig, false).c_str(), aSig._unique_id);
                        }
                    }

                    // if (newPos.getExpansions().count(rSig) == 0) {
                    //     int a = 0;
                    // }
                    // // Print all the expansion of 29
                    // for (USignature aSig : newPos.getExpansions().at(rSig)) {
                    //     Log::i("Expansion of 29: %s\n", Names::to_SMT_string(aSig, true).c_str());
                    // }
                    int c = 0;
                }


                // if (rSig._unique_id == 1) {
                //     int dbg = 0;
                //     // Display the parent to check something
                //     for (USignature aSig : newPos.getPredecessorsWithUniqueID().at(subRSig._unique_id)) {
                //         if (aSig._unique_id == 1) {
                //             Log::i("Parent: %s\n", Names::to_SMT_string(aSig, true).c_str());
                //         }
                //     }
                // }

                if (USE_LIFTED_TREE_PATH) {
                    // Needs to inherit the domain from the parent
                    _htn.inheritQConstFromParent(subRSig, rSig);
                    // if (offset == 0) {
                        // // Inherit the substitution constrains from the parent
                        //                 // Inherit as well all the substitution constains from the parent reduction
                        // if (above.getSubstitutionConstraints().count(rSig) > 0) {
                        //     for (SubstitutionConstraint constraint : above.getSubstitutionConstraints().at(rSig)) {
                        //         newPos.addSubstitutionConstraint(subRSig, std::move(constraint));
                        //     }
                        // }
                    // }
                }
            }
        }

        // Any action(s) fitting the subtask?
        for (USignature& aSig : allActions) {

            // TEST
            aSig.setNextId();
            if (offset == 0) {
                aSig.setFirstChildOfReduction(true);
            }
            // END TEST

            assert(_htn.isFullyGround(aSig));
            newPos.addAction(aSig);

            if (newPos.getLayerIndex() == 4 && newPos.getPositionIndex() == 17) {
                Log::i("Flow: %s\n", Names::to_SMT_string(aSig, true).c_str());
                // ACTION__drive-truck_0-Q_3-12_location%0_4e6d4ef15ccc6897-Q_2-8_location%0_e4354a9774db1231
                int dbg = 0;
            }

            for (const auto& rSig : parents) {
                reductionsWithChildren.insert(rSig);
                newPos.addExpansion(rSig, aSig);

                if (USE_LIFTED_TREE_PATH) {
                    // Needs to inherit the domain from the parent
                    _htn.inheritQConstFromParent(aSig, rSig);

                    // if (above.getSubstitutionConstraints().count(rSig) > 0) {
                    //     for (SubstitutionConstraint constraint : above.getSubstitutionConstraints().at(rSig)) {
                    //         newPos.addSubstitutionConstraint(aSig, std::move(constraint));
                    //     }
                    // }
                }
            }

            // TESTETSTEST Iterate over all actions
            // for (USignature& aSig : newPos.getActions()) {
            //     int dbg = 0;
            // }

            // for (USignature& aSig : allActions) {
            //     int dbg = 0;
            // }

            // // Try a test here
            // for (auto& [parent, children] : newPos.getExpansions()) {
            //     // Iterate over all childre
            //     for (USignature& child : children) {
            //         std::string childCurrentName = Names::to_SMT_string(child, false);
            //         Log::i("Flow: %s\n", childCurrentName.c_str());
            //     }
            // }
        }
    }


    // Print all the expansions
    if (newPos.getPositionIndex() == 0 && newPos.getLayerIndex() == 4) {
        for (auto& [rSig, exps] : newPos.getExpansions()) {
            for (USignature aSig : exps) {
                Log::i("Expansion of (%i): (%i)\n", rSig._unique_id, aSig._unique_id);
            }
        }

        int ebg = 0;
    }

    // Check if any reduction has no valid children at all
    for (const auto& rSig : above.getReductionsWithUniqueID()) {
        if (!reductionsWithChildren.count(rSig)) {
            Log::i("Retroactively prune reduction %s@(%i,%i): no children at offset %i\n", 
                    TOSTR(rSig), _layer_idx-1, _old_pos, offset);
            if (USE_LIFTED_TREE_PATH) {
                _pruning.pruneLiftedTreePath(rSig, _layer_idx-1, _old_pos);
            } else {
                _pruning.prune(rSig, _layer_idx-1, _old_pos);
            }
        }
    }
}

std::vector<USignature> Planner::instantiateAllActionsOfTask(const USignature& task) {
    std::vector<USignature> result;

    if (!_htn.isAction(task)) return result;
    
    for (USignature& sig : _instantiator.getApplicableInstantiations(_htn.toAction(task._name_id, task._args))) {
        //Log::d("ADDACTION %s ?\n", TOSTR(action.getSignature()));
        Action action = _htn.toAction(sig._name_id, sig._args);

        // Rename any remaining variables in each action as unique q-constants,
        action = _htn.replaceVariablesWithQConstants(action, _analysis.getReducedArgumentDomains(action), _layer_idx, _pos);

        // Remove any contradictory ground effects that were just created
        action.removeInconsistentEffects();

        // Check validity
        if (!_htn.isFullyGround(action.getSignature())) continue;
        if (!_htn.hasConsistentlyTypedArgs(sig)) continue;
        if (!_analysis.hasValidPreconditions(action.getPreconditions())) continue;
        if (!_analysis.hasValidPreconditions(action.getExtraPreconditions())) continue;
        
        // Action is valid
        sig = action.getSignature();
        _htn.getOpTable().addAction(action);
        result.push_back(action.getSignature());
    }
    return result;
}

std::vector<USignature> Planner::instantiateAllReductionsOfTask(const USignature& task) {
    std::vector<USignature> result;

    if (!_htn.hasReductions(task._name_id)) return result;

    // Filter and minimally instantiate methods
    // applicable in current (super)state
    for (int redId : _htn.getReductionIdsOfTaskId(task._name_id)) {
        Reduction r = _htn.getReductionTemplate(redId);

        if (_htn.isReductionPrimitivizable(redId)) {
            const Action& a = _htn.getReductionPrimitivization(redId);

            std::vector<Substitution> subs = Substitution::getAll(r.getTaskArguments(), task._args);
            for (const Substitution& s : subs) {
                USignature primSig = a.getSignature().substitute(s);
                for (const auto& sig : instantiateAllActionsOfTask(primSig)) {
                    result.push_back(sig);
                }
            }
            continue;
        }

        std::vector<Substitution> subs = Substitution::getAll(r.getTaskArguments(), task._args);
        for (const Substitution& s : subs) {
            for (const auto& entry : s) assert(entry.second != 0);

            Reduction rSub = r.substituteRed(s);
            USignature origSig = rSub.getSignature();
            if (!_htn.hasConsistentlyTypedArgs(origSig)) continue;
            
            for (USignature& red : _instantiator.getApplicableInstantiations(rSub)) {
                auto rOpt = createValidReduction(red, task);
                if (rOpt) result.push_back(rOpt.value().getSignature());
            }
        }
    }
    return result;
}

std::optional<Reduction> Planner::createValidReduction(const USignature& sig, const USignature& task) {
    std::optional<Reduction> rOpt;

    // Rename any remaining variables in each action as new, unique q-constants 
    Reduction red = _htn.toReduction(sig._name_id, sig._args);
    auto domains = _analysis.getReducedArgumentDomains(red);
    red = _htn.replaceVariablesWithQConstants(red, domains, _layer_idx, _pos);

    // Check validity
    bool isValid = true;
    if (task._name_id >= 0 && red.getTaskSignature() != task) isValid = false;
    else if (!_htn.isFullyGround(red.getSignature())) isValid = false;
    else if (!_htn.hasConsistentlyTypedArgs(red.getSignature())) isValid = false;
    else if (!_analysis.hasValidPreconditions(red.getPreconditions())) isValid = false;
    else if (!_analysis.hasValidPreconditions(red.getExtraPreconditions())) isValid = false;

    if (isValid) {
        _htn.getOpTable().addReduction(red);
        rOpt.emplace(red);
    }
    return rOpt;
}

void Planner::initializeNextEffects() {
    Position& newPos = (*_layers[_layer_idx])[_pos];
    
    // For each possible operation effect:
    const USigSet* ops[2] = {&newPos.getActions(), &newPos.getReductions()};
    bool isAction = true;
    for (const auto& set : ops) {
        for (const auto& aSig : *set) {
            // std::cout << "METHOD or ACTION: " << Names::to_string(aSig) << std::endl;
            // std::cout << "Possible facts changed: " << std::endl;
            const SigSet& pfc = _analysis.getPossibleFactChanges(aSig, FactAnalysis::FULL, isAction ? FactAnalysis::ACTION : FactAnalysis::REDUCTION);
            int i = 0;
            for (const Signature& eff : pfc) {

                if (!_htn.hasQConstants(eff._usig)) {
                    // New ground fact: set before the action may happen

                    // std::cout << "(" << i << ") " << Names::to_string(eff) << std::endl;
                    i++;
                    initializeFact(newPos, eff._usig); 
                } else {
                    std::vector<int> sorts = _htn.getOpSortsForCondition(eff._usig, aSig);
                    for (const USignature& decEff : _htn.decodeObjects(eff._usig, _htn.getEligibleArgs(eff._usig, sorts))) {           
                        // New ground fact: set before the action may happen
                        // std::cout << "(" << i << ") " << Names::to_string(decEff) << std::endl;
                        i++;
                        initializeFact(newPos, decEff);
                    }
                }
            }
        }
        isAction = false;
    }
}

void Planner::initializeNextEffectsPrimitiveTree(Position& newPos) {
    
    // For each possible operation effect:
    for (const auto& aSig : newPos.getActionsInPrimitiveTree()) {
        std::cout << "METHOD or ACTION: " << Names::to_string(aSig) << std::endl;
        // std::cout << "Possible facts changed: " << std::endl;
        const SigSet& pfc = _analysis.getPossibleFactChanges(aSig, FactAnalysis::FULL, FactAnalysis::ACTION);
        int i = 0;
        for (const Signature& eff : pfc) {

            if (!_htn.hasQConstants(eff._usig)) {
                // New ground fact: set before the action may happen

                std::cout << "(" << i << ") " << Names::to_string(eff) << std::endl;
                i++;
                initializeFact(newPos, eff._usig); 
            } else {
                std::vector<int> sorts = _htn.getOpSortsForCondition(eff._usig, aSig);
                for (const USignature& decEff : _htn.decodeObjects(eff._usig, _htn.getEligibleArgs(eff._usig, sorts))) {           
                    // New ground fact: set before the action may happen
                    // std::cout << "(" << i << ") " << Names::to_string(decEff) << std::endl;
                    i++;
                    initializeFact(newPos, decEff);
                }
            }
        }
    }
}

void Planner::initializeFact(Position& newPos, const USignature& fact) {
    assert(!_htn.hasQConstants(fact));

    // Has the fact already been defined? -> Not new!
    if (_analysis.isInitialized(fact)) return;

    _analysis.addInitializedFact(fact);

    if (_analysis.isReachable(fact, /*negated=*/true)) newPos.addFalseFact(fact);
    else newPos.addTrueFact(fact);
}

void Planner::addQConstantTypeConstraints(const USignature& op) {
    // Add type constraints for q constants
    std::vector<TypeConstraint> cs = _htn.getQConstantTypeConstraints(op);
    // Add to this position's data structure
    for (const TypeConstraint& c : cs) {
        (*_layers[_layer_idx])[_pos].addQConstantTypeConstraint(op, c);
    }
}

void Planner::clearDonePositions(int offset) {

    Position* positionToClearLeft = nullptr;
    if (_pos == 0 && _layer_idx > 0) {
        positionToClearLeft = &_layers.at(_layer_idx-1)->last();
    } else if (_pos > 0) positionToClearLeft = &_layers.at(_layer_idx)->at(_pos-1);
    if (positionToClearLeft != nullptr) {
        Log::v("  Freeing some memory of (%i,%i) ...\n", positionToClearLeft->getLayerIndex(), positionToClearLeft->getPositionIndex());
        positionToClearLeft->clearAtPastPosition();
    }

    if (_layer_idx == 0 || offset > 0) return;
    
    Position* positionToClearAbove = nullptr;
    if (_old_pos == 0) {
        // Clear rightmost position of "above above" layer
        if (_layer_idx > 1) positionToClearAbove = &_layers.at(_layer_idx-2)->at(_layers.at(_layer_idx-2)->size()-1);
    } else {
        // Clear previous parent position of "above" layer
        positionToClearAbove = &_layers.at(_layer_idx-1)->at(_old_pos-1);
    }
    if (positionToClearAbove != nullptr) {
        Log::v("  Freeing most memory of (%i,%i) ...\n", positionToClearAbove->getLayerIndex(), positionToClearAbove->getPositionIndex());
        positionToClearAbove->clearAtPastLayer();
    }
}

void Planner::checkTermination() {
    bool exitSet = SignalManager::isExitSet();
    bool cancelOpt = cancelOptimization();
    if (exitSet) {
        if (_has_plan) {
            Log::i("Termination signal caught - printing last found plan.\n");
            _plan_writer.outputPlan(_plan);
        } else {
            Log::i("Termination signal caught.\n");
        }
    } else if (cancelOpt) {
        Log::i("Cancelling optimization according to provided limit.\n");
        _plan_writer.outputPlan(_plan);
    } else if (_time_at_first_plan == 0 
            && _init_plan_time_limit > 0
            && Timer::elapsedSeconds() > _init_plan_time_limit) {
        Log::i("Time limit to find an initial plan exceeded.\n");
        exitSet = true;
    }
    if (exitSet || cancelOpt) {
        printStatistics();
        Log::i("Exiting happily.\n");
        exit(0);
    }
}

bool Planner::cancelOptimization() {
    return _time_at_first_plan > 0 &&
            _optimization_factor > 0 &&
            Timer::elapsedSeconds() > (1+_optimization_factor) * _time_at_first_plan;
}

int Planner::getTerminateSatCall() {
    // Breaking out of first SAT call after some time
    if (_sat_time_limit > 0 &&
        _enc.getTimeSinceSatCallStart() > _sat_time_limit) {
        return 1;
    }
    // Termination due to initial planning time limit (-T)
    if (_time_at_first_plan == 0 &&
        _init_plan_time_limit > 0 &&
        Timer::elapsedSeconds() > _init_plan_time_limit) {
        return 1;
    }
    // Plan length optimization limit hit
    if (cancelOptimization()) {
        return 1;
    }
    // Termination by interruption signal
    if (SignalManager::isExitSet()) return 1;
    return 0;
}

void Planner::printStatistics() {
    _enc.printStatistics();
    Log::i("# instantiated positions: %i\n", _num_instantiated_positions);
    Log::i("# instantiated actions: %i\n", _num_instantiated_actions);
    Log::i("# instantiated reductions: %i\n", _num_instantiated_reductions);
    Log::i("# introduced pseudo-constants: %i\n", _htn.getNumberOfQConstants());
    Log::i("# retroactive prunings: %i\n", _pruning.getNumRetroactivePunings());
    Log::i("# retroactively pruned operations: %i\n", _pruning.getNumRetroactivelyPrunedOps());
    Log::i("# dominated operations: %i\n", _domination_resolver.getNumDominatedOps());
}
