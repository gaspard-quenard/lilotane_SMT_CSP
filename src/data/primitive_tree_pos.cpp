#include "data/primitive_tree_pos.h"


void PrimitiveTreePos::addAction(PositionedUSig action) {
    this->actions.insert(action);
}

NodeHashSet<PositionedUSig, PositionedUSigHasher> PrimitiveTreePos::getActions() {
    return this->actions;
}

void PrimitiveTreePos::addNextAction(PositionedUSig action, PositionedUSig next) {
    this->nextsOfActions[action].insert(next);
}


PositionedUSig PrimitiveTreePos::getActionByID(int id) {
    for (PositionedUSig action : this->getActions()) {
        if (action.usig._unique_id == id) {
            return action;
        }
    }

    // SHOULD NOT HAPPENEND
    assert (0 != 0);
    return Sig::NONE_POS_SIG;
}


NodeHashSet<PositionedUSig, PositionedUSigHasher> PrimitiveTreePos::getNextsOfAction(PositionedUSig action) {
    if (this->nextsOfActions.find(action) == this->nextsOfActions.end()) {
        return NodeHashSet<PositionedUSig, PositionedUSigHasher>();
    }
    return this->nextsOfActions[action];
}