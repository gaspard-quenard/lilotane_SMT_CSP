#ifndef DOMPASCH_LILOTANE_PRIMITIVE_TREE_POS_H
#define DOMPASCH_LILOTANE_PRIMITIVE_TREE_POS_H

#include <vector>
#include <set>

#include "util/hashmap.h"
#include "data/signature.h"
#include "util/names.h"
#include "sat/variable_domain.h"
#include "util/log.h"
#include "sat/literal_tree.h"
#include "data/substitution_constraint.h"

class PrimitiveTreePos {


    private:
        NodeHashSet<PositionedUSig, PositionedUSigHasher> actions;
        NodeHashMap<PositionedUSig, NodeHashSet<PositionedUSig, PositionedUSigHasher>, PositionedUSigHasher> nextsOfActions;


public:
    PrimitiveTreePos() = default;
    void addAction(PositionedUSig action);
    NodeHashSet<PositionedUSig, PositionedUSigHasher> getActions();

    void addNextAction(PositionedUSig action, PositionedUSig next);
    NodeHashSet<PositionedUSig, PositionedUSigHasher> getNextsOfAction(PositionedUSig action);

    PositionedUSig getActionByID(int id);
};


#endif