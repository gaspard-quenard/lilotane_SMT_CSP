
#ifndef DOMPASCH_TREE_REXX_VARIABLE_POSITION_H
#define DOMPASCH_TREE_REXX_VARIABLE_POSITION_H

#include "util/params.h"
#include "data/signature.h"

class VariablePosition {

private:
    static int _running_pos_var_id;

public:

    static int nextVar();
    static int getMaxVar();
};

#endif