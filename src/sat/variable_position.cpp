
#include "variable_position.h"

#include "util/log.h"
#include "util/names.h"

int VariablePosition::_running_pos_var_id = 1;

int VariablePosition::nextVar() {
    return _running_pos_var_id++;
}
int VariablePosition::getMaxVar() {
    return _running_pos_var_id-1;
}