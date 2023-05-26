#ifndef DOMPASCH_LILOTANE_PRIMITIVE_TREE_H
#define DOMPASCH_LILOTANE_PRIMITIVE_TREE_H

#include <vector>
#include <set>

#include "util/hashmap.h"
#include "data/signature.h"
#include "util/names.h"
#include "sat/variable_domain.h"
#include "util/log.h"
#include "sat/literal_tree.h"
#include "data/substitution_constraint.h"
#include "data/primitive_tree_pos.h"

class PrimitiveTree {


    private:
        size_t _layer_idx;
        std::vector<PrimitiveTreePos> _content;


public:
    PrimitiveTree(size_t layer_idx);

    size_t size() const;
    void createNewPos();
    void prettyDisplay();

    PrimitiveTreePos& at(size_t pos);
    PrimitiveTreePos& operator[](size_t pos);
    PrimitiveTreePos& last();

};


#endif