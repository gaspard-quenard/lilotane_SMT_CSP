#include "data/primitive_tree.h"


PrimitiveTree::PrimitiveTree(size_t layer_idx): _layer_idx(layer_idx) {}


size_t PrimitiveTree::size() const {return _content.size();}
PrimitiveTreePos& PrimitiveTree::operator[](size_t pos) {assert(pos < size()); return _content[pos];}
PrimitiveTreePos& PrimitiveTree::at(size_t pos) {return (*this)[pos];}
PrimitiveTreePos& PrimitiveTree::last() {return (*this)[size()-1];}

void PrimitiveTree::createNewPos() {
    PrimitiveTreePos newPos = PrimitiveTreePos();
    this->_content.push_back(newPos);
}

void PrimitiveTree::prettyDisplay() {
    Log::i("==== Primitive Tree ====\n");
    for (int i = 0; i < this->_content.size(); i++) {
        Log::i("At position %i\n", i);
        PrimitiveTreePos pos = this->_content[i];
        NodeHashSet<PositionedUSig, PositionedUSigHasher> actionsInPos = pos.getActions();
        for (PositionedUSig action : actionsInPos) {
            Log::i("    %s\n", Names::to_SMT_string(action.usig).c_str(), true);
            // Indicate all the nexts
            NodeHashSet<PositionedUSig, PositionedUSigHasher> nexts = _content[i].getNextsOfAction(action);
            for (PositionedUSig next : nexts) {
                Log::i("        -> %s\n", Names::to_SMT_string(next.usig).c_str(), true);
            }
        }
        
    }
    Log::i("=====================\n");
}