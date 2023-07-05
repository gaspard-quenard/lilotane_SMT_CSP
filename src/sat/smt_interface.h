
#ifndef DOMPASCH_LILOTANE_SMT_INTERFACE_H
#define DOMPASCH_LILOTANE_SMT_INTERFACE_H

#include <initializer_list>
#include <fstream>
#include <string>
#include <iostream>
#include <assert.h>
#include <vector>
#include <string>
#include <cstring>
#include <chrono>

#include "util/params.h"
#include "util/log.h"
#include "util/names.h"
#include "sat/variable_domain.h"
#include "sat/encoding_statistics.h"
#include "cvc5.h"
#include "z3++.h"
#include "unordered_set"

extern "C"
{
#include "sat/ipasir.h"
}

struct NameAndLayerElement
{
    std::string name;
    std::string full_name;
    int layer;
    int layerElement;
    int ltp_pos;
    bool isSubstitute = false;
    cvc5::Term cvc5Term;
    cvc5::Term cvc5TermNeg;
    z3::expr z3Term;
    z3::expr z3TermNeg;
};

struct substituteVar
{
    int qConstId;
    int trueConstId;
};

class SmtInterface
{

private:
    Parameters &_params;
    void *_solver;
    std::ofstream _out;
    EncodingStatistics &_stats;
    std::vector<NameAndLayerElement> dict_var_id_to_name;
    std::string clauseLine;

    const bool _is_used;

    bool useCVC5;

    bool _began_line = false;

    int num_objects;

    const bool _print_formula;
    const std::string _formula_file;
    const bool use_one_var_for_qconst;
    const bool use_enum_sort_for_objects;

    std::string _logic;

    // Structure for CVC5
    cvc5::Solver _solverCVC5;
    std::vector<cvc5::Term> termsLine;
    std::vector<cvc5::Term> assumptions;
    FlatHashMap<int, cvc5::Term> _mapConstantToTerm;
    FlatHashMap<int, cvc5::Term> _mapQConstIdToTerm;
    cvc5::Sort boolSort = _solverCVC5.getBooleanSort();
    cvc5::Sort intSort = _solverCVC5.getIntegerSort();
    cvc5::Sort sort_all_objects;
    cvc5::Datatype datatype_all_objetcs;

    // Structure for Z3
    z3::context _contextZ3;
    z3::solver _solverZ3;
    z3::model _modelZ3;
    z3::expr_vector termsLines_Z3;
    z3::expr_vector assumptions_Z3;
    FlatHashMap<int, int> _mapConstantIdToExpressionId;
    z3::expr_vector expressionObjects;
    FlatHashMap<int, int> _mapQConstIdToToExpressionId;
    z3::expr_vector expressionQConst;

    z3::func_decl_vector enum_consts;
    z3::func_decl_vector enum_testers;
    z3::sort sort_all_objects_Z3;

    std::vector<int> _last_assumptions;
    std::vector<int> _no_decision_variables;

    FlatHashMap<int, substituteVar> _allSubstituteVars;

public:
    SmtInterface(bool is_used, Parameters &params, EncodingStatistics &stats, NodeHashMap<int, FlatHashSet<int>> constants_by_sort) : 
            _is_used(is_used), 
            _params(params), 
            _stats(stats), 
            _contextZ3(), 
            _solverZ3(initializeSolverZ3(params)), 
            _modelZ3(_contextZ3), 
            termsLines_Z3(_contextZ3), 
            assumptions_Z3(_contextZ3), 
            expressionObjects(_contextZ3), 
            expressionQConst(_contextZ3), 
            enum_consts(_contextZ3), 
            enum_testers(_contextZ3), 
            sort_all_objects_Z3(_contextZ3),
            _print_formula(_params.getParam("wf") != ""),
            _formula_file(params.getParam("wf")),
            use_one_var_for_qconst(params.isNonzero("one_var_qconst")),
            use_enum_sort_for_objects(params.isNonzero("use_enum_sort"))
    {

        if (!is_used)
        {
            _stats.is_used = false;
            return;
        }


        std::string paramSolver = params.getParam("smtSolver");  
        if (paramSolver.compare("cvc5") == 0)
        {
            std::cout << "Use SMT solver CVC5" << std::endl;
            useCVC5 = true;
        } else if (paramSolver.compare("z3") == 0)
        {
            std::cout << "Use SMT solver Z3" << std::endl;
            useCVC5 = false;
        } else {
            std::cout << "Error: SMT solver not supported (supported solver: cvc5 or z3)" << std::endl;
            std::cout << "Use default solver: z3" << std::endl;
            useCVC5 = false;
        }

        if (!use_one_var_for_qconst)
        {
            if (useCVC5)
            {
                _logic = "QF_SAT";
                _solverCVC5.setLogic(_logic);
            }
        }
        else
        {
            if (useCVC5)
            {
                if (use_enum_sort_for_objects) {
                    _logic = "QF_DT";
                    _solverCVC5.setLogic(_logic);
                }   
                else {
                    _logic = "QF_LIA";
                    _solverCVC5.setLogic(_logic);
                }
            }
        }

        if (useCVC5)
        {
            _solverCVC5.setOption("produce-models", "true");
            _solverCVC5.setOption("incremental", "true");
        }

        // const char * enum_names[] = {"a", "b", "c"};
        // sort_all_objects_Z3 = _contextZ3.enumeration_sort("Objects", 3, enum_names, enum_consts, enum_testers);

        // z3::expr a = enum_consts[0u]();
        // z3::expr b = enum_consts[1u]();
        // z3::expr x = _contextZ3.constant("x", sort_all_objects_Z3);
        // z3::expr test = (x==a) && (x==b);

        // std::cout << sort_all_objects_Z3 << std::endl;
        // std::cout << "1: " << test << std::endl;

        // _solverZ3.add(test);

        // std::cout << "2: " << _solverZ3.to_smt2() << std::endl;

        if (use_one_var_for_qconst)
        {
            // First, get an unique value for each constant object
            FlatHashSet<int> allConstants;

            for (const auto &[sort, constants] : constants_by_sort)
            {
                allConstants.insert(constants.begin(), constants.end());
            }

            std::cout << "All uniques constants" << std::endl;
            for (const auto &constant : allConstants)
            {
                std::cout << "Constant: " << constant << " " << Names::to_string(constant) << std::endl;
            }

            num_objects = allConstants.size();

            // Here, we have two choices:
            // either we make an enum for each arg of a  pseudo_fact with all the possible values that they can take
            // or we define each constant as an unique integer and we add a constraint that the value of the argument
            // is in the range of the possible values for that pseudo_fact

            ///// TEST DATATYPE CVC5 /////////////

            // cvc5::DatatypeDecl colorDecl = _solverCVC5.mkDatatypeDecl("Color");
            // cvc5::DatatypeConstructorDecl redDecl = _solverCVC5.mkDatatypeConstructorDecl("red");
            // cvc5::DatatypeConstructorDecl blueDecl = _solverCVC5.mkDatatypeConstructorDecl("blue");
            // colorDecl.addConstructor(redDecl);
            // colorDecl.addConstructor(blueDecl);
            // cvc5::Sort color = _solverCVC5.mkDatatypeSort(colorDecl);

            // // print the datatype
            // std::cout << "Datatype: " << colorDecl << std::endl;
            // std::cout << color << std::endl;

            // // Create a term of this datatype
            // cvc5::Term one_color = _solverCVC5.mkConst(color, "one_color");

            // std::cout << one_color << std::endl;

            // const cvc5::Datatype &consList = color.getDatatype();

            // // Create an assertion that one_color should not be red
            // // cvc5::Term red = _solverCVC5.mkTerm(cvc5::APPLY_CONSTRUCTOR, {consList.getConstructor("red").getTerm()});
            // cvc5::Term not_red = _solverCVC5.mkTerm(cvc5::EQUAL, {one_color, _solverCVC5.mkTerm(cvc5::APPLY_CONSTRUCTOR, {consList.getConstructor("red").getTerm()})});
            // not_red = _solverCVC5.mkTerm(cvc5::NOT, {not_red});

            // std::cout << not_red << std::endl;
            // not_red = _solverCVC5.mkTerm(cvc5::Kind::NOT, {not_red});

            // std::cout << not_red << std::endl;

            // colorDecl.addConstructor("red");
            // colorDecl.addConstructor("green");
            // _solverCVC5.mkDatatypeSort("Color");

            ////// END TEST DATATYPE CVC5 ////////

            // For now, we will do the second option

            int valueConstant = 0;
            _out << "; All uniques constants" << std::endl;

            if (use_enum_sort_for_objects)
            {
                if (useCVC5) {
                    cvc5::DatatypeDecl datatype_objects = _solverCVC5.mkDatatypeDecl("Objects");
                    for (const auto &constant : allConstants)
                    {
                        // Create the constructor for this constant
                        cvc5::DatatypeConstructorDecl constructor_obj = _solverCVC5.mkDatatypeConstructorDecl(Names::to_string(constant));
                        // Add it to the datatype
                        datatype_objects.addConstructor(constructor_obj);
                    }
                    // Create our sort from the datatype
                    sort_all_objects = _solverCVC5.mkDatatypeSort(datatype_objects);
                    datatype_all_objetcs = sort_all_objects.getDatatype(); 
                }
                else
                {

                    // First, create the array which will contains the name of all the objects
                    const char *enum_names[allConstants.size()];
                    int i = 0;
                    for (const auto &constant : allConstants)
                    {
                        char *value = (char *)malloc(Names::to_string(constant).size() + 1);
                        strcpy(value, Names::to_string(constant).c_str());
                        enum_names[i] = value;
                        // Make the mapping from the constant id to the enum id
                        _mapConstantIdToExpressionId[constant] = i;
                        i++;
                    }
                    sort_all_objects_Z3 = _contextZ3.enumeration_sort("Objects", allConstants.size(), enum_names, enum_consts, enum_testers);
                }
            }
            else
            {

                for (const auto &constant : allConstants)
                {

                    if (useCVC5)
                    {
                        // Create the term for this constant
                        _mapConstantToTerm[constant] = _solverCVC5.mkInteger(valueConstant);
                    }
                    else
                    {
                        // Add the constant into the vector of expression
                        expressionObjects.push_back(_contextZ3.int_val(valueConstant));
                        // Add a mapping from the constant id to the expression id
                        _mapConstantIdToExpressionId[constant] = expressionObjects.size() - 1;
                    }

                    _out << "(declare-const " << Names::to_string(constant) << " Int)" << std::endl;
                    _out << "(assert (= " << Names::to_string(constant) << " " << valueConstant << "))" << std::endl;
                    valueConstant++;
                }
            }
        }
    }

    z3::solver initializeSolverZ3(Parameters &params) {

        std::string logic = params.getParam("SMT_logic");
        if (logic.compare("default") == 0) {
            std::cout << "Use default logic" << std::endl;
            return z3::solver(_contextZ3);
        }
        else if (logic.compare("0") == 0) {
            std::cout << "Try to infer best logic" << std::endl;
            if (params.isNonzero("one_var_qconst") && params.isNonzero("use_enum_sort")) {
                return z3::solver(_contextZ3, "QF_UFDT");
            }
            else if (params.isNonzero("one_var_qconst")) {
                return z3::solver(_contextZ3, "QF_UFLIA");
            } else {
                // return z3::solver(_contextZ3, "QF_UF");
                z3::tactic tactic = z3::tactic(_contextZ3, "sat");
                return tactic.mk_solver();
            }
        } else {
            std::cout << "Use logic " << logic << std::endl;
            return z3::solver(_contextZ3, logic.c_str());
        }        
    }

    int idx = 0;

    inline void addVar(int var_id, std::string var_name, int layer, int layerElement, int ltpPos = -1, bool isSubstituteVar = false, int substituteVarQConstId = -1, int substituteVarTrueConstId = -1)
    {

        if (dict_var_id_to_name.size() > var_id - 1)
        {
            if (dict_var_id_to_name[var_id - 1].name == "")
            {
                // Initialize element
                if (use_one_var_for_qconst && isSubstituteVar)
                {
                    dict_var_id_to_name[var_id - 1].name = Names::to_string_without_invalid_SMT_symbols(substituteVarQConstId);
                }
                else
                {
                    dict_var_id_to_name[var_id - 1].name = var_name;
                }

                dict_var_id_to_name[var_id - 1].layer = layer;
                dict_var_id_to_name[var_id - 1].layerElement = layerElement;
                dict_var_id_to_name[var_id - 1].ltp_pos = ltpPos;

                if (layer == -1)
                {

                    if (use_one_var_for_qconst && isSubstituteVar)
                    {
                        dict_var_id_to_name[var_id - 1].full_name = "(= " + Names::to_string_without_invalid_SMT_symbols(substituteVarQConstId) + " " + Names::to_string(substituteVarTrueConstId) + ")";
                    }
                    else
                    {
                        dict_var_id_to_name[var_id - 1].full_name = var_name;
                    }
                }
                else {
                    // dict_var_id_to_name[var_id - 1].full_name = var_name + "__" + std::to_string(layer) + "_" + std::to_string(layerElement);
                    dict_var_id_to_name[var_id - 1].full_name = var_name + "__" + std::to_string(ltpPos);

                }

                if (use_one_var_for_qconst && isSubstituteVar)
                {
                    if (useCVC5)
                    {
                        cvc5::Term term;
                        if (!_mapQConstIdToTerm.count(substituteVarQConstId))
                        {
                            if (use_enum_sort_for_objects) {
                                term = _solverCVC5.mkConst(sort_all_objects, Names::to_string(substituteVarQConstId));
                            }
                            else {
                                term = _solverCVC5.mkConst(intSort, Names::to_string(substituteVarQConstId));
                            }
                            _mapQConstIdToTerm[substituteVarQConstId] = term;
                        }
                        else
                        {
                            term = _mapQConstIdToTerm[substituteVarQConstId];
                        }
                        if (use_enum_sort_for_objects) {
                            cvc5::Term termEqual = _solverCVC5.mkTerm(cvc5::EQUAL, {term, _solverCVC5.mkTerm(cvc5::APPLY_CONSTRUCTOR, {datatype_all_objetcs.getConstructor(Names::to_string(substituteVarTrueConstId)).getTerm()})});
                            dict_var_id_to_name[var_id - 1].cvc5Term = termEqual;
                            dict_var_id_to_name[var_id - 1].cvc5TermNeg = _solverCVC5.mkTerm(cvc5::NOT, {termEqual});
                        }
                        else {
                            cvc5::Term termEqual = _solverCVC5.mkTerm(cvc5::EQUAL, {term, _mapConstantToTerm[substituteVarTrueConstId]});
                            dict_var_id_to_name[var_id - 1].cvc5Term = termEqual;
                            dict_var_id_to_name[var_id - 1].cvc5TermNeg = _solverCVC5.mkTerm(cvc5::NOT, {termEqual});
                        }
                    }
                    else
                    {
                        z3::expr expr(_contextZ3);
                        if (!_mapQConstIdToToExpressionId.count(substituteVarQConstId))
                        {
                            if (use_enum_sort_for_objects)
                            {
                                expr = _contextZ3.constant(Names::to_string(substituteVarQConstId).c_str(), sort_all_objects_Z3);
                            }
                            else
                            {
                                expr = _contextZ3.int_const(Names::to_string(substituteVarQConstId).c_str());
                            };
                            // Add it into our vector
                            expressionQConst.push_back(expr);
                            // Add a mapping from the qconst id to the expression id
                            _mapQConstIdToToExpressionId[substituteVarQConstId] = expressionQConst.size() - 1;
                        }
                        else
                        {
                            expr = expressionQConst[_mapQConstIdToToExpressionId[substituteVarQConstId]];
                        }
                        if (use_enum_sort_for_objects)
                        {
                            z3::expr exprEqual = expr == enum_consts[_mapConstantIdToExpressionId[substituteVarTrueConstId]]();
                            dict_var_id_to_name[var_id - 1].z3Term = exprEqual;
                            dict_var_id_to_name[var_id - 1].z3TermNeg = !exprEqual;
                        }
                        else
                        {
                            z3::expr exprEqual = expr == expressionObjects[_mapConstantIdToExpressionId[substituteVarTrueConstId]];
                            dict_var_id_to_name[var_id - 1].z3Term = exprEqual;
                            dict_var_id_to_name[var_id - 1].z3TermNeg = !exprEqual;
                        }
                    }
                    dict_var_id_to_name[var_id - 1].isSubstitute = true;
                }
                else
                {
                    if (useCVC5)
                    {
                        cvc5::Term term = _solverCVC5.mkConst(boolSort, dict_var_id_to_name[var_id - 1].full_name);
                        dict_var_id_to_name[var_id - 1].cvc5Term = term;
                        dict_var_id_to_name[var_id - 1].cvc5TermNeg = _solverCVC5.mkTerm(cvc5::NOT, {term});
                    }
                    else
                    {
                        z3::expr expr = _contextZ3.bool_const(dict_var_id_to_name[var_id - 1].full_name.c_str());
                        dict_var_id_to_name[var_id - 1].z3Term = expr;
                        dict_var_id_to_name[var_id - 1].z3TermNeg = !expr;
                    }
                }
            }
            return;
        }
        else if (dict_var_id_to_name.size() < var_id - 1)
        {
            // Add blank elements
            for (int i = dict_var_id_to_name.size(); i < var_id - 1; i++)
            {
                NameAndLayerElement nameAndLayerElementBlank = {
                    .z3Term = z3::expr(_contextZ3),
                    .z3TermNeg = z3::expr(_contextZ3)};
                nameAndLayerElementBlank.name = "";
                nameAndLayerElementBlank.layer = -1;
                nameAndLayerElementBlank.layerElement = -1;
                nameAndLayerElementBlank.full_name = "";
                dict_var_id_to_name.push_back(nameAndLayerElementBlank);
            }
        }

        NameAndLayerElement nameAndLayerElement = {
            .z3Term = z3::expr(_contextZ3),
            .z3TermNeg = z3::expr(_contextZ3)};

        if (use_one_var_for_qconst && isSubstituteVar)
        {
            nameAndLayerElement.name = Names::to_string_without_invalid_SMT_symbols(substituteVarQConstId);
        }
        else
        {
            nameAndLayerElement.name = var_name;
        }
        nameAndLayerElement.layer = layer;
        nameAndLayerElement.layerElement = layerElement;
        if (layer == -1)
        {
            if (use_one_var_for_qconst && isSubstituteVar)
            {
                nameAndLayerElement.full_name = "(= " + Names::to_string_without_invalid_SMT_symbols(substituteVarQConstId) + " " + Names::to_string(substituteVarTrueConstId) + ")";
            }
            else
            {
                nameAndLayerElement.full_name = var_name;
            }
        }

        else {
            // nameAndLayerElement.full_name = var_name + "__" + std::to_string(layer) + "_" + std::to_string(layerElement);
            nameAndLayerElement.full_name = var_name + "__" + std::to_string(ltpPos);
        }

        if (use_one_var_for_qconst && isSubstituteVar)
        {
            if (useCVC5)
            {
                // Should only be declare once !
                cvc5::Term term;
                if (!_mapQConstIdToTerm.count(substituteVarQConstId))
                {
                    if (use_enum_sort_for_objects)
                    {
                        term = _solverCVC5.mkConst(sort_all_objects, Names::to_string_without_invalid_SMT_symbols(substituteVarQConstId));
                    }
                    else
                    {
                        term = _solverCVC5.mkConst(intSort, Names::to_string_without_invalid_SMT_symbols(substituteVarQConstId));
                    }
                    _mapQConstIdToTerm[substituteVarQConstId] = term;
                }
                else
                {
                    term = _mapQConstIdToTerm[substituteVarQConstId];
                }
                if (use_enum_sort_for_objects) {
                    cvc5::Term termEqual = _solverCVC5.mkTerm(cvc5::EQUAL, {term, _solverCVC5.mkTerm(cvc5::APPLY_CONSTRUCTOR, {datatype_all_objetcs.getConstructor(Names::to_string(substituteVarTrueConstId)).getTerm()})});
                    nameAndLayerElement.cvc5Term = termEqual;
                    nameAndLayerElement.cvc5TermNeg = _solverCVC5.mkTerm(cvc5::NOT, {termEqual});
                }
                else {
                    cvc5::Term termEqual = _solverCVC5.mkTerm(cvc5::EQUAL, {term, _mapConstantToTerm[substituteVarTrueConstId]});
                    nameAndLayerElement.cvc5Term = termEqual;
                    nameAndLayerElement.cvc5TermNeg = _solverCVC5.mkTerm(cvc5::NOT, {termEqual});
                }
            }
            else
            {
                z3::expr expr(_contextZ3);
                if (!_mapQConstIdToToExpressionId.count(substituteVarQConstId))
                {

                    if (use_enum_sort_for_objects)
                    {
                        expr = _contextZ3.constant(Names::to_string(substituteVarQConstId).c_str(), sort_all_objects_Z3);
                    }
                    else
                    {
                        expr = _contextZ3.int_const(Names::to_string(substituteVarQConstId).c_str());
                    }
                    // Add it into our vector
                    expressionQConst.push_back(expr);
                    // Add a mapping from the qconst id to the expression id
                    _mapQConstIdToToExpressionId[substituteVarQConstId] = expressionQConst.size() - 1;
                }
                else
                {
                    expr = expressionQConst[_mapQConstIdToToExpressionId[substituteVarQConstId]];
                }
                if (use_enum_sort_for_objects)
                {
                    z3::expr exprEqual = expr == enum_consts[_mapConstantIdToExpressionId[substituteVarTrueConstId]]();
                    nameAndLayerElement.z3Term = exprEqual;
                    nameAndLayerElement.z3TermNeg = !exprEqual;
                }
                else
                {
                    z3::expr exprEqual = expr == expressionObjects[_mapConstantIdToExpressionId[substituteVarTrueConstId]];
                    nameAndLayerElement.z3Term = exprEqual;
                    nameAndLayerElement.z3TermNeg = !exprEqual;
                }
            }
            nameAndLayerElement.isSubstitute = true;
        }
        else
        {
            if (useCVC5)
            {
                cvc5::Term term = _solverCVC5.mkConst(boolSort, nameAndLayerElement.full_name);
                nameAndLayerElement.cvc5Term = term;
                nameAndLayerElement.cvc5TermNeg = _solverCVC5.mkTerm(cvc5::NOT, {term});
            }
            else
            {

                // z3::expr expr(_contextZ3, Z3_mk_const(_contextZ3, _contextZ3.int_symbol(idx++), Z3_mk_bool_sort(_contextZ3)));
                z3::expr expr = _contextZ3.bool_const(nameAndLayerElement.full_name.c_str());
                nameAndLayerElement.z3Term = expr;
                nameAndLayerElement.z3TermNeg = !expr;
            }
        }

        dict_var_id_to_name.push_back(nameAndLayerElement);
    }

    /******************* FOR USING DIRECTLY THE SOLVER *********************/

    inline void addClauseInSolver(int lit)
    {
        assert(lit != 0);

        if (lit < 0)
        {
            if (useCVC5)
                _solverCVC5.assertFormula(dict_var_id_to_name[-lit - 1].cvc5TermNeg);
            else
                _solverZ3.add(dict_var_id_to_name[-lit - 1].z3TermNeg);
        }
        else
        {
            if (useCVC5)
                _solverCVC5.assertFormula(dict_var_id_to_name[lit - 1].cvc5Term);
            else
                _solverZ3.add(dict_var_id_to_name[lit - 1].z3Term);
        }

        _stats._num_lits++;
        _stats._num_cls++;
    }

    inline void addClauseInSolver(int lit1, int lit2)
    {
        assert(lit1 != 0);
        assert(lit2 != 0);

        cvc5::Term term1;
        z3::expr term1_Z3(_contextZ3);

        if (lit1 < 0)
        {
            if (useCVC5)
                term1 = dict_var_id_to_name[-lit1 - 1].cvc5TermNeg;
            else
                term1_Z3 = dict_var_id_to_name[-lit1 - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term1 = dict_var_id_to_name[lit1 - 1].cvc5Term;
            else
                term1_Z3 = dict_var_id_to_name[lit1 - 1].z3Term;
        }

        cvc5::Term term2;
        z3::expr term2_Z3(_contextZ3);

        if (lit2 < 0)
        {
            if (useCVC5)
                term2 = dict_var_id_to_name[-lit2 - 1].cvc5TermNeg;
            else
                term2_Z3 = dict_var_id_to_name[-lit2 - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term2 = dict_var_id_to_name[lit2 - 1].cvc5Term;
            else
                term2_Z3 = dict_var_id_to_name[lit2 - 1].z3Term;
        }

        _stats._num_lits += 2;
        _stats._num_cls++;

        if (useCVC5)
            _solverCVC5.assertFormula(_solverCVC5.mkTerm(cvc5::OR, {term1, term2}));
        else
            _solverZ3.add(term1_Z3 || term2_Z3);
    }

    inline void addClauseInSolver(int lit1, int lit2, int lit3)
    {
        assert(lit1 != 0);
        assert(lit2 != 0);
        assert(lit3 != 0);

        cvc5::Term term1;
        z3::expr term1_Z3(_contextZ3);

        if (lit1 < 0)
        {
            if (useCVC5)
                term1 = dict_var_id_to_name[-lit1 - 1].cvc5TermNeg;
            else
                term1_Z3 = dict_var_id_to_name[-lit1 - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term1 = dict_var_id_to_name[lit1 - 1].cvc5Term;
            else
                term1_Z3 = dict_var_id_to_name[lit1 - 1].z3Term;
        }

        cvc5::Term term2;
        z3::expr term2_Z3(_contextZ3);

        if (lit2 < 0)
        {
            if (useCVC5)
                term2 = dict_var_id_to_name[-lit2 - 1].cvc5TermNeg;
            else
                term2_Z3 = dict_var_id_to_name[-lit2 - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term2 = dict_var_id_to_name[lit2 - 1].cvc5Term;
            else
                term2_Z3 = dict_var_id_to_name[lit2 - 1].z3Term;
        }

        cvc5::Term term3;
        z3::expr term3_Z3(_contextZ3);

        if (lit3 < 0)
        {
            if (useCVC5)
                term3 = dict_var_id_to_name[-lit3 - 1].cvc5TermNeg;
            else
                term3_Z3 = dict_var_id_to_name[-lit3 - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term3 = dict_var_id_to_name[lit3 - 1].cvc5Term;
            else
                term3_Z3 = dict_var_id_to_name[lit3 - 1].z3Term;
        }

        _stats._num_lits += 3;
        _stats._num_cls++;

        if (useCVC5)
            _solverCVC5.assertFormula(_solverCVC5.mkTerm(cvc5::OR, {term1, term2, term3}));
        else
            _solverZ3.add(term1_Z3 || term2_Z3 || term3_Z3);
    }

    inline void addClauseInSolver(const std::vector<int> &cls)
    {

        std::vector<cvc5::Term> terms;
        z3::expr_vector terms_Z3(_contextZ3);

        for (int lit : cls)
        {
            assert(lit != 0);

            cvc5::Term term;
            z3::expr term_Z3(_contextZ3);

            if (lit < 0)
            {
                if (useCVC5)
                    term = dict_var_id_to_name[-lit - 1].cvc5TermNeg;
                else
                    term_Z3 = dict_var_id_to_name[-lit - 1].z3TermNeg;
            }
            else
            {
                if (useCVC5)
                    term = dict_var_id_to_name[lit - 1].cvc5Term;
                else
                    term_Z3 = dict_var_id_to_name[lit - 1].z3Term;
            }

            if (useCVC5)
                terms.push_back(term);
            else
                terms_Z3.push_back(term_Z3);
        }

        _stats._num_cls++;
        _stats._num_lits += cls.size();

        if (useCVC5)
            _solverCVC5.assertFormula(_solverCVC5.mkTerm(cvc5::OR, terms));
        else
            _solverZ3.add(z3::mk_or(terms_Z3));
    }

    inline void appendClauseInSolver(int lit)
    {

        assert(lit != 0);

        cvc5::Term term;
        z3::expr term_Z3(_contextZ3);

        if (lit < 0)
        {
            if (useCVC5)
                term = dict_var_id_to_name[-lit - 1].cvc5TermNeg;
            else
                term_Z3 = dict_var_id_to_name[-lit - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term = dict_var_id_to_name[lit - 1].cvc5Term;
            else
                term_Z3 = dict_var_id_to_name[lit - 1].z3Term;
        }

        _stats._num_lits++;

        if (useCVC5)
            termsLine.push_back(term);
        else
            termsLines_Z3.push_back(term_Z3);
    }

    inline void appendClauseInSolver(int lit1, int lit2)
    {

        assert(lit1 != 0);
        assert(lit2 != 0);

        cvc5::Term term1;
        z3::expr term1_Z3(_contextZ3);

        if (lit1 < 0)
        {
            if (useCVC5)
                term1 = dict_var_id_to_name[-lit1 - 1].cvc5TermNeg;
            else
                term1_Z3 = dict_var_id_to_name[-lit1 - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term1 = dict_var_id_to_name[lit1 - 1].cvc5Term;
            else
                term1_Z3 = dict_var_id_to_name[lit1 - 1].z3Term;
        }

        cvc5::Term term2;
        z3::expr term2_Z3(_contextZ3);

        if (lit2 < 0)
        {
            if (useCVC5)
                term2 = dict_var_id_to_name[-lit2 - 1].cvc5TermNeg;
            else
                term2_Z3 = dict_var_id_to_name[-lit2 - 1].z3TermNeg;
        }
        else
        {
            if (useCVC5)
                term2 = dict_var_id_to_name[lit2 - 1].cvc5Term;
            else
                term2_Z3 = dict_var_id_to_name[lit2 - 1].z3Term;
        }

        _stats._num_lits += 2;

        if (useCVC5)
        {
            termsLine.push_back(term1);
            termsLine.push_back(term2);
        }
        else
        {
            termsLines_Z3.push_back(term1_Z3);
            termsLines_Z3.push_back(term2_Z3);
        }
    }

    inline void endClauseInSolver()
    {
        if ((useCVC5 && termsLine.size() == 0) || (!useCVC5 && termsLines_Z3.size() == 0))
            return;
        else if (useCVC5 && termsLine.size() == 1)
        {
            _solverCVC5.assertFormula(termsLine[0]);
            termsLine.clear();
            _stats._num_cls++;
            return;
        }
        else if (!useCVC5 && termsLines_Z3.size() == 1)
        {
            _solverZ3.add(termsLines_Z3[0]);
            termsLines_Z3.resize(0);
            _stats._num_cls++;
            return;
        }
        else
        {
            if (useCVC5)
            {
                _solverCVC5.assertFormula(_solverCVC5.mkTerm(cvc5::OR, termsLine));
                termsLine.clear();
            }
            else
            {
                _solverZ3.add(z3::mk_or(termsLines_Z3));
                termsLines_Z3.resize(0);
            }
        }
        _stats._num_cls++;
    }

    bool hasLastAssumptions()
    {
        if (useCVC5)
            return !assumptions.empty();
        else
            return !assumptions_Z3.empty();
    }

    // void setTerminateCallback(void *state, int (*terminate)(void *state))
    // {
    //     ipasir_set_terminate(_solver, state, terminate);
    // }

    // void setLearnCallback(int maxLength, void *state, void (*learn)(void *state, int *clause))
    // {
    //     ipasir_set_learn(_solver, state, maxLength, learn);
    // }

    /*********API FOR CHOOSING THE SOLVER OF WRITING IN FILE*/

    inline void addClause(int lit)
    {
        addClauseInSolver(lit);
    }

    inline void addClause(int lit1, int lit2)
    {
        addClauseInSolver(lit1, lit2);
    }

    inline void addClause(int lit1, int lit2, int lit3)
    {
        addClauseInSolver(lit1, lit2, lit3);
    }

    inline void addClause(const std::vector<int> &cls)
    {
        addClauseInSolver(cls);
    }

    inline void appendClause(int lit)
    {
        appendClauseInSolver(lit);
    }

    inline void appendClause(int lit1, int lit2)
    {
        appendClauseInSolver(lit1, lit2);
    }

    inline void endClause()
    {
        endClauseInSolver();
    }

    inline void assume(int lit)
    {
        if (_stats._num_asmpts == 0)
        {
            if (useCVC5)
                assumptions.clear();
            else
                assumptions_Z3.resize(0);
        }

        assert(lit != 0);

        cvc5::Term term;
        z3::expr termZ3(_contextZ3);

        if (lit < 0)
        {
            if (useCVC5)
                term = _solverCVC5.mkTerm(cvc5::NOT, {dict_var_id_to_name[-lit - 1].cvc5Term});
            else
                termZ3 = !dict_var_id_to_name[-lit - 1].z3Term;
        }
        else
        {
            if (useCVC5)
                term = dict_var_id_to_name[lit - 1].cvc5Term;
            else
                termZ3 = dict_var_id_to_name[lit - 1].z3Term;
        }

        if (useCVC5)
            assumptions.push_back(term);
        else
            assumptions_Z3.push_back(termZ3);

        _stats._num_asmpts++;
    }

    int solve()
    {
        if (_stats._num_asmpts == 0)
        {
            if (useCVC5)
                assumptions.clear();
            else
                assumptions_Z3.resize(0);
        }

        _stats._num_asmpts = 0;

        if (useCVC5)
        {
            auto start = std::chrono::high_resolution_clock::now();
            cvc5::Result resultSMT = _solverCVC5.checkSatAssuming(assumptions);
            auto stop = std::chrono::high_resolution_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
            long long int time_ms = duration.count();
            _stats.time_spend_on_solver_per_layer_ms.push_back(time_ms);
            _stats.total_time_spend_on_solver_ms += time_ms;
            std::cout << "result: " << resultSMT << std::endl;
            if (resultSMT.isSat())
                return 10;
            else if (resultSMT.isUnsat())
                return 20;
            else if (resultSMT.isUnknown())
                return 0;
            else
                return 0;
        }
        else
        {
            auto start = std::chrono::high_resolution_clock::now();
            // Try a push pop for assumptions
            _solverZ3.push();
            for (int i = 0; i < assumptions_Z3.size(); i++)
            {
                _solverZ3.add(assumptions_Z3[i]);
            }

            
            z3::check_result resultSMT = _solverZ3.check();
            auto stop = std::chrono::high_resolution_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
            long long int time_ms = duration.count();
            _stats.time_spend_on_solver_per_layer_ms.push_back(time_ms);
            _stats.total_time_spend_on_solver_ms += time_ms;

            std::cout << "result: " << resultSMT << std::endl;
            if (resultSMT == z3::sat)
            {
                // Save the model
                _modelZ3 = _solverZ3.get_model();
                return 10;
            }

            else if (resultSMT == z3::unsat) {
                _solverZ3.pop();
                return 20;
            }
            else if (resultSMT == z3::unknown) {
                _solverZ3.pop();
               return 0;
            }
            else {
                _solverZ3.pop();
                return 0;
            }
        }
    }

    inline bool holds(int lit)
    {
        if (useCVC5)
            return _solverCVC5.getValue(dict_var_id_to_name[lit - 1].cvc5Term).getBooleanValue() > 0;
        else
            return _modelZ3.eval(dict_var_id_to_name[lit - 1].z3Term, true).bool_value() == Z3_L_TRUE;
    }

    inline void reset_solver() {
        if (useCVC5) {
            dict_var_id_to_name.clear();
            _solverCVC5.resetAssertions();
        } else {
            dict_var_id_to_name.clear();
            _solverZ3.reset();
        }
    }


    inline void print_formula(std::string filename)
    {

        if (filename.length() == 0) {
            filename == "FORMULA.SMT";
        }


        std::cout << "WRITING FORMULA TO FILE: " << filename << std::endl;

        // Create final formula file
        std::ofstream ffile;
        ffile.open(filename);

        if (useCVC5)
        {

            ffile << "(set-logic " << _logic << ")\n";

            FlatHashSet<std::string> qConstAlreadyDeclared;

            // Declare all constants
            for (int i = 0; i < dict_var_id_to_name.size(); i++)
            {
                // std::cout << "var " << i + 1 << " = " << dict_var_id_to_name[i].full_name << std::endl;
                if (dict_var_id_to_name[i].name.length() > 0)
                {
                    std::string full_name_var;
                    std::string type;
                    if (use_one_var_for_qconst && dict_var_id_to_name[i].isSubstitute)
                    {
                        full_name_var = dict_var_id_to_name[i].name;
                        if (qConstAlreadyDeclared.count(full_name_var))
                        {
                            continue;
                        }
                        else
                        {
                            qConstAlreadyDeclared.insert(full_name_var);
                        }
                        type = "Int";
                    }
                    else
                    {
                        full_name_var = dict_var_id_to_name[i].full_name;
                        type = "Bool";
                    }
                    ffile << "(declare-const " << full_name_var << " " << type << ")\n";
                }
            }

            std::vector<cvc5::Term> assertions = _solverCVC5.getAssertions();

            for (int i = 0; i < assertions.size(); i++)
            {
                ffile << "(assert " << assertions[i].toString() << ")\n";
            }

            ffile << "(check-sat)\n";
            // ffile << "(get-model)\n";
            ffile << "(exit)\n";
        }
        else
        {
            ffile << _solverZ3.to_smt2() << std::endl;
        }

        // Remove old file
        // remove("test.SMT");

        // Finish
        ffile.flush();
        ffile.close();
    }

    ~SmtInterface()
    {
        if (!_is_used)
        {
            return;
        }
        if (_print_formula)
        {

            std::cout << "WRITING FORMULA TO FILE" << std::endl;

            // Create final formula file
            std::ofstream ffile;
            ffile.open(_formula_file);

            if (useCVC5)
            {

                ffile << "(set-logic " << _logic << ")\n";

                FlatHashSet<std::string> qConstAlreadyDeclared;

                // Declare all constants
                for (int i = 0; i < dict_var_id_to_name.size(); i++)
                {
                    // std::cout << "var " << i + 1 << " = " << dict_var_id_to_name[i].full_name << std::endl;
                    if (dict_var_id_to_name[i].name.length() > 0)
                    {
                        std::string full_name_var;
                        std::string type;
                        if (use_one_var_for_qconst && dict_var_id_to_name[i].isSubstitute)
                        {
                            full_name_var = dict_var_id_to_name[i].name;
                            if (qConstAlreadyDeclared.count(full_name_var))
                            {
                                continue;
                            }
                            else
                            {
                                qConstAlreadyDeclared.insert(full_name_var);
                            }
                            type = "Int";
                        }
                        else
                        {
                            full_name_var = dict_var_id_to_name[i].full_name;
                            type = "Bool";
                        }
                        ffile << "(declare-const " << full_name_var << " " << type << ")\n";
                    }
                }

                std::vector<cvc5::Term> assertions = _solverCVC5.getAssertions();

                for (int i = 0; i < assertions.size(); i++)
                {
                    ffile << "(assert " << assertions[i].toString() << ")\n";
                }

                ffile << "(check-sat)\n";
                // ffile << "(get-model)\n";
                ffile << "(exit)\n";
            }
            else
            {
                ffile << _solverZ3.to_smt2() << std::endl;
            }

            // Remove old file
            remove("test.SMT");

            // Finish
            ffile.flush();
            ffile.close();
        }

        // Display all stats
        std::cout << "STATS SOLVER" << std::endl;
        if (useCVC5)
            std::cout << _solverCVC5.getStatistics() << std::endl;
        else
            std::cout << _solverZ3.statistics() << std::endl;
    }
};

#endif
