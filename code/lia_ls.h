#pragma once
#include <cstdio>
#include <chrono>
#include <string.h>
#include<stack>
#include<random>
#include<map>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdlib>
#include<exception>
#include<time.h>
#include<signal.h>
#include<unistd.h>
#include<sys/types.h>
#include<string>
#include "lia_Array.h"

namespace lia {
//one arith lit is in the form of a_1*x_1+...+a_n*x_n<=k, the cofficient are divided into positive ones and negative ones
struct lit{
    std::vector<int>            pos_coff_var_idx;
    std::vector<int>            pos_coff;
    std::vector<int>            neg_coff_var_idx;
    std::vector<int>            neg_coff;
    int                         key;
    int                         clause_idx;
};

struct variable{
    std::vector<int>            literals;
    std::vector<int>            clasue_idxs;
    std::string                 var_name;
};

struct clause{
    std::vector<int>            literals;
    std::vector<int>            var_idxs;
};

class ls_solver{
public:
    
    //basic information
    uint64_t                    _num_vars;
    uint64_t                    _num_lits;
    uint64_t                    _num_clauses;
    std::vector<variable>       _vars;
    std::vector<lit>            _lits;
    std::vector<clause>         _clauses;
    Array                       *unsat_clauses;
    //solution
    std::vector<int>            _solution;
    std::vector<int>            _best_solutin;
    int                         best_found_cost;
    int                         best_found_this_restart;
    //control
    uint64_t                    _step;
    const uint64_t              _max_step;
    std::vector<uint64_t>       tabulist;//tabulist[2*var] and [2*var+1] means that var are forbidden to move forward or backward until then
    std::vector<int>            CClist;//CClist[2*var]==1 and [2*var+1]==1 means that var is allowed to move forward or backward
    int                          CC_mode;
    std::vector<uint64_t>       last_move;
    std::vector<int>            operation_vec;
    std::chrono::steady_clock::time_point start;
    double                      best_cost_time;
    double                      _cutoff;
    std::mt19937                mt;
    const uint64_t              _additional_len;
    std::map<std::string,uint64_t> name2var;//map the name of a variable to its index
    // data structure for clause weighting
    const uint64_t              smooth_probability;
    uint64_t                    _swt_threshold;
    float                       _swt_p;//w=w*p+ave_w*(1-p)
    uint64_t                    total_clause_weight;
    
    //initialize
    ls_solver();
    ls_solver(int random_seed);
    void                        make_space();
    void                        make_lits_space(uint64_t num_lits){_num_lits=num_lits;_lits.resize(num_lits+_additional_len);};
    void                        initialize();
    void                        initialize_variable_datas();
    void                        initialize_clause_datas();
    
    //local search
    void                        local_search();
    
    //random walk
    void                        update_clause_weight();
    void                        smooth_clause_weight();
    void                        random_walk();
    
    //construction
    void                        construct_slution_score();//construct the solution based on score
    uint64_t                    pick_construct_idx(int &best_value);
    void                        construct_move(uint64_t var_idx,int value);
    int                         construct_score(uint64_t var_idx,int value);
    
    //basic operations
    inline void                 sat_a_clause(uint64_t clause_idx){unsat_clauses->delete_element((int)clause_idx);};
    inline void                 unsat_a_clause(uint64_t clause_idx){unsat_clauses->insert_element((int)clause_idx);};
    bool                        update_best_solution();
    void                        modify_CC();
    int                         pick_critical_move();
    void                        critical_move(uint64_t var_idx,int change_value);
    void                        invert_lit(lit &l);
    int                         delta_lit(lit &l);
    double                      TimeElapsed();
    void                        clear_prev_data();
    //print
    void                        print_formula();
    void                        print_literal(lit &l);
    void                        print_solution(bool detail);
    //calculate score
    int                         critical_score(uint64_t var_idx,int change_value);
    int                         critical_subscore(uint64_t var_idx,int change_value);
    void                        critical_score_subscore(uint64_t var_idx,int change_value);
    //check
    bool                        check_solution();
    bool                        check_best_solution();

};
}
