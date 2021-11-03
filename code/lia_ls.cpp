#include "lia_ls.h"
namespace lia{
//initialize
ls_solver::ls_solver()
:_swt_p(0.3),
_swt_threshold(50),
smooth_probability(3),
_cutoff(600),
_additional_len(10),
_max_step(UINT64_MAX),
CC_mode(-1)
{mt.seed(1);}

ls_solver::ls_solver(int random_seed)
:_swt_p(0.3),
_swt_threshold(50),
smooth_probability(3),
_cutoff(600),
_additional_len(10),
_max_step(UINT64_MAX),
CC_mode(-1)
{mt.seed(random_seed);}

void ls_solver::make_space(){
    _solution.resize(_num_vars+_additional_len);
    _best_solutin.resize(_num_vars+_additional_len);
    tabulist.resize(2*_num_vars+_additional_len);
    CClist.resize(2*_num_vars+_additional_len);
    operation_vec.resize(2*_num_lits+_additional_len);
    last_move.resize(2*_num_vars+_additional_len);
    unsat_clauses=new Array((int)_num_clauses+(int)_additional_len);
}

void ls_solver::initialize(){
    
}

void ls_solver::initialize_variable_datas(){
    
}

void ls_solver::initialize_clause_datas(){
    
}

//random walk
void ls_solver::update_clause_weight(){
    for(int i=0;i<unsat_clauses->size();i++){
        _clauses[unsat_clauses->element_at(i)].weight++;
    }
    total_clause_weight+=unsat_clauses->size();
}

void ls_solver::smooth_clause_weight(){
    for(int i=0;i<_num_clauses;i++){
        if(_clauses[i].weight>1&&!unsat_clauses->is_in_array(i)){
            _clauses[i].weight--;
            total_clause_weight--;
        }
    }
}

void ls_solver::random_walk(){
    
}

//construction
void ls_solver::construct_slution_score(){
    
}

uint64_t ls_solver::pick_construct_idx(int &best_value){
    return 0;
}

void ls_solver::construct_move(uint64_t var_idx, int change_value){
    
}

int ls_solver::construct_score(uint64_t var_idx,int change_value){
    return 0;
}

//basic operations
bool ls_solver::update_best_solution(){
    bool improve=false;
    if(unsat_clauses->size()<best_found_this_restart){
        improve=true;
        best_found_this_restart=unsat_clauses->size();
    }
    if(unsat_clauses->size()<best_found_cost){
        improve=true;
        best_found_cost=unsat_clauses->size();
        best_cost_time=TimeElapsed();
    }
    return improve;
}

void ls_solver::modify_CC(){
    
}

int ls_solver::pick_critical_move(int &best_value){
    return 0;
}

void ls_solver::critical_move(uint64_t var_idx, int change_value){
    
}

void ls_solver::invert_lit(lit &l){
    l.key=1-l.key;
    std::vector<int> tmp_coff_var_idx=l.pos_coff_var_idx;
    std::vector<int> tmp_coff=l.pos_coff;
    l.pos_coff_var_idx=l.neg_coff_var_idx;
    l.pos_coff=l.neg_coff;
    l.neg_coff_var_idx=tmp_coff_var_idx;
    l.neg_coff=tmp_coff;
}

int ls_solver::delta_lit(lit &l){
    int delta=l.key;
    for(int i=0;i<l.pos_coff.size();i++){delta+=(l.pos_coff[i]*_solution[l.pos_coff_var_idx[i]]);}
    for(int i=0;i<l.neg_coff.size();i++){delta-=(l.neg_coff[i]*_solution[l.neg_coff_var_idx[i]]);}
    return delta;
}

double ls_solver::TimeElapsed(){
    std::chrono::steady_clock::time_point finish = std::chrono::steady_clock::now();
    std::chrono::duration<double> duration = finish - start;
    return duration.count();
}

void ls_solver::clear_prev_data(){
    
}

//print
void ls_solver::print_formula(){
    int i=0;
    for(clause & cl :_clauses){
        std::cout<<i++<<"\n";
        for(int l_idx: cl.literals){print_literal(_lits[l_idx]);}
        std::cout<<"\n";
    }
}

void ls_solver::print_literal(lit &l){
    for(int i=0;i<l.pos_coff.size();i++)
        {std::cout<<"( "<<l.pos_coff[i]<<" * "<<_vars[l.pos_coff_var_idx[i]].var_name<<" ) + ";}
    for(int i=0;i<l.neg_coff.size();i++)
        {std::cout<<"( "<<l.neg_coff[i]<<" * "<<_vars[l.neg_coff_var_idx[i]].var_name<<" ) + ";}
    std::cout<<"( "<<l.key<<" )\n";
}

//calculate score
int ls_solver::critical_score(uint64_t var_idx, int change_value){
    return 0;
}

int ls_solver::critical_subscore(uint64_t var_idx, int change_value){
    return 0;
}

void ls_solver::critical_score_subscore(uint64_t var_idx, int change_value){
    
}

//check
bool ls_solver::check_solution(){
    clause *cp;
    int unsat_num=0;
    for(uint64_t i=0;i<_num_clauses;i++){
        bool unsat_flag=false;//false means the clause is unsat
        cp=&(_clauses[i]);
        for(int i: cp->literals){
            if(delta_lit(_lits[i])<=0){
                unsat_flag=true;//the clause is already sat
                break;
            }
        }
        if(!unsat_flag){unsat_num++;}
    }
    if(unsat_num==unsat_clauses->size())
        std::cout<<"right solution\n";
    else
        std::cout<<"wrong solution\n";
    return unsat_num==unsat_clauses->size();
}

//local search
void ls_solver::local_search(){
    
}


}
