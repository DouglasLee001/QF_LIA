#include "lia_ls.h"
namespace lia{
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

}
