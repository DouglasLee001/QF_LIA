#include "lia_ls.h"
namespace lia{
//input transformation
void ls_solver::split_string(std::string &in_string, std::vector<std::string> &str_vec,std::string pattern=" "){
    std::string::size_type pos;
    in_string+=pattern;
    size_t size=in_string.size();
    for(size_t i=0; i<size; i++){
    pos=in_string.find(pattern,i);
    if(pos<size){
        std::string s=in_string.substr(i,pos-i);
        str_vec.push_back(s);
        i=pos+pattern.size()-1;
        }
    }
}

void ls_solver::build_lits(std::string &in_string){
    std::vector<std::string> vec;
    split_string(in_string, vec);
    if(vec[0]=="0"){_lits[0].lits_index=0; return;}//true literal
    int lit_index=std::atoi(vec[0].c_str());
    if(vec[1][1]=='!'){_lits[lit_index].lits_index=0;return;}//lits index==0 means that the lit is true
    lit *l=&(_lits[lit_index]);
    if(vec[1]=="or"){
        l->delta=transfer_name_to_resolution_var(vec[2], false);
        l->key=1;
        l->is_lia_lit=false;
        l->lits_index=lit_index;
        return;
    }//or term in the form: 1 or newvar_2
    if(vec.size()>2){
        l->is_lia_lit=true;
        if(vec.size()>6){
            l->lits_index=std::atoi(vec[0].c_str());
            int idx=5;
            if(vec[2]=="="&&vec[3]!="("){
                idx++;
                l->key=-std::atoll(vec[3].c_str());
            }
            l->is_equal=(vec[2]=="=");
            for(;idx<vec.size();idx++){
                if(vec[idx]==")"){break;}
                if(vec[idx]=="("){
                    idx+=2;
                    int64_t coff=std::atoll(vec[idx].c_str());
                    if(coff>0){
                        l->pos_coff.push_back(coff);
                        l->pos_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[++idx]));
                    }
                    else{
                        l->neg_coff.push_back(-coff);
                        l->neg_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[++idx]));
                    }
                    idx++;
                }
                else{
                    l->pos_coff.push_back(1);
                    l->pos_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[idx]));
                }
                _num_opt+=l->pos_coff.size();
                _num_opt+=l->neg_coff.size();
            }
            if(vec[2]!="="||vec[3]=="(") {l->key=-std::atoll(vec[++idx].c_str());}
            if(vec[2]==">="){l->key++;invert_lit(*l);}
        }//( <= ( + x1 ( * -1 x2 ) x7 ( * -1 x8 ) ) 0 )
        else{
            l->lits_index=std::atoi(vec[0].c_str());
            int64_t bound=std::atoll(vec[4].c_str());
            uint64_t var_idx=transfer_name_to_tmp_var(vec[3]);
            if(vec[2]==">="){l->key=bound;l->neg_coff.push_back(1);l->neg_coff_var_idx.push_back((int)var_idx);}
            else{l->key=-bound;l->pos_coff.push_back(1);l->pos_coff_var_idx.push_back((int)var_idx);}
            l->is_equal=(vec[2]=="=");
        }//( >= x 0 )
        
    }//lia lit
    else{
        l->delta=transfer_name_to_resolution_var(vec[1],false);
        l->key=1;
        l->is_lia_lit=false;
        l->lits_index=lit_index;
    }//boolean lit
    
}

void ls_solver::build_instance(std::vector<std::vector<int> >& clause_vec){
    for(int clause_idx=0;clause_idx<clause_vec.size();clause_idx++){
        if(clause_vec[clause_idx].size()==1){
            lit *l=&(_lits[std::abs(clause_vec[clause_idx][0])]);
            if(l->is_equal||!l->is_lia_lit){continue;}//equal lit is not bound lit
            if(l->pos_coff.size()==0&&l->neg_coff.size()==1){
                if(clause_vec[clause_idx][0]>0&&l->key>_tmp_vars[l->neg_coff_var_idx[0]].low_bound){_tmp_vars[l->neg_coff_var_idx[0]].low_bound=l->key;}
                else if(clause_vec[clause_idx][0]<0&&(l->key-1)<_tmp_vars[l->neg_coff_var_idx[0]].upper_bound){_tmp_vars[l->neg_coff_var_idx[0]].upper_bound=(l->key-1);}
                _bound_lits.push_back(l->lits_index);
                l->lits_index=0;
                if(clause_vec[clause_idx][0]<0){
                    clause_vec[clause_idx][0]=-clause_vec[clause_idx][0];
                }
            }
            else if(l->pos_coff.size()==1&&l->neg_coff.size()==0){
                if(clause_vec[clause_idx][0]>0&&(-l->key)<_tmp_vars[l->pos_coff_var_idx[0]].upper_bound){_tmp_vars[l->pos_coff_var_idx[0]].upper_bound=-l->key;}
                else if(clause_vec[clause_idx][0]<0&&(1-l->key)>_tmp_vars[l->pos_coff_var_idx[0]].low_bound){_tmp_vars[l->pos_coff_var_idx[0]].low_bound=(1-l->key);}
                _bound_lits.push_back(l->lits_index);
                l->lits_index=0;
                if(clause_vec[clause_idx][0]<0){
                    clause_vec[clause_idx][0]=-clause_vec[clause_idx][0];
                }
            }
        }
    }
    reduce_vars();
    _clauses.resize(clause_vec.size());
    _num_clauses=0;
    for (auto clause_curr:clause_vec) {
        bool is_tautology=false;
        for (auto l_idx : clause_curr) {if(_lits[std::abs(l_idx)].lits_index==0){is_tautology=true;break;}}
        if(is_tautology){continue;}
        for (auto l_idx : clause_curr) {
            _clauses[_num_clauses].literals.push_back(l_idx);
            lit *l=&(_lits[std::abs(l_idx)]);
            if(l->lits_index==0){continue;}
            if(!l->is_lia_lit){_resolution_vars[l->delta].clause_idxs.push_back(_num_clauses);}
        }
        _num_clauses++;
    }
    _clauses.resize(_num_clauses);
    //now the vars are all in the resolution vars
//    unit_prop();
//    resolution();
//    unit_prop();
    reduce_clause();
    print_formula();
    best_found_cost=(int)_num_clauses;
    make_space();
}

uint64_t ls_solver::transfer_name_to_reduced_var(std::string &name, bool is_lia){
    if(name2var.find(name)==name2var.end()){
        name2var[name]=_vars.size();
        variable var;
        var.var_name=name;
        var.is_lia=is_lia;
        _vars.push_back(var);
        if(is_lia){lia_var_vec.push_back((int)_vars.size()-1);}
        else{bool_var_vec.push_back((int)_vars.size()-1);}
        return _vars.size()-1;
    }
    else return name2var[name];
}

uint64_t ls_solver::transfer_name_to_resolution_var(std::string & name,bool is_lia){
    if(name2resolution_var.find(name)==name2resolution_var.end()){
        name2resolution_var[name]=_resolution_vars.size();
        variable var;
        var.clause_idxs.reserve(64);
        var.literals.reserve(64);
        var.literal_clause.reserve(64);
        var.literal_coff.reserve(64);
        var.var_name=name;
        var.is_lia=is_lia;
        _resolution_vars.push_back(var);
        if(is_lia){lia_var_vec.push_back((int)_resolution_vars.size()-1);}
        else{bool_var_vec.push_back((int)_resolution_vars.size()-1);}
        return _resolution_vars.size()-1;
    }
    else return name2resolution_var[name];
}

uint64_t ls_solver::transfer_name_to_tmp_var(std::string & name){
    if(name2tmp_var.find(name)==name2tmp_var.end()){
        name2tmp_var[name]=_tmp_vars.size();
        variable var;
        var.is_lia=true;
        var.var_name=name;
        _tmp_vars.push_back(var);
        return _tmp_vars.size()-1;
    }
    else return name2tmp_var[name];
}
//transfer the lia var into _resolution_vars, turn (x-y) to z
void ls_solver::reduce_vars(){
    const uint64_t tmp_vars_size=_tmp_vars.size();
    std::vector<int> hash_map(tmp_vars_size*tmp_vars_size,0);//hash_map[A*(size)+b]=n means A-B has occurred n times
    std::vector<int> occur_time(tmp_vars_size,0);//occur_time[a]=n means that a has occured in lits for n times
    Array *pair_x=new Array((int)tmp_vars_size);
    Array *pair_y=new Array((int)tmp_vars_size);
    lit *l;
    variable * original_var;
    variable * new_var;
    std::string var_name;
    int pos_var_idx,neg_var_idx,original_var_idx;
    use_pbs=!(_resolution_vars.size()==0);
    for(int var_idx=0;var_idx<tmp_vars_size;var_idx++){
        if(_tmp_vars[var_idx].upper_bound>1||_tmp_vars[var_idx].low_bound<0){use_pbs=false;break;}
    }
    if(use_pbs){_resolution_vars=_tmp_vars;}//if there is no boolean vars and all lia vars are in [0,1], then use pbs, and no need to reduce the vars
    else{
    //calculate the hash_map
    for(uint64_t l_idx=0;l_idx<_num_lits;l_idx++){
        l=&(_lits[l_idx]);
        if(l->lits_index==0){continue;}
        for(int i=0;i<l->pos_coff.size();i++){
            pos_var_idx=l->pos_coff_var_idx[i];
            for(int j=0;j<l->neg_coff.size();j++){
                if(l->pos_coff[i]!=l->neg_coff[j]){continue;}
                neg_var_idx=l->neg_coff_var_idx[j];
                if(neg_var_idx<pos_var_idx){hash_map[neg_var_idx*tmp_vars_size+pos_var_idx]++;}//small_idx* num_var+ large_idx
                else{hash_map[pos_var_idx*tmp_vars_size+neg_var_idx]++;}
            }
        }
    }
    //calculate the occur time
    for(uint64_t l_idx=0;l_idx<_num_lits;l_idx++){
        l=&(_lits[l_idx]);
        if(l->lits_index==0||!l->is_lia_lit){continue;}
        for(int i=0;i<l->pos_coff.size();i++){occur_time[l->pos_coff_var_idx[i]]++;}
        for(int i=0;i<l->neg_coff.size();i++){occur_time[l->neg_coff_var_idx[i]]++;}
    }
    //calculate the x-y pair
    for(int pre_idx=0;pre_idx<tmp_vars_size-1;pre_idx++){
        if(pair_y->is_in_array(pre_idx)||occur_time[pre_idx]==0){continue;}//prevent reinsert
        for(int pos_idx=pre_idx+1;pos_idx<tmp_vars_size;pos_idx++){
            if(hash_map[pre_idx*tmp_vars_size+pos_idx]==occur_time[pre_idx]&&occur_time[pre_idx]==occur_time[pos_idx]){
                pair_x->insert_element(pre_idx);
                pair_y->insert_element(pos_idx);
                break;
            }
        }
    }
    name2var.clear();
    //rewrite lits
    for(uint64_t l_idx=0;l_idx<_num_lits;l_idx++){
        l=&(_lits[l_idx]);
        lit new_lit;
        if(l->lits_index==0||!l->is_lia_lit){continue;}
        new_lit.key=l->key;
        new_lit.lits_index=l->lits_index;
        new_lit.is_equal=l->is_equal;
        new_lit.is_lia_lit=l->is_lia_lit;
        for(int i=0;i<l->pos_coff.size();i++){
            original_var_idx=l->pos_coff_var_idx[i];
            original_var=&(_tmp_vars[original_var_idx]);
            if(pair_x->is_in_array(original_var_idx)){
                new_lit.pos_coff.push_back(l->pos_coff[i]);
//                var_name="_new_var_"+std::to_string(pair_x->index_of(original_var_idx));
                var_name="_new_var_"+original_var->var_name;
                new_lit.pos_coff_var_idx.push_back((int)transfer_name_to_resolution_var(var_name,true));
            }
            else if(pair_y->is_in_array(original_var_idx)){
                new_lit.neg_coff.push_back(l->pos_coff[i]);
//                var_name="_new_var_"+std::to_string(pair_y->index_of(original_var_idx));
                var_name="_new_var_"+_tmp_vars[pair_x->element_at(pair_y->index_of(original_var_idx))].var_name;
                new_lit.neg_coff_var_idx.push_back((int)transfer_name_to_resolution_var(var_name,true));
            }
            else{
                new_lit.pos_coff.push_back(l->pos_coff[i]);
                new_lit.pos_coff_var_idx.push_back((int)transfer_name_to_resolution_var(original_var->var_name,true));
            }
        }
        for(int i=0;i<l->neg_coff.size();i++){
            original_var_idx=l->neg_coff_var_idx[i];
            original_var=&(_tmp_vars[original_var_idx]);
            if(!pair_x->is_in_array(original_var_idx)&&!pair_y->is_in_array(original_var_idx)){
                new_lit.neg_coff.push_back(l->neg_coff[i]);
                new_lit.neg_coff_var_idx.push_back((int)transfer_name_to_resolution_var(original_var->var_name,true));
            }
        }
        _lits[l_idx]=new_lit;
    }
    //set low and upbound
    for(original_var_idx=0;original_var_idx<_tmp_vars.size();original_var_idx++){
        original_var=&(_tmp_vars[original_var_idx]);
        if(occur_time[original_var_idx]==0){continue;}
        //original var
        if(!pair_x->is_in_array(original_var_idx)&&!pair_y->is_in_array(original_var_idx)){
            new_var=&(_resolution_vars[transfer_name_to_resolution_var(original_var->var_name,true)]);
            new_var->low_bound=original_var->low_bound;
            new_var->upper_bound=original_var->upper_bound;
        }
        //new var
        else if(pair_x->is_in_array(original_var_idx)){
            int pair_idx=pair_x->index_of(original_var_idx);
//            var_name="_new_var_"+std::to_string(pair_idx);
            var_name="_new_var_"+original_var->var_name;
            new_var=&(_resolution_vars[transfer_name_to_resolution_var(var_name,true)]);
            int64_t x_low=original_var->low_bound;
            int64_t x_upper=original_var->upper_bound;
            int64_t y_low=_tmp_vars[pair_y->element_at(pair_idx)].low_bound;
            int64_t y_upper=_tmp_vars[pair_y->element_at(pair_idx)].upper_bound;
            if(x_low==-max_int||y_upper==max_int){new_var->low_bound=-max_int;}
            else{new_var->low_bound=x_low-y_upper;}
            if(x_upper==max_int||y_low==-max_int){new_var->upper_bound=max_int;}
            else{new_var->upper_bound=x_upper-y_low;}
        }
    }
    }
    int num_var_with_bound=0;
    for(int var_idx=0;var_idx<_resolution_vars.size();var_idx++){
        new_var=&(_resolution_vars[var_idx]);
        if(!new_var->is_lia){continue;}
        if(new_var->upper_bound!=max_int&&new_var->low_bound!=-max_int){continue;}//if a var has both upper bound and lower bound, no bound lits is added.
        if(new_var->low_bound!=-max_int){
            int lit_idx=_bound_lits[num_var_with_bound++];
            lit bound_lit;
            bound_lit.is_lia_lit=true;
            bound_lit.lits_index=lit_idx;
            bound_lit.neg_coff.push_back(1);
            bound_lit.neg_coff_var_idx.push_back(var_idx);
            bound_lit.key=new_var->low_bound;
            _lits[lit_idx]=bound_lit;
            new_var->low_bound=-max_int;
        }
        if(new_var->upper_bound!=max_int){
            int lit_idx=_bound_lits[num_var_with_bound++];
            lit bound_lit;
            bound_lit.is_lia_lit=true;
            bound_lit.lits_index=lit_idx;
            bound_lit.pos_coff.push_back(1);
            bound_lit.pos_coff_var_idx.push_back(var_idx);
            bound_lit.key=-new_var->upper_bound;
            _lits[lit_idx]=bound_lit;
            new_var->upper_bound=max_int;
        }
    }
}

void ls_solver::unit_prop(){
    std::stack<uint64_t> unit_clause;//the var_idx in the unit clause
    for(uint64_t clause_idx=0;clause_idx<_num_clauses;clause_idx++){//the unit clause is the undeleted clause containing only one bool var
        if(!_clauses[clause_idx].is_delete&&_clauses[clause_idx].literals.size()==1&&!_lits[std::abs(_clauses[clause_idx].literals[0])].is_lia_lit){unit_clause.push(clause_idx);}
    }
    while(!unit_clause.empty()){
        uint64_t unit_clause_idx=unit_clause.top();
        unit_clause.pop();
        if(_clauses[unit_clause_idx].is_delete){continue;}
        int is_pos_lit=(_clauses[unit_clause_idx].literals[0]>0)?1:-1;//determine the sign of the var in unit clause
        uint64_t unit_var=_lits[std::abs(_clauses[unit_clause_idx].literals[0])].delta;//determing the var in unit clause
        _resolution_vars[unit_var].is_delete=true;//delete the unit var
        for(uint64_t cl_idx:_resolution_vars[unit_var].clause_idxs){
            clause *cl=&(_clauses[cl_idx]);
            if(cl->is_delete)continue;
            for(uint64_t lit_idx=0;lit_idx<cl->literals.size();lit_idx++){
                int l_id_in_lits=cl->literals[lit_idx];
                lit *l=&(_lits[std::abs(l_id_in_lits)]);
                if(!l->is_lia_lit&&l->delta==unit_var){//go through the clauses of the unit var, find the var in corresponding clause
                    if((is_pos_lit>0&&l_id_in_lits>0)||(is_pos_lit<0&&l_id_in_lits<0)){
                        cl->is_delete=true;
                        for(int l_idx_inner:cl->literals){//delete the clause from corresponding bool var
                            lit *l_inner=&(_lits[std::abs(l_idx_inner)]);
                            if(!l_inner->is_lia_lit&&l_inner->delta!=unit_var){
                                variable *var_inner=&(_resolution_vars[l_inner->delta]);
                                for(uint64_t delete_idx=0;delete_idx<var_inner->clause_idxs.size();delete_idx++){
                                    if(var_inner->clause_idxs[delete_idx]==cl_idx){
                                        var_inner->clause_idxs[delete_idx]=var_inner->clause_idxs.back();
                                        var_inner->clause_idxs.pop_back();
                                        break;
                                    }
                                }
                            }
                        }
                    }//if there exist same lit, the clause is already set true, then delete the clause
                    else{//else delete the lit
                        cl->literals[lit_idx]=cl->literals.back();
                        cl->literals.pop_back();
                        if(cl->literals.size()==1&&!_lits[std::abs(cl->literals[0])].is_lia_lit){unit_clause.push(cl_idx);}//if after deleting, it becomes unit clause
                    }
                    break;
                }
            }
        }
    }
}

void ls_solver::resolution(){
    std::vector<uint64_t> pos_clauses(10*_num_clauses);
    std::vector<uint64_t> neg_clauses(10*_num_clauses);
    int pos_clause_size,neg_clause_size;
    bool is_improve=true;
    while(is_improve){
        is_improve=false;
    for(uint64_t bool_var_idx:bool_var_vec){
        if(_resolution_vars[bool_var_idx].is_delete)continue;
        pos_clause_size=0;neg_clause_size=0;
        for(int i=0;i<_resolution_vars[bool_var_idx].clause_idxs.size();i++){
            uint64_t clause_idx=_resolution_vars[bool_var_idx].clause_idxs[i];
            if(_clauses[clause_idx].is_delete)continue;
            for(int l_var_sign:_clauses[clause_idx].literals){
                if(_lits[std::abs(l_var_sign)].delta==bool_var_idx){
                    if(l_var_sign>0){pos_clauses[pos_clause_size++]=clause_idx;}
                    else{neg_clauses[neg_clause_size++]=clause_idx;}
                    break;
                }
            }
        }//determine the pos_clause and neg_clause
        int tautology_num=0;
        for(int i=0;i<pos_clause_size;i++){//pos clause X neg clause
            uint64_t pos_clause_idx=pos_clauses[i];
            for(int j=0;j<neg_clause_size;j++){
                uint64_t neg_clause_idx=neg_clauses[j];
                for(int k=0;k<_clauses[neg_clause_idx].literals.size();k++){
                    int l_neg_lit=_clauses[neg_clause_idx].literals[k];
                    if(_lits[std::abs(l_neg_lit)].delta!=bool_var_idx){//the bool_var for resolution is not considered
                        for(int l_pos_lit:_clauses[pos_clause_idx].literals){
                            if(-l_neg_lit==(l_pos_lit)){
                                tautology_num++;
                                break;
                            }//if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                    }
                }
            }
        }
        if((pos_clause_size*neg_clause_size-tautology_num)>(pos_clause_size+neg_clause_size)){continue;}//if deleting the var can cause 2 times clauses, then skip it
        for(uint64_t clause_idx:_resolution_vars[bool_var_idx].clause_idxs){//delete the clauses of bool_var
            _clauses[clause_idx].is_delete=true;
            for(int l_idx_sign:_clauses[clause_idx].literals){//delete the clause from corresponding bool var
                lit *l=&(_lits[std::abs(l_idx_sign)]);
                if(!l->is_lia_lit&&l->delta!=bool_var_idx){
                    variable *var_inner=&(_resolution_vars[l->delta]);
                    for(uint64_t delete_idx=0;delete_idx<var_inner->clause_idxs.size();delete_idx++){
                        if(var_inner->clause_idxs[delete_idx]==clause_idx){
                            var_inner->clause_idxs[delete_idx]=var_inner->clause_idxs.back();
                            var_inner->clause_idxs.pop_back();
                            break;
                        }
                    }
                }
            }
        }
        is_improve=true;
        _resolution_vars[bool_var_idx].is_delete=true;
        if(pos_clause_size==0||neg_clause_size==0)continue;//pos or neg clause is empty, meaning the clauses are SAT when assigned to true or false, then cannot resolute, just delete the clause
        for(int i=0;i<pos_clause_size;i++){//pos clause X neg clause
            uint64_t pos_clause_idx=pos_clauses[i];
            for(int j=0;j<neg_clause_size;j++){
                uint64_t neg_clause_idx=neg_clauses[j];
                clause new_clause;
                uint64_t pos_lit_size=_clauses[pos_clause_idx].literals.size();
                uint64_t neg_lit_size=_clauses[neg_clause_idx].literals.size();
                new_clause.literals.reserve(pos_lit_size+neg_lit_size);
                bool is_tautology=false;
                for(int k=0;k<pos_lit_size;k++){
                    int l_sign_idx=_clauses[pos_clause_idx].literals[k];
                    if(_lits[std::abs(l_sign_idx)].is_lia_lit||_lits[std::abs(l_sign_idx)].delta!=bool_var_idx){new_clause.literals.push_back(l_sign_idx);}
                }//add the lits in pos clause to new clause
                for(int k=0;k<neg_lit_size;k++){
                    int l_sign_idx=_clauses[neg_clause_idx].literals[k];
                    if(_lits[std::abs(l_sign_idx)].is_lia_lit||_lits[std::abs(l_sign_idx)].delta!=bool_var_idx){
                        bool is_existed_lit=false;
                        for(uint64_t i=0;i<pos_lit_size-1;i++){
                            if(l_sign_idx==(new_clause.literals[i])){is_existed_lit=true;break;}// if the lit has existed, then it will not be added
                            if(l_sign_idx==(-new_clause.literals[i])){is_tautology=true;break;}//if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                        if(is_tautology){break;}
                        if(!is_existed_lit){new_clause.literals.push_back(l_sign_idx);}
                    }
                }
                if(!is_tautology){//add new clause, and modify the clause of corresponding bool var
                    for(int l_sign_idx:new_clause.literals){
                        lit *l_inner=&(_lits[std::abs(l_sign_idx)]);
                        if(!l_inner->is_lia_lit){
                            _resolution_vars[l_inner->delta].clause_idxs.push_back((int)_num_clauses);
                        }
                    }
                    _clauses.push_back(new_clause);
                    _num_clauses++;
                }
            }
        }
    }
    }
}

void ls_solver::reduce_clause(){
    bool_var_vec.clear();
    lia_var_vec.clear();
    _vars.reserve(_resolution_vars.size());
    int i,reduced_clause_num;
    i=0;reduced_clause_num=0;
    for(;i<_num_clauses;i++){if(!_clauses[i].is_delete){_clauses[reduced_clause_num++]=_clauses[i];}}
    _clauses.resize(reduced_clause_num);
    
    _num_lia_lits=0;_num_bool_lits=0;
    for(int l_idx=0;l_idx<_lits.size();l_idx++){
        lit *l=&(_lits[l_idx]);
        if(l->lits_index==0){continue;}
        if(l->is_lia_lit){
            _num_lia_lits++;
            for(int pos_var_idx=0;pos_var_idx<l->pos_coff.size();pos_var_idx++)
                {l->pos_coff_var_idx[pos_var_idx]=(int)transfer_name_to_reduced_var(_resolution_vars[l->pos_coff_var_idx[pos_var_idx]].var_name, true);}
            for(int neg_var_idx=0;neg_var_idx<l->neg_coff.size();neg_var_idx++)
                {l->neg_coff_var_idx[neg_var_idx]=(int)transfer_name_to_reduced_var(_resolution_vars[l->neg_coff_var_idx[neg_var_idx]].var_name, true);}
        }
        else{
            if(!_resolution_vars[l->delta].is_delete){
                l->delta=transfer_name_to_reduced_var(_resolution_vars[l->delta].var_name, false);
                _num_bool_lits++;
            }
            else{l->lits_index=0;}
        }
    }//transfer the resolution vars to vars
    _num_clauses=reduced_clause_num;
    _vars.resize(_vars.size());
    _num_vars=_vars.size();
    for(int clause_idx=0;clause_idx<reduced_clause_num;clause_idx++){
        _clauses[clause_idx].weight=1;
        for(int k=0;k<_clauses[clause_idx].literals.size();k++){
            int l_sign_idx=_clauses[clause_idx].literals[k];
            lit *l=&(_lits[std::abs(l_sign_idx)]);
            if(l->is_lia_lit){
                variable *v;
                for(int j=0;j<l->pos_coff.size();j++){
                    v=&(_vars[l->pos_coff_var_idx[j]]);
                    v->literals.push_back(l_sign_idx);
                    v->literal_clause.push_back(clause_idx);
                    v->literal_coff.push_back(l->pos_coff[j]);
                }
                for(int j=0;j<l->neg_coff.size();j++){
                    v=&(_vars[l->neg_coff_var_idx[j]]);
                    v->literals.push_back(l_sign_idx);
                    v->literal_clause.push_back(clause_idx);
                    v->literal_coff.push_back(-l->neg_coff[j]);
                }
                _clauses[clause_idx].lia_literals.push_back(l_sign_idx);
            }
            else{
                _vars[l->delta].literals.push_back(l_sign_idx);
                _clauses[i].bool_literals.push_back(l_sign_idx);
            }
        }
    }//determine the literals of vars
    for(variable & v:_vars){
        int pre_clause_idx=INT32_MAX;
        for(int i=0;i<v.literal_clause.size();i++){
            int tmp_clause_idx=v.literal_clause[i];
            if(pre_clause_idx!=tmp_clause_idx){
                v.clause_idxs.push_back(tmp_clause_idx);
                pre_clause_idx=tmp_clause_idx;
            }
        }
    }//determine the clause_idxs of var
    int64_t max_lit_num=0;
    for(int var_idx=0;var_idx<_num_vars;var_idx++){
        if(!_vars[var_idx].is_lia){continue;}
        if(_vars[var_idx].literals.size()>max_lit_num){
            lia_var_idx_with_most_lits=var_idx;
            max_lit_num=_vars[var_idx].literals.size();
        }
    }
    for(int lit_idx=0;lit_idx<_lits.size();lit_idx++){
        lit *l=&(_lits[lit_idx]);
        if(l->lits_index==0||!l->is_lia_lit){continue;}
        if(l->pos_coff.size()!=1||l->neg_coff.size()!=1||l->pos_coff[0]!=1||l->neg_coff[0]!=1){
            lia_var_idx_with_most_lits=-1;
            is_idl=false;
            break;
        }//var_with most lit are dedicated for IDL
    }
}

//initialize
ls_solver::ls_solver()
:_swt_p(0.3),
_swt_threshold(50),
smooth_probability(3),
_cutoff(1200),
_additional_len(10),
_max_step(UINT64_MAX),
CC_mode(-1)
{mt.seed(1);}

ls_solver::ls_solver(int random_seed)
:_swt_p(0.3),
_swt_threshold(50),
smooth_probability(3),
_cutoff(1200),
_additional_len(10),
_max_step(UINT64_MAX),
CC_mode(-1)
{mt.seed(random_seed);}


void ls_solver::make_space(){
    _solution.resize(_num_vars+_additional_len);
    _best_solutin.resize(_num_vars+_additional_len);
    tabulist.resize(2*_num_vars+_additional_len,0);
    CClist.resize(2*_num_vars+_additional_len,1);
    operation_var_idx_vec.resize(_num_opt+_additional_len);
    operation_change_value_vec.resize(_num_opt+_additional_len);
    last_move.resize(2*_num_vars+_additional_len,0);
    unsat_clauses=new Array((int)_num_clauses+(int)_additional_len);
    sat_clause_with_false_literal=new Array((int)_num_clauses+(int)_additional_len);
    lit_occur=new Array((int)_num_lits);
}

void ls_solver::initialize(){
    clear_prev_data();
    construct_slution_score();
    initialize_lit_datas();
    initialize_clause_datas();
    initialize_variable_datas();
    best_found_this_restart=unsat_clauses->size();
    update_best_solution();
}

void ls_solver::initialize_variable_datas(){
    
}
//initialize the delta of each literal by delta_lit operation
void ls_solver::initialize_lit_datas(){
    for(int i=0;i<_num_lits;i++){
        if(_lits[i].lits_index!=0){_lits[i].delta=delta_lit(_lits[i]);}
    }
}
//set the sat num of each clause, and sat/unsat a clause
void ls_solver::initialize_clause_datas(){
    int64_t pos_delta;
    for(uint64_t c=0;c<_num_clauses;c++){
        clause *cl=&(_clauses[c]);
        cl->sat_count=0;
        cl->weight=1;
        cl->min_delta=INT64_MAX;
        for(int l_idx:cl->literals){
            int64_t delta=_lits[std::abs(l_idx)].delta;
            bool is_equal=_lits[std::abs(l_idx)].is_equal;
            if( (!is_equal&&((delta<=0&&l_idx>0)||(delta>0&&l_idx<0))) || (is_equal&&((delta==0&&l_idx>0)||(delta!=0&&l_idx<0))) ){cl->sat_count++;}
            pos_delta=delta;
            convert_to_pos_delta(pos_delta, l_idx);
            if(pos_delta<cl->min_delta){
                cl->min_delta=pos_delta;
                cl->min_delta_lit_index=l_idx;
            }
        }
        if(cl->sat_count==0){unsat_a_clause(c);}
        else{sat_a_clause(c);}
        if(cl->sat_count>0&&cl->sat_count<cl->literals.size()){sat_clause_with_false_literal->insert_element((int)c);}
    }
    total_clause_weight=_num_clauses;
}

void ls_solver::build_neighbor(){
    
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
    int clause_idx,operation_idx,var_idx,operation_direction;
    int64_t change_value;
    int64_t best_subscore=INT64_MAX;
    int64_t subscore;
    int best_operation_idx=0;
    uint64_t best_last_move=UINT64_MAX;
    uint64_t last_move_step;
    operation_idx=0;
    clause *cp;
    lit *l;
    //determine the operations
    for(int i=0;i<3&&operation_idx<5;i++){
        clause_idx=unsat_clauses->element_at(mt()%unsat_clauses->size());
        cp=&(_clauses[clause_idx]);
        for(int l_idx:cp->literals){
            l=&(_lits[std::abs(l_idx)]);
            if(l->is_equal){
                if(l_idx<0){
                    for(int var_idx:l->pos_coff_var_idx){
                        insert_operation(var_idx, 1, operation_idx);
                        insert_operation(var_idx, -1, operation_idx);
                    }
                    for(int var_idx:l->neg_coff_var_idx){
                        insert_operation(var_idx, 1, operation_idx);
                        insert_operation(var_idx, -1, operation_idx);
                    }
                }//delta should not be 0, while it is 0, so the var should increase 1/-1
                else{
                    for(int j=0;j<l->pos_coff.size();j++){
                        int var_idx=l->pos_coff_var_idx[j];
                        if((l->delta%l->pos_coff[j])!=0){continue;}
                        insert_operation(var_idx, (-l->delta/l->pos_coff[j]), operation_idx);
                    }
                    for(int j=0;j<l->neg_coff.size();j++){
                        int var_idx=l->neg_coff_var_idx[j];
                        if((l->delta%l->neg_coff[j])!=0){continue;}
                        insert_operation(var_idx, (l->delta/l->neg_coff[j]), operation_idx);
                    }
                }//delta should be 0, while it is not 0, so the var should increase (-delta/coff), while (-delta%coff)==0
                continue;
            }
            for(int k=0;k<l->pos_coff.size();k++){
                var_idx=l->pos_coff_var_idx[k];
                change_value=(l_idx>0)?devide(-l->delta,l->pos_coff[k]):devide(1-l->delta, l->pos_coff[k]);
                insert_operation(var_idx, change_value, operation_idx);
            }
            for(int k=0;k<l->neg_coff.size();k++){
                var_idx=l->neg_coff_var_idx[k];
                change_value=(l_idx>0)?devide(l->delta, l->neg_coff[k]):devide(l->delta-1, l->neg_coff[k]);
                insert_operation(var_idx, change_value, operation_idx);
            }
        }
    }
    //choose the best operation
    for(int i=0;i<operation_idx;i++){
        var_idx=operation_var_idx_vec[i];
        change_value=operation_change_value_vec[i];
        subscore=critical_subscore(var_idx, change_value);
        operation_direction=(change_value>0)?0:1;
        last_move_step=last_move[2*var_idx+(operation_direction+1)%2];
        if(subscore<best_subscore||(subscore==best_subscore&&last_move_step<best_last_move)){
            best_subscore=subscore;
            best_last_move=last_move_step;
            best_operation_idx=i;
        }
    }
    //make move
    var_idx=operation_var_idx_vec[best_operation_idx];
    change_value=operation_change_value_vec[best_operation_idx];
    critical_move(var_idx, change_value);
}

//construction
void ls_solver::construct_slution_score(){
//TODO::this is a temp function, setting all vars 0
    for(int i=0;i<_num_vars;i++){
        if(_vars[i].low_bound>0){_solution[i]=_vars[i].low_bound;}
        else if(_vars[i].upper_bound<0){_solution[i]=_vars[i].upper_bound;}
        else{_solution[i]=0;}
    }
}

uint64_t ls_solver::pick_construct_idx(int64_t &best_value){
    return 0;
}

void ls_solver::construct_move(uint64_t var_idx, int64_t change_value){
    
}

int ls_solver::construct_score(uint64_t var_idx,int64_t change_value){
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

void ls_solver::modify_CC(uint64_t var_idx, int direction){
    
}

int ls_solver::pick_critical_move(int64_t &best_value){
    int best_score,score,operation_var_idx,best_var_idx,cnt;
    int64_t operation_change_value,change_value;
    bool BMS=false;
    bool should_push_vec;
    best_score=(is_idl)?0:1;
    best_var_idx=-1;
    change_value=0;
    uint64_t best_last_move=UINT64_MAX;
    int        operation_idx=0;
    //determine the critical value
    for(int i=0;i<unsat_clauses->size();i++){
        clause *cl=&(_clauses[unsat_clauses->element_at(i)]);
        for(int l_idx:cl->literals){
            lit *l=&(_lits[std::abs(l_idx)]);
            if(l->is_equal){
                if(l_idx<0){
                    for(int var_idx:l->pos_coff_var_idx){
                        if(_step>tabulist[2*var_idx]){insert_operation(var_idx, 1, operation_idx);}
                        if(_step>tabulist[2*var_idx+1]){insert_operation(var_idx, -1, operation_idx);}
                    }
                    for(int var_idx:l->neg_coff_var_idx){
                        if(_step>tabulist[2*var_idx]){insert_operation(var_idx, 1, operation_idx);}
                        if(_step>tabulist[2*var_idx+1]){insert_operation(var_idx, -1, operation_idx);}
                    }
                }//delta should not be 0, while it is 0, so the var should increase 1/-1
                else{
                    for(int j=0;j<l->pos_coff.size();j++){
                        int var_idx=l->pos_coff_var_idx[j];
                        if((l->delta%l->pos_coff[j])!=0){continue;}
                        if((l->delta<0&&_step>tabulist[2*var_idx])||(l->delta>0&&_step>tabulist[2*var_idx+1])){insert_operation(var_idx, (-l->delta/l->pos_coff[j]), operation_idx);}
                    }
                    for(int j=0;j<l->neg_coff.size();j++){
                        int var_idx=l->neg_coff_var_idx[j];
                        if((l->delta%l->neg_coff[j])!=0){continue;}
                        if((l->delta>0&&_step>tabulist[2*var_idx])||(l->delta<0&&_step>tabulist[2*var_idx+1])){insert_operation(var_idx, (l->delta/l->neg_coff[j]), operation_idx);}
                    }
                }//delta should be 0, while it is not 0, so the var should increase (-delta/coff), while (-delta%coff)==0
                continue;
            }
            for(int i=0;i<l->neg_coff.size();i++){
                should_push_vec=false;
                int var_idx=l->neg_coff_var_idx[i];
                if(var_idx==lia_var_idx_with_most_lits){continue;}
                if(l_idx>0&&_step>tabulist[2*var_idx]){
                    should_push_vec=true;
                    change_value=devide(l->delta, l->neg_coff[i]);
                }
                else if(l_idx<0&&_step>tabulist[2*var_idx+1]){
                    should_push_vec=true;
                    change_value=devide(l->delta-1, l->neg_coff[i]);
                }
                if(should_push_vec){insert_operation(var_idx, change_value, operation_idx);}
                //if l_idx>0, delta should be <=0, while it is now >0(too large), so the var should enlarge by (delta/coff) (this is a positive value since the coff is neg), if l_idx<0, the delta should be >=1, while it is now <1(too small), so the var should enlarge by (delta-1)/coff (neg value)
            }
            for(int i=0;i<l->pos_coff.size();i++){
                should_push_vec=false;
                int var_idx=l->pos_coff_var_idx[i];
                if(var_idx==lia_var_idx_with_most_lits){continue;}
                if(l_idx>0&&_step>tabulist[2*var_idx+1]){
                    should_push_vec=true;
                    change_value=devide(-l->delta,l->pos_coff[i]);
                }
                else if(l_idx<0&&_step>tabulist[2*var_idx]){
                    should_push_vec=true;
                    change_value=devide(1-l->delta, l->pos_coff[i]);
                }
                if(should_push_vec){insert_operation(var_idx, change_value, operation_idx);}
                //if l_idx>0, delta should be <=0, while it is now >0(too large), so the var should enlarge by (-delta/coff) (this is a negative value), if l_idx<0, delta should be >=1, while it is now <1(too small), so the var should enlarge by (1-delta)/coff (positive value)
            }
        }
    }
    //go through the forward and backward move of vars, evaluate their score, pick the untabued best one
    if(operation_idx>45){BMS=true;cnt=45;}
    else{BMS=false;cnt=operation_idx;}
    for(int i=0;i<cnt;i++){
        if(BMS){
            int idx=mt()%(operation_idx-i);
            operation_change_value=operation_change_value_vec[idx];
            operation_var_idx=operation_var_idx_vec[idx];
            operation_change_value_vec[idx]=operation_change_value_vec[operation_idx-i-1];
            operation_var_idx_vec[idx]=operation_var_idx_vec[operation_idx-i-1];
        }
        else{
            operation_change_value=operation_change_value_vec[i];
            operation_var_idx=operation_var_idx_vec[i];
        }
        score=critical_score(operation_var_idx,operation_change_value);
        int opposite_direction=(operation_change_value>0)?1:0;//if the change value is >0, then means it is moving forward, the opposite direction is 1(backward)
        uint64_t last_move_step=last_move[2*operation_var_idx+opposite_direction];
        if(score>best_score||(score==best_score&&last_move_step<best_last_move)){
                best_score=score;
                best_var_idx=operation_var_idx;
                best_value=operation_change_value;
                best_last_move=last_move_step;
            }
    }
    //if there is untabu decreasing move
    if(best_var_idx!=-1){return best_var_idx;}
    //choose from swap operations if there is no decreasing unsat critical
    if(!sat_clause_with_false_literal->empty()){
        best_score=0;
        operation_idx=0;
        for(int i=0;operation_idx<20&&i<50;i++){add_swap_operation(operation_idx);}
        for(int i=0;i<operation_idx;i++){
            operation_change_value=operation_change_value_vec[i];
            operation_var_idx=operation_var_idx_vec[i];
            score=critical_score(operation_var_idx,operation_change_value);
            int opposite_direction=(operation_change_value>0)?1:0;
            uint64_t last_move_step=last_move[2*operation_var_idx+opposite_direction];
            if(score>best_score||(score==best_score&&last_move_step<best_last_move)){
                best_score=score;
                best_var_idx=operation_var_idx;
                best_value=operation_change_value;
                best_last_move=last_move_step;
            }
        }
        if(best_var_idx!=-1){return best_var_idx;}
    }
    //update weight and random walk
    if(mt()%10000>smooth_probability){update_clause_weight();}
    else {smooth_clause_weight();}
    random_walk();
    return -1;
}

void ls_solver::critical_move(uint64_t var_idx, int64_t change_value){
    int direction=(change_value>0)?0:1;
    critical_score_subscore(var_idx, change_value);
    _solution[var_idx]+=change_value;
    //step
    last_move[2*var_idx+direction]=_step;
    tabulist[var_idx*2+(direction+1)%2]=_step+3+mt()%10;
    if(CC_mode!=-1){modify_CC(var_idx,direction);}
}
//transfer the ">" to "<="
void ls_solver::invert_lit(lit &l){
    l.key=1-l.key;
    std::vector<int> tmp_coff_var_idx=l.pos_coff_var_idx;
    std::vector<int64_t> tmp_coff=l.pos_coff;
    l.pos_coff_var_idx=l.neg_coff_var_idx;
    l.pos_coff=l.neg_coff;
    l.neg_coff_var_idx=tmp_coff_var_idx;
    l.neg_coff=tmp_coff;
}
//all coffs are positive, go through all terms of the literal
int64_t ls_solver::delta_lit(lit &l){
    int64_t delta=l.key;
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
//return the upper round of (a/b): (-3.5)->-4; (3.5)->4
int64_t ls_solver::devide(int64_t a, int64_t b){
    int64_t up_round=(std::abs(a))/(b);
    if(std::abs(a)%b>0){up_round++;}
    return a>0?up_round:-up_round;
}
void ls_solver::insert_operation(int var_idx,int64_t change_value,int &operation_idx){
    int64_t future_solution=_solution[var_idx]+change_value;
    if(future_solution>=_vars[var_idx].low_bound&&future_solution<=_vars[var_idx].upper_bound){
        operation_var_idx_vec[operation_idx]=var_idx;
        operation_change_value_vec[operation_idx++]=change_value;
    }
}

void ls_solver::add_swap_operation(int &operation_idx){
    int clause_idx=sat_clause_with_false_literal->element_at(mt()%sat_clause_with_false_literal->size());
    clause *cl=&(_clauses[clause_idx]);
    lit *l;
    int var_idx;
    int64_t change_value=0;
    for(int l_idx:cl->literals){
        l=&(_lits[std::abs(l_idx)]);
        if((l->delta>0&&l_idx>0)||(l->delta<=0&&l_idx<0)){//determine a false literal
            for(int i=0;i<l->neg_coff.size();i++){
                var_idx=l->neg_coff_var_idx[i];
                if(l_idx>0){change_value=devide(l->delta, l->neg_coff[i]);}//delta should <=0, while it is now >0, it should enlarge by (-delta/-coff) pos
                else{change_value=devide(l->delta-1, l->neg_coff[i]);}//delta should >=1, while it is now <=0, it should enlarge by (1-delta/-coff) neg
                insert_operation(var_idx, change_value, operation_idx);
            }
            for(int i=0;i<l->pos_coff.size();i++){
                var_idx=l->pos_coff_var_idx[i];
                if(l_idx>0){change_value=devide(-l->delta,l->pos_coff[i]);}//delta should <=0, while it is now >0, it should enlarge by (-delta/coff) neg
                else{change_value=devide(1-l->delta, l->pos_coff[i]);}//delta should >=1, while it is now <=0, it should enlarge by (1-delta/coff) pos
                insert_operation(var_idx, change_value, operation_idx);//do not consider tabu here
            }
        }
    }
}
//print
void ls_solver::print_formula(){
    for(int i=0;i<_num_clauses;i++){
        clause *cl=&(_clauses[i]);
        std::cout<<i<<"\n";
        for(int l_idx: cl->literals){
            if(l_idx<0){std::cout<<"neg: ";}
            print_literal(_lits[std::abs(l_idx)]);}
        std::cout<<"\n";
    }
}

void ls_solver::print_formula_pbs(){
    std::cout<<"p wcnf "<<_num_vars<<" "<<(_num_lits-_num_vars*2)<<" "<<_num_vars+1<<"\n";
    for(int lit_idx=1;lit_idx<_num_lits;lit_idx++){
        lit *l=&(_lits[lit_idx]);
        if(l->pos_coff.size()==1&&l->neg_coff.size()==0&&l->pos_coff[0]==1&&l->key==-1){continue;}
        if(l->neg_coff.size()==1&&l->pos_coff.size()==0&&l->neg_coff[0]==1&&l->key==0){continue;}
        if(l->lits_index==0){continue;}
        print_lit_pbs(_lits[lit_idx]);
    }
    std::cout<<"2 0 1 1 0\n";
}

void ls_solver::print_literal(lit &l){
    if(!l.is_lia_lit){std::cout<<_vars[l.delta].var_name<<"\n";}
    else{
    for(int i=0;i<l.pos_coff.size();i++)
        {std::cout<<"( "<<l.pos_coff[i]<<" * "<<_vars[l.pos_coff_var_idx[i]].var_name<<" ) + ";}
    for(int i=0;i<l.neg_coff.size();i++)
        {std::cout<<"( -"<<l.neg_coff[i]<<" * "<<_vars[l.neg_coff_var_idx[i]].var_name<<" ) + ";}
    std::cout<<"( "<<l.key<<" ) "<<(l.is_equal?"==":"<=")<<" 0\n";
    }
}

void ls_solver::print_lit_pbs(lit &l){
    int64_t degree=l.key;
    for(int i=0;i<l.pos_coff.size();i++){degree+=l.pos_coff[i];}
    std::cout<<_num_vars+1<<" "<<degree<<" ";
    for(int i=0;i<l.pos_coff.size();i++)
    {std::cout<<l.pos_coff[i]<<" "<<-(l.pos_coff_var_idx[i]+1)<<" ";}
    for(int i=0;i<l.neg_coff.size();i++)    {std::cout<<l.neg_coff[i]<<" "<<l.neg_coff_var_idx[i]+1<<" ";}
    std::cout<<"0\n";
}

//calculate score
int ls_solver::critical_score(uint64_t var_idx, int64_t change_value){
    lit *l;
    clause *cp;
    int critical_score=0;
    int64_t delta_old,delta_new,l_clause_idx;
    //number of make_lits in a clause
    int make_break_in_clause=0;
    variable *var=&(_vars[var_idx]);
    for(int i=0;i<var->literals.size();i++){
        l=&(_lits[std::abs(var->literals[i])]);
        l_clause_idx=var->literal_clause[i];
        delta_old=l->delta;
        delta_new=delta_old+(var->literal_coff[i]*change_value);//l_clause_idx means that the coff is positive, and vice versa
        if((!l->is_equal&&delta_old<=0&&delta_new>0)||(l->is_equal&&delta_old==0&&delta_new!=0)) make_break_in_clause=(var->literals[i]>0)?(make_break_in_clause-1):(make_break_in_clause+1);
        else if((!l->is_equal&&delta_old>0&&delta_new<=0)||(l->is_equal&&delta_old!=0&&delta_new==0)) make_break_in_clause=(var->literals[i]>0)?(make_break_in_clause+1):(make_break_in_clause-1);
        //enter a new clause or the last literal
        if( (i!=(var->literals.size()-1)&&l_clause_idx!=var->literal_clause[i+1]) ||i==(var->literals.size()-1)){
            cp=&(_clauses[std::abs(l_clause_idx)]);
            if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) critical_score+=cp->weight;
            else if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) critical_score-=cp->weight;
            make_break_in_clause=0;
        }
    }
    return critical_score;
}

int64_t ls_solver::critical_subscore(uint64_t var_idx, int64_t change_value){
    int64_t critical_subscore=0;
    int64_t delta_old,delta_new;
    variable *var=&(_vars[var_idx]);
    int lit_idx,l_clause_idx;
    //the future min delta containing var
    int64_t new_future_min_delta=INT64_MAX;
    bool contained_in_min_delta_lit=false;//determing if the var appears in the lit with min delta
    lit_occur->clear();
    for(int i=0;i<var->literals.size();i++){
        lit_idx=var->literals[i];
        l_clause_idx=var->literal_clause[i];
        lit_occur->insert_element(lit_idx);
        if(lit_idx==_clauses[l_clause_idx].min_delta_lit_index){contained_in_min_delta_lit=true;}
        delta_new=_lits[std::abs(lit_idx)].delta+(change_value*var->literal_coff[i]);
        convert_to_pos_delta(delta_new, lit_idx);
        if(delta_new<new_future_min_delta){new_future_min_delta=delta_new;}
        //enter a new clause or the last literal
        if((i!=(var->literals.size()-1)&&l_clause_idx!=var->literal_clause[i+1])||i==(var->literals.size()-1)){
            clause *cp=&(_clauses[l_clause_idx]);
            if(new_future_min_delta<=cp->min_delta){critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;}
            else if(contained_in_min_delta_lit){
                for(int lit_idx_in_cp:cp->literals){
                    if(!lit_occur->is_in_array(lit_idx_in_cp)){
                        delta_old=_lits[std::abs(lit_idx_in_cp)].delta;
                        convert_to_pos_delta(delta_old, lit_idx_in_cp);
                        if(delta_old<new_future_min_delta){new_future_min_delta=delta_old;}
                    }
                }
                critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;
            }//if new_future_min_delta>cp->min_delta and var_idx belongs to the min_delta_lit
            new_future_min_delta=INT64_MAX;
            contained_in_min_delta_lit=false;
            lit_occur->clear();
        }
    }
    return critical_subscore;
    }
//sat or unsat a clause, update the delta
void ls_solver::critical_score_subscore(uint64_t var_idx, int64_t change_value){
    static std::vector<int> lit_exist(_num_lits+_additional_len,0);
    variable * var=&(_vars[var_idx]);
    lit *l;
    clause *cp;
    int64_t l_clause_idx,delta_old,delta_new,curr_clause_idx;
    int64_t pos_delta;
    int64_t new_future_min_delta=INT64_MAX;
    int min_delta_lit_idx=-1;
    bool contained_in_min_delta_lit=false;
    int lit_idx;
    lit_occur->clear();
    int make_break_in_clause=0;
    for(int i=0;i<var->literals.size();i++){
        lit_idx=var->literals[i];
        l=&(_lits[std::abs(lit_idx)]);
        l_clause_idx=var->literal_clause[i];
        delta_old=l->delta;
        pos_delta=delta_new=(l->delta+var->literal_coff[i]*change_value);
        convert_to_pos_delta(pos_delta, lit_idx);
        if(pos_delta<new_future_min_delta){
            new_future_min_delta=pos_delta;
            min_delta_lit_idx=lit_idx;
        }
        lit_occur->insert_element(lit_idx);
        if(lit_idx==_clauses[l_clause_idx].min_delta_lit_index){contained_in_min_delta_lit=true;}
        bool is_equal=l->is_equal;
        if((!is_equal&&delta_old<=0&&delta_new>0)||(is_equal&&delta_old==0&&delta_new!=0)){make_break_in_clause=(var->literals[i]>0)?(make_break_in_clause-1):(make_break_in_clause+1);}
        else if((!is_equal&&delta_old>0&&delta_new<=0)||(is_equal&&delta_old!=0&&delta_new==0)){make_break_in_clause=(var->literals[i]>0)?(make_break_in_clause+1):(make_break_in_clause-1);}
        //enter a new clause or the last literal
        if( (i!=(var->literals.size()-1)&&l_clause_idx!=var->literal_clause[i+1]) ||i==(var->literals.size()-1)){
            curr_clause_idx=std::abs(l_clause_idx);
            cp=&(_clauses[curr_clause_idx]);
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {
                unsat_a_clause(curr_clause_idx);//unsat clause
            }
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {
                sat_a_clause(curr_clause_idx);//sat a clause
            }
            cp->sat_count+=make_break_in_clause;
            make_break_in_clause=0;
            if(cp->sat_count>0&&cp->sat_count<cp->literals.size()){sat_clause_with_false_literal->insert_element((int)curr_clause_idx);}
            else{sat_clause_with_false_literal->delete_element((int)curr_clause_idx);}
            //if new_future_min_delta<=cp->min_delta, then min_delta and watch needs updating if var is changed
            if(new_future_min_delta<=cp->min_delta){
                cp->min_delta=new_future_min_delta;
                cp->min_delta_lit_index=min_delta_lit_idx;
            }
            else if(contained_in_min_delta_lit){
                for(int cp_lit_idx:cp->literals){
                    if(!lit_occur->is_in_array(cp_lit_idx)){
                        pos_delta=_lits[std::abs(cp_lit_idx)].delta;
                        convert_to_pos_delta(pos_delta, cp_lit_idx);
                        if(pos_delta<new_future_min_delta){
                            new_future_min_delta=pos_delta;
                            min_delta_lit_idx=cp_lit_idx;
                        }
                    }
                }
            cp->min_delta=new_future_min_delta;
            cp->min_delta_lit_index=min_delta_lit_idx;
            }//if new_future_min_delta>cp->min_delta and var_idx belongs to the watch_lit
            new_future_min_delta=INT64_MAX;
            contained_in_min_delta_lit=false;
            lit_occur->clear();
        }
    }
    for(int i=0;i<var->literals.size();i++){
        lit_idx=std::abs(var->literals[i]);
        if(lit_exist[lit_idx]==0){
            l=&(_lits[lit_idx]);
            l->delta+=(var->literal_coff[i]*change_value);
            lit_exist[lit_idx]=1;
        }
    }
    for(int i=0;i<var->literals.size();i++){
        lit_idx=std::abs(var->literals[i]);
        lit_exist[lit_idx]=0;
    }
}

//check
bool ls_solver::check_solution(){
    clause *cp;
    int unsat_num=0;
    for(uint64_t i=0;i<_num_clauses;i++){
        int sat_count=0;
        cp=&(_clauses[i]);
        for(int lit_idx: cp->literals){
            int64_t delta=delta_lit(_lits[std::abs(lit_idx)]);
            bool is_equal=_lits[std::abs(lit_idx)].is_equal;
            if( (!is_equal&&((delta<=0&&lit_idx>0)||(delta>0&&lit_idx<0))) || (is_equal&&((delta==0&&lit_idx>0)||(delta!=0&&lit_idx<0))) ){sat_count++;}
        }
        if(sat_count!=cp->sat_count){std::cout<<"sat count wrong at clause "<<i<<"\n";}
        if(sat_count==0){unsat_num++;}
    }
    for(int var_idx=0;var_idx<_vars.size();var_idx++){if(_solution[var_idx]>_vars[var_idx].upper_bound||_solution[var_idx]<_vars[var_idx].low_bound){std::cout<<"var "<<var_idx<<" out of range\n";}}
    if(unsat_num==unsat_clauses->size())
        std::cout<<"right solution\n";
    else
        std::cout<<"wrong solution\n";
    return unsat_num==unsat_clauses->size();
}

//local search
bool ls_solver::local_search(){
    int no_improve_cnt=0;
    int flipv;
    int64_t change_value;
    start = std::chrono::steady_clock::now();
    initialize();
    for(_step=1;_step<_max_step;_step++){
        if(0==unsat_clauses->size()){
            check_solution();
            return true;}
        if(_step%1000==0&&(TimeElapsed()>_cutoff)){break;}
        if(no_improve_cnt>500000){initialize();no_improve_cnt=0;}//restart
        flipv=pick_critical_move(change_value);
        if(flipv!=-1){critical_move(flipv, change_value);}
        no_improve_cnt=(update_best_solution())?0:(no_improve_cnt+1);
    }
    return false;
}


}
