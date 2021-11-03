//
//  call.cpp
//  lia_ls
//
//  Created by DouglasLee on 2021/11/2.
//

#include "call.hpp"
using namespace std;
namespace call{
Call_fun::Call_fun(){
    m_ls=new lia::ls_solver();
}

int Call_fun::func(int argc,char *argv[]){
    return 0;
}
}
using namespace call;
int main(int argc,char *argv[]){
    Call_fun c;
    c.func(argc,argv);
    return 0;
}
