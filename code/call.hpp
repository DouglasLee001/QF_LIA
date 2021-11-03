//
//  call.hpp
//  idl_ls_light
//
//  Created by DouglasLee on 2021/9/6.
//

#ifndef call_hpp
#define call_hpp

#include <stdio.h>
#include"lia_ls.h"

namespace call {
class Call_fun{
public:
    Call_fun();
    int num;
    int func(int argc,char *argv[]);
    lia::ls_solver * m_ls;
};

}

#endif /* call_hpp */
