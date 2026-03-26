#include <stdint.h>

typedef short my_short;

/*@ 
predicate foo_params(int16_t x, my_short y) = true;
@*/

void foo(int16_t x, my_short y)
//@ requires foo_params(x, y);
//@ ensures foo_params(x, y);
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

/*@ 
predicate main_predicate() = true;
@*/
int main()
//@ requires main_predicate();
//@ ensures main_predicate();
{
    return 0;
}