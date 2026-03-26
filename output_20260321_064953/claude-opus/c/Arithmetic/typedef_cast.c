#include <stdint.h>

typedef short my_short;

/*@
predicate my_short_ptr(my_short *p) = p |-> _;
@*/

void foo(int16_t x, my_short y)
    //@ requires true;
    //@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    /*@ open my_short_ptr(&z); @*/ 
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
    //@ close my_short_ptr(&z);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}