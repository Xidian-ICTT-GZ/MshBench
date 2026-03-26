#include <stdint.h>

typedef short my_short;

/*@ predicate my_short_ptr(my_short *p; my_short v) = p |-> v; @*/

void foo(int16_t x, my_short y)
    //@ requires true;
    //@ ensures true;
{
    my_short z = (my_short)(x - y);
    //@ close my_short_ptr(&z, z);
    z = (int16_t)(x - y);
    //@ open my_short_ptr(&z, _);
    my_short *pz = &z;
    //@ close my_short_ptr(pz, z);
    void *pv = pz;
    pz = (my_short *)pv;
    //@ open my_short_ptr(pz, _);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}