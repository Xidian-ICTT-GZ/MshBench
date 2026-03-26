#include <stdint.h>

typedef short my_short;

/*@
predicate my_short_box(my_short *p; my_short v) =
    p != 0 &*& integer(p, v);
@*/

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    //@ close my_short_box(&z, z);
    z = (int16_t)(x - y);
    //@ close my_short_box(&z, z);
    my_short *pz = &z;
    //@ open my_short_box(pz, z);
    void *pv = pz;
    pz = (my_short *)pv;
    //@ close my_short_box(pz, z);
    //@ open my_short_box(pz, z);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}