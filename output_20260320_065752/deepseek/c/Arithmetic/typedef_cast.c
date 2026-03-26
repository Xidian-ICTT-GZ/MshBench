#include <stdint.h>

typedef short my_short;

/*@
predicate my_short_pointer(my_short *p;) = true;
@*/

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    //@ close my_short_pointer(pz);
    void *pv = pz;
    //@ open my_short_pointer(pz);
    pz = (my_short *)pv;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}