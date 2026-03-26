#include <stdint.h>

typedef short my_short;

/*@
predicate my_shortp(my_short *p; my_short v) = integer(p, v);
@*/

//@ requires true;
//@ ensures true;
void foo(int16_t x, my_short y)

{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    //@ close my_shortp(pz, z);
    void *pv = pz;
    //@ open my_shortp(pz, z);
    pz = (my_short *)pv;
}

//@ requires true;
//@ ensures true;
int main()

{
    return 0;
}