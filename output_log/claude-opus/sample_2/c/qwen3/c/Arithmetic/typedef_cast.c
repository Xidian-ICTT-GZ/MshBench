#include <stdint.h>

typedef short my_short;

/*@ predicate valid_my_short(my_short *p) = p->_;
@*/

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    //@ close valid_my_short(pz);
    //@ assert valid_my_short(pz);
    //@ open valid_my_short(pz);
    void *pv = pz;
    pz = (my_short *)pv;
    //@ close valid_my_short(pz);
    //@ assert valid_my_short(pz);
    //@ open valid_my_short(pz);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}