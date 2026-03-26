#include <stdint.h>

typedef short my_short;

/*@ predicate valid_my_short(my_short *p) =
      p |-> ?v &*&
      (0 <= v && v <= 32767) || (-32768 <= v && v < 0);
@*/

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    //@ assert valid_my_short(pz);
    void *pv = pz;
    pz = (my_short *)pv;
    //@ assert valid_my_short(pz);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}