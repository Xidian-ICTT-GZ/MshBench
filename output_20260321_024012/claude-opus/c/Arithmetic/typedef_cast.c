#include <stdint.h>

typedef short my_short;

/*@
predicate my_short_ptr(my_short *p) = p |-> ?v;
@*/

void foo(int16_t x, my_short y)
  //@ requires true;
  //@ ensures true;
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    //@ close my_short_ptr(&z);
    my_short *pz = &z;
    void *pv = pz;
    //@ open my_short_ptr(pz);
    pz = (my_short *)pv;
}

int main()
  //@ requires true;
  //@ ensures true;
{
    return 0;
}