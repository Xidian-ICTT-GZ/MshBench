#include <stdint.h>

typedef short my_short;

/*@ requires true;
    ensures true;
@*/
void foo(int16_t x, my_short y)

{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

/*@ requires true;
    ensures true;
@*/
int main()

{
    return 0;
}