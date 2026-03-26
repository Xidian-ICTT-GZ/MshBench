#include <stdint.h>

typedef short my_short;

void foo(int16_t x, my_short y)
//@ requires true;
//@ ensures true;
{
    int16_t diff = x - y;
    my_short z = (my_short)diff;
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}