#include <stdint.h>

typedef short my_short;

/*@
predicate foo_pre() = true;
predicate foo_post() = true;
@*/

/*@
predicate main_pre() = true;
predicate main_post() = true;
@*/

void foo(int16_t x, my_short y)
/*@ requires foo_pre(); @*/
/*@ ensures foo_post(); @*/
{
    my_short z = (my_short)(x - y);
    z = (int16_t)(x - y);
    my_short *pz = &z;
    void *pv = pz;
    pz = (my_short *)pv;
}

int main()
/*@ requires main_pre(); @*/
/*@ ensures main_post(); @*/
{
    return 0;
}