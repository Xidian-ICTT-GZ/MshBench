//@ #include <assert.h>

typedef int my_int;

/*@
predicate main_locals(my_int x, int y, my_int z, my_int t) = true;
@*/

int main()
//@ requires true;
//@ ensures true;
{
    //@ close main_locals(0, 0, 0, 0);
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    //@ open main_locals(_, _, _, _);
    assert(t == 8);
    return 0;
}