typedef int my_int;

/*@
predicate my_int_own(my_int v) = true;
@*/

int main()
//@ requires true;
//@ ensures true;
{
    my_int x = 5;
    //@ close my_int_own(x);
    int y = x;
    //@ open my_int_own(x);
    my_int z = 3;
    //@ close my_int_own(z);
    my_int t = x + z;
    //@ open my_int_own(z);
    assert(t == 8);
    return 0;
}