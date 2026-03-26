typedef int my_int;

/*@
predicate my_int_ownership(my_int v) = true;
@*/

int main()
    //@ requires true;
    //@ ensures true;
{
    my_int x = 5;
    //@ close my_int_ownership(x);
    int y = x;
    //@ open my_int_ownership(x);
    my_int z = 3;
    //@ close my_int_ownership(z);
    my_int t = x + z;
    //@ open my_int_ownership(z);
    //@ assert t == 8;
    return 0;
}