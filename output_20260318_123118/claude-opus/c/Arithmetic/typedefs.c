typedef int my_int;

/*@ predicate ints(my_int *p; int v) = p |-> v; */

int main()
    //@ requires true;
    //@ ensures true;
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    //@ assert t == 8;
    assert(t == 8);
    return 0;
}