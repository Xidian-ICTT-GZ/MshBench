typedef int my_int;

/*@ predicate my_int_perm(my_int *p;) =  p |-> _; @*/

int main()
    //@ requires true;
    //@ ensures true;
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    //@ assert t == 8;
    return 0;
}