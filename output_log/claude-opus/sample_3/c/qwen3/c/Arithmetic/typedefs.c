typedef int my_int;

/*@ predicate int_var(int *p, int v) = p |-> v; */

int main()
    //@ requires true;
    //@ ensures true;
{
    my_int x = 5;
    //@ int x_val = 5;
    int y = x;
    my_int z = 3;
    //@ int z_val = 3;
    my_int t = x + z;
    //@ int t_val = x_val + z_val;
    //@ assert t == 8;
    return 0;
}