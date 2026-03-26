/*@ predicate argv_chars(char **argv, int n) =
    n == 0 ?
        true
    :
        argv != 0 &*&
        chars(argv, sizeof(char *)) &*&
        *argv != 0 &*&
        string(*argv) &*&
        argv_chars(argv + 1, n - 1);
@*/

//@ requires argc >= 0 &*& argv_chars(argv, argc);
//@ ensures true;
int main(int argc, char **argv) 
{
    //@ loop_invariant 0 <= i &*& i <= argc &*& argv_chars(argv, argc);
    for (int i = 0; i < argc; i++)
    {
        puts(*(argv + i));
    }
    
    return 0;
}