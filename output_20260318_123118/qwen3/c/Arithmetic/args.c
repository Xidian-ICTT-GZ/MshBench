/*@ predicate argv_chars(char **argv, int n) =
    n == 0 ?
        true
    :
        argv != 0 &*&
        [_]argv[0..n] |-> ?cs &*&
        chars(cs[0], ?m0) &*& m0 >= 0 &*&
        argv_chars(argv + 1, n - 1);
@*/

//@ predicate main_args(int argc, char **argv) = argc >= 0 &*& argv_chars(argv, argc);

int main(int argc, char **argv) 
//@ requires main_args(argc, argv);
//@ ensures true;
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i &*& i <= argc &*& main_args(argc, argv);
    {
        puts(*(argv + i));
    }
    
    return 0;
}