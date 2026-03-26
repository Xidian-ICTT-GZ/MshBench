typedef int my_int;

//@ requires module(mainModule, true) &*& 0 <= argc &*& [_]argv(argv, argc, ?arguments);
//@ ensures true;
int main(int argc, char **argv)
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    assert(t == 8);
    return 0;
}