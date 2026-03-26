typedef int my_int;

/*@
predicate mainModule() = true;
@*/

int main()
//@ requires mainModule();
//@ ensures mainModule();
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    assert(t == 8);
    return 0;
}