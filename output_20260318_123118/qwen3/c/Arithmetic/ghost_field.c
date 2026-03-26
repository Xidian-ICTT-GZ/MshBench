/*@ predicate foo(struct foo *f; int x) = f->x |-> x; @*/

int main()
//@ requires true;
//@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    //@ assert f != 0;
    f->x = 5;
    //@ close foo(f, 5);
    
    free(f);
    return 0;
}