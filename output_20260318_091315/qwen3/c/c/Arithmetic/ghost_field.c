/*@ predicate foo(struct foo *p; int v) = p->x |-> v; @*/

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