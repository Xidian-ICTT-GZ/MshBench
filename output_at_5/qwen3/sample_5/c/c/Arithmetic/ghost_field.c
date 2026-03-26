#include "stdlib.h"

struct foo {
    int x;
    
};

//@ predicate Foo(struct foo *f) = f->x ~~> ? &*& true;

int main() 
    
    
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    
    //@ open Foo(f);
    f->x = 5;
    //@ close Foo(f);
    
    
    free(f);
    return 0;
}