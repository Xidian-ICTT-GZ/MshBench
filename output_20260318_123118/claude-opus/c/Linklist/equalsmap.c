#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@ 
predicate map(struct node *map;) = 
    map == 0 ?
        emp
    :
        map->key |-> ?k &*& 
        map->value |-> ?v &*& 
        map->next |-> ?n &*& 
        malloc_block_node(map) &*&
        map(n);
@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures map(result);
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires map(tail);
    //@ ensures map(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map);
    //@ ensures true;
{
    if (map != 0) {
        //@ open map(map);
        map_dispose(map->next);
        free(map);
    } else {
        //@ close map(0);
    }
}

typedef bool equalsFuncType(void *key, void *key0);

/*@ 
fixpoint bool map_contains_key_fp(struct node *map, void *key, (void*_, void*_) => bool equalsFunc) {
    switch(map) {
        case 0: return false;
        default: return equalsFunc(map->key, key) || map_contains_key_fp(map->next, key, equalsFunc);
    }
}
@*/

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires map(map);
    //@ ensures map(map) &*& result == map_contains_key_fp(map, key, equalsFunc);
{
    if (map == 0)
        return false;
    else {
        //@ open map(map);
        bool eq = equalsFunc(map->key, key);
        if (eq)
            return true;
        else {
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ close map(map);
            return res;
        }
    }
}

struct foo {
    int value;
};

/*@
predicate foo_pred(struct foo *f;) = 
    f->value |-> ?v &*& malloc_block_foo(f);
@*/

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foo_pred(f1) &*& foo_pred(f2);
    //@ ensures foo_pred(f1) &*& foo_pred(f2) &*& result == (f1->value == f2->value);
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures foo_pred(result);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    //@ close foo_pred(foo);
    return foo;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct foo *foo1 = create_foo(100);
    struct foo *foo2 = create_foo(200);
    struct foo *foo3 = create_foo(300);
    struct node *map = map_nil();
    map = map_cons(foo3, 0, map);
    map = map_cons(foo2, 0, map);
    map = map_cons(foo1, 0, map);
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);

    //@ open foo_pred(fooX);
    //@ open foo_pred(fooY);

    bool c = map_contains_key(map, fooX, (equalsFuncType*)foo_equals);
    assert(c);

    c = map_contains_key(map, fooY, (equalsFuncType*)foo_equals);
    assert(!c);

    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}