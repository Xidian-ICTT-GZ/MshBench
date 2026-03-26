#include "stdlib.h"

/*@
predicate node(struct node *n) =
    n == 0 ? true :
    malloc_block(n, sizeof(struct node)) &*&
    n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value &*&
    node(next);
predicate malloc_block_foo(struct foo *p) = malloc_block(p, sizeof(struct foo));
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct node *map_nil()
    //@ requires true;
    //@ ensures result == 0 &*& true;
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires node(tail);
    //@ ensures node(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n);
    return n;
}

void map_dispose(struct node *map)
    //@ requires node(map);
    //@ ensures true;
{
    if (map != 0) {
        //@ open node(map);
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires node(map);
    //@ ensures node(map);
{
    if (map == 0)
        return false;
    else {
        //@ open node(map);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map);
            return true;
        } else {
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ close node(map);
            return res;
        }
    }
}

struct foo {
    int value;
};

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires malloc_block_foo(f1) &*& malloc_block_foo(f2);
    //@ ensures true;
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures malloc_block_foo(result);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    //@ close malloc_block_foo(foo);
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

    bool c = map_contains_key(map, fooX, foo_equals);
    assert(c);

    c = map_contains_key(map, fooY, foo_equals);
    assert(!c);

    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}