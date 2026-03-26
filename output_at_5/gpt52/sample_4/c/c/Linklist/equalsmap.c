#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@
predicate nodes(struct node *n) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& n->key |-> ?k &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next);

predicate is_equals_func(equalsFuncType *f) = true;

predicate foo(struct foo *f; int v) = f->value |-> v &*& malloc_block_foo(f);
@*/

struct node *map_nil()
    
    
    //@ requires true;
    //@ ensures result == 0 &*& nodes(result);
{
    //@ close nodes(0);
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    
    
    //@ requires nodes(tail);
    //@ ensures nodes(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close nodes(n);
    return n;
}

void map_dispose(struct node *map)
    
    
    //@ requires nodes(map);
    //@ ensures true;
{
    
    //@ open nodes(map);
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    
    

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    
    
    //@ requires nodes(map) &*& is_equals_func(equalsFunc);
    //@ ensures nodes(map) &*& is_equals_func(equalsFunc);
{
    
    if (map == 0) {
        //@ close nodes(0);
        return false;
    } else {
        //@ open nodes(map);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close nodes(map);
            return true;
        } else {
            bool r = map_contains_key(map->next, key, equalsFunc);
            //@ close nodes(map);
            return r;
        }
    }
}

struct foo {
    int value;
};

bool foo_equals(struct foo *f1, struct foo *f2)
    
    
    //@ requires foo(f1, ?v1) &*& foo(f2, ?v2);
    //@ ensures foo(f1, v1) &*& foo(f2, v2) &*& result == (v1 == v2);
{
    
    
    return f1->value == f2->value;
    
    
}

struct foo *create_foo(int value)
    
    
    //@ requires true;
    //@ ensures foo(result, value);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    //@ close foo(foo, value);
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
    
    
    
    
    
    
    
    
    //@ open foo(foo1, 100);
    //@ open foo(foo2, 200);
    //@ open foo(foo3, 300);
    //@ open foo(fooX, 200);
    //@ open foo(fooY, 400);
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}