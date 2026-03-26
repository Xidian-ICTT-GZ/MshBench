#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@

predicate node(struct node *n; struct node *next, void *key, void *value) =
    n->next |-> next &*& n->key |-> key &*& n->value |-> value;

predicate map(struct node *m) =
    m == 0 ?
        true
    :
        node(m, ?next, ?key, ?value) &*& malloc_block_node(m) &*& map(next);

@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures map(result);
{
    //@ close map(0);
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
    //@ close node(n, tail, key, value);
    //@ close map(n);
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map);
    //@ ensures true;
{
    
    if (map != 0) {
        //@ open map(map);
        //@ open node(map, ?next, ?key, ?value);
        map_dispose(map->next);
        free(map);
    } else {
        //@ open map(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    //@ requires true;
    //@ ensures true;

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires map(map) &*& is_equalsFuncType(equalsFunc);
    //@ ensures map(map) &*& is_equalsFuncType(equalsFunc);
{
    
    if (map == 0)
        return false;
    else {
        
        //@ open map(map);
        //@ open node(map, ?next, ?k, ?v);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map, next, k, v);
            //@ close map(map);
            return true;
        } else {
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ close node(map, next, k, v);
            //@ close map(map);
            return res;
        }
    }
}

struct foo {
    int value;
};

/*@ predicate foo(struct foo *f; int v) = f->value |-> v &*& malloc_block_foo(f); @*/

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
    
    
    
    
    
    
    
    
    //@ open foo(foo1, _);
    free(foo1);
    //@ open foo(foo2, _);
    free(foo2);
    //@ open foo(foo3, _);
    free(foo3);
    //@ open foo(fooX, _);
    free(fooX);
    //@ open foo(fooY, _);
    free(fooY);
    map_dispose(map);
    return 0;
}