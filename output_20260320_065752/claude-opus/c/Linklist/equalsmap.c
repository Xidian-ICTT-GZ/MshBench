#include "stdlib.h"

/*@ 
predicate node(struct node *n;) = n != 0 &*& 
    malloc_block_node(n) &*& 
    n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value; 
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@ 
predicate list(struct node *map;) = 
    map == 0 ? emp : 
    node(map) &*& list(map->next);
@*/

struct node *map_nil()
//@ requires true;
//@ ensures list(result);
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
//@ requires list(tail);
//@ ensures list(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n);
    //@ close list(n);
    return n;
}

void map_dispose(struct node *map)
//@ requires list(map);
//@ ensures true;
{
    
    if (map != 0) {
        //@ open list(map);
        //@ open node(map);
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    
bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
//@ requires list(map);
//@ ensures list(map) &*& result == (exists struct node *n; in_list(map,n) && equalsFunc(n->key,key));
{
    if (map == 0)
        return false;
    else {
        //@ open list(map);
        //@ open node(map);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map);
            //@ close list(map);
            return true;
        } else {
            //@ close node(map);
            //@ close list(map);
            return map_contains_key(map->next, key, equalsFunc);
        }
    }
}

struct foo {
    int value;
};

bool foo_equals(struct foo *f1, struct foo *f2)
//@ requires f1 != 0 &*& f2 != 0;
//@ ensures  true;
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
//@ requires true;
//@ ensures malloc_block_foo(result) &*& result != 0;
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

/*@ 
predicate malloc_block_node(struct node *p;) = true;
predicate malloc_block_foo(struct foo *p;) = true;
@*/