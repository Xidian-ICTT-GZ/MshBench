#include "stdlib.h"

/*@
predicate nodes(struct node *n) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& n->key |-> ?k &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next);

predicate foo(struct foo *f; int v) =
    f->value |-> v &*& malloc_block_foo(f);
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct node *map_nil()
    //@ requires true;
    //@ ensures nodes(result);
    
    
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
    //@ requires nodes(map) &*& is_equalsFuncType(equalsFunc) == true;
    //@ ensures nodes(map) &*& is_equalsFuncType(equalsFunc) == true;
    
    
{
    //@ open nodes(map);
    if (map == 0) {
        //@ close nodes(0);
        return false;
    } else {
        
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close nodes(map);
            return true;
        } else {
            
            
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ close nodes(map);
            return res;
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
    //@ open foo(f1, v1);
    //@ open foo(f2, v2);
    
    
    bool r = f1->value == f2->value;
    
    
    //@ close foo(f1, v1);
    //@ close foo(f2, v2);
    return r;
    
    
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
    //@ open foo(foo3, 300);
    map = map_cons(foo3, 0, map);
    //@ close foo(foo3, 300);
    //@ open foo(foo2, 200);
    map = map_cons(foo2, 0, map);
    //@ close foo(foo2, 200);
    //@ open foo(foo1, 100);
    map = map_cons(foo1, 0, map);
    //@ close foo(foo1, 100);
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);
    
    

    
    
    
    
    
    
    
    
    //@ open foo(fooX, 200);
    //@ open foo(foo1, 100);
    //@ open foo(foo2, 200);
    //@ open foo(foo3, 300);
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ close foo(foo3, 300);
    //@ close foo(foo2, 200);
    //@ close foo(foo1, 100);
    //@ close foo(fooX, 200);
    assert(c);
    

    
    
    //@ open foo(fooY, 400);
    //@ open foo(foo1, 100);
    //@ open foo(foo2, 200);
    //@ open foo(foo3, 300);
    c = map_contains_key(map, fooY, foo_equals);
    //@ close foo(foo3, 300);
    //@ close foo(foo2, 200);
    //@ close foo(foo1, 100);
    //@ close foo(fooY, 400);
    assert(!c);
    
    
    
    
    
    
    
    
    //@ open foo(foo1, 100);
    free(foo1);
    //@ open foo(foo2, 200);
    free(foo2);
    //@ open foo(foo3, 300);
    free(foo3);
    //@ open foo(fooX, 200);
    free(fooX);
    //@ open foo(fooY, 400);
    free(fooY);
    map_dispose(map);
    return 0;
}