#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@
predicate nodes(struct node *n;) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value &*& malloc_block_node(n) &*& nodes(next);
@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures nodes(result);
{
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
    
/*@
predicate is_equalsFuncType(equalsFuncType *f) = true;
@*/

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires nodes(map) &*& is_equalsFuncType(equalsFunc);
    //@ ensures nodes(map) &*& is_equalsFuncType(equalsFunc);
{
    //@ open nodes(map);
    if (map == 0) {
        //@ close nodes(map);
        return false;
    } else {
        //@ assert map->key |-> ?k;
        //@ assert map->value |-> ?v;
        //@ assert map->next |-> ?next;
        //@ assert malloc_block_node(map);
        //@ assert nodes(next);
        //@ close is_equalsFuncType(equalsFunc);
        bool eq = equalsFunc(map->key, key);
        //@ open is_equalsFuncType(equalsFunc);
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

/*@
predicate foo(struct foo *f;) = f->value |-> ?val &*& malloc_block_foo(f);
@*/

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foo(f1) &*& foo(f2);
    //@ ensures foo(f1) &*& foo(f2);
{
    //@ open foo(f1);
    //@ open foo(f2);
    bool r = f1->value == f2->value;
    //@ close foo(f1);
    //@ close foo(f2);
    return r;
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures foo(result);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    //@ close foo(foo);
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
    
    //@ close is_equalsFuncType(foo_equals);
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ open is_equalsFuncType(foo_equals);
    assert(c);
    
    //@ close is_equalsFuncType(foo_equals);
    c = map_contains_key(map, fooY, foo_equals);
    //@ open is_equalsFuncType(foo_equals);
    assert(!c);
    
    //@ open foo(foo1);
    free(foo1);
    //@ open foo(foo2);
    free(foo2);
    //@ open foo(foo3);
    free(foo3);
    //@ open foo(fooX);
    free(fooX);
    //@ open foo(fooY);
    free(fooY);
    map_dispose(map);
    return 0;
}