#include "stdlib.h"
/*@
predicate node(struct node *n; struct node *next, void *key, void *value) =
    n->next |-> next &*& n->key |-> key &*& n->value |-> value &*& malloc_block_node(n);
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@
predicate lseg(struct node *first, struct node *last; list<pair<void *, void *> > pairs) =
    first == last ?
        pairs == nil
    :
        node(first, ?next, ?key, ?value) &*& lseg(next, last, ?tailpairs) &*& pairs == cons(pair(key, value), tailpairs);
@*/

/*@
predicate map(struct node *n; list<pair<void *, void *> > pairs) =
    lseg(n, 0, pairs);
@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures map(result, nil);
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires map(tail, ?pairs);
    //@ ensures map(result, cons(pair(key, value), pairs));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n, tail, key, value);
    //@ close lseg(n, 0, cons(pair(key, value), pairs));
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map, ?pairs);
    //@ ensures true;
{
    //@ open map(map, pairs);
    if (map != 0) {
        //@ open lseg(map, 0, pairs);
        //@ open node(map, ?next, ?key, ?value);
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    //@ requires true;
    //@ ensures true;

/*@
predicate equalsFuncState(equalsFuncType *equalsFunc) = true;
@*/

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires map(map, ?pairs) &*& equalsFuncState(equalsFunc);
    //@ ensures map(map, pairs) &*& equalsFuncState(equalsFunc);
{
    //@ open map(map, pairs);
    if (map == 0) {
        //@ close map(map, pairs);
        return false;
    } else {
        //@ open lseg(map, 0, pairs);
        //@ open node(map, ?next, ?k, ?v);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map, next, k, v);
            //@ close lseg(map, 0, pairs);
            //@ close map(map, pairs);
            return true;
        } else {
            //@ close node(map, next, k, v);
            //@ close lseg(next, 0, ?tailpairs);
            //@ close map(next, tailpairs);
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ open map(next, tailpairs);
            //@ open lseg(next, 0, tailpairs);
            //@ open node(map, next, k, v);
            //@ close node(map, next, k, v);
            //@ close lseg(map, 0, pairs);
            //@ close map(map, pairs);
            return res;
        }
    }
}

struct foo {
    int value;
};

/*@
predicate foo(struct foo *f; int value) =
    f->value |-> value &*& malloc_block_foo(f);
@*/

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foo(f1, ?v1) &*& foo(f2, ?v2);
    //@ ensures foo(f1, v1) &*& foo(f2, v2);
{
    //@ open foo(f1, v1);
    //@ open foo(f2, v2);
    bool result = f1->value == f2->value;
    //@ close foo(f1, v1);
    //@ close foo(f2, v2);
    return result;
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
    
    //@ close equalsFuncState(foo_equals);
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ open equalsFuncState(foo_equals);
    assert(c);
    
    //@ close equalsFuncState(foo_equals);
    c = map_contains_key(map, fooY, foo_equals);
    //@ open equalsFuncState(foo_equals);
    assert(!c);
    
    //@ open map(map, _);
    //@ open lseg(map, 0, _);
    //@ open node(map, ?n1, ?k1, ?v1);
    //@ open lseg(n1, 0, _);
    //@ open node(n1, ?n2, ?k2, ?v2);
    //@ open lseg(n2, 0, _);
    //@ open node(n2, ?n3, ?k3, ?v3);
    //@ open lseg(n3, 0, _);
    //@ close node(n2, n3, k3, v3);
    //@ close lseg(n2, 0, _);
    //@ close node(n1, n2, k2, v2);
    //@ close lseg(n1, 0, _);
    //@ close node(map, n1, k1, v1);
    //@ close lseg(map, 0, _);
    //@ close map(map, _);
    
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