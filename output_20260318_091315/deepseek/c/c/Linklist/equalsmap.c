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
        node(first, ?next, ?key, ?value) &*& lseg(next, last, ?tail) &*& pairs == cons(pair(key, value), tail);
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
    //@ close map(n, cons(pair(key, value), pairs));
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map, _);
    //@ ensures true;
{
    //@ open map(map, _);
    if (map != 0) {
        //@ open node(map, ?next, ?key, ?value);
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    //@ requires true;
    //@ ensures true;

/*@
predicate lseg_with_key(struct node *first, struct node *last; list<pair<void *, void *> > pairs, void *key, equalsFuncType *equalsFunc) =
    lseg(first, last, pairs);
@*/

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires lseg_with_key(map, 0, ?pairs, key, equalsFunc);
    //@ ensures lseg_with_key(map, 0, pairs, key, equalsFunc);
{
    //@ open lseg_with_key(map, 0, pairs, key, equalsFunc);
    if (map == 0) {
        //@ close lseg_with_key(map, 0, pairs, key, equalsFunc);
        return false;
    } else {
        //@ open lseg(map, 0, pairs);
        //@ open node(map, ?next, ?k, ?v);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map, next, k, v);
            //@ close lseg(map, 0, pairs);
            //@ close lseg_with_key(map, 0, pairs, key, equalsFunc);
            return true;
        } else {
            //@ close node(map, next, k, v);
            //@ close lseg(map, next, cons(pair(k, v), ?tail));
            //@ close lseg_with_key(next, 0, tail, key, equalsFunc);
            bool result = map_contains_key(map->next, key, equalsFunc);
            //@ open lseg_with_key(next, 0, tail, key, equalsFunc);
            //@ open lseg(next, 0, tail);
            //@ close lseg(map, 0, pairs);
            //@ close lseg_with_key(map, 0, pairs, key, equalsFunc);
            return result;
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
    
    //@ close lseg_with_key(map, 0, cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil))), fooX, foo_equals);
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ open lseg_with_key(map, 0, cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil))), fooX, foo_equals);
    assert(c);
    
    //@ close lseg_with_key(map, 0, cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil))), fooY, foo_equals);
    c = map_contains_key(map, fooY, foo_equals);
    //@ open lseg_with_key(map, 0, cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil))), fooY, foo_equals);
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