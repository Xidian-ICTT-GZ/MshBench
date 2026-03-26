#include "stdlib.h"

/*@ predicate node(struct node *n, void *key, void *value, struct node *next) =
    n != 0 &*&
    n->key |-> key &*&
    n->value |-> value &*&
    n->next |-> next;
@*/

/*@ predicate map(struct node *m, list<pair<void *, void *>> items) =
    m == 0 ?
        items == nil
    :
        exists<pair<void *, void *>> item &*&
        node(m, item.fst, item.snd, ?next) &*&
        map(next, ?rest) &*&
        items == cons(item, rest);
@*/

/*@ predicate foo(struct foo *f, int value) =
    f != 0 &*&
    f->value |-> value;
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct node *map_nil()
//@ requires true;
//@ ensures map(result, nil);
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
//@ requires map(tail, ?items);
//@ ensures map(result, cons(pair(key, value), items));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n, key, value, tail);
    //@ close map(n, cons(pair(key, value), items));
    return n;
}

void map_dispose(struct node *map)
//@ requires map(map, ?items);
//@ ensures true;
{
    if (map != 0) {
        //@ open map(map, items);
        //@ open node(map, _, _, ?next);
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    
bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
//@ requires map(map, ?items) &*& is_equalsFuncType(equalsFunc, ?eqPred);
//@ ensures map(map, items) &*& result == mem(pair(_, key), items);
{
    if (map == 0)
        return false;
    else {
        //@ open map(map, items);
        //@ open node(map, ?k, ?v, ?next);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close map(map, items);
            return true;
        } else {
            //@ close map(next, ?rest);
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ close map(map, items);
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
    //@ assert c == true;
    assert(c);
    
    c = map_contains_key(map, fooY, foo_equals);
    //@ assert c == false;
    assert(!c);
    
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}