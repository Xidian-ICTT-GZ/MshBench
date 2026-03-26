#include "stdlib.h"

/*@

predicate node(struct node *p; void *key, void *value, struct node *next) =
    p != 0 &*&
    p->key |-> key &*&
    p->value |-> value &*&
    p->next |-> next &*&
    struct_node(p);

fixpoint bool nodekey_equals(void *k1, void *k2, equalsFuncType *eq) {
    return eq(k1, k2);
}

predicate map(struct node *map; list<tuple<void*,void*>> ms) =
    map == 0 ? ms == nil :
    map != 0 &*&
    node(map; ?k, ?v, ?tail) &*&
    map(tail; ?rest) &*&
    ms == cons(tuple(k,v), rest);

predicate foo(struct foo *f; int value) =
    f != 0 &*&
    f->value |-> value &*&
    struct_foo(f);

@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct node *map_nil()
{
    //@ ensures map(result; nil);
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
{
    //@ requires map(tail; ?ms);
    //@ ensures node(result; key, value, tail) &*& map(result; cons(tuple(key,value), ms));
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map; ?ms);
    //@ ensures true;
{
    if (map != 0) {
        //@ open map(map; ms);
        //@ open node(map; _, _, _);
        //@ map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires map(map; ?ms);
    //@ ensures result <==> exists(?i, nth(i, ms, ?t) &*& t == tuple(key, ?v));
{
    if (map == 0)
        return false;
    else {
        //@ open map(map; ms);
        //@ open node(map; ?k, ?v, ?tail);
        bool eq = equalsFunc(map->key, key);
        if (eq)
            return true;
        else {
            return map_contains_key(map->next, key, equalsFunc);
        }
    }
}

struct foo {
    int value;
};

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foo(f1; ?v1) &*& foo(f2; ?v2);
    //@ ensures result <==> v1 == v2;
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures foo(result; value);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
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
    //@ assert c;
    assert(c);

    c = map_contains_key(map, fooY, foo_equals);
    //@ assert !c;
    assert(!c);

    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}