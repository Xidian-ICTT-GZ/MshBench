#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@
predicate node(struct node *n; struct node *next, void *key, void *value) =
    n->next |-> next &*& n->key |-> key &*& n->value |-> value &*& malloc_block_node(n);
@*/

/*@
predicate lseg(struct node *from, struct node *to; list<void*> keys, list<void*> values) =
    from == to ?
        keys == nil &*& values == nil
    :
        node(from, ?next, ?key, ?value) &*& lseg(next, to, ?ks, ?vs) &*& keys == cons(key, ks) &*& values == cons(value, vs);
@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures lseg(result, 0, nil, nil);
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires lseg(tail, 0, ?ks, ?vs);
    //@ ensures lseg(result, 0, cons(key, ks), cons(value, vs));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n, tail, key, value);
    //@ close lseg(n, 0, cons(key, ks), cons(value, vs));
    return n;
}

void map_dispose(struct node *map)
    //@ requires lseg(map, 0, ?ks, ?vs);
    //@ ensures true;
{
    //@ open lseg(map, 0, ks, vs);
    if (map != 0) {
        //@ open node(map, ?next, ?key, ?value);
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    //@ requires true;
    //@ ensures true;

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires lseg(map, 0, ?ks, ?vs) &*& is_equalsFuncType(equalsFunc) == true;
    //@ ensures lseg(map, 0, ks, vs);
{
    //@ open lseg(map, 0, ks, vs);
    if (map == 0) {
        //@ close lseg(0, 0, nil, nil);
        return false;
    } else {
        //@ open node(map, ?next, ?k, ?v);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map, next, k, v);
            //@ close lseg(map, 0, ks, vs);
            return true;
        } else {
            //@ close node(map, next, k, v);
            //@ close lseg(map, next, cons(k, ?ks0), cons(v, ?vs0));
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ open lseg(map->next, 0, ks0, vs0);
            //@ open node(map, next, k, v);
            //@ close node(map, next, k, v);
            //@ close lseg(map, 0, cons(k, ks0), cons(v, vs0));
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
    //@ ensures foo(f1, v1) &*& foo(f2, v2) &*& result == (v1 == v2);
{
    //@ open foo(f1, v1);
    //@ open foo(f2, v2);
    bool res = f1->value == f2->value;
    //@ close foo(f1, v1);
    //@ close foo(f2, v2);
    return res;
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
    
    //@ close lseg(0, 0, nil, nil);
    //@ close lseg(map, 0, ?ks, ?vs);
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ assert lseg(map, 0, ks, vs);
    assert(c);
    
    c = map_contains_key(map, fooY, foo_equals);
    //@ assert lseg(map, 0, ks, vs);
    assert(!c);
    
    //@ open lseg(map, 0, ks, vs);
    //@ open lseg(map, ?n1, ?ks1, ?vs1);
    //@ open node(map, ?next1, ?k1, ?v1);
    //@ open lseg(next1, ?n2, ?ks2, ?vs2);
    //@ open node(next1, ?next2, ?k2, ?v2);
    //@ open lseg(next2, ?n3, ?ks3, ?vs3);
    //@ open node(next2, ?next3, ?k3, ?v3);
    //@ open lseg(next3, 0, nil, nil);
    //@ close node(next2, next3, k3, v3);
    //@ close lseg(next2, 0, cons(k3, nil), cons(v3, nil));
    //@ close node(next1, next2, k2, v2);
    //@ close lseg(next1, 0, cons(k2, cons(k3, nil)), cons(v2, cons(v3, nil)));
    //@ close node(map, next1, k1, v1);
    //@ close lseg(map, 0, cons(k1, cons(k2, cons(k3, nil))), cons(v1, cons(v2, cons(v3, nil))));
    map_dispose(map);
    
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
    return 0;
}