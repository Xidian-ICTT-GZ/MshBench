#include "stdlib.h"

/*@
predicate node(struct node *n; void *key, void *value, struct node *next) =
    n != 0 &*& n->key |-> key &*& n->value |-> value &*& n->next |-> next;
predicate lseg(struct node *first, struct node *last; list<pair<void*,void*>> elems) =
    first == last ? elems == nil : 
    node(first, ?key, ?value, ?next) &*& lseg(next, last, ?elems0) &*& elems == cons(pair(key,value), elems0);
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct node *map_nil()
    //@ requires true;
    //@ ensures result == 0 &*& lseg(0,0,nil);
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires lseg(tail, 0, ?elems);
    //@ ensures lseg(result, 0, cons(pair(key,value), elems));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n, key, value, tail);
    //@ close lseg(n, 0, cons(pair(key,value), elems));
    return n;
}

void map_dispose(struct node *map)
    //@ requires lseg(map, 0, ?elems);
    //@ ensures true;
{
    if (map != 0) {
        //@ open lseg(map, 0, ?elems);
        //@ open node(map, ?key, ?value, ?next);
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires lseg(map, 0, ?elems);
    //@ ensures lseg(map, 0, elems);
{
    if (map == 0)
        return false;
    else {
        //@ open lseg(map, 0, elems);
        //@ open node(map, ?k, ?v, ?next);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map, k, v, next);
            //@ close lseg(map, 0, elems);
            return true;
        }
        else {
            //@ close node(map, k, v, next);
            //@ close lseg(map, 0, elems);
            return map_contains_key(map->next, key, equalsFunc);
        }
    }
}

struct foo {
    int value;
};

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires f1->value |-> ?v1 &*& f2->value |-> ?v2;
    //@ ensures f1->value |-> v1 &*& f2->value |-> v2;
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures result != 0 &*& result->value |-> value;
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
    //@ assert c == true || c == false;
    assert(c);

    c = map_contains_key(map, fooY, foo_equals);
    //@ assert c == true || c == false;
    assert(!c);

    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}