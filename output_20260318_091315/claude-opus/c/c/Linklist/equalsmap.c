#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@ predicate map(struct node *m) =
      m == 0 ?
        true
      :
        m->key |-> _ &*& m->value |-> _ &*& m->next |-> ?next &*&
        map(next);
@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures map(result);
{
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
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map);
    //@ ensures true;
{
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);

/*@ predicate nodes_key(struct node *m, void *key, equalsFuncType *equalsFunc) =
      m == 0 ? false
      : equalsFunc(m->key, key) ? true
      : nodes_key(m->next, key, equalsFunc);
@*/

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires map(map);
    //@ ensures map(map) &*& result == nodes_key(map, key, equalsFunc);
{
    if (map == 0)
        return false;
    else {
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

/*@ predicate foo_pred(struct foo *f; int v) = 
      f->value |-> v;
@*/

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foo_pred(f1, ?v1) &*& foo_pred(f2, ?v2);
    //@ ensures foo_pred(f1, v1) &*& foo_pred(f2, v2) &*& result == (v1 == v2);
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures foo_pred(result, value);
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

    bool c = map_contains_key(map, fooX, (equalsFuncType *)foo_equals);
    //@ assert c == true;
    assert(c);

    c = map_contains_key(map, fooY, (equalsFuncType *)foo_equals);
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