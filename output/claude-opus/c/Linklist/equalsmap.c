#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@
predicate nodes(struct node *node) =
    node == 0 ?
        true
    :
        node->next |-> ?next &*& node->key |-> ?key &*& node->value |-> ?value &*&
        malloc_block_node(node) &*&
        nodes(next);
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
    //@ requires true;
    //@ ensures true;

/*@
predicate equals_func(equalsFuncType *func) = is_equalsFuncType(func) == true;
@*/

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires nodes(map) &*& is_equalsFuncType(equalsFunc) == true;
    //@ ensures nodes(map);
{
    //@ open nodes(map);
    if (map == 0)
        return false;
    else {
        //@ close nodes(map);
        //@ open nodes(map);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close nodes(map);
            return true;
        } else {
            bool result = map_contains_key(map->next, key, equalsFunc);
            //@ close nodes(map);
            return result;
        }
    }
}

struct foo {
    int value;
};

/*@
predicate foo(struct foo *f, int v) =
    f->value |-> v &*& malloc_block_foo(f);
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
    //@ open foo(fooX, 200);
    //@ close foo(fooX, 200);
    //@ open foo(fooY, 400);
    //@ close foo(fooY, 400);
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ open foo(foo1, 100);
    //@ close foo(foo1, 100);
    //@ open foo(foo2, 200);
    //@ close foo(foo2, 200);
    //@ open foo(foo3, 300);
    //@ close foo(foo3, 300);
    c = map_contains_key(map, fooY, foo_equals);
    //@ open foo(foo1, 100);
    //@ open foo(foo2, 200);
    //@ open foo(foo3, 300);
    free(foo1);
    free(foo2);
    free(foo3);
    //@ open foo(fooX, 200);
    free(fooX);
    //@ open foo(fooY, 400);
    free(fooY);
    map_dispose(map);
    return 0;
}