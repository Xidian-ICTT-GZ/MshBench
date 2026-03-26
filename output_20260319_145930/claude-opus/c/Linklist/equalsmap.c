#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@
predicate map(struct node *n;) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& n->key |-> _ &*& n->value |-> _ &*&
        malloc_block_node(n) &*& map(next);
@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures result == 0 &*& map(result);
{
    //@ close map(0);
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires map(tail);
    //@ ensures map(result) &*& result != 0;
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close map(n);
    return n;
}

void map_dispose(struct node *map)
    //@ requires map(map);
    //@ ensures true;
{
    //@ open map(map);
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    //@ requires true;
    //@ ensures true;

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires map(map) &*& is_equalsFuncType(equalsFunc) == true;
    //@ ensures map(map);
{
    //@ open map(map);
    if (map == 0) {
        //@ close map(map);
        return false;
    } else {
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close map(map);
            return true;
        } else {
            bool result = map_contains_key(map->next, key, equalsFunc);
            //@ close map(map);
            return result;
        }
    }
}

struct foo {
    int value;
};

/*@
predicate foo(struct foo *f;) =
    f->value |-> _ &*& malloc_block_foo(f);
@*/

bool foo_equals(struct foo *f1, struct foo *f2) //@ : equalsFuncType
    //@ requires true;
    //@ ensures true;
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures result != 0 &*& result->value |-> value &*& malloc_block_foo(result);
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

    c = map_contains_key(map, fooY, foo_equals);
    //@ assert c == true || c == false;

    //@ open map(map);
    //@ open map(map->next);
    //@ open map(map->next->next);
    //@ open map(0);
    free(map->next->next);
    free(map->next);
    free(map);
    free(fooX);
    free(fooY);
    return 0;
}