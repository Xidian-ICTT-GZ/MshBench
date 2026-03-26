#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@
predicate node(struct node *n;) =
    n == 0 ?
        emp
    :
        n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value &*& malloc_block_node(n) &*& node(next);
@*/

/*@
predicate foo(struct foo *f;) =
    f->value |-> _ &*& malloc_block_foo(f);
@*/

struct node *map_nil()
    //@ requires true;
    //@ ensures node(result);
{
    //@ close node(0);
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires node(tail);
    //@ ensures node(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n);
    return n;
}

void map_dispose(struct node *map)
    //@ requires node(map);
    //@ ensures true;
{
    //@ open node(map);
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);
    //@ requires true;
    //@ ensures true;

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires node(map) &*& is_equalsFuncType(equalsFunc) == true;
    //@ ensures node(map);
{
    //@ open node(map);
    if (map == 0) {
        //@ close node(map);
        return false;
    } else {
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map);
            return true;
        } else {
            bool result = map_contains_key(map->next, key, equalsFunc);
            //@ close node(map);
            return result;
        }
    }
}

struct foo {
    int value;
};

bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires true;
    //@ ensures true;
{
    return f1->value == f2->value;
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
    //@ open foo(foo3);
    map = map_cons(foo3, 0, map);
    //@ open foo(foo2);
    map = map_cons(foo2, 0, map);
    //@ open foo(foo1);
    map = map_cons(foo1, 0, map);
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);
    //@ open foo(fooX);
    //@ open foo(fooY);
    
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ assert c == true;
    
    c = map_contains_key(map, fooY, foo_equals);
    //@ assert c == false;
    
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}