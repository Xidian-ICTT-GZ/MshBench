#include "stdlib.h"
#include "stdbool.h"

//@ predicate node(struct node *n, void *key, void *value, struct node *tail) = n != 0 &*& n->next |-> ? &*& n->key |-> key &*& n->value |-> value &*& tail == map_nil() || (tail != 0 && tail == ?);
//@ predicate map_list(struct node *map) = map == 0 || exists k, v, t. map_list(t) &*& node(map, k, v, t);

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct node *map_nil()
    
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
    
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}

void map_dispose(struct node *map)
    
{
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    
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

bool foo_equals(struct foo *f1, struct foo *f2)
    
{
    
    return f1->value == f2->value;
    
}

struct foo *create_foo(int value)
    
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    return foo;
}

int main()
    
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
    assert(c);
    

    
    
    c = map_contains_key(map, fooY, foo_equals);
    assert(!c);
    
    
    
    
    
    
    
    
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}