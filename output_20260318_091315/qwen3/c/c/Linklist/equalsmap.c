/*@ predicate nodes(struct node *map, int length) =
    map == 0 ?
        length == 0
    :
        malloc_block_node(map) &*&
        nodes(map->next, length - 1);
@*/

/*@ predicate foos(struct foo *f) =
    f != 0 ?
        malloc_block_foo(f)
    :
        false;
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct node *map_nil()
//@ requires true;
//@ ensures result == 0;
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
//@ requires foos((struct foo *)key) &*& nodes(tail, _);
//@ ensures nodes(result, _) &*& foos((struct foo *)key) &*& nodes(tail, _);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}

void map_dispose(struct node *map)
//@ requires nodes(map, _);
//@ ensures true;
{
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

typedef bool equalsFuncType(void *key, void *key0);

bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
//@ requires nodes(map, _) &*& foos((struct foo *)key);
//@ ensures nodes(map, _) &*& foos((struct foo *)key);
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
//@ requires foos(f1) &*& foos(f2);
//@ ensures foos(f1) &*& foos(f2);
{
    return f1->value == f2->value;
}

struct foo *create_foo(int value)
//@ requires true;
//@ ensures foos(result);
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