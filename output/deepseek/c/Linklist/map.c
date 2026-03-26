#include "stdlib.h"
#include "assert.h"
/*@
predicate nodes(struct node *n; list<int> vs) =
    n == 0 ?
        vs == nil
    :
        n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);
@*/

struct node
{
    struct node *next;
    int value;
};

struct node *list_cons(int value, struct node *next)
//@ requires nodes(next, ?vs)
//@ ensures nodes(result, cons(value, vs));
{
    struct node *result = (struct node *)malloc(sizeof(struct node));
    if (result == 0)
    {
        abort();
    }
    result->value = value;
    result->next = next;

    return result;
}

bool equals(struct node *n1, struct node *n2)
//@ requires nodes(n1, ?vs1) &*& nodes(n2, ?vs2)
//@ ensures nodes(n1, vs1) &*& nodes(n2, vs2) &*& result == (vs1 == vs2);
{
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else
    {
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
    }

    return result;
}

void dispose(struct node *l)
//@ requires nodes(l, _)
//@ ensures true;
{
    if (l != 0)
    {
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (*mapfunc)(void *data, int x);
/*@
predicate mapfunc_pre(mapfunc f, void *data, int x;) = true;
predicate mapfunc_post(mapfunc f, void *data, int x, int result;) = true;
@*/

struct node *fmap(struct node *list, mapfunc f, void *data)
//@ requires nodes(list, ?vs) &*& is_mapfunc(f) == true &*& foreach(vs, mapfunc_pre(f, data));
//@ ensures nodes(result, ?vs2) &*& foreach(vs2, mapfunc_post(f, data)) &*& length(vs) == length(vs2);
{
    if (list == 0)
    {
        return 0;
    }
    else
    {
        //@ open nodes(list, vs);
        //@ open foreach(vs, mapfunc_pre(f, data));
        int fvalue = f(data, list->value);
        //@ close mapfunc_post(f, data, list->value, fvalue);
        struct node *fnext = fmap(list->next, f, data);
        //@ assert nodes(fnext, ?vsnext) &*& foreach(vsnext, mapfunc_post(f, data));
        struct node *result = list_cons(fvalue, fnext);
        //@ close foreach(cons(fvalue, vsnext), mapfunc_post(f, data));
        return result;
    }
}

int plusOneFunc(void *data, int x)
//@ requires mapfunc_pre(plusOneFunc, data, x)
//@ ensures mapfunc_post(plusOneFunc, data, x, result) &*& result == x + 1;
{
    if (x == INT_MAX)
        abort();

    return x + 1;
}

int main()
//@ requires true
//@ ensures true;
{
    struct node *l = 0;
    //@ close nodes(0, nil);
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    //@ close foreach(cons(1, cons(2, cons(3, nil))), mapfunc_pre(plusOneFunc, 0));
    struct node *l2 = fmap(l, plusOneFunc, 0);

    struct node *l3 = 0;
    //@ close nodes(0, nil);
    l3 = list_cons(4, l3);
    l3 = list_cons(3, l3);
    l3 = list_cons(2, l3);
    bool tmp = equals(l2, l3);

    assert(tmp);
    dispose(l);
    dispose(l2);
    dispose(l3);
    return 0;
}