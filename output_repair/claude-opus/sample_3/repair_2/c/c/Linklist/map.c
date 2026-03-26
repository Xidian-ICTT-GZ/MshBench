#include "stdlib.h"
#include "assert.h"

struct node
{
    struct node *next;
    int value;
};

/*@
predicate list(struct node *p;) =
    p == 0 ?
        emp
    :
        p->next |-> ?n &*& p->value |-> ?v &*& malloc_block_node(p) &*& list(n);
@*/

/*@
predicate_family mapfunc_pre(void *f)(void *data, int x);
predicate_family mapfunc_post(void *f)(void *data, int x, int result);
@*/

/*@
predicate_family_instance mapfunc_pre(plusOneFunc)(void *data, int x) = true;
predicate_family_instance mapfunc_post(plusOneFunc)(void *data, int x, int result) = true;
@*/

struct node *list_cons(int value, struct node *next)
//@ requires list(next);
//@ ensures list(result);
{
    struct node *result = (struct node *)malloc(sizeof(struct node));
    if (result == 0)
    {
        abort();
    }
    result->value = value;
    result->next = next;
    //@ close list(result);
    return result;
}

bool equals(struct node *n1, struct node *n2)
//@ requires list(n1) &*& list(n2);
//@ ensures list(n1) &*& list(n2);
{
    //@ open list(n1);
    //@ open list(n2);
    bool result = false;
    if (n1 == 0)
    {
        result = n2 == 0;
        //@ close list(n1);
        //@ close list(n2);
    }
    else if (n2 == 0)
    {
        result = false;
        //@ close list(n1);
        //@ close list(n2);
    }
    else if (n1->value != n2->value)
    {
        result = false;
        //@ close list(n1);
        //@ close list(n2);
    }
    else
    {
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
        //@ close list(n1);
        //@ close list(n2);
    }

    return result;
}

void dispose(struct node *l)
//@ requires list(l);
//@ ensures true;
{
    //@ open list(l);
    if (l != 0)
    {
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (*mapfunc)(void *data, int x);

struct node *fmap(struct node *list, mapfunc f, void *data)
//@ requires list(list) &*& mapfunc_pre(f)(data, _);
//@ ensures list(result) &*& list(list) &*& mapfunc_post(f)(data, _, _);
{
    //@ open list(list);
    if (list == 0)
    {
        //@ close list(0);
        //@ close list(list);
        return 0;
    }
    else
    {
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);

        struct node *result = list_cons(fvalue, fnext);
        //@ close list(list);
        return result;
    }
}

int plusOneFunc(void *data, int x)
//@ requires mapfunc_pre(plusOneFunc)(data, x);
//@ ensures mapfunc_post(plusOneFunc)(data, x, result);
{
    if (x == INT_MAX)
        abort();

    return x + 1;
}

int main()
//@ requires true;
//@ ensures true;
{
    //@ close list(0);
    struct node *l = 0;

    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);

    struct node *l2 = fmap(l, plusOneFunc, 0);

    //@ close list(0);
    struct node *l3 = 0;

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