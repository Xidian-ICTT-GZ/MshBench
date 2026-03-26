#include "stdlib.h"
#include "assert.h"

struct node
{
    struct node *next;
    int value;
};

/*@ predicate list(struct node *p) =
    p == 0 ? emp : p->next |-> ?n &*& p->value |-> ?v &*& list(n);
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

    bool result = false;
    if (n1 == 0)
    {
        //@ open list(n1);
        //@ close list(n1);
        result = n2 == 0;
    }
    else if (n2 == 0)
    {
        result = false;
    }
    else if (n1->value != n2->value)
    {
        result = false;
    }
    else
    {
        //@ open list(n1);
        //@ open list(n2);
        bool tmp = equals(n1->next, n2->next);
        //@ close list(n2);
        //@ close list(n1);
        result = tmp;
    }

    return result;
}

void dispose(struct node *l)
//@ requires list(l);
//@ ensures emp;
{

    if (l != 0)
    {
        //@ open list(l);
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
    else
    {
        //@ open list(l);
    }
}

typedef int (*mapfunc)(void *data, int x);

struct node *fmap(struct node *list, mapfunc f, void *data)
//@ requires list(list);
//@ ensures list(result);
{

    if (list == 0)
    {
        //@ open list(list);
        //@ close list(0);
        return 0;
    }
    else
    {
        //@ open list(list);
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);

        struct node *result = list_cons(fvalue, fnext);

        return result;
    }
}

int plusOneFunc(void *data, int x)
//@ requires true;
//@ ensures true;
{
    if (x == INT_MAX)
        abort();

    return x + 1;
}

int main()
//@ requires emp;
//@ ensures emp;
{
    struct node *l = 0;
    //@ close list(0);

    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);

    struct node *l2 = fmap(l, plusOneFunc, 0);

    struct node *l3 = 0;
    //@ close list(0);

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