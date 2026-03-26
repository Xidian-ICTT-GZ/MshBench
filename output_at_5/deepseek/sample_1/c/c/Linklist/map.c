#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *n;) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*& nodes(next);
@*/

struct node *list_cons(int value, struct node *next)
    //@ requires nodes(next);
    //@ ensures nodes(result);
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    //@ close nodes(result);
    return result;
}

bool equals(struct node *n1, struct node *n2)
    //@ requires nodes(n1) &*& nodes(n2);
    //@ ensures nodes(n1) &*& nodes(n2);
{
    //@ open nodes(n1);
    //@ open nodes(n2);
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else {
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
    }
    //@ close nodes(n1);
    //@ close nodes(n2);
    return result;
}

void dispose(struct node *l)
    //@ requires nodes(l);
    //@ ensures true;
{
    //@ open nodes(l);
    if (l != 0) {
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);
    
/*@
predicate_family mapfunc_state(void *mapfunc)(void *data, int x);
@*/

struct node *fmap(struct node *list, mapfunc f, void *data)
    //@ requires nodes(list) &*& is_mapfunc(f) == true &*& mapfunc_state(f)(data, ?ignore);
    //@ ensures nodes(list) &*& nodes(result) &*& mapfunc_state(f)(data, ignore);
{
    //@ open nodes(list);
    if (list == 0) {
        //@ close nodes(list);
        return 0;
    } else {
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        //@ close nodes(list);
        struct node *result = list_cons(fvalue, fnext);
        return result;
    }
}

int plusOneFunc(void *data, int x) 
    //@ requires true;
    //@ ensures true;
{
    if (x == INT_MAX) abort();
    return x + 1;
}

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct node *l = 0;
    //@ close nodes(0);
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    
    //@ close mapfunc_state(plusOneFunc)(0, 0);
    struct node *l2 = fmap(l, plusOneFunc, 0);
    //@ open mapfunc_state(plusOneFunc)(0, 0);
    
    struct node *l3 = 0;
    //@ close nodes(0);
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