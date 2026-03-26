#include "stdlib.h"
#include "assert.h"
/*@
predicate nodes(struct node *n;) =
    n == 0 ?
        emp
    :
        n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next);
@*/

struct node {
    struct node *next;
    int value;
};

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
    //@ ensures nodes(n1) &*& nodes(n2) &*& result == (n1 == n2 ? true : (n1 == 0 || n2 == 0 ? false : (n1->value != n2->value ? false : equals(n1->next, n2->next))));
{
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else {
        //@ open nodes(n1);
        //@ open nodes(n2);
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
        //@ close nodes(n1);
        //@ close nodes(n2);
    }
    return result;
}

void dispose(struct node *l)
    //@ requires nodes(l);
    //@ ensures emp;
{
    if (l != 0) {
        //@ open nodes(l);
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);
    
struct node *fmap(struct node *list, mapfunc f, void *data)
    //@ requires nodes(list) &*& is_mapfunc(f) == true;
    //@ ensures nodes(list) &*& nodes(result);
{
    if (list == 0) {
        //@ close nodes(0);
        return 0;
    } else {
        //@ open nodes(list);
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        struct node *result = list_cons(fvalue, fnext);
        //@ close nodes(list);
        return result;
    }
}

/*@
predicate_family mapfunc(void *fp)(void *data, int x);
@*/

int plusOneFunc(void *data, int x) 
    //@ requires mapfunc(plusOneFunc)(data, x);
    //@ ensures mapfunc(plusOneFunc)(data, x);
{
    if (x == INT_MAX) abort();
    return x + 1;
}

int main() 
    //@ requires emp;
    //@ ensures emp;
{
    //@ close nodes(0);
    struct node *l = 0;
    
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    
    //@ close mapfunc(plusOneFunc)(0, 0);
    struct node *l2 = fmap(l, plusOneFunc, 0);
    //@ open mapfunc(plusOneFunc)(0, 0);
    
    //@ close nodes(0);
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