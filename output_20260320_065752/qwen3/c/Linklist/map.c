#include "stdlib.h"
#include "assert.h"

/*@ predicate list(struct node *node;) =
    node == 0 ?
        true
    :
        malloc_block_node(node) &*& node->next |-> ?next &*& node->value |-> _ &*& list(next);
@*/

struct node {
    struct node *next;
    int value;
};

//@ requires true;
//@ ensures list(result);
struct node *list_cons(int value, struct node *next)
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    //@ close list(result);
    return result;
}

//@ requires list(n1) &*& list(n2);
//@ ensures list(n1) &*& list(n2) &*& result == (n1 == n2 || (n1 != 0 && n2 != 0 && n1->value == n2->value && equals(n1->next, n2->next)));
bool equals(struct node *n1, struct node *n2)
{
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else {
        //@ open list(n1);
        //@ open list(n2);
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
        //@ close list(n1);
        //@ close list(n2);
    }
    return result;
}

//@ requires list(l);
//@ ensures true;
void dispose(struct node *l)
{
    if (l != 0) {
        //@ open list(l);
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);
    
//@ requires list(list) &*& true;
//@ ensures list(result);
struct node *fmap(struct node *list, mapfunc f, void *data)
{
    if (list == 0) {
        return 0;
    } else {
        //@ open list(list);
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        struct node *result = list_cons(fvalue, fnext);
        //@ close list(result);
        return result;
    }
}

//@ requires true;
//@ ensures true;
int plusOneFunc(void *data, int x) 
{
    if (x == INT_MAX) abort();
    return x + 1;
}

//@ requires true;
//@ ensures true;
int main() 
{
    struct node *l = 0;
    //@ close list(l);
    
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    
    struct node *l2 = fmap(l, plusOneFunc, 0);
    
    struct node *l3 = 0;
    //@ close list(l3);
    
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