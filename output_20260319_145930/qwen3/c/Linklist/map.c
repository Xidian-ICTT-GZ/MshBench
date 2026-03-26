#include "stdlib.h"
#include "assert.h"

/*@ predicate nodes(struct node *node; int length) =
    node == 0 ?
        length == 0
    :
        malloc_block_node(node) &*&
        nodes(node->next, length - 1) &*&
        length > 0;
@*/

struct node {
    struct node *next;
    int value;
};

//@ requires true;
//@ ensures nodes(result, 1) &*& result->value |-> value &*& result->next |-> next;
struct node *list_cons(int value, struct node *next)
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    
    return result;
}

//@ requires nodes(n1, ?n1_len) &*& nodes(n2, ?n2_len);
//@ ensures nodes(n1, n1_len) &*& nodes(n2, n2_len) &*& result == (n1_len == n2_len && equal_values(n1, n2));
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
        //@ open nodes(n1, _);
        //@ open nodes(n2, _);
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
        //@ close nodes(n1, _);
        //@ close nodes(n2, _);
    }
    
    return result;
}

/*@ predicate equal_values(struct node *n1, struct node *n2) =
    n1 == 0 ?
        n2 == 0
    :
        n2 != 0 &*& n1->value == n2->value &*& equal_values(n1->next, n2->next);
@*/

//@ requires nodes(l, ?len);
//@ ensures true;
void dispose(struct node *l)
{
    if (l != 0) {
        //@ open nodes(l, _);
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);
//@ requires true;
//@ ensures true;

//@ requires nodes(list, ?len) &*& function_pointer(f, mapfunc);
//@ ensures nodes(result, len);
struct node *fmap(struct node *list, mapfunc f, void *data)
{
    if (list == 0) {
        return 0;
    } else {
        //@ open nodes(list, _);
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        struct node *result = list_cons(fvalue, fnext);
        //@ close nodes(result, _);
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

int main() 
{
    struct node *l = 0;
    //@ close nodes(l, 0);
    
    l = list_cons(3, l);
    //@ close nodes(l, 1);
    l = list_cons(2, l);
    //@ close nodes(l, 2);
    l = list_cons(1, l);
    //@ close nodes(l, 3);
    
    struct node *l2 = fmap(l, plusOneFunc, 0);
    //@ assert nodes(l2, 3);
    
    struct node *l3 = 0;
    //@ close nodes(l3, 0);
    
    l3 = list_cons(4, l3);
    //@ close nodes(l3, 1);
    l3 = list_cons(3, l3);
    //@ close nodes(l3, 2);
    l3 = list_cons(2, l3);
    //@ close nodes(l3, 3);
    bool tmp = equals(l2, l3);
    
    assert(tmp);
    //@ open nodes(l, _);
    dispose(l);
    //@ open nodes(l2, _);
    dispose(l2);
    //@ open nodes(l3, _);
    dispose(l3);
    return 0;
}