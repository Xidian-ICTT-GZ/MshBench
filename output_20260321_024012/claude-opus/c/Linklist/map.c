#include "stdlib.h"
#include "assert.h"

/*@
predicate node(struct node *n; int value, struct node *next) =
    n->value |-> value &*& n->next |-> next;
@*/

struct node {
    struct node *next;
    int value;
};

struct node *list_cons(int value, struct node *next)
    //@ requires true;
    //@ ensures node(result, value, next);
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    
    //@ close node(result, value, next);
    return result;
}

bool equals(struct node *n1, struct node *n2)
    //@ requires (n1 == 0 ? true : node(n1, ?v1, ?nx1)) &*& (n2 == 0 ? true : node(n2, ?v2, ?nx2));
    //@ ensures  (n1 == 0 ? true : node(n1, v1, nx1)) &*& (n2 == 0 ? true : node(n2, v2, nx2)) &*& result == (v1 == v2 && ( (nx1 == 0 && nx2 == 0) || equals(nx1, nx2)));
{
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else {
        //@ open node(n1, _, _);
        //@ open node(n2, _, _);
        bool tmp = equals(n1->next, n2->next);
        //@ close node(n1, n1->value, n1->next);
        //@ close node(n2, n2->value, n2->next);
        result = tmp;
    }
    
    return result;
}

void dispose(struct node *l)
    //@ requires l == 0 ? true : node(l, _, ?next);
    //@ ensures true;
{
    if (l != 0) {
        //@ open node(l, _, _);
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
    //@ close true;
}

typedef int (* mapfunc)(void *data, int x);
    
struct node *fmap(struct node *list, mapfunc f, void *data)
    //@ requires list == 0 ? true : node(list, ?v, ?nx);
    //@ ensures result == 0 ? true : node(result, ?fv, ?fnx);
{
    if (list == 0) {
        return 0;
    } else {
        //@ open node(list, _, _);
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        //@ close node(list, list->value, list->next);
        
        struct node *result = list_cons(fvalue, fnext);
        
        return result;
    }
}

int plusOneFunc(void *data, int x) 
    //@ requires true;
    //@ ensures result == x + 1;
{
    if (x == INT_MAX) abort();
    return x + 1;
}

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct node *l = 0;
    
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    
    struct node *l2 = fmap(l, plusOneFunc, 0);
    
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