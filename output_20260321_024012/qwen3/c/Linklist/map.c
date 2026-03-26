/*@ predicate node(struct node *n; int value, struct node *next) = n != 0 &*& n->value |-> value &*& n->next |-> next; @*/

/*@ predicate list(struct node *l; list<int> vs) =
    l == 0 ? vs == nil : 
    exists<int> v, struct node *n . node(l, v, n) &*& list(n, ?vs0) &*& vs == cons(v, vs0);
@*/

#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

struct node *list_cons(int value, struct node *next)
//@ requires list(next, ?vs);
//@ ensures list(result, cons(value, vs));
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    //@ close node(result, value, next);
    return result;
}

bool equals(struct node *n1, struct node *n2)
//@ requires list(n1, ?vs1) &*& list(n2, ?vs2);
//@ ensures list(n1, vs1) &*& list(n2, vs2) &*& result == (vs1 == vs2);
{
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else {
        //@ open list(n1, _);
        //@ open list(n2, _);
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
        //@ close list(n1, cons(n1->value, ?vs1_rest));
        //@ close list(n2, cons(n2->value, ?vs2_rest));
    }
    return result;
}

void dispose(struct node *l)
//@ requires list(l, ?vs);
//@ ensures true;
{
    if (l != 0) {
        //@ open list(l, _);
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);
    
    

struct node *fmap(struct node *list, mapfunc f, void *data)
//@ requires list(list, ?vs) &*& data |-> ?d;
//@ ensures list(result, ?fvs) &*& data |-> d;
{
    if (list == 0) {
        return 0;
    } else {
        //@ open list(list, _);
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        struct node *result = list_cons(fvalue, fnext);
        //@ close list(result, cons(fvalue, ?fvs_rest));
        return result;
    }
}

int plusOneFunc(void *data, int x) 
//@ requires data |-> ?d;
//@ ensures data |-> d;
{
    if (x == INT_MAX) abort();
    return x + 1;
}

int main() 
//@ requires true;
//@ ensures true;
{
    struct node *l = 0;
    //@ close list(l, nil);
    
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    
    struct node *l2 = fmap(l, plusOneFunc, 0);
    
    struct node *l3 = 0;
    //@ close list(l3, nil);
    
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