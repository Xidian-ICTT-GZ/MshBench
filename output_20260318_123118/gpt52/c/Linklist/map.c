#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *n; struct node *next, int value) =
    n != 0 &*& n->next |-> next &*& n->value |-> value;

predicate list(struct node *l; list<int> vs) =
    l == 0 &*& vs == nil
    ||
    l != 0 &*& nodes(l, ?n, ?v) &*& list(n, ?vs0) &*& vs == cons(v, vs0);

lemma void equals_reflexive(struct node *n)
    requires list(n, ?vs);
    ensures list(n, vs) &*& equals(n, n) == true;
{
    open list(n, vs);
    if (n != 0) {
        equals_reflexive(n->next);
    }
    close list(n, vs);
}

@*/

struct node *list_cons(int value, struct node *next)
    //@ requires list(next, ?vs);
    //@ ensures list(result, cons(value, vs));
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    
    //@ close nodes(result, next, value);
    //@ close list(result, cons(value, vs));
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
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
    }
    
    
    return result;
}

void dispose(struct node *l)
    //@ requires list(l, ?vs);
    //@ ensures true;
{
    
    if (l != 0) {
        //@ open list(l, vs);
        struct node *next = l->next;
        //@ open nodes(l, next, ?v);
        free(l);
        dispose(next);
    } else {
        //@ open list(l, vs);
    }
}

typedef int (* mapfunc)(void *data, int x);
    
    

struct node *fmap(struct node *list0, mapfunc f, void *data)
    //@ requires list(list0, ?vs);
    //@ ensures list(list0, vs) &*& list(result, ?ws);
{
    
    if (list0 == 0) {
        //@ open list(list0, vs);
        //@ close list(list0, nil);
        //@ close list(result, nil);
        return 0;
    } else {
        //@ open list(list0, vs);
        int fvalue = f(data, list0->value);
        struct node *fnext = fmap(list0->next, f, data);
        //@ close list(list0->next, ?vsTail);
        //@ close nodes(list0, list0->next, list0->value);
        //@ close list(list0, cons(list0->value, vsTail));
        
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
    
    //@ assert tmp == ((cons(2, cons(3, cons(4, nil))) == cons(2, cons(3, cons(4, nil)))));
    assert(tmp);
    dispose(l);
    dispose(l2);
    dispose(l3);
    return 0;
}