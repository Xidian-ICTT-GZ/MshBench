#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

/*@ 
predicate nodes(struct node *n, list<int> vs) =
    n == 0 ?
        vs == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) 
        &*& nodes(next, ?vs0)
        &*& vs == cons(v, vs0);
@*/

struct node *list_cons(int value, struct node *next)
    //@ requires nodes(next, ?vs);
    //@ ensures nodes(result, cons(value, vs));
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    
    return result;
}

bool equals(struct node *n1, struct node *n2)
    //@ requires nodes(n1, ?vs1) &*& nodes(n2, ?vs2);
    //@ ensures nodes(n1, vs1) &*& nodes(n2, vs2) &*& result == (vs1 == vs2);
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
    //@ requires nodes(l, ?vs);
    //@ ensures true;
{
    
    if (l != 0) {
        struct node *next = l->next;
        //@ open nodes(l, _);
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);

/*@ 
predicate_ctor mapfunc_pred(void *data)() = true; 
@*/

struct node *fmap(struct node *list, mapfunc f, void *data)
    //@ requires nodes(list, ?vs) &*& mapfunc_pred(data)();
    //@ ensures nodes(list, vs) &*& mapfunc_pred(data)() &*& result != 0 || vs == nil &*& nodes(result, ?vs2) &*& (forall<int> vs2 == map(?g, vs));
{
    
    if (list == 0) {
        
        return 0;
    } else {
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        
        struct node *result = list_cons(fvalue, fnext);
        
        return result;
    }
}

int plusOneFunc(void *data, int x) 
    //@ requires true;
    //@ ensures x == INT_MAX ==> false;
    //@ ensures x != INT_MAX ==> result == x + 1;
{
    if (x == INT_MAX) abort();
    return x + 1;
}

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct node *l = 0;
    //@ close nodes(l, nil);
    
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    //@ open nodes(l, ?vs);
    //@ close mapfunc_pred(0)();
    
    struct node *l2 = fmap(l, plusOneFunc, 0);
    
    struct node *l3 = 0;
    //@ close nodes(l3, nil);
    
    l3 = list_cons(4, l3);
    l3 = list_cons(3, l3);
    l3 = list_cons(2, l3);
    //@ open nodes(l3, ?vs3);
    bool tmp = equals(l2, l3);
    
    assert(tmp);
    dispose(l);
    dispose(l2);
    dispose(l3);
    return 0;
}