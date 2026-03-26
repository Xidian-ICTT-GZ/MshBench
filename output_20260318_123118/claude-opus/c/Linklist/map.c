#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

/*@ 
predicate nodes(struct node *l; list<int> vs) =
    l == 0 ? vs == nil :
    l->value |-> ?v &*& l->next |-> ?n &*& malloc_block_node(l) &*& nodes(n, ?vs0) &*& vs == cons(v, vs0);
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
        //@ open nodes(l, ?vs0);
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);

/*@ 
fixpoint list<int> map_list(list<int> vs, int f(void *data, int x), void *data) {
    switch(vs) {
        case nil: return nil;
        case cons(h,t): return cons(f(data,h), map_list(t,f,data));
    }
}
@*/

struct node *fmap(struct node *list, mapfunc f, void *data)
    //@ requires nodes(list, ?vs) &*& f(data, 0) == f(data, 0);
    //@ ensures nodes(list, vs) &*& nodes(result, map_list(vs, f, data));
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
    //@ close nodes(l, nil);
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    
    struct node *l2 = fmap(l, plusOneFunc, 0);
    struct node *l3 = 0;
    //@ close nodes(l3, nil);
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