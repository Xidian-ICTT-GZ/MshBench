/*@ predicate node(struct node *n, int v, struct node *next) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->value |-> v &*&
    n->next |-> next;
@*/

/*@ predicate list(struct node *l, list<int> vs) =
    l == 0 ?
        vs == nil
    :
        exists<int> v, struct node *next, list<int> tail.
        vs == cons(v, tail) &*&
        node(l, v, next) &*&
        list(next, tail);
@*/

struct node {
    struct node *next;
    int value;
};

//@ requires true;
//@ ensures result == 0 ? true : node(result, value, next) &*& malloc_block_node(result);
struct node *list_cons(int value, struct node *next)
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); 
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    
    return result;
}

//@ requires list(n1, ?vs1) &*& list(n2, ?vs2);
//@ ensures list(n1, vs1) &*& list(n2, vs2) &*& result == (vs1 == vs2);
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
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
    }
    
    return result;
}

//@ requires list(l, ?vs);
//@ ensures true;
void dispose(struct node *l)
{
    if (l != 0) {
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);

//@ requires list(list, ?vs) &*& data |-> ?d;
//@ ensures list(result, map(f, d, vs)) &*& data |-> d;
struct node *fmap(struct node *list, mapfunc f, void *data)
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

//@ requires data |-> ?d &*& x != INT_MAX;
//@ ensures result == x + 1 &*& data |-> d;
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