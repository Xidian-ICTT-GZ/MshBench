#include "stdlib.h"
#include "assert.h"

struct node
{
    struct node *next;
    int value;
};

/*@ predicate list(struct node *l; int *values, int len) =
    l == 0 &*& len == 0
    || (l != 0 &*& len > 0 &*& malloc_block_node(l) &*&
        l->value |-> values[0] &*& l->next |-> ?n &*&
        list(n, values + 1, len - 1));
@*/

/*@ predicate list_disjoint(struct node *l1, struct node *l2) =
    l1 == 0 || l2 == 0 || (l1 != l2 &*&
    l1->next |-> ?n1 &*& l2->next |-> ?n2 &*&
    list_disjoint(n1, l2) &*& list_disjoint(l1, n2));
@*/

/*@ requires true;
    ensures result != 0 &*& malloc_block_node(result) &*&
            result->value |-> ?v &*& result->next |-> ?n &*&
            v == value &*& n == next;
@*/
struct node *list_cons(int value, struct node *next)

{
    struct node *result = (struct node *)malloc(sizeof(struct node));
    if (result == 0)
    {
        abort();
    }
    result->value = value;
    result->next = next;

    return result;
}

/*@ requires list(n1, ?vals1, ?len1) &*& list(n2, ?vals2, ?len2);
    ensures result <==> (len1 == len2 &*& forall(i; 0 <= i && i < len1 ==> vals1[i] == vals2[i]));
@*/
bool equals(struct node *n1, struct node *n2)

{

    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else
    {
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
    }

    return result;
}

/*@ requires list(l, ?vals, ?len);
    ensures l == 0;
@*/
void dispose(struct node *l)

{

    if (l != 0)
    {
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (*mapfunc)(void *data, int x);

/*@ requires list(list, ?vals, ?len) &*&
            \valid(data) &*& \valid_func_ptr(f);
    ensures list(result, ?fvals, len) &*&
            forall(i; 0 <= i && i < len ==> fvals[i] == f(data, vals[i]));
@*/
struct node *fmap(struct node *list, mapfunc f, void *data)

{

    if (list == 0)
    {

        return 0;
    }
    else
    {
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);

        struct node *result = list_cons(fvalue, fnext);

        return result;
    }
}

/*@ requires true;
    ensures result == x + 1 &*& x != INT_MAX;
@*/
int plusOneFunc(void *data, int x)

{
    if (x == INT_MAX)
        abort();

    return x + 1;
}

/*@ requires true;
    ensures true;
@*/
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