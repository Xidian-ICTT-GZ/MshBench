#include "stdlib.h"

/*@
predicate node_pred(struct node *n; struct node *next, int value) =
  n->next |-> next &*& n->value |-> value;

predicate nodes(struct node *start, struct node *end) =
  start == end ? emp : node_pred(start, ?next, ?value) &*& nodes(next, end);

predicate llist_pred(struct llist *l; struct node *first, struct node *last) =
  l->first |-> first &*& l->last |-> last &*& nodes(first, last);

predicate iter_pred(struct iter *i; struct node *current) =
  i->current |-> current;
@*/

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct llist *create_llist()
  //@ requires emp;
  //@ ensures llist_pred(result, ?f, ?l);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node_pred(n, 0, 0);
  //@ close nodes(n, n);
  //@ close llist_pred(l, n, n);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist_pred(list, ?first, ?last);
  //@ ensures llist_pred(list, first, ?new_last);
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open llist_pred(list, first, last);
  //@ open nodes(first, last);
  //@ open node_pred(last, 0, _);
  l->next = n;
  l->value = x;
  //@ close node_pred(last, n, x);
  //@ close node_pred(n, 0, 0);
  //@ close nodes(n, n);
  //@ close nodes(first, n);
  list->last = n;
  //@ close llist_pred(list, first, n);
  
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist_pred(list1, ?f1, ?l1) &*& llist_pred(list2, ?f2, ?l2);
  //@ ensures llist_pred(list1, f1, ?new_last);
  //@ ensures true;
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open llist_pred(list1, f1, l1);
  //@ open llist_pred(list2, f2, l2);
  //@ open nodes(f1, l1);
  //@ open nodes(f2, l2);
  if (f2 == l2) {
    //@ open node_pred(f2, 0, _);
    free(l2);
    free(list2);
    //@ close nodes(f1, l1);
    //@ close llist_pred(list1, f1, l1);
  } else {
    //@ open node_pred(f2, ?f2next, ?f2val);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close nodes(f2->next, l2);
    //@ close nodes(f1, l2);
    free(f2);
    free(list2);
    //@ close llist_pred(list1, f1, l2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist_pred(list, ?f, ?l);
  //@ ensures emp;
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist_pred(list, f, l);
  //@ open nodes(f, l);
  while (n != l)
    //@ invariant nodes(n, l);
  {
    struct node *next = n->next;
    //@ open node_pred(n, _, _);
    free(n);
    n = next;
  }
  //@ open node_pred(l, 0, _);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist_pred(list, ?f, ?l);
  //@ ensures true;
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist_pred(list, f, l);
  //@ open nodes(f, l);
  while (n != l)
    //@ invariant nodes(n, l);
  {
    struct node *next = n->next;
    //@ open node_pred(n, _, _);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist_pred(list, ?f, ?l);
  //@ ensures true;
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist_pred(list, f, l);
  //@ open nodes(f, l);
  while (i < index)
    //@ invariant nodes(n, l);
  {
    struct node *next = n->next;
    //@ open node_pred(n, _, _);
    n = next;
    i = i + 1;
  }
  int value = n->value;
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist_pred(l, ?f, ?l_);
  //@ ensures llist_pred(l, ?new_f, l_);
{
  struct node *nf = l->first;
  //@ open llist_pred(l, f, l_);
  //@ open nodes(f, l_);
  //@ open node_pred(nf, _, _);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  //@ close nodes(nfn, l_);
  free(nf);
  l->first = nfn;
  //@ close llist_pred(l, nfn, l_);
  return nfv;
}

void main0()
  //@ requires emp;
  //@ ensures emp;
{
  struct llist *l = create_llist();
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  int x1 = llist_removeFirst(l);
  assert(x1 == 10);
  int x2 = llist_removeFirst(l);
  assert(x2 == 20);
  llist_dispose(l);
}

int main() 
  //@ requires emp;
  //@ ensures emp;
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); assert(n == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

struct iter *llist_create_iter(struct llist *l)
  //@ requires llist_pred(l, ?f, ?l_);
  //@ ensures iter_pred(result, f);
{
    struct iter *i = 0;
    struct node *f = 0;
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f = l->first;
    i->current = f;
    //@ close iter_pred(i, f);
    return i;
}

int iter_next(struct iter *i)
  //@ requires iter_pred(i, ?c);
  //@ ensures iter_pred(i, ?n);
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter_pred(i, n);
    return value;
}

void iter_dispose(struct iter *i)
  //@ requires iter_pred(i, _);
  //@ ensures emp;
{
    free(i);
}

int main2()
  //@ requires emp;
  //@ ensures emp;
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}