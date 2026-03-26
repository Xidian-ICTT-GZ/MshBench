#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
predicate nodes(struct node *first, struct node *last, list<int> values) =
  first == last ?
    values == nil
  :
    first->next |-> ?next &*& first->value |-> ?value &*& malloc_block_node(first) &*&
    nodes(next, last, ?values0) &*& values == cons(value, values0);
@*/

/*@
predicate llist(struct llist *l, list<int> values) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  nodes(first, last, values);
@*/

struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close nodes(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?values);
  //@ ensures llist(list, append(values, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, values);
  l = list->last;
  //@ open nodes(_, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close nodes(n, n, nil);
  //@ close nodes(l, n, cons(x, nil));
  //@ close llist(list, append(values, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?values1) &*& llist(list2, ?values2);
  //@ ensures llist(list1, append(values1, values2));
{
  //@ open llist(list1, values1);
  //@ open llist(list2, values2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  if (f2 == l2) {
    //@ open nodes(f2, l2, values2);
    free(l2);
    free(list2);
    //@ close llist(list1, append(values1, values2));
  } else {
    //@ open nodes(f2, l2, values2);
    struct node *f2next = f2->next;
    int f2value = f2->value;
    l1->next = f2next;
    l1->value = f2value;
    list1->last = l2;
    //@ close nodes(l1, l2, cons(f2value, ?values2tail));
    //@ assert values2 == cons(f2value, values2tail);
    free(f2);
    free(list2);
    //@ close llist(list1, append(values1, values2));
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, _);
  //@ ensures true;
{
  //@ open llist(list, _);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ close nodes(l, l, nil);
  while (n != l)
    //@ invariant nodes(n, l, _);
  {
    //@ open nodes(n, l, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(l, l, _);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?values);
  //@ ensures llist(list, values) &*& result == length(values);
{
  //@ open llist(list, values);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ close nodes(l, l, nil);
  while (n != l)
    //@ invariant nodes(n, l, ?values0) &*& c + length(values0) == length(values);
  {
    //@ open nodes(n, l, values0);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ assert length(values0) == ?len0;
  }
  //@ open nodes(l, l, _);
  //@ close llist(list, values);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?values) &*& 0 <= index &*& index < length(values);
  //@ ensures llist(list, values) &*& result == nth(index, values);
{
  //@ open llist(list, values);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ close nodes(l, l, nil);
  while (i < index)
    //@ invariant nodes(n, l, ?values0) &*& i + length(values0) == length(values) &*& 0 <= i;
  {
    //@ open nodes(n, l, values0);
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  //@ open nodes(n, l, ?values1);
  int value = n->value;
  //@ close nodes(n, l, values1);
  //@ close llist(list, values);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?values) &*& values != nil;
  //@ ensures llist(l, tail(values)) &*& result == head(values);
{
  //@ open llist(l, values);
  struct node *nf = l->first;
  //@ open nodes(nf, ?last, values);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(values));
  return nfv;
}

void main0()
  //@ requires true;
  //@ ensures true;
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
  //@ requires true;
  //@ ensures true;
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

/*@
predicate iter(struct iter *i, struct node *current, struct node *last, list<int> values) =
  i->current |-> current &*& malloc_block_iter(i) &*& nodes(current, last, values);
@*/

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l, ?values);
    //@ ensures iter(result, ?first, ?last, values) &*& llist(l, values);
{
    struct iter *i = 0;
    struct node *f = 0;
    //@ open llist(l, values);
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    f = l->first;
    i->current = f;
    //@ close iter(i, f, l->last, values);
    //@ close llist(l, values);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?current, ?last, ?values) &*& values != nil;
    //@ ensures iter(i, ?next, last, tail(values)) &*& result == head(values);
{
    //@ open iter(i, current, last, values);
    struct node *c = i->current;
    //@ open nodes(c, last, values);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close iter(i, n, last, tail(values));
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i, _, _, _);
    //@ ensures true;
{
    //@ open iter(i, _, _, _);
    free(i);
}

int main2()
    //@ requires true;
    //@ ensures true;
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