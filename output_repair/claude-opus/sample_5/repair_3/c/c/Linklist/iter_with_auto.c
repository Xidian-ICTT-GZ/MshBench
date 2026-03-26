#include "stdlib.h"

struct node
{
  struct node *next;
  int value;
};

struct llist
{
  struct node *first;
  struct node *last;
};

/*@ predicate nodes(struct node *n, struct node *end) = 
  n == end ? emp : n->next |-> ?next &*& n->value |-> _ &*& nodes(next, end); @*/

/*@ predicate llist(struct llist *l) = 
  malloc_block_llist(l) &*& l->first |-> ?f &*& l->last |-> ?last &*& malloc_block_node(f) &*& nodes(f, last); @*/

struct llist *create_llist()
//@ requires true;
//@ ensures result != 0 &*& llist(result);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0)
    abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
    abort();
  l->first = n;
  l->last = n;
  //@ close nodes(n, n);
  //@ close llist(l);
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list);
//@ ensures llist(list);
{
  //@ open llist(list);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
  {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close llist(list);
}

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1) &*& llist(list2);
//@ ensures llist(list1);
{
  //@ open llist(list1);
  //@ open llist(list2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2)
  {
    //@ open nodes(f2, l2);
    free(l2);
    free(list2);
  }
  else
  {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
  //@ close llist(list1);
}

void llist_dispose(struct llist *list)
//@ requires llist(list);
//@ ensures true;
{
  //@ open llist(list);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant nodes(n, l) &*& malloc_block_node(l);
  {
    //@ open nodes(n, l);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(l, l);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
//@ requires llist(list);
//@ ensures llist(list);
{
  //@ open llist(list);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;

  while (n != l)
  //@ invariant nodes(n, l) &*& c >= 0;
  {
    //@ open nodes(n, l);
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX)
      abort();
    c = c + 1;
  }
  //@ open nodes(l, l);
  //@ close nodes(l, l);
  //@ close llist(list);
  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list);
//@ ensures llist(list);
{
  //@ open llist(list);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)
  //@ invariant nodes(n, l) &*& i >= 0 &*& i <= index;
  {
    //@ open nodes(n, l);
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  //@ open nodes(n, l);
  int value = n->value;
  //@ close nodes(n, l);
  //@ close llist(list);
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l);
//@ ensures llist(l);
{
  //@ open llist(l);
  struct node *nf = l->first;
  //@ open nodes(nf, l->last);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l);
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
  int x = llist_removeFirst(l2);
  assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1);
  assert(n == 5);
  int e0 = llist_lookup(l1, 0);
  assert(e0 == 10);
  int e1 = llist_lookup(l1, 1);
  assert(e1 == 20);
  int e2 = llist_lookup(l1, 2);
  assert(e2 == 30);
  int e3 = llist_lookup(l1, 3);
  assert(e3 == 50);
  int e4 = llist_lookup(l1, 4);
  assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter
{
  struct node *current;
};

/*@ predicate iter(struct iter *i, struct node *end) = 
  malloc_block_iter(i) &*& i->current |-> ?c &*& nodes(c, end); @*/

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l);
//@ ensures result != 0 &*& iter(result, ?end) &*& llist(l);
{
  struct iter *i = 0;
  struct node *f = 0;
  i = malloc(sizeof(struct iter));
  if (i == 0)
  {
    abort();
  }
  //@ open llist(l);
  f = l->first;
  i->current = f;
  //@ close iter(i, l->last);
  //@ close llist(l);
  return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?end);
//@ ensures iter(i, end);
{
  //@ open iter(i, end);
  struct node *c = i->current;
  //@ open nodes(c, end);
  int value = c->value;
  struct node *n = c->next;
  i->current = n;
  //@ close iter(i, end);
  return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?end);
//@ ensures true;
{
  //@ open iter(i, end);
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
  int i1e1 = iter_next(i1);
  assert(i1e1 == 5);
  int i2e1 = iter_next(i2);
  assert(i2e1 == 5);
  int i1e2 = iter_next(i1);
  assert(i1e2 == 10);
  int i2e2 = iter_next(i2);
  assert(i2e2 == 10);
  iter_dispose(i1);
  iter_dispose(i2);
  llist_dispose(l);
  return 0;
}