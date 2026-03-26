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

/*@ predicate node(struct node *n) = n->next |-> _ &*& n->value |-> _; @*/

/*@ predicate llist(struct llist *l) = l->first |-> _ &*& l->last |-> _; @*/

struct llist *create_llist()
//@ requires true;
//@ ensures llist(result);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0)
    abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
    abort();
  l->first = n;
  l->last = n;
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list);
//@ ensures llist(list);
{
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
}

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1) &*& llist(list2);
//@ ensures llist(list1);
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2)
  {

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
}

void llist_dispose(struct llist *list)
//@ requires llist(list);
//@ ensures true;
{

  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant n != l;
  {

    struct node *next = n->next;
    free(n);
    n = next;
  }

  free(l);
  free(list);
}

int llist_length(struct llist *list)
//@ requires llist(list);
//@ ensures true;
{

  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;

  while (n != l)
  //@ invariant c >= 0;
  {

    struct node *next = n->next;

    n = next;
    if (c == INT_MAX)
      abort();
    c = c + 1;
  }

  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list) &*& index >= 0;
//@ ensures true;
{

  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;

  while (i < index)
  //@ invariant i >= 0 &*& i <= index;
  {

    struct node *next = n->next;

    n = next;
    i = i + 1;
  }

  int value = n->value;

  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l);
//@ ensures llist(l);
{

  struct node *nf = l->first;

  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;

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

/*@ predicate iter(struct iter *i) = i->current |-> _; @*/

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l);
//@ ensures iter(result) &*& llist(l);
{
  struct iter *i = 0;
  struct node *f = 0;

  i = malloc(sizeof(struct iter));
  if (i == 0)
  {
    abort();
  }

  f = l->first;
  i->current = f;

  return i;
}

int iter_next(struct iter *i)
//@ requires iter(i);
//@ ensures iter(i);
{

  struct node *c = i->current;

  int value = c->value;
  struct node *n = c->next;

  i->current = n;

  return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i);
//@ ensures true;
{

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