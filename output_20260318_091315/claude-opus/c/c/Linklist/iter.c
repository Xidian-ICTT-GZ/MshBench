#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

/*@ predicate nodes(struct node *first, struct node *last, list<int> vs) =
  first == last ?
    last == 0 ? vs == nil : // empty list
    (first->value |-> ?v &*& first->next |-> ?n &*& malloc_block_node(first)) &*&
    nodes(n, last, ?vs0) &*& vs == cons(v, vs0);
@*/

struct llist {
  struct node *first;
  struct node *last;
};

/*@ predicate llist(struct llist *l, list<int> vs) =
  l->first |-> ?f &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  nodes(f, last, vs);
@*/

struct iter {
  struct node *current;
};

/*@ predicate iter(struct iter *i, struct node *cur) =
  i->current |-> cur &*& malloc_block_iter(i);
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
  //@ requires llist(list, ?vs);
  //@ ensures llist(list, append(vs, cons(x, nil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, vs);
  l = list->last;
  //@ open nodes(list->first, list->last, vs);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close nodes(n, n, nil);
  //@ close nodes(list->first, n, append(vs, cons(x, nil)));
  //@ close llist(list, append(vs, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
  //@ ensures llist(list1, append(vs1, vs2)) &*& vs2 == nil || vs2 != nil &&  true;
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  //@ open llist(list2, vs2);
  //@ open nodes(f2, l2, vs2);
  if (f2 == l2) {
    //@ close nodes(f2, l2, vs2);
    free(l2);
    free(list2);
    //@ open llist(list1, vs1);
    //@ close llist(list1, vs1);
  } else {
    //@ open nodes(f2, l2, vs2);
    //@ open llist(list1, vs1);
    //@ open nodes(list1->first, l1, vs1);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close nodes(f2->next, l2, tail(vs2));
    //@ close nodes(list1->first, l2, append(vs1, vs2));
    free(f2);
    free(list2);
    //@ close llist(list1, append(vs1, vs2));
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?vs);
  //@ ensures true;
{
  //@ open llist(list, vs);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant nodes(n, l, ?vs0);
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?vs);
  //@ ensures llist(list, vs) &*& result == length(vs);
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open nodes(f, l, vs);
  while (n != l)
    //@ invariant nodes(n, l, ?vs0) &*& c == length(take(length(vs) - length(vs0), vs));
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ open nodes(next, l, ?vs1);
  }
  //@ close nodes(n, l, drop(c, vs));
  //@ close nodes(f, l, vs);
  //@ close llist(list, vs);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
  //@ ensures llist(list, vs) &*& result == nth(index, vs);
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open nodes(f, l, vs);
  while (i < index)
    //@ invariant nodes(n, l, ?vs0) &*& i <= index &*& take(i, vs) == take(i, vs);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ open nodes(next, l, ?vs1);
  }
  int value = n->value;
  //@ close nodes(n, l, drop(index, vs));
  //@ close nodes(f, l, vs);
  //@ close llist(list, vs);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?vs) &*& vs != nil;
  //@ ensures llist(l, tail(vs)) &*& result == head(vs);
{
  //@ open llist(l, vs);
  struct node *nf = l->first;
  //@ open nodes(nf, l->last, vs);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close nodes(nfn, l->last, tail(vs));
  //@ close llist(l, tail(vs));
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

struct iter *llist_create_iter(struct llist *l)
  //@ requires llist(l, ?vs);
  //@ ensures iter(result, l->first);
{
  struct iter *i = 0;
  struct node *f = 0;

  i = malloc(sizeof(struct iter));
  if (i == 0) {
    abort();
  }

  f = l->first;
  i->current = f;
  //@ close iter(i, f);
  return i;
}

int iter_next(struct iter *i)
  //@ requires iter(i, ?c) &*& c != 0;
  //@ ensures iter(i, c->next) &*& result == c->value;
{
  //@ open iter(i, c);
  struct node *c = i->current;
  int value = c->value;
  struct node *n = c->next;
  i->current = n;
  //@ close iter(i, n);
  return value;
}

void iter_dispose(struct iter *i)
  //@ requires iter(i, _);
  //@ ensures true;
{
  //@ open iter(i, _);
  free(i);
}