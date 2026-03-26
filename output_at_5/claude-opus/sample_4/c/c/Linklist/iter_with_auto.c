#include "stdlib.h"

/*@
predicate node(struct node *n; struct node *next, int value) =
  n->next |-> next &*& n->value |-> value;
predicate nodes(struct node *first, struct node *last; list<int> vs) =
  first == last ? vs == nil : 
  exists<struct node*> n2; 
    exists<int> v; 
      exists<list<int>> vs2;
        node(first; n2, v) &*& nodes(n2, last; vs2) &*& vs == cons(v, vs2);
predicate llist(struct llist *l; list<int> vs) =
  l->first |-> ?f &*& l->last |-> ?last &*& nodes(f, last; vs);
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
/*@ requires true;
    ensures llist(result, nil);
@*/
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close nodes(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

void llist_add(struct llist *list, int x)
/*@ requires llist(list, ?vs);
    ensures llist(list, append(vs, cons(x, nil)));
@*/
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, vs);
  //@ open nodes(list->first, list->last, vs);
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(n, 0, 0);
  //@ close nodes(list->first, n, append(vs, cons(x, nil)));
  //@ close llist(list, append(vs, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
/*@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
    ensures llist(list1, append(vs1, vs2)) &*& true;
@*/
{
  //@ open llist(list1, vs1);
  //@ open nodes(list1->first, list1->last, vs1);
  //@ open llist(list2, vs2);
  //@ open nodes(list2->first, list2->last, vs2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
  //@ close llist(list1, append(vs1, vs2));
}

void llist_dispose(struct llist *list)
/*@ requires llist(list, ?vs);
    ensures true;
@*/
{
  //@ open llist(list, vs);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open nodes(n, l, vs);
  while (n != l)
    //@ invariant nodes(n, l, ?vs1);
  {
    struct node *next = n->next;
    free(n);
    n = next;
    //@ open node(n, _, _);
  }
  free(l);
  free(list);
}

int llist_length(struct llist *list)
/*@ requires llist(list, ?vs);
    ensures llist(list, vs) &*& result == length(vs);
@*/
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open nodes(f, l, vs);
  while (n != l)
    //@ invariant nodes(n, l, ?vs1) &*& c == length(vs) - length(vs1);
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ open node(n, _, _);
  }
  //@ close nodes(n, l, nil);
  //@ close llist(list, vs);
  return c;
}

int llist_lookup(struct llist *list, int index)
/*@ requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
    ensures llist(list, vs) &*& result == nth(index, vs);
@*/
{
  //@ open llist(list, vs);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open nodes(f, l, vs);
  list<int> rest = vs;
  while (i < index)
    //@ invariant nodes(n, l, rest) &*& length(rest) > index - i;
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
    //@ open node(n, _, _);
    rest = tail(rest);
  }
  int value = n->value;
  //@ close nodes(n, l, ?vs2);
  //@ close nodes(f, l, vs);
  //@ close llist(list, vs);
  return value;
}

int llist_removeFirst(struct llist *l)
/*@ requires llist(l, ?vs) &*& vs != nil;
    ensures llist(l, tail(vs)) &*& result == head(vs);
@*/
{
  //@ open llist(l, vs);
  struct node *nf = l->first;
  //@ open nodes(nf, l->last, vs);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(vs));
  return nfv;
}

void main0()
/*@ requires true; ensures true; @*/
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
/*@ requires true; ensures true; @*/
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
predicate iter(struct iter *i; struct node *current) =
  i->current |-> current &*& (current == 0 || node(current, ?next, _));
@*/

struct iter *llist_create_iter(struct llist *l)
/*@ requires llist(l, ?vs);
    ensures iter(result, l->first);
@*/
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    //@ open llist(l, vs);
    f = l->first;
    i->current = f;
    //@ close iter(i, f);
    return i;
}

int iter_next(struct iter *i)
/*@ requires iter(i, ?c) &*& c != 0;
    ensures iter(i, c->next) &*& result == c->value;
@*/
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
/*@ requires iter(i, _);
    ensures true;
@*/
{
    free(i);
}

int main2()
/*@ requires true; ensures true; @*/
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