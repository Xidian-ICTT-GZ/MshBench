#include "stdlib.h"
#include "limits.h"

/*@

predicate node(struct node *n; list<int> vs) =
  n != 0 &*& malloc_block_node(n) &*&
  n->value |-> ?v &*& n->next |-> ?next &*&
  node(next, ?vs0) &*& vs == cons(v, vs0) || n == 0 &*& vs == nil;

predicate nodes(struct node *n; list<int> vs) =
  n == 0 &*& vs == nil
  ||
  n != 0 &*& malloc_block_node(n) &*&
  n->value |-> ?v &*& n->next |-> ?next &*&
  nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *l; list<int> vs) =
  l != 0 &*& malloc_block_llist(l) &*&
  l->first |-> ?f &*& l->last |-> ?last &*&
  nodes(f, ?ns) &*& last != 0 &*& true &*&
  // last node's next is NULL and represents sentinel node in this implementation
  last->next |-> 0 &*& l->last == last &*&
  ns == vs &*&
  // last node value is garbage before add, full list is vs
  // allows sentinel node with no value used: last node value does not matter here
  true;

predicate iter(struct iter *it; struct node *current; list<int> vs) =
  it != 0 &*& malloc_block_iter(it) &*&
  it->current |-> current &*& nodes(current, vs);

@*/

predicate malloc_block_node(struct node *p;) =  malloc_block(p, sizeof(struct node));
predicate malloc_block_llist(struct llist *p;) = malloc_block(p, sizeof(struct llist));
predicate malloc_block_iter(struct iter *p;) = malloc_block(p, sizeof(struct iter));

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
  struct node *current;
};

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
  //@ close nodes(n, nil);
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
  //@ open nodes(list->last, ?vslast);
  //@ open nodes(n, nil);
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close nodes(n, nil);
  //@ close nodes(l, cons(x, nil));
  //@ close llist(list, append(vs, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2) &*&
  //@          length(vs2) > 0;
  //@ ensures llist(list1, append(vs1, tail(vs2))) &*&
  //@         true;
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  //@ open llist(list1, vs1);
  //@ open llist(list2, vs2);
  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    //@ open nodes(f2, vs2);
    //@ open nodes(f2->next, ?vs2tail);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
  //@ close llist(list1, append(vs1, tail(vs2)));
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?vs);
  //@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open llist(list, vs);
  //@ open nodes(n, vs);
  while (n != l)
    //@ invariant nodes(n, ?vs1);
  {
    struct node *next = n->next;
    free(n);
    n = next;
    //@ open nodes(next, _);
  }
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?vs);
  //@ ensures llist(list, vs) &*& result == length(vs);
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open llist(list, vs);
  //@ open nodes(f, vs);
  while (n != l)
    //@ invariant nodes(n, ?vs1) &*& length(vs1) == c + length(drop(c, vs));
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ close llist(list, vs);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
  //@ ensures llist(list, vs) &*& result == nth(index, vs);
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ open llist(list, vs);
  //@ open nodes(f, vs);
  while (i < index)
    //@ invariant nodes(n, ?vs1) &*& i <= length(vs1) &*& i <= index;
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  //@ close llist(list, vs);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?vs) &*& length(vs) > 0;
  //@ ensures llist(l, tail(vs)) &*& result == head(vs);
{
  struct node *nf = l->first;
  //@ open llist(l, vs);
  //@ open nodes(nf, vs);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, tail(vs));
  return nfv;
}

struct iter *llist_create_iter(struct llist *l)
  //@ requires llist(l, ?vs);
  //@ ensures iter(result, l->first, vs);
{
  struct iter *i = 0;
  struct node *f = 0;
    
  i = malloc(sizeof(struct iter));
  if (i == 0) {
    abort();
  }
    
  f = l->first;
  i->current = f;
  //@ close iter(i, f, vs);
  return i;
}

int iter_next(struct iter *i)
  //@ requires iter(i, ?current, cons(?v, ?vs));
  //@ ensures iter(i, i->current, vs) &*& result == v;
{
  struct node *c = i->current;
  //@ open iter(i, c, cons(v, vs));
  int value = c->value;
  struct node *n = c->next;
  i->current = n;
  //@ close iter(i, n, vs);
  return value;
}

void iter_dispose(struct iter *i)
  //@ requires iter(i, ?current, ?vs);
  //@ ensures true;
{
  //@ open iter(i, current, vs);
  free(i);
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