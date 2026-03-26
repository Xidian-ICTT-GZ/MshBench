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

/*@
predicate nodes(struct node *n, struct node *last, list<int> vs) =
  n == last ?
    n->next |-> _ &*& n->value |-> _ &*& vs == nil
  :
    n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*&
    nodes(next, last, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *l, list<int> vs) =
  l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
  malloc_block_node(last) &*& last->next |-> _ &*& last->value |-> _ &*&
  nodes(first, last, vs);

predicate iter(struct iter *i, struct node *current) =
  i->current |-> current &*& malloc_block_iter(i);

predicate nodes_shared(struct node *n, struct node *last, list<int> vs) =
  n == last ?
    n->next |-> _ &*& n->value |-> _ &*& vs == nil
  :
    n->next |-> ?next &*& n->value |-> ?v &*&
    nodes_shared(next, last, ?vs0) &*& vs == cons(v, vs0);
@*/

struct llist *create_llist()
//@ requires true;
//@ ensures llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0)
    abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
    abort();
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
  if (n == 0)
  {
    abort();
  }
  //@ open llist(list, vs);
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close nodes(n, n, nil);
  //@ close nodes(l, n, cons(x, nil));
  //@ nodes_append(list->first, l, n);
  //@ close llist(list, append(vs, cons(x, nil)));
}

/*@
lemma void nodes_append(struct node *n1, struct node *n2, struct node *n3)
  requires nodes(n1, n2, ?vs1) &*& nodes(n2, n3, ?vs2);
  ensures nodes(n1, n3, append(vs1, vs2));
{
  open nodes(n1, n2, vs1);
  if (n1 == n2) {
    close nodes(n1, n3, append(vs1, vs2));
  } else {
    nodes_append(n1->next, n2, n3);
    close nodes(n1, n3, append(vs1, vs2));
  }
}

lemma void nodes_split(struct node *n1, struct node *n2, struct node *n3)
  requires nodes(n1, n3, ?vs) &*& nodes(n2, n3, ?vs2);
  ensures nodes(n1, n2, ?vs1) &*& nodes(n2, n3, vs2) &*& vs == append(vs1, vs2);
{
  open nodes(n1, n3, vs);
  if (n1 == n3) {
    close nodes(n1, n2, nil);
  } else {
    nodes_split(n1->next, n2, n3);
    close nodes(n1, n2, _);
  }
}
@*/

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
//@ ensures llist(list1, append(vs1, vs2));
{
  //@ open llist(list1, vs1);
  //@ open llist(list2, vs2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2)
  {
    //@ open nodes(f2, l2, vs2);
    free(l2);
    free(list2);
    //@ close llist(list1, vs1);
  }
  else
  {
    //@ open nodes(f2, l2, vs2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close nodes(l1, l2, vs2);
    //@ nodes_append(list1->first, l1, l2);
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
  //@ invariant nodes(n, l, ?vs0) &*& malloc_block_node(l) &*& l->next |-> _ &*& l->value |-> _;
  {
    //@ open nodes(n, l, vs0);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(l, l, _);
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

  while (n != l)
  //@ invariant nodes(n, l, ?vs0) &*& nodes(f, l, vs) &*& c == length(vs) - length(vs0) &*& c >= 0;
  {
    //@ open nodes(n, l, vs0);
    struct node *next = n->next;

    n = next;
    if (c == INT_MAX)
      abort();
    c = c + 1;
  }
  //@ open nodes(n, l, _);
  //@ close nodes(n, l, nil);
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

  while (i < index)
  //@ invariant nodes(n, l, ?vs0) &*& nodes(f, l, vs) &*& 0 <= i &*& i <= index &*& index < length(vs) &*& length(vs0) == length(vs) - i;
  {
    //@ open nodes(n, l, vs0);
    struct node *next = n->next;

    n = next;
    i = i + 1;
  }
  //@ open nodes(n, l, ?vs1);
  int value = n->value;
  //@ close nodes(n, l, vs1);
  //@ close llist(list, vs);
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?vs) &*& length(vs) > 0;
//@ ensures llist(l, tail(vs)) &*& result == head(vs);
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

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l, ?vs);
//@ ensures llist(l, vs) &*& iter(result, l->first);
{
  struct iter *i = 0;
  struct node *f = 0;

  i = malloc(sizeof(struct iter));
  if (i == 0)
  {
    abort();
  }
  //@ open llist(l, vs);
  f = l->first;
  i->current = f;
  //@ close llist(l, vs);
  //@ close iter(i, f);
  return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?current) &*& current->next |-> ?next &*& current->value |-> ?v;
//@ ensures iter(i, next) &*& current->next |-> next &*& current->value |-> v &*& result == v;
{
  //@ open iter(i, current);
  struct node *c = i->current;

  int value = c->value;
  struct node *n = c->next;

  i->current = n;
  //@ close iter(i, n);
  return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?current);
//@ ensures true;
{
  //@ open iter(i, current);
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
  //@ open llist(l, _);
  //@ open nodes(l->first, l->last, _);
  int i1e1 = iter_next(i1);
  assert(i1e1 == 5);
  int i2e1 = iter_next(i2);
  assert(i2e1 == 5);
  //@ open nodes(_, l->last, _);
  int i1e2 = iter_next(i1);
  assert(i1e2 == 10);
  int i2e2 = iter_next(i2);
  assert(i2e2 == 10);
  iter_dispose(i1);
  iter_dispose(i2);
  //@ close nodes(_, l->last, _);
  //@ close nodes(l->first, l->last, _);
  //@ close llist(l, _);
  llist_dispose(l);
  return 0;
}