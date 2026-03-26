#include "stdlib.h"
#include "limits.h"

/*@
predicate node(struct node *n; struct node *next, int value) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->next |-> next &*&
    n->value |-> value;

predicate nodes(struct node *from, struct node *to;) =
    from == to ?
        emp
    :
        node(from, ?next, _) &*& nodes(next, to);

predicate llist(struct llist *l;) =
    l != 0 &*&
    malloc_block_llist(l) &*&
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    nodes(first, last) &*&
    node(last, 0, _);

predicate iter(struct iter *i, struct node *current;) =
    i != 0 &*&
    malloc_block_iter(i) &*&
    i->current |-> current;

lemma void nodes_add(struct node *first)
    requires nodes(first, ?last) &*& node(last, ?next, ?v);
    ensures nodes(first, next) &*& node(last, next, v);
{
    open nodes(first, last);
    if (first == last) {
        close nodes(last, next);
    } else {
        nodes_add(?n);
    }
    close nodes(first, next);
}

lemma void nodes_append(struct node *first, struct node *mid, struct node *last)
    requires nodes(first, mid) &*& nodes(mid, last);
    ensures nodes(first, last);
{
    open nodes(first, mid);
    if (first == mid) {
    } else {
        nodes_append(?next, mid, last);
        close nodes(first, last);
    }
}
@*/

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

struct iter
{
  struct node *current;
};

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
  //@ close nodes(n, n);
  //@ close llist(l);
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
  //@ open llist(list);
  l = list->last;
  //@ open node(l, 0, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ nodes_add(list->first);
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

  //@ open nodes(f2, l2);
  if (f2 == l2)
  {
    //@ open node(l2, 0, _);
    free(l2);
    free(list2);
    //@ close llist(list1);
  }
  else
  {
    //@ open node(l1, 0, _);
    //@ open node(f2, ?next2, ?v2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node(l1, next2, v2);
    //@ nodes_add(list1->first);
    //@ nodes_append(list1->first, next2, l2);
    //@ close llist(list1);
    free(f2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
//@ requires llist(list);
//@ ensures true;
{
  //@ open llist(list);
  struct node *n = list->first;
  struct node *last = list->last;
  while (n != last)
  //@ invariant nodes(n, last) &*& node(last, 0, _);
  {
    //@ open nodes(n, last);
    //@ open node(n, ?next, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open nodes(last, last);
  //@ open node(last, 0, _);
  free(last);
  free(list);
}

int llist_length(struct llist *list)
//@ requires llist(list);
//@ ensures llist(list);
{
  //@ open llist(list);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int c = 0;
  //@ close nodes(f, f);

  while (n != l)
  //@ invariant nodes(f, n) &*& nodes(n, l) &*& node(l, 0, _) &*& c >= 0;
  {
    //@ open nodes(n, l);
    //@ open node(n, ?next, ?v);
    struct node *next = n->next;
    //@ close node(n, next, v);
    //@ nodes_add(f);
    n = next;
    if (c == INT_MAX)
      abort();
    c = c + 1;
  }
  //@ nodes_append(f, l, l);
  //@ close llist(list);
  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list) &*& index >= 0;
//@ ensures llist(list);
{
  //@ open llist(list);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  //@ close nodes(f, f);

  while (i < index)
  //@ invariant nodes(f, n) &*& nodes(n, l) &*& node(l, 0, _) &*& i >= 0 &*& i <= index;
  {
    //@ open nodes(n, l);
    //@ open node(n, ?next, ?v);
    struct node *next = n->next;
    //@ close node(n, next, v);
    //@ nodes_add(f);
    n = next;
    i = i + 1;
  }

  //@ open nodes(n, l);
  //@ open node(n, ?nn, ?nv);
  int value = n->value;
  //@ close node(n, nn, nv);
  //@ close nodes(n, l);
  //@ nodes_append(f, n, l);
  //@ close llist(list);
  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l);
//@ ensures llist(l);
{
  //@ open llist(l);
  struct node *nf = l->first;
  //@ open nodes(nf, ?last);
  //@ open node(nf, ?next, ?val);
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

struct iter *llist_create_iter(struct llist *l)
//@ requires llist(l);
//@ ensures iter(result, ?c) &*& llist(l);
{
  //@ open llist(l);
  struct iter *i = malloc(sizeof(struct iter));
  if (i == 0)
  {
    abort();
  }
  struct node *f = l->first;
  i->current = f;
  //@ close iter(i, f);
  //@ close llist(l);
  return i;
}

int iter_next(struct iter *i)
//@ requires iter(i, ?c) &*& node(c, ?next, ?val);
//@ ensures iter(i, next) &*& node(c, next, val);
{
  //@ open iter(i, c);
  struct node *cur = i->current;
  //@ open node(cur, next, val);
  int value = cur->value;
  struct node *n = cur->next;
  i->current = n;
  //@ close node(cur, next, val);
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

int main2()
//@ requires true;
//@ ensures true;
{
  struct llist *l = create_llist();
  llist_add(l, 5);
  llist_add(l, 10);
  llist_add(l, 15);
  //@ open llist(l);
  //@ open nodes(?f, ?last);
  //@ open node(f, ?n1, ?v1);
  //@ close node(f, n1, v1);
  //@ open nodes(n1, last);
  //@ open node(n1, ?n2, ?v2);
  //@ close node(n1, n2, v2);
  //@ open nodes(n2, last);
  //@ open node(n2, ?n3, ?v3);
  //@ close node(n2, n3, v3);
  //@ close nodes(n2, last);
  //@ close nodes(n1, last);
  //@ close nodes(f, last);
  //@ close llist(l);
  struct iter *i1 = llist_create_iter(l);
  struct iter *i2 = llist_create_iter(l);
  //@ open llist(l);
  //@ open nodes(f, last);
  int i1e1 = iter_next(i1);
  assert(i1e1 == 5);
  int i2e1 = iter_next(i2);
  assert(i2e1 == 5);
  //@ open nodes(n1, last);
  int i1e2 = iter_next(i1);
  assert(i1e2 == 10);
  int i2e2 = iter_next(i2);
  assert(i2e2 == 10);
  //@ close nodes(n1, last);
  //@ close nodes(f, last);
  //@ close llist(l);
  iter_dispose(i1);
  iter_dispose(i2);
  llist_dispose(l);
  return 0;
}