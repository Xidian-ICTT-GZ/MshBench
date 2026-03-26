#include "stdlib.h"

/*@ predicate node(struct node *n, struct node *next, int value) =
    n != 0 &*& malloc_block_node(n) &*&
    n->next |-> next &*& n->value |-> value;
@*/

/*@ predicate node_list(struct node *head, struct node *tail) =
    head == tail ?
        node(head, 0, _) &*& tail == head
    :
        exists(struct node *next, int v;
            node(head, next, v) &*& node_list(next, tail));
@*/

/*@ predicate llist(struct llist *l; struct node *first, struct node *last) =
    l != 0 &*&
    malloc_block_llist(l) &*&
    first != 0 &*& last != 0 &*&
    l->first |-> first &*& l->last |-> last &*&
    node_list(first, last);
@*/

/*@ predicate iter(struct iter *i; struct node *current) =
    i != 0 &*& malloc_block_iter(i) &*& i->current |-> current;
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
/*@ requires true;
    ensures llist(result, ?f, ?l) &*& node_list(f, l);
@*/
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0)
    abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
    abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close node_list(n, n);
  //@ close llist(l, n, n);
  return l;
}

void llist_add(struct llist *list, int x)
/*@ requires llist(list, ?f, ?t) &*& node_list(f, t);
    ensures llist(list, f, ?nt) &*& node_list(f, nt);
@*/
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
  {
    abort();
  }
  //@ open llist(list, ?f, ?t);
  l = list->last;
  //@ open node_list(f, t);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ close node_list(f, n);
  //@ close llist(list, f, n);
}

void llist_append(struct llist *list1, struct llist *list2)
/*@ requires llist(list1, ?f1, ?t1) &*& node_list(f1, t1) &*&
             llist(list2, ?f2, ?t2) &*& node_list(f2, t2);
    ensures llist(list1, f1, ?nt) &*& node_list(f1, nt);
@*/
{
  //@ open llist(list1, ?f1, ?t1);
  //@ open llist(list2, ?f2, ?t2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2)
  {
    //@ open node(f2, 0, _);
    free(l2);
    free(list2);
    //@ close llist(list1, f1, t1);
  }
  else
  {
    //@ open node_list(f2, t2);
    //@ open node(f2, ?next2, ?v2);
    l1->next = f2->next;
    l1->value = v2;
    list1->last = l2;

    //@ close node(l1, next2, v2);
    //@ close node_list(f1, l2);
    //@ close llist(list1, f1, l2);

    free(f2);
    free(list2);
  }
}

void llist_dispose(struct llist *list)
/*@ requires llist(list, ?f, ?l) &*& node_list(f, l);
    ensures true;
@*/
{
  //@ open llist(list, ?f, ?l);
  struct node *n = list->first;
  struct node *last = list->last;
  while (n != last)
  //@ invariant node_list(n, last) &*& llist(list, f, last) &*& n != 0;
  {
    struct node *next = n->next;
    //@ open node(n, next, _);
    free(n);
    n = next;
  }

  //@ open node(last, 0, _);
  free(last);
  free(list);
}

int llist_length(struct llist *list)
/*@ requires llist(list, ?f, ?l) &*& node_list(f, l);
    ensures llist(list, f, l) &*& result >= 0;
@*/
{
  //@ open llist(list, ?f, ?l);
  struct node *n = f;
  struct node *last = l;
  int c = 0;

  while (n != last)
  //@ invariant node_list(n, last) &*& c >= 0 &*& c <= INT_MAX;
  {
    struct node *next = n->next;
    //@ open node(n, next, _);
    n = next;
    if (c == INT_MAX)
      abort();
    c = c + 1;
  }

  //@ close llist(list, f, l);
  return c;
}

int llist_lookup(struct llist *list, int index)
/*@ requires llist(list, ?f, ?l) &*& node_list(f, l);
    ensures llist(list, f, l) &*& true;
@*/
{
  //@ open llist(list, ?f, ?l);
  struct node *n = f;
  int i = 0;
  while (i < index)
  //@ invariant node_list(f, l) &*& i <= index &*& n != 0;
  {
    struct node *next = n->next;
    //@ open node(n, next, _);
    n = next;
    i = i + 1;
  }

  int value = n->value;
  //@ close llist(list, f, l);
  return value;
}

int llist_removeFirst(struct llist *l)
/*@ requires llist(l, ?f, ?last) &*& node_list(f, last) &*& f != last;
    ensures llist(l, ?nf, last) &*& node_list(nf, last);
@*/
{
  //@ open llist(l, ?f, ?last);
  struct node *nf = l->first;
  //@ open node(nf, ?next, ?val);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close node_list(nfn, last);
  //@ close llist(l, nfn, last);
  return nfv;
}

struct iter *llist_create_iter(struct llist *l)
/*@ requires llist(l, ?f, ?l2) &*& node_list(f, l2);
    ensures iter(result, f);
@*/
{
  //@ open llist(l, ?f, ?_);
  struct iter *i = malloc(sizeof(struct iter));
  if (i == 0)
  {
    abort();
  }

  i->current = f;
  //@ close iter(i, f);
  return i;
}

int iter_next(struct iter *i)
/*@ requires iter(i, ?c) &*& node(c, ?next, ?val);
    ensures iter(i, next);
@*/
{
  //@ open iter(i, ?c);
  struct node *cur = i->current;
  //@ open node(cur, ?next, ?val);
  int value = cur->value;
  struct node *n = cur->next;
  i->current = n;
  //@ close iter(i, n);
  return value;
}

void iter_dispose(struct iter *i)
/*@ requires iter(i, _);
    ensures true;
@*/
{
  //@ open iter(i, _);
  free(i);
}

void main0()
/*@ requires true;
    ensures true;
@*/
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
/*@ requires true;
    ensures true;
@*/
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

int main2()
/*@ requires true;
    ensures true;
@*/
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