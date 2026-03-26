#include "stdlib.h"
#include "limits.h"

/*@

predicate node(struct node *n; struct node *next, int value) =
  n->next |-> next &*& n->value |-> value;

predicate nodes(struct node *from, struct node *to) =
  from == to ?
    emp
  :
    node(from, ?nxt, ?v) &*& nodes(nxt, to);

predicate llist(struct llist *l; struct node *first, struct node *last) =
  l->first |-> first &*& l->last |-> last &*& malloc_block_llist(l) &*& nodes(first, last) &*& node(last, _, _);

predicate iter(struct iter *it; struct node *current) =
  it->current |-> current &*& malloc_block_iter(it);

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
  //@ requires true;
  //@ ensures llist(result, ?f, ?l) &*& f == l;
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close nodes(n, n);
  //@ close llist(l, n, n);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?f, ?last);
  //@ ensures llist(list, f, ?newLast);
{
  //@ open llist(list, f, last);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open node(last, ?lnext0, ?lval0);
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l, n, x);
  //@ close node(n, 0, 0);
  //@ close nodes(f, n);
  //@ close llist(list, f, n);
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?f1, ?l1) &*& llist(list2, ?f2, ?l2);
  //@ ensures llist(list1, f1, ?l) ;
{
  //@ open llist(list1, f1, l1);
  //@ open llist(list2, f2, l2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  if (f2 == l2) {
    //@ open nodes(f2, l2);
    //@ open node(l2, ?nxt2, ?val2);
    free(l2);
    free(list2);
    //@ close nodes(f1, l1);
    //@ close node(l1, _, _);
    //@ close llist(list1, f1, l1);
  } else {
    //@ open nodes(f2, l2);
    //@ open node(f2, ?f2next, ?f2val);
    //@ open node(l1, ?l1next0, ?l1val0);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    //@ close node(l1, f2next, f2val);
    free(f2);
    free(list2);
    //@ close llist(list1, f1, l2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?f, ?l);
  //@ ensures true;
{
  //@ open llist(list, f, l);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open nodes(n, l);
  while (n != l)
    //@ invariant nodes(n, l) &*& node(l, _, _) &*& malloc_block_llist(list) &*& list->first |-> ?ff &*& list->last |-> l;
  {
    //@ open nodes(n, l);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open node(l, ?lnext, ?lval);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?f, ?l);
  //@ ensures llist(list, f, l);
{
  //@ open llist(list, f, l);
  struct node *f_ = list->first;
  struct node *n = f_;
  struct node *l_ = list->last;
  int c = 0;
  //@ close nodes(f_, l_);
  while (n != l_)
    //@ invariant nodes(f_, n) &*& nodes(n, l_) &*& node(l_, _, _) &*& list->first |-> f_ &*& list->last |-> l_ &*& malloc_block_llist(list) &*& c >= 0;
  {
    //@ open nodes(n, l_);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    //@ close node(n, nnext, nval);
    //@ close nodes(f_, next);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ close llist(list, f_, l_);
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?f, ?l) &*& index >= 0;
  //@ ensures llist(list, f, l);
{
  //@ open llist(list, f, l);
  struct node *f_ = list->first;
  struct node *l_ = list->last;
  struct node *n = f_;
  int i = 0;
  //@ close nodes(f_, l_);
  while (i < index)
    //@ invariant nodes(f_, n) &*& nodes(n, l_) &*& node(l_, _, _) &*& list->first |-> f_ &*& list->last |-> l_ &*& malloc_block_llist(list) &*& i >= 0;
  {
    //@ open nodes(n, l_);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    //@ close node(n, nnext, nval);
    //@ close nodes(f_, next);
    n = next;
    i = i + 1;
  }
  //@ open node(n, ?nnext2, ?nval2);
  int value = n->value;
  //@ close node(n, nnext2, nval2);
  //@ close nodes(n, l_);
  //@ close llist(list, f_, l_);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?f, ?last) &*& f != last;
  //@ ensures llist(l, ?newFirst, last);
{
  //@ open llist(l, f, last);
  struct node *nf = l->first;
  //@ open nodes(nf, last);
  //@ open node(nf, ?nfnext, ?nfv0);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close llist(l, nfn, last);
  return nfv;
}

void main0()
  //@ requires true;
  //@ ensures true;
{
  struct llist *l = create_llist();
  //@ open llist(l, ?f, ?last);
  //@ close llist(l, f, last);
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  //@ open llist(l, ?ff, ?ll);
  //@ close llist(l, ff, ll);
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

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l, ?f, ?last);
    //@ ensures llist(l, f, last) &*& iter(result, f);
{
    //@ open llist(l, f, last);
    struct iter *i = 0;
    struct node *f0 = 0;
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f0 = l->first;
    i->current = f0;
    
    //@ close llist(l, f, last);
    //@ close iter(i, f0);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?c) &*& node(c, ?n, ?v);
    //@ ensures iter(i, n) &*& node(c, n, v) &*& result == v;
{
    //@ open iter(i, c);
    struct node *c0 = i->current;
    //@ open node(c0, n, v);
    int value = c0->value;
    struct node *n0 = c0->next;
    i->current = n0;
    //@ close node(c0, n0, v);
    //@ close iter(i, n0);
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?c);
    //@ ensures true;
{
    //@ open iter(i, c);
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