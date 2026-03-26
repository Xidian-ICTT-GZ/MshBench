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
predicate node(struct node *n; struct node *next, int value) =
  n != 0 &*& n->next |-> next &*& n->value |-> value;

predicate nodes(struct node *from, struct node *to; int count) =
  from == to ?
    count == 0
  :
    exists<struct node *>(?next) &*& exists<int>(?v) &*& node(from; next, v) &*& nodes(next, to; ?c) &*& count == c + 1;

predicate llist(struct llist *l; struct node *first, struct node *last, int count) =
  l != 0 &*& l->first |-> first &*& l->last |-> last &*& first != 0 &*& last != 0 &*& nodes(first, last; count) &*& node(last; 0, _);

predicate iter(struct iter *it; struct node *current) =
  it != 0 &*& it->current |-> current;
@*/

struct llist *create_llist()
  //@ requires true;
  //@ ensures llist(result; ?f, ?la, 0);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n; 0, 0);
  //@ close nodes(n, n; 0);
  //@ close llist(l; n, n, 0);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list; ?f, ?la, ?c);
  //@ ensures llist(list; f, ?newLast, c + 1);
{
  //@ open llist(list; f, la, c);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node(n; 0, 0);
  l = list->last;
  //@ open node(l; 0, ?oldv);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(l; n, x);
  //@ close nodes(f, n; c + 1);
  //@ close llist(list; f, n, c + 1);
  
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1; ?f1, ?la1, ?c1) &*& llist(list2; ?f2, ?la2, ?c2);
  //@ ensures llist(list1; f1, ?newLast, c1 + c2) &*& list2 == 0;
{
  //@ open llist(list1; f1, la1, c1);
  //@ open llist(list2; f2, la2, c2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  if (f2 == l2) {
    //@ open nodes(f2, l2; c2);
    //@ open node(l2; 0, ?vv);
    free(l2);
    free(list2);
    //@ close nodes(f1, la1; c1);
    //@ close llist(list1; f1, la1, c1);
  } else {
    //@ open nodes(f2, l2; c2);
    //@ open node(f2; ?f2next, ?f2v);
    //@ open node(l1; 0, ?l1v);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    //@ close node(l1; f2next, f2v);
    free(f2);
    free(list2);
    //@ close nodes(f1, l2; c1 + c2);
    //@ close llist(list1; f1, l2, c1 + c2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list; ?f, ?la, ?c);
  //@ ensures true;
{
  //@ open llist(list; f, la, c);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant nodes(n, l; ?k) &*& node(l; 0, _) &*& list->first |-> f &*& list->last |-> l &*& list != 0;
  {
    //@ open nodes(n, l; k);
    struct node *next = n->next;
    //@ open node(n; next, ?v);
    free(n);
    n = next;
  }
  //@ open nodes(l, l; 0);
  //@ open node(l; 0, ?lv);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list; ?f, ?la, ?c);
  //@ ensures llist(list; f, la, c) &*& result == c;
{
  //@ open llist(list; f, la, c);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  while (n != l)
    //@ invariant nodes(f, n; c) &*& nodes(n, l; ?k) &*& node(l; 0, _) &*& c + k == ?total &*& total == c + k;
  {
    //@ open nodes(n, l; k);
    struct node *next = n->next;
    //@ close nodes(f, next; c + 1);
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ assert nodes(n, l; k - 1) | true;
  }
  //@ open nodes(n, l; ?kk);
  //@ close nodes(n, l; kk);
  //@ close llist(list; f, la, c);
  
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list; ?f, ?la, ?c) &*& 0 <= index &*& index < c;
  //@ ensures llist(list; f, la, c);
{
  //@ open llist(list; f, la, c);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)
    //@ invariant nodes(f, n; i) &*& nodes(n, l; ?k) &*& node(l; 0, _) &*& i + k == c &*& i <= index;
  {
    //@ open nodes(n, l; k);
    struct node *next = n->next;
    //@ close nodes(f, next; i + 1);
    n = next;
    i = i + 1;
  }
  
  //@ open nodes(n, l; ?k2);
  //@ open node(n; ?nn, ?vv);
  int value = n->value;
  //@ close node(n; nn, vv);
  //@ close nodes(n, l; k2);
  //@ close llist(list; f, la, c);
  
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l; ?f, ?la, ?c) &*& 0 < c;
  //@ ensures llist(l; ?nf, la, c - 1);
{
  //@ open llist(l; f, la, c);
  //@ open nodes(f, la; c);
  struct node *nf = l->first;
  
  struct node *nfn = nf->next;
  //@ open node(nf; nfn, ?nfv0);
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close nodes(nfn, la; c - 1);
  //@ close llist(l; nfn, la, c - 1);
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

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l; ?f, ?la, ?c);
    //@ ensures llist(l; f, la, c) &*& iter(result; f);
{
    //@ open llist(l; f, la, c);
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f = l->first;
    i->current = f;
    //@ close llist(l; f, la, c);
    //@ close iter(i; f);
    
    
    
    
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i; ?c) &*& node(c; ?n, ?v);
    //@ ensures iter(i; n) &*& node(c; n, v) &*& result == v;
{
    //@ open iter(i; c);
    
    struct node *c = i->current;
    
    //@ open node(c; n, v);
    int value = c->value;
    struct node *n = c->next;
    
    i->current = n;
    
    //@ close node(c; n, v);
    //@ close iter(i; n);
    
    
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i; ?c);
    //@ ensures true;
{
    //@ open iter(i; c);
    
    
    
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