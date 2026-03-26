#include "stdlib.h"
#include "limits.h"

/*@

predicate node(struct node *n; struct node *next, int value) =
  n->next |-> next &*& n->value |-> value;

predicate nodes(struct node *from, struct node *to; int count) =
  from == to ?
    count == 0
  :
    node(from, ?nxt, ?v) &*& nodes(nxt, to, ?c0) &*& count == c0 + 1;

predicate llist(struct llist *l; struct node *first, struct node *last, int count) =
  l->first |-> first &*& l->last |-> last &*& nodes(first, last, count) &*& node(last, _, _);

predicate iter(struct iter *it; struct node *current) =
  it->current |-> current;

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
  //@ ensures llist(result, ?f, ?la, 0);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ close node(n, 0, 0);
  l->first = n;
  l->last = n;
  //@ close nodes(n, n, 0);
  //@ close llist(l, n, n, 0);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?f, ?la, ?c);
  //@ ensures llist(list, f, ?newLast, c + 1);
{
  //@ open llist(list, f, la, c);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ close node(n, 0, 0);
  l = list->last;
  //@ open node(l, ?lnext, ?lval);
  l->next = n;
  l->value = x;
  //@ close node(l, n, x);
  list->last = n;
  //@ close nodes(f, n, c + 1);
  //@ close llist(list, f, n, c + 1);
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?f1, ?l1, ?c1) &*& llist(list2, ?f2, ?l2, ?c2);
  //@ ensures llist(list1, f1, ?lnew, c1 + c2) &*& c2 >= 0;
{
  //@ open llist(list1, f1, l1, c1);
  //@ open llist(list2, f2, l2, c2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  if (f2 == l2) {
    //@ assert c2 == 0;
    //@ open nodes(f2, l2, c2);
    //@ open node(l2, ?l2n, ?l2v);
    free(l2);
    //@ open llist(list2, f2, l2, c2); // already open, but keep structure explicit
    free(list2);
    //@ close llist(list1, f1, l1, c1);
    //@ close llist(list1, f1, l1, c1 + 0);
  } else {
    //@ assert c2 > 0;
    //@ open nodes(f2, l2, c2);
    //@ open node(f2, ?f2n, ?f2v);
    l1->next = f2->next;
    l1->value = f2->value;
    //@ open node(l1, ?l1n, ?l1v);
    //@ close node(l1, f2n, f2v);
    list1->last = l2;
    //@ close nodes(f1, l2, c1 + c2);
    //@ open node(f2, f2n, f2v);
    free(f2);
    free(list2);
    //@ close llist(list1, f1, l2, c1 + c2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?f, ?la, ?c);
  //@ ensures true;
{
  //@ open llist(list, f, la, c);
  
  struct node *n = list->first;
  struct node *l = list->last;
  //@ close nodes(n, l, c);
  while (n != l)
    //@ invariant nodes(n, l, ?k) &*& k >= 0 &*& node(l, _, _);
  {
    //@ open nodes(n, l, k);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    free(n);
    n = next;
    //@ close nodes(n, l, k - 1);
  }
  
  //@ open nodes(l, l, 0);
  //@ open node(l, ?ln, ?lv);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?f, ?la, ?c);
  //@ ensures llist(list, f, la, c) &*& result == c;
{
  //@ open llist(list, f, la, c);
  
  struct node *f_ = list->first;
  struct node *n = f_;
  struct node *l = list->last;
  int c_ = 0;
  
  //@ close nodes(n, l, c);
  while (n != l)
    //@ invariant nodes(n, l, ?k) &*& node(l, _, _) &*& c_ + k == c &*& 0 <= c_;
  {
    //@ open nodes(n, l, k);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    
    
    
    n = next;
    if (c_ == INT_MAX) abort();
    c_ = c_ + 1;
    
    
    //@ close nodes(n, l, k - 1);
  }
  
  //@ assert nodes(l, l, ?k0) &*& c_ + k0 == c;
  //@ open nodes(l, l, k0);
  //@ close nodes(f_, l, c);
  //@ close llist(list, f, la, c);
  return c_;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?f, ?la, ?c) &*& 0 <= index &*& index < c;
  //@ ensures llist(list, f, la, c);
{
  //@ open llist(list, f, la, c);
  
  struct node *f_ = list->first;
  struct node *l = list->last;
  struct node *n = f_;
  int i = 0;
  
  //@ close nodes(n, l, c);
  while (i < index)
    //@ invariant nodes(n, l, ?k) &*& node(l, _, _) &*& 0 <= i &*& i <= index &*& i + k == c;
  {
    //@ open nodes(n, l, k);
    //@ open node(n, ?nnext, ?nval);
    struct node *next = n->next;
    
    
    
    
    
    n = next;
    i = i + 1;
    
    //@ close nodes(n, l, k - 1);
  }
  
  //@ open nodes(n, l, ?k);
  //@ open node(n, ?nn, ?nv);
  int value = n->value;
  //@ close node(n, nn, nv);
  //@ close nodes(n, l, k);
  //@ close nodes(f_, l, c);
  //@ close llist(list, f, la, c);
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?f, ?la, ?c) &*& c > 0;
  //@ ensures llist(l, ?f2, la, c - 1) &*& result == ?v;
{
  //@ open llist(l, f, la, c);
  //@ open nodes(f, la, c);
  
  struct node *nf = l->first;
  
  
  //@ open node(nf, ?nfn, ?nfv);
  struct node *nfn = nf->next;
  int nfv_ = nf->value;
  free(nf);
  l->first = nfn;
  //@ close nodes(nfn, la, c - 1);
  //@ close llist(l, nfn, la, c - 1);
  
  
  return nfv_;
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
    //@ requires llist(l, ?f, ?la, ?c);
    //@ ensures llist(l, f, la, c) &*& iter(result, f);
{
    //@ open llist(l, f, la, c);
    struct iter *i = 0;
    struct node *f_ = 0;
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f_ = l->first;
    i->current = f_;
    //@ close iter(i, f_);
    //@ close llist(l, f, la, c);
    
    
    
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?cur) &*& node(cur, ?nxt, ?val);
    //@ ensures iter(i, nxt) &*& node(cur, nxt, val) &*& result == val;
{
    
    struct node *c = i->current;
    
    
    
    int value = c->value;
    struct node *n = c->next;
    
    
    
    i->current = n;
    //@ open iter(i, cur);
    //@ close iter(i, n);
    
    
    
    
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?cur);
    //@ ensures true;
{
    //@ open iter(i, cur);
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