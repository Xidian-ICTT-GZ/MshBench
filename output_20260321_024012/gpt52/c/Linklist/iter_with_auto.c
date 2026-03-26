#include "stdlib.h"

/*@
predicate nodes(struct node *from, struct node *to; int n) =
  from == to ?
    n == 0
  :
    from != 0 &*& from->next |-> ?next &*& from->value |-> _ &*& malloc_block_node(from) &*&
    nodes(next, to, ?n0) &*& n == n0 + 1;

predicate llist(struct llist *l; int n) =
  l->first |-> ?f &*& l->last |-> ?la &*& malloc_block_llist(l) &*&
  f != 0 &*& la != 0 &*& nodes(f, la, n) &*& la->next |-> _ &*& la->value |-> _ &*& malloc_block_node(la);

predicate iter(struct iter *it; struct node *cur) =
  it->current |-> cur &*& malloc_block_iter(it);
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
  //@ ensures llist(result, 0);
  
  
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ assume(n->next == 0);
  //@ assume(n->value == 0);
  l->first = n;
  l->last = n;
  //@ close nodes(n, n, 0);
  //@ close llist(l, 0);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?n);
  //@ ensures llist(list, n+1);
  
  
{
  //@ open llist(list, n);
  struct node *l = 0;
  struct node *n0 = calloc(1, sizeof(struct node));
  if (n0 == 0) {
    abort();
  }
  //@ assume(n0->next == 0);
  //@ assume(n0->value == 0);
  l = list->last;
  //@ open nodes(?f, l, n);
  l->next = n0;
  l->value = x;
  list->last = n0;
  //@ close nodes(n0, n0, 0);
  //@ close nodes(f, n0, n+1);
  //@ close llist(list, n+1);
  
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?n1) &*& llist(list2, ?n2);
  //@ ensures llist(list1, n1+n2) &*& true;
  
  
{
  //@ open llist(list1, n1);
  //@ open llist(list2, n2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  if (f2 == l2) {
    //@ open nodes(f2, l2, n2);
    free(l2);
    free(list2);
    //@ close llist(list1, n1);
  } else {
    //@ assert f2 != l2;
    //@ open nodes(f2, l2, n2);
    //@ open nodes(?f1, l1, n1);
    
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    free(f2);
    free(list2);
    //@ close nodes(f1, l2, n1 + n2);
    //@ close llist(list1, n1 + n2);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?n);
  //@ ensures true;
  
  
{
  //@ open llist(list, n);
  struct node *n0 = list->first;
  struct node *l = list->last;
  //@ open nodes(n0, l, n);
  while (n0 != l)
    //@ invariant n0 != 0 &*& l != 0 &*& nodes(n0, l, ?k) &*& l->next |-> _ &*& l->value |-> _ &*& malloc_block_node(l);
    
    
  {
    //@ open nodes(n0, l, k);
    struct node *next = n0->next;
    free(n0);
    n0 = next;
  }
  //@ close nodes(l, l, 0);
  
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list, ?n);
  //@ ensures llist(list, n) &*& result == n;
  
  
{
  //@ open llist(list, n);
  struct node *f = list->first;
  struct node *n0 = f;
  struct node *l = list->last;
  int c = 0;
  
  //@ open nodes(f, l, n);
  while (n0 != l)
    //@ invariant nodes(f, n0, c) &*& nodes(n0, l, n - c) &*& 0 <= c &*& c <= n &*& l->next |-> _ &*& l->value |-> _ &*& malloc_block_node(l);
    
    
  {
    
    
    //@ open nodes(n0, l, n - c);
    struct node *next = n0->next;
    
    
    n0 = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    //@ close nodes(f, n0, c);
    
    
  }
  //@ close nodes(l, l, 0);
  //@ close nodes(f, l, n);
  //@ close llist(list, n);
  
  
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list, ?n) &*& 0 <= index &*& index < n;
  //@ ensures llist(list, n);
  
  
{
  //@ open llist(list, n);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n0 = f;
  int i = 0;
  //@ open nodes(f, l, n);
  while (i < index)
    //@ invariant nodes(f, n0, i) &*& nodes(n0, l, n - i) &*& 0 <= i &*& i <= index &*& index < n &*& l->next |-> _ &*& l->value |-> _ &*& malloc_block_node(l);
    
    
  {
    
    
    //@ open nodes(n0, l, n - i);
    struct node *next = n0->next;
    
    
    
    n0 = next;
    i = i + 1;
    //@ close nodes(f, n0, i);
    
  }
  //@ open nodes(n0, l, n - i);
  
  int value = n0->value;
  
  //@ close nodes(n0, l, n - i);
  //@ close nodes(f, l, n);
  //@ close llist(list, n);
  
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l, ?n) &*& 0 < n;
  //@ ensures llist(l, n-1);
  
  
{
  //@ open llist(l, n);
  struct node *nf = l->first;
  
  //@ open nodes(nf, ?la, n);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  //@ close nodes(nfn, la, n-1);
  //@ close llist(l, n-1);
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
    //@ requires llist(l, ?n);
    //@ ensures llist(l, n) &*& iter(result, ?cur) &*& cur == (struct node*)0 ? true : true;
    
    
{
    //@ open llist(l, n);
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f = l->first;
    i->current = f;
    
    
    //@ close llist(l, n);
    //@ close iter(i, f);
    
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?cur) &*& cur != 0 &*& cur->next |-> ?nxt &*& cur->value |-> ?v &*& malloc_block_node(cur);
    //@ ensures iter(i, nxt) &*& result == v &*& cur->next |-> nxt &*& cur->value |-> v &*& malloc_block_node(cur);
    
    
{
    //@ open iter(i, cur);
    
    struct node *c = i->current;
    
    
    
    int value = c->value;
    struct node *n = c->next;
    
    
    
    i->current = n;
    
    
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
    //@ open llist(l, 3);
    //@ assert l->first |-> ?f &*& l->last |-> ?la;
    //@ open nodes(f, la, 3);
    //@ open nodes(f, la, 3);
    //@ open nodes(f, la, 3);
    //@ close nodes(f, la, 3);
    //@ close llist(l, 3);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}