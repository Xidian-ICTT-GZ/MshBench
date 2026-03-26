#include "stdlib.h"

/*@
predicate nodes(struct node *from, struct node *to) =
  from == to ?
    from->next |-> ?nx &*& from->value |-> ?v
  :
    from->next |-> ?nx &*& from->value |-> ?v &*& nodes(nx, to);

predicate llist(struct llist *l) =
  l->first |-> ?f &*& l->last |-> ?la &*& malloc_block_llist(l) &*& nodes(f, la);

predicate iter(struct iter *it, struct node *cur) =
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
  //@ ensures llist(result);
  
  
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
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
  //@ open llist(list);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open nodes(?f, ?la);
  //@ assert la->next |-> ?lanx;
  //@ assert la->value |-> ?lav;
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close nodes(n, n);
  //@ close nodes(f, n);
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
  
  if (f2 == l2) {
    //@ open nodes(f2, l2);
    
    free(l2);
    free(list2);
    //@ close llist(list1);
    
  } else {
    //@ open nodes(f2, l2);
    //@ assert f2->next |-> ?f2n;
    //@ assert f2->value |-> ?f2v;
    //@ open nodes(f2n, l2);
    //@ open nodes(?f1, l1);
    //@ assert l1->next |-> ?l1n;
    //@ assert l1->value |-> ?l1v;
    
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    
    
    
    
    free(f2);
    free(list2);
    //@ close nodes(f1, l2);
    //@ close llist(list1);
  }
}

void llist_dispose(struct llist *list)
  //@ requires llist(list);
  //@ ensures true;
  
  
{
  //@ open llist(list);
  
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open nodes(n, l);
  while (n != l)
    //@ invariant nodes(n, l);
    
  {
    
    
    struct node *next = n->next;
    //@ open nodes(next, l);
    free(n);
    n = next;
  }
  
  
  //@ open nodes(l, l);
  free(l);
  free(list);
}

int llist_length(struct llist *list)
  //@ requires llist(list);
  //@ ensures llist(list);
  
  
{
  //@ open llist(list);
  
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  
  //@ open nodes(f, l);
  while (n != l)
    //@ invariant nodes(f, n) &*& nodes(n, l) &*& c >= 0;
    
  {
    
    
    struct node *next = n->next;
    
    
    //@ open nodes(n, l);
    //@ close nodes(n, n);
    //@ close nodes(f, next);
    
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
    
    
  }
  
  
  //@ close nodes(f, l);
  //@ close llist(list);
  
  return c;
}

int llist_lookup(struct llist *list, int index)
  //@ requires llist(list) &*& 0 <= index;
  //@ ensures llist(list);
  
  
{
  //@ open llist(list);
  
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  
  //@ open nodes(f, l);
  while (i < index)
    //@ invariant nodes(f, n) &*& nodes(n, l) &*& 0 <= i;
    
  {
    
    
    
    
    struct node *next = n->next;
    
    
    
    
    
    //@ open nodes(n, l);
    //@ close nodes(n, n);
    //@ close nodes(f, next);
    n = next;
    i = i + 1;
    
  }
  
  
  //@ open nodes(n, l);
  int value = n->value;
  //@ close nodes(n, l);
  //@ close nodes(f, l);
  //@ close llist(list);
  
  
  return value;
}

int llist_removeFirst(struct llist *l)
  //@ requires llist(l) &*& l->first != l->last;
  //@ ensures llist(l);
  
  
{
  //@ open llist(l);
  
  struct node *nf = l->first;
  
  
  //@ open nodes(nf, ?la);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  //@ open nodes(nfn, la);
  free(nf);
  l->first = nfn;
  
  
  //@ close nodes(nfn, la);
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
    //@ requires llist(l);
    //@ ensures llist(l) &*& iter(result, ?cur);
    
    
{
    //@ open llist(l);
    struct iter *i = 0;
    struct node *f = 0;
    
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    
    f = l->first;
    i->current = f;
    
    
    //@ close llist(l);
    //@ close iter(i, f);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?cur) &*& cur->next |-> ?nx &*& cur->value |-> ?v;
    //@ ensures iter(i, nx);
    

    
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
    //@ open llist(l);
    //@ assert l->first |-> ?f &*& l->last |-> ?la;
    //@ open nodes(f, la);
    //@ assert f->next |-> ?n1;
    //@ assert f->value |-> ?v0;
    //@ open nodes(n1, la);
    //@ assert n1->next |-> ?n2;
    //@ assert n1->value |-> ?v1;
    //@ close nodes(n1, la);
    //@ close nodes(f, la);
    //@ close llist(l);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    //@ open llist(l);
    //@ assert l->first |-> ?f2 &*& l->last |-> ?la2;
    //@ open nodes(f2, la2);
    //@ assert f2->next |-> ?m1;
    //@ assert f2->value |-> ?w0;
    //@ open nodes(m1, la2);
    //@ assert m1->next |-> ?m2;
    //@ assert m1->value |-> ?w1;
    //@ close nodes(m1, la2);
    //@ close nodes(f2, la2);
    //@ close llist(l);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    //@ open llist(l);
    //@ assert l->first |-> ?f3 &*& l->last |-> ?la3;
    //@ open nodes(f3, la3);
    //@ assert f3->next |-> ?p1;
    //@ assert f3->value |-> ?u0;
    //@ open nodes(p1, la3);
    //@ assert p1->next |-> ?p2;
    //@ assert p1->value |-> ?u1;
    //@ open nodes(p2, la3);
    //@ assert p2->next |-> ?p3;
    //@ assert p2->value |-> ?u2;
    //@ close nodes(p2, la3);
    //@ close nodes(p1, la3);
    //@ close nodes(f3, la3);
    //@ close llist(l);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    //@ open llist(l);
    //@ assert l->first |-> ?f4 &*& l->last |-> ?la4;
    //@ open nodes(f4, la4);
    //@ assert f4->next |-> ?q1;
    //@ assert f4->value |-> ?t0;
    //@ open nodes(q1, la4);
    //@ assert q1->next |-> ?q2;
    //@ assert q1->value |-> ?t1;
    //@ open nodes(q2, la4);
    //@ assert q2->next |-> ?q3;
    //@ assert q2->value |-> ?t2;
    //@ close nodes(q2, la4);
    //@ close nodes(q1, la4);
    //@ close nodes(f4, la4);
    //@ close llist(l);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}