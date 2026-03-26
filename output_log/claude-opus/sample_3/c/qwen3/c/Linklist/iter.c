#include "stdlib.h"

/*@ predicate llist(struct llist *l; struct node *first, struct node *last) =
    l != 0 &*& 
    malloc_block_llist(l) &*&
    first != 0 &*& last != 0 &*&
    node_list(first, last, ?ps) &*&
    ps != nil;
@*/

/*@ predicate node_list(struct node *head, struct node *tail, list<int> ps) =
    head == tail ?
        ps == cons(head->value, nil) &*&
        head->next == 0 &*&
        malloc_block_node(head)
    :
        head != tail &*&
        head->next != 0 &*&
        malloc_block_node(head) &*&
        node_list(head->next, tail, ?qs) &*&
        ps == cons(head->value, qs);
@*/

/*@ predicate iter(struct iter *i; struct node *current) =
    i != 0 &*& malloc_block_iter(i) &*& current != 0 &*&
    malloc_block_node(current) &*& i->current == current;
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

struct llist *create_llist()

{
  //@ requires true;
  //@ ensures llist(result; ?f, ?l) &*& f == l;
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0)
    abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
    abort();
  l->first = n;
  l->last = n;
  //@ assert malloc_block_node(n);
  //@ assert node_list(n, n, cons(n->value, nil));
  //@ assert n->value == 0;
  //@ leak node_list(n, n, cons(0, nil));
  return l;
}

void llist_add(struct llist *list, int x)

{
  //@ requires llist(list; ?f, ?l);
  //@ ensures llist(list; f, ?new_last) &*& node_list(f, new_last, ?ps) &*&
  //@         exists<list<int> > (ps_prefix, ps) (node_list(f, l, ps_prefix) &*&
  //@         ps == append(ps_prefix, cons(x, nil)));
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0)
  {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ assert malloc_block_node(n);
  //@ assert node_list(l, n, cons(x, nil));
  //@ assert node_list(list->first, l, ?prefix);
  //@ assert node_list(list->first, n, append(prefix, cons(x, nil)));
}

void llist_append(struct llist *list1, struct llist *list2)

{
  //@ requires llist(list1; ?f1, ?l1) &*& llist(list2; ?f2, ?l2);
  //@ ensures llist(list1; f1, ?new_last) &*&
  //@         (f2 == l2 ? true : 
  //@          node_list(f1, new_last, ?ps) &*&
  //@          exists<list<int> > (p1, p2) (ps == append(p1, p2) &*& node_list(f1, l1, p1) &*& node_list(f2, l2, p2)));
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;

  if (f2 == l2)
  {
    //@ assert f2 == l2;
    //@ assert node_list(f2, l2, cons(f2->value, nil));
    free(l2);
    free(list2);
  }
  else
  {
    //@ assert f2 != l2;
    //@ assert node_list(f2, l2, ?p2) &*& p2 != nil;
    //@ assert node_list(list1->first, l1, ?p1) &*& p1 != nil;
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;

    free(f2);
    free(list2);
    //@ assert node_list(list1->first, l2, append(p1, p2));
  }
}

void llist_dispose(struct llist *list)

{
  //@ requires llist(list; ?f, ?l);
  //@ ensures true;
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant node_list(n, l, ?ps) &*& ps != nil &*& malloc_block_llist(list);
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }

  free(l);
  free(list);
}

int llist_length(struct llist *list)

{
  //@ requires llist(list; ?f, ?l);
  //@ ensures llist(list; f, l) &*& result == length(?ps) &*& node_list(f, l, ps);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;

  while (n != l)
  //@ invariant node_list(n, l, ?ps) &*& ps != nil &*& c == length(?prefix) &*&
  //@          node_list(f, n, prefix) &*& malloc_block_llist(list);
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX)
      abort();
    c = c + 1;
  }

  return c;
}

int llist_lookup(struct llist *list, int index)

{
  //@ requires llist(list; ?f, ?l) &*& 0 <= index &*& index < length(?ps) &*& node_list(f, l, ps);
  //@ ensures llist(list; f, l) &*& result == nth(index, ps);
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;

  while (i < index)
  //@ invariant node_list(n, l, ?ps) &*& i <= index &*& i == length(?prefix) &*&
  //@          node_list(f, n, prefix) &*& malloc_block_llist(list);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }

  int value = n->value;

  return value;
}

int llist_removeFirst(struct llist *l)

{
  //@ requires llist(l; ?f, ?last) &*& node_list(f, last, ?ps) &*& ps != nil;
  //@ ensures llist(l; ?new_first, last) &*&
  //@         node_list(new_first, last, ?qs) &*&
  //@         ps == cons(?v, qs) &*& result == v;
  struct node *nf = l->first;

  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;

  return nfv;
}

void main0()

{
  //@ requires true;
  //@ ensures true;
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

{
  //@ requires true;
  //@ ensures true;
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

{
  //@ requires llist(l; ?f, ?_);
  //@ ensures iter(result; f);
  struct iter *i = 0;
  struct node *f = 0;

  i = malloc(sizeof(struct iter));
  if (i == 0)
  {
    abort();
  }

  f = l->first;
  i->current = f;

  return i;
}

int iter_next(struct iter *i)

{
  //@ requires iter(i; ?c);
  //@ ensures iter(i; ?next) &*& result == c->value;
  struct node *c = i->current;

  int value = c->value;
  struct node *n = c->next;

  i->current = n;

  return value;
}

void iter_dispose(struct iter *i)

{
  //@ requires iter(i; ?_);
  //@ ensures true;
  free(i);
}

int main2()

{
  //@ requires true;
  //@ ensures true;
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