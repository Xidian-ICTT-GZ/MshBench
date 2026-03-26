/*@ predicate node(struct node *n; struct node *next, int value) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->next |-> next &*&
    n->value |-> value;
@*/

/*@ predicate llist(struct llist *l; struct node *first, struct node *last) =
    l != 0 &*&
    malloc_block_llist(l) &*&
    l->first |-> first &*&
    l->last |-> last;
@*/

/*@ predicate nodes(struct node *first, struct node *last; int count) =
    first == last ?
        node(first, 0, _) &*& count == 0
    :
        node(first, ?next, _) &*& nodes(next, last, count - 1) &*& count > 0;
@*/

/*@ predicate iter(struct iter *i; struct node *current) =
    i != 0 &*&
    malloc_block_iter(i) &*&
    i->current |-> current;
@*/

//@ requires true;
//@ ensures llist(result, ?f, ?l) &*& nodes(f, l, 0);
struct llist *create_llist()
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  return l;
}

//@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?c);
//@ ensures llist(list, f, ?l2) &*& nodes(f, l2, c + 1);
void llist_add(struct llist *list, int x)
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
}

//@ requires llist(list1, ?f1, ?l1) &*& nodes(f1, l1, ?c1) &*&

//@ ensures llist(list1, f1, l2) &*& nodes(f1, l2, c1 + c2);
void llist_append(struct llist *list1, struct llist *list2)
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  
  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
}

//@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?c);
//@ ensures true;
void llist_dispose(struct llist *list)
{
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant nodes(n, l, ?k) &*& k >= 0;
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}

//@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?c);
//@ ensures result == c;
int llist_length(struct llist *list)
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  while (n != l)
  //@ invariant nodes(n, l, ?k) &*& c + k == ?total &*& total == c + k &*& k >= 0;
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  return c;
}

//@ requires llist(list, ?f, ?l) &*& nodes(f, l, ?c) &*& index < c;
//@ ensures true;
int llist_lookup(struct llist *list, int index)
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;
  while (i < index)
  //@ invariant nodes(n, l, ?k) &*& i + k == c &*& i <= index &*& k >= 0;
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  return value;
}

//@ requires llist(l, ?f, ?l) &*& nodes(f, l, ?c) &*& c > 0;
//@ ensures result == ?v &*& llist(l, ?f2, l) &*& nodes(f2, l, c - 1);
int llist_removeFirst(struct llist *l)
{
  struct node *nf = l->first;
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
  return nfv;
}

//@ requires true;
//@ ensures true;
void main0()
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

//@ requires true;
//@ ensures true;
int main() 
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

//@ requires llist(l, ?f, ?l) &*& nodes(f, l, ?c);
//@ ensures iter(result, f);
struct iter *llist_create_iter(struct llist *l)
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    f = l->first;
    i->current = f;
    return i;
}

//@ requires iter(i, ?c) &*& c != 0 &*& node(c, ?next, ?v);
//@ ensures result == v &*& iter(i, next);
int iter_next(struct iter *i)
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    return value;
}

//@ requires iter(i, _);
//@ ensures true;
void iter_dispose(struct iter *i)
{
    free(i);
}

//@ requires true;
//@ ensures true;
int main2()
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