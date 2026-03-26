/*@ predicate node(struct node *n; struct node *next, int value) =
  n != 0 &*&
  malloc_block_node(n) &*&
  n->next |-> next &*&
  n->value |-> value;
@*/

/*@ predicate llist(struct llist *l; list<struct node *> nodes) =
  l != 0 &*&
  malloc_block_llist(l) &*&
  l->first |-> ?f &*&
  l->last |-> ?lst &*&
  nodes == cons(f, ?rest) &*&
  length(nodes) >= 1 &*&
  (
    length(nodes) == 1 ?
      f == lst &*& node(f, 0, _)
    :
      node(f, ?n1, _) &*& llist_nodes(rest, f, lst)
  );
@*/

/*@ predicate llist_nodes(list<struct node *> nodes, struct node *first, struct node *last) =
  switch (nodes) {
    case nil: false;
    case cons(h, t):
      h == first &*&
      (
        t == nil ?
          first == last &*& node(first, 0, _)
        :
          node(first, ?next, _) &*& llist_nodes(t, next, last)
      )
  };
@*/

/*@ predicate iter(struct iter *i; struct node *current) =
  i != 0 &*&
  malloc_block_iter(i) &*&
  i->current |-> current;
@*/

//@ lemma void llist_nodes_nonempty(list<struct node *> nodes, struct node *f, struct node *l)
//@   requires llist_nodes(nodes, f, l);
//@   ensures length(nodes) >= 1;
//@ { }

//@ lemma void llist_nodes_split(list<struct node *> nodes, struct node *f, struct node *l)
//@   requires llist_nodes(nodes, f, l) &*& length(nodes) > 1;
//@   ensures node(f, ?n, _) &*& llist_nodes(tail(nodes), n, l);
//@ { }

//@ lemma void llist_unfold(struct llist *l, list<struct node *> nodes)
//@   requires llist(l, nodes);
//@   ensures
//@     l != 0 &*&
//@     malloc_block_llist(l) &*&
//@     l->first |-> ?f &*&
//@     l->last |-> ?lst &*&
//@     nodes == cons(f, ?rest) &*&
//@     length(nodes) >= 1 &*&
//@     (
//@       length(nodes) == 1 ?
//@         f == lst &*& node(f, 0, ?v)
//@       :
//@         node(f, ?n1, ?v) &*& llist_nodes(rest, f, lst)
//@     );
//@ { }

//@ lemma void llist_fold(struct llist *l, list<struct node *> nodes)
//@   requires
//@     l != 0 &*&
//@     malloc_block_llist(l) &*&
//@     l->first |-> ?f &*&
//@     l->last |-> ?lst &*&
//@     nodes == cons(f, ?rest) &*&
//@     length(nodes) >= 1 &*&
//@     (
//@       length(nodes) == 1 ?
//@         f == lst &*& node(f, 0, _)
//@       :
//@         node(f, ?n1, _) &*& llist_nodes(rest, f, lst)
//@     );
//@   ensures llist(l, nodes);
//@ { }

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
//@ ensures llist(result, cons(?n, nil)) &*& node(n, 0, 0);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  return l;
}

void llist_add(struct llist *list, int x)
//@ requires llist(list, ?nodes) &*& length(nodes) >= 1;
//@ ensures llist(list, append(nodes, cons(?n, nil))) &*& node(n, 0, x);
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

void llist_append(struct llist *list1, struct llist *list2)
//@ requires llist(list1, ?nodes1) &*& llist(list2, ?nodes2) &*& length(nodes1) >= 1 &*& length(nodes2) >= 1;
//@ ensures llist(list1, ?result_nodes) &*& length(result_nodes) == length(nodes1) + length(nodes2) - 1;
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

void llist_dispose(struct llist *list)
//@ requires llist(list, ?nodes);
//@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
    //@ invariant llist_nodes(?loop_nodes, n, l) &*& length(loop_nodes) >= 2;
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}

int llist_length(struct llist *list)
//@ requires llist(list, ?nodes);
//@ ensures llist(list, nodes) &*& result == length(nodes) - 1;
{
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;

  while (n != l)
    //@ invariant llist_nodes(?loop_nodes, n, l) &*& c == length(nodes) - length(loop_nodes);
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }

  return c;
}

int llist_lookup(struct llist *list, int index)
//@ requires llist(list, ?nodes) &*& 0 <= index &*& index < length(nodes) - 1;
//@ ensures llist(list, nodes) &*& result == ?val;
{
  struct node *f = list->first;
  struct node *l = list->last;
  struct node *n = f;
  int i = 0;

  while (i < index)
    //@ invariant llist_nodes(?loop_nodes, n, l) &*& i <= index &*& i == length(nodes) - length(loop_nodes);
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }

  int value = n->value;

  return value;
}

int llist_removeFirst(struct llist *l)
//@ requires llist(l, ?nodes) &*& length(nodes) >= 2;
//@ ensures llist(l, tail(nodes)) &*& result == ?val;
{
  struct node *nf = l->first;
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  l->first = nfn;
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
//@ requires llist(l, ?nodes);
//@ ensures iter(result, ?current) &*& llist(l, nodes);
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

int iter_next(struct iter *i)
//@ requires iter(i, ?current) &*& current != 0 &*& node(current, ?next, ?val);
//@ ensures iter(i, next) &*& result == val;
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    return value;
}

void iter_dispose(struct iter *i)
//@ requires iter(i, ?current);
//@ ensures true;
{
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