/*@ predicate nodes(struct node *n, void *x) =
  n == 0 ?
    true
  :
    malloc_block_node(n) &*& n->val |-> ?v &*& n->next |-> ?next &*&
    (v == x || nodes(next, x));
@*/

/*@ predicate nodes_full(struct node *n) =
  n == 0 ?
    true
  :
    malloc_block_node(n) &*& n->val |-> ?v &*& n->next |-> ?next &*&
    nodes_full(next);
@*/

/*@ predicate set(struct set *s, void *x) =
  malloc_block_set(s) &*& s->head |-> ?h &*& nodes(h, x);
@*/

/*@ predicate set_full(struct set *s) =
  malloc_block_set(s) &*& s->head |-> ?h &*& nodes_full(h);
@*/

//@ requires true;
//@ ensures result == 0 ? true : set_full(result);
struct set *create_set()
{
  struct set *set = malloc(sizeof(struct set));
  if (set == 0)
    return 0;
  set->head = 0;

  return set;
}

//@ requires set(set, x);
//@ ensures set(set, x);
void set_add(struct set *set, void *x)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
    abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
}

//@ requires set(set, x);
//@ ensures set(set, x);
bool set_contains(struct set *set, void *x)
{
  struct node *curr = set->head;
  bool found = false;

  //@ invariant set(set, x) &*& (curr == set->head || nodes(curr, x));
  while (curr != 0 && !found)
  {
    if (curr->val == x)
    {
      found = true;
    }
    curr = curr->next;
  }

  return found;
}

//@ requires set_full(set);
//@ ensures true;
void set_dispose(struct set *set)
{
  struct node *curr = set->head;
  //@ open set_full(set);
  while (curr != 0)
  {
    struct node *nxt;
    //@ open nodes_full(curr);
    nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  free(set);
}