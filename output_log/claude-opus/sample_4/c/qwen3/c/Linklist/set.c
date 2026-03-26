/*@ predicate nodes(struct node *n, void *x) =
  n == 0 ?
    true
  :
    malloc_block_node(n) &*& n->val |-> ?v &*& n->next |-> ?next &*&
    (v == x || nodes(next, x));
@*/

/*@ predicate set(struct set *s, void *x) =
  malloc_block_set(s) &*& s->head |-> ?h &*& nodes(h, x);
@*/

struct node
{
  void *val;
  struct node *next;
};

struct set
{
  struct node *head;
};

//@ requires true;
//@ ensures result == 0 ? true : malloc_block_set(result) &*& result->head |-> 0;
struct set *create_set()
{
  struct set *set = malloc(sizeof(struct set));
  if (set == 0)
    return 0;
  set->head = 0;

  return set;
}

//@ requires malloc_block_set(set) &*& set->head |-> ?h &*& nodes(h, x);
//@ ensures malloc_block_set(set) &*& set->head |-> ?nh &*& nodes(nh, x);
void set_add(struct set *set, void *x)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
    abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
}

//@ requires malloc_block_set(set) &*& set->head |-> ?h &*& nodes(h, x);
//@ ensures result ? (malloc_block_set(set) &*& set->head |-> ?h2 &*& nodes(h2, x)) : (malloc_block_set(set) &*& set->head |-> ?h2 &*& nodes(h2, x));
bool set_contains(struct set *set, void *x)
{
  struct node *curr = set->head;
  bool found = false;

  //@ invariant malloc_block_set(set) &*& set->head |-> ?h &*& (curr == h || nodes(curr, x)) &*& found == false || found == true;
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

//@ requires malloc_block_set(set) &*& set->head |-> ?h &*& nodes(h, _);
//@ ensures true;
void set_dispose(struct set *set)
{
  struct node *curr = set->head;
  //@ open nodes(curr, _);
  while (curr != 0)
  {
    struct node *nxt = curr->next;
    free(curr);
    curr = nxt;
    //@ open nodes(curr, _);
  }

  free(set);
}

int main()
{
  struct set *set = create_set();
  if (set == 0)
    return 0;
  set_add(set, (void *)1);
  set_add(set, (void *)2);
  set_add(set, (void *)3);
  bool cnt = set_contains(set, (void *)1);
  //@ assert cnt;
  set_dispose(set);
  return 0;
}