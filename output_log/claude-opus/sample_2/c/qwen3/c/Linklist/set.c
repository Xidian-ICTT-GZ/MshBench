/*@ 
predicate nodes(struct node *n, void *x) =
  n == 0 ?
    true
  :
    malloc_block_node(n) &*& n->val |-> ?v &*& n->next |-> ?next &*&
    (v == x || nodes(next, x));

predicate set(struct set *s, void *x) =
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
//@ ensures result == 0 ? true : set(result, _);
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
//@ ensures result == true ? set(set, x) : set(set, x);
bool set_contains(struct set *set, void *x)
  //@ invariant set(set, x) &*& curr == set->head || nodes(curr, x);
{
  struct node *curr = set->head;
  bool found = false;

  while (curr != 0 && !found)
    //@ invariant set(set, x) &*& curr != 0 &*& nodes(curr, x);
  {
    if (curr->val == x)
    {
      found = true;
    }
    curr = curr->next;
  }

  return found;
}

//@ requires set(set, _);
//@ ensures true;
void set_dispose(struct set *set)
{
  struct node *curr = set->head;
  while (curr != 0)
    //@ invariant curr != 0 ? malloc_block_node(curr) : true;
  {
    struct node *nxt = curr->next;
    free(curr);
    curr = nxt;
  }

  free(set);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct set *set = create_set();
  if (set == 0)
    return 0;
  set_add(set, (void *)1);
  set_add(set, (void *)2);
  set_add(set, (void *)3);
  bool cnt = set_contains(set, (void *)1);
  //@ assert cnt == true;
  set_dispose(set);
  return 0;
}