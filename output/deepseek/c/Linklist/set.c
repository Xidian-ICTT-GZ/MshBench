#include "stdlib.h"
/*@
predicate nodes(struct node *node;) =
    node == 0 ?
        emp
    :
        node->val |-> ?val &*& node->next |-> ?next &*& malloc_block_node(node) &*& nodes(next);
@*/

/*@
predicate set(struct set *set;) =
    set->head |-> ?head &*& malloc_block_set(set) &*& nodes(head);
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

struct set *create_set()
//@ requires true;
//@ ensures result == 0 ? true : set(result);
{
  struct set *set = malloc(sizeof(struct set));
  if (set == 0)
    return 0;
  set->head = 0;
  //@ close nodes(0);
  //@ close set(set);
  return set;
}

void set_add(struct set *set, void *x)
//@ requires set(set);
//@ ensures set(set);
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
    abort();
  //@ open set(set);
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n);
  //@ close set(set);
}

bool set_contains(struct set *set, void *x)
//@ requires set(set);
//@ ensures set(set);
{
  //@ open set(set);
  struct node *curr = set->head;
  bool found = false;
  //@ open nodes(curr);
  while (curr != 0 && !found)
  //@ invariant nodes(curr) &*& found == false ? true : true;
  {
    if (curr->val == x)
    {
      found = true;
    }
    //@ open nodes(curr->next);
    curr = curr->next;
  }
  //@ close set(set);
  return found;
}

void set_dispose(struct set *set)
//@ requires set(set);
//@ ensures true;
{
  //@ open set(set);
  struct node *curr = set->head;
  while (curr != 0)
  //@ invariant nodes(curr);
  {
    //@ open nodes(curr);
    struct node *nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ close nodes(0);
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
  assert(cnt);
  set_dispose(set);
  return 0;
}