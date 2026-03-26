#include "stdlib.h"
#include <stdbool.h>

struct node
{
  void *val;
  struct node *next;
};

struct set
{
  struct node *head;
};

/*@
predicate nodes(struct node *n;) =
  n == 0 ? emp : n->val |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);
@*/

/*@
predicate set_inv(struct set *s;) =
  s->head |-> ?head &*& malloc_block_set(s) &*& nodes(head);
@*/

/*@
lemma void nodes_split(struct node *n)requires nodes(n) &*& n != 0;
  ensures n->val |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);
{
  open nodes(n);
}
@*/

/*@
lemma void nodes_join(struct node *n)
  requires n->val |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);ensures nodes(n);
{
  close nodes(n);
}
@*/

struct set *create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set_inv(result);
{
  struct set *set = malloc(sizeof(struct set));
  if (set == 0)
    return 0;
  set->head = 0;
  //@ close nodes(0);
  //@ close set_inv(set);
  return set;
}

void set_add(struct set *set, void *x)
  //@ requires set_inv(set);
  //@ ensures set_inv(set);
{
  //@ open set_inv(set);
  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
    abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n);
  //@ close set_inv(set);
}

bool set_contains(struct set *set, void *x)
  //@ requires set_inv(set);
  //@ ensures set_inv(set);
{
  //@ open set_inv(set);
  struct node *curr = set->head;
  bool found = false;
  //@ close nodes(curr);
  //@ struct node *orig = curr;
  
  while (curr != 0 && !found)
    //@ invariant nodes(curr);
  {
    //@ open nodes(curr);
    if (curr->val == x)
    {
      found = true;
    }
    struct node *next = curr->next;
    //@ close nodes(curr);
    //@ open nodes(curr);
    curr = curr->next;
  }
  
  //@ close set_inv(set);
  return found;
}

void set_dispose(struct set *set)
  //@ requires set_inv(set);
  //@ ensures true;
{
  //@ open set_inv(set);
  struct node *curr = set->head;
  while (curr != 0)
    //@ invariant nodes(curr);
  {
    //@ open nodes(curr);
    struct node *nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open nodes(0);
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
  //@ assert true;
  set_dispose(set);
  return 0;
}