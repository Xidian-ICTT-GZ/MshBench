#include "stdlib.h"
#include "stdbool.h"

struct node
{
  void *val;
  struct node *next;
};

struct set
{
  struct node *head;
};

/*@ predicate nodes(struct node *n) =
  n == 0 ? emp : n->val |-> _ &*& n->next |-> ?next &*& nodes(next);
@*/

/*@ predicate set_pred(struct set *s) =
  s != 0 &*& s->head |-> ?head &*& nodes(head);
@*/

struct set *create_set()
//@ requires true;
//@ ensures result == 0 || result != 0 &*& set_pred(result);
{
  struct set *set = malloc(sizeof(struct set));
  if (set == 0)
    return 0;
  set->head = 0;

  return set;
}

void set_add(struct set *set, void *x)
//@ requires set_pred(set);
//@ ensures set_pred(set);
{

  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
    abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
}

bool set_contains(struct set *set, void *x)
//@ requires set_pred(set);
//@ ensures set_pred(set);
{

  struct node *curr = set->head;
  bool found = false;

  //@ invariant nodes(curr) &*& found == false || nodes(curr) &*& found == true;
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

void set_dispose(struct set *set)
//@ requires set_pred(set);
//@ ensures true;
{

  struct node *curr = set->head;
  //@ invariant nodes(curr);
  while (curr != 0)

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
  assert(cnt);
  set_dispose(set);
  return 0;
}