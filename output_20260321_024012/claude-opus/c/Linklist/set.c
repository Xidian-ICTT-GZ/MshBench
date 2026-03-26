#include "stdlib.h"

struct node {
  void* val;
  struct node* next;
};
/*@
predicate nodes(struct node* n) =
  n == 0 ? emp : malloc_block_node(n) &*& nodes(n->next);
@*/

struct set {
  struct node* head;
};
/*@
predicate set_pred(struct set* s) =
  s != 0 &*& malloc_block_set(s) &*& nodes(s->head);
@*/

struct set* create_set()
  //@ requires emp;
  //@ ensures set_pred(result) || result == 0;
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0);
  //@ close set_pred(set);
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set_pred(set);
  //@ ensures set_pred(set);
{
  //@ open set_pred(set);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n);
  //@ close set_pred(set);
}

bool set_contains(struct set* set, void* x)
  //@ requires set_pred(set);
  //@ ensures set_pred(set);
{
  //@ open set_pred(set);
  struct node* curr = set->head;
  bool found = false;
  /*@
  predicate loop_inv(struct node* curr, bool found) =
    nodes(curr) &*& set->head == curr &*& found == false;
  @*/
  while(curr != 0 && !found)
    //@ invariant nodes(curr) &*& set->head != 0;
  {
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
  }
  //@ close set_pred(set);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set_pred(set);
  //@ ensures emp;
{
  //@ open set_pred(set);
  struct node* curr = set->head;
  while(curr != 0)
    //@ invariant nodes(curr);
  {
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  free(set);
}

int main()
  //@ requires emp;
  //@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}