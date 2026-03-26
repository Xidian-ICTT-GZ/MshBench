#include "stdlib.h"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

/*@
predicate nodes(struct node* n;) =
  n == 0 ? true : n->val |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);

predicate set(struct set* s;) =
  s->head |-> ?head &*& malloc_block_set(s) &*& nodes(head);
@*/

struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0);
  //@ close set(set);
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set);
{
  //@ open set(set);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ close nodes(n);
  //@ close set(set);
}

/*@
predicate nodes_with_curr(struct node* n, struct node* curr, bool found;) =
  n == curr ? true : n->val |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes_with_curr(next, curr, found);

lemma void nodes_to_nodes_with_curr(struct node* n)
  requires nodes(n);
  ensures nodes_with_curr(n, 0, false);
{
  open nodes(n);
  if (n == 0) {
    close nodes_with_curr(0, 0, false);
  } else {
    nodes_to_nodes_with_curr(n->next);
    close nodes_with_curr(n, 0, false);
  }
}

lemma void nodes_with_curr_to_nodes(struct node* n)
  requires nodes_with_curr(n, 0, ?f);
  ensures nodes(n);
{
  open nodes_with_curr(n, 0, f);
  if (n == 0) {
    close nodes(0);
  } else {
    nodes_with_curr_to_nodes(n->next);
    close nodes(n);
  }
}

lemma void nodes_with_curr_join(struct node* head, struct node* curr)
  requires nodes_with_curr(head, curr, ?f) &*& nodes(curr);
  ensures nodes(head);
{
  open nodes_with_curr(head, curr, f);
  if (head == curr) {
  } else {
    nodes_with_curr_join(head->next, curr);
    close nodes(head);
  }
}

lemma void nodes_split(struct node* head, struct node* curr)
  requires nodes(head) &*& curr != 0;
  ensures nodes_with_curr(head, curr, false) &*& nodes(curr);
{
  open nodes(head);
  if (head == 0) {
    close nodes_with_curr(0, curr, false);
    close nodes(0);
  } else if (head == curr) {
    close nodes_with_curr(curr, curr, false);
    close nodes(head);
  } else {
    nodes_split(head->next, curr);
    close nodes_with_curr(head, curr, false);
  }
}
@*/

bool set_contains(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set);
{
  //@ open set(set);
  struct node* curr = set->head;
  bool found = false;
  //@ struct node* head = curr;
  //@ nodes_to_nodes_with_curr(head);
  //@ close nodes(curr);
  
  while(curr != 0 && ! found) 
    //@ invariant nodes_with_curr(head, curr, found) &*& nodes(curr);
  {
    //@ open nodes(curr);
    if(curr->val == x) {
      found = true;
    }
    //@ struct node* old_curr = curr;
    curr = curr->next;
    //@ close nodes_with_curr(old_curr, curr, found);
    //@ open nodes_with_curr(head, old_curr, _);
    //@ if (head != old_curr) { close nodes_with_curr(head, old_curr, _); }
    
    /*@
    if (head == old_curr) {
      close nodes_with_curr(head, curr, found);
    } else {
      open nodes_with_curr(head, old_curr, _);
      close nodes_with_curr(old_curr, curr, found);
      // Need to rebuild the prefix
    }
    @*/
  }
  //@ nodes_with_curr_join(head, curr);
  //@ close set(set);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set(set);
  //@ ensures true;
{
  //@ open set(set);
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant nodes(curr);
  {
    //@ open nodes(curr);
    struct node* nxt = curr->next;
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
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  //@ assert true;
  set_dispose(set);
  return 0;
}