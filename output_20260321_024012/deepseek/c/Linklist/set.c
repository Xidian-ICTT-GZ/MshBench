#include "stdlib.h"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};

/*@
predicate node(struct node* n, void* v, struct node* nxt) =
  n->val |-> v &*& n->next |-> nxt &*& malloc_block_node(n);
@*/

/*@
predicate lseg(struct node* from, struct node* to, list<void*> vs) =
  from == to ? vs == nil : node(from, ?v, ?nxt) &*& lseg(nxt, to, ?vs0) &*& vs == cons(v, vs0);
@*/

/*@
predicate set(struct set* s, list<void*> vs) =
  s->head |-> ?h &*& lseg(h, 0, vs) &*& malloc_block_set(s);
@*/

struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result, nil);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close lseg(0, 0, nil);
  //@ close set(set, nil);
  return set;
}

void set_add(struct set* set, void* x)
  //@ requires set(set, ?vs);
  //@ ensures set(set, cons(x, vs));
{
  //@ open set(set, vs);
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  //@ close node(n, x, set->head);
  //@ close lseg(n, 0, cons(x, vs));
  set->head = n;
  //@ close set(set, cons(x, vs));
}

bool set_contains(struct set* set, void* x)
  //@ requires set(set, ?vs);
  //@ ensures set(set, vs) &*& result == mem(x, vs);
{
  //@ open set(set, vs);
  struct node* curr = set->head;
  bool found = false;
  //@ open lseg(curr, 0, vs);
  //@ close lseg(curr, 0, vs);
  //@ struct node* curr0 = curr;
  //@ list<void*> vs0 = vs;
  while(curr != 0 && ! found) 
    //@ invariant lseg(curr, 0, ?vs1) &*& lseg(curr0, curr, ?vs2) &*& vs0 == append(vs2, vs1) &*& found == mem(x, vs2);
  {
    //@ open lseg(curr, 0, vs1);
    //@ open node(curr, ?v, ?nxt);
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
    //@ close lseg(curr, curr, nil);
    //@ close lseg(curr0, curr, append(vs2, cons(v, nil)));
    //@ vs2 = append(vs2, cons(v, nil));
    //@ vs1 = tail(vs1);
    //@ close lseg(curr, 0, vs1);
  }
  //@ open lseg(curr, 0, vs1);
  //@ close lseg(curr, 0, vs1);
  //@ close lseg(curr0, 0, vs0);
  //@ close set(set, vs0);
  return found;
}

void set_dispose(struct set* set)
  //@ requires set(set, _);
  //@ ensures true;
{
  //@ open set(set, _);
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant lseg(curr, 0, _);
  {
    //@ open lseg(curr, 0, _);
    //@ open node(curr, _, _);
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open lseg(0, 0, _);
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
  //@ assert cnt == true;
  assert(cnt);
  set_dispose(set);
  return 0;
}