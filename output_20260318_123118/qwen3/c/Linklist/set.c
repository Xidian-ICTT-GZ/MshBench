/*@ predicate nodes(struct node* n; list<void*> vs) =
    n == 0 ?
      vs == nil
    :
      malloc_block_node(n) &*&
      nodes(n->next, ?vs1) &*&
      vs == cons(n->val, vs1);
@*/

/*@ predicate set(struct set* s; list<void*> vs) =
    malloc_block_set(s) &*&
    nodes(s->head, vs);
@*/

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};

struct set* create_set()
//@ requires true;
//@ ensures set(result, nil) || result == 0;
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  //@ close nodes(0, nil);
  //@ close set(set, nil);
  return set;
}

void set_add(struct set* set, void* x)
//@ requires set(set, ?vs);
//@ ensures set(set, cons(x, vs));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
  //@ open set(set, vs);
  //@ close nodes(n, cons(x, vs));
  //@ close set(set, cons(x, vs));
}

bool set_contains(struct set* set, void* x)
//@ requires set(set, ?vs);
//@ ensures set(set, vs) &*& result == (mem(x, vs) ? true : false);
{
  //@ open set(set, vs);
  struct node* curr = set->head;
  bool found = false;
  //@ close nodes(0, nil);
  //@ assert nodes(curr, ?curr_vs);
  //@ assert vs == curr_vs;
  
  while(curr != 0 && ! found) 
    //@ invariant nodes(curr, ?w) &*& mem(x, w) == mem(x, vs) &*& !found ==> !mem(x, take(length(vs) - length(w), vs));
  {
    if(curr->val == x) {
      found = true;
    }
    //@ open nodes(curr, w);
    curr = curr->next;
    //@ assert nodes(curr, ?w1);
    //@ w == cons(curr->val, w1);
  }
  //@ close set(set, vs);
  return found;
}

void set_dispose(struct set* set)
//@ requires set(set, ?vs);
//@ ensures true;
{
  //@ open set(set, vs);
  struct node* curr = set->head;
  while(curr != 0) 
    //@ invariant nodes(curr, ?w);
  {
    struct node* nxt = curr->next;
    //@ open nodes(curr, w);
    free(curr);
    curr = nxt;
  }
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
  set_dispose(set);
  return 0;
}