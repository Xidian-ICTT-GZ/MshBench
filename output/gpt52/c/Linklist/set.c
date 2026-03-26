#include "stdlib.h"

/*@

predicate nodes(struct node *n; list<void*> vs) =
  n == 0 ?
    vs == nil
  :
    n->val |-> ?v &*& n->next |-> ?nx &*& malloc_block_node(n) &*& nodes(nx; ?vs0) &*& vs == cons(v, vs0);

predicate setp(struct set *s; list<void*> vs) =
  s->head |-> ?h &*& malloc_block_set(s) &*& nodes(h; vs);

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
//@ ensures result == 0 ? true : setp(result; nil);
struct set *create_set()

{
  struct set *set = malloc(sizeof(struct set));
  if (set == 0)
    return 0;
  set->head = 0;

  return set;
}

//@ requires setp(set; ?vs);
//@ ensures setp(set; cons(x, vs));
void set_add(struct set *set, void *x)

{

  struct node *n = malloc(sizeof(struct node));
  if (n == 0)
    abort();
  n->next = set->head;
  n->val = x;
  set->head = n;
}

//@ requires setp(set; ?vs);
//@ ensures setp(set; vs) &*& (mem(x, vs) == true ? result == true : true);
bool set_contains(struct set *set, void *x)

{

  struct node *curr = set->head;
  bool found = false;

  //@ open setp(set, vs);
  //@ assert nodes(curr; vs);
  //@ list<void*> seen = nil;
  while (curr != 0 && !found)

    //@ invariant nodes(curr; ?rest) &*& nodes(set->head; vs) &*& append(reverse(seen), rest) == vs &*& found == false;
  {

    if (curr->val == x)
    {

      found = true;
    }
    //@ open nodes(curr; rest);
    curr = curr->next;
    //@ close nodes(curr; ?rest2);
    //@ seen = cons(x, seen);
  }
  //@ close setp(set, vs);

  return found;
}

//@ requires setp(set; ?vs);
//@ ensures true;
void set_dispose(struct set *set)

{

  struct node *curr = set->head;
  //@ open setp(set, vs);
  while (curr != 0)

    //@ invariant nodes(curr; ?rest);
  {

    //@ open nodes(curr; rest);
    struct node *nxt = curr->next;
    free(curr);
    curr = nxt;
  }
  //@ open nodes(curr; nil);
  free(set);
}

int main()

//@ requires true;
//@ ensures true;
{
  struct set *set = create_set();
  if (set == 0)
    return 0;
  //@ open setp(set, nil);
  //@ close setp(set, nil);
  set_add(set, (void *)1);
  set_add(set, (void *)2);
  set_add(set, (void *)3);
  bool cnt = set_contains(set, (void *)1);
  assert(cnt);
  set_dispose(set);
  return 0;
}