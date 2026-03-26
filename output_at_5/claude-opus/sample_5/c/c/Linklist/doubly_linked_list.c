typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@
predicate node_pred(node n) =
  n == 0 ? true :
  n->item |-> _ &*& n->next |-> ?nx &*& n->prev |-> ?pv &*& malloc_block_node(n);
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate dllist_pred(dllist d) =
  d == 0 ? true :
  d->head |-> ?h &*& d->tail |-> ?t &*& malloc_block_dllist(d);
@*/

void reverse(dllist arg)
  //@ requires dllist_pred(arg) &*& (arg->head == 0 || node_pred(arg->head));
  //@ ensures dllist_pred(arg);
{
  //@ open dllist_pred(arg);
  node ptr = arg->head;
  node temp1 = 0;
  node temp2 = 0;

  while (ptr != 0)
    /*@ invariant dllist_pred(arg) &*& ptr != 0 ? node_pred(ptr) : true; @*/
  {
    //@ open node_pred(ptr);
    temp1 = ptr->next;
    temp2 = ptr->prev;
    ptr->next = temp2;
    ptr->prev = temp1;
    //@ close node_pred(ptr);

    ptr = temp1;
  }

  temp1 = arg->head;
  temp2 = arg->tail;
  arg->head = temp2;
  arg->tail = temp1;

  //@ close dllist_pred(arg);
}