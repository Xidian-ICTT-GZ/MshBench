typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@
predicate nodes(node n) = n == 0 ? true : 
  n->next |-> ?nx &*& n->prev |-> ?pv &*& n->item |-> _ &*& malloc_block_node(n) &*& nodes(nx);
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate dllist_pred(dllist d) = 
  d->head |-> ?h &*& d->tail |-> ?t &*& malloc_block_dllist(d);
@*/

void reverse(dllist arg)
  //@ requires dllist_pred(arg);
  //@ ensures dllist_pred(arg);
{
	//@ open dllist_pred(arg);
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	while (ptr != 0)
	  /*@ invariant dllist_pred(arg) &*& nodes(ptr); @*/
	{
		//@ open nodes(ptr);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		ptr = temp1;
	}
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dllist_pred(arg);
}