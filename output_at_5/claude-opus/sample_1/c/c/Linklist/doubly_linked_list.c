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
  d->head |-> ?h &*& d->tail |-> ?t &*& malloc_block_dllist(d) &*& nodes(h);
@*/

void reverse(dllist arg)
  //@ requires dllist_pred(arg);
  //@ ensures dllist_pred(arg);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ open dllist_pred(arg);
	//@ open nodes(ptr);
	while (ptr != 0)
	  //@ invariant nodes(ptr) &*& dllist_pred(arg);
	{
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		ptr = temp1;
		//@ open nodes(temp1);
	}
	//@ close nodes(ptr);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dllist_pred(arg);
}