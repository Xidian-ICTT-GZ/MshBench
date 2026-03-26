typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@
predicate node_ptr(struct node *n) = n != 0 &*&
    malloc_block_node(n);
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate dllist_ptr(struct dllist *l) = l != 0 &*& 
    malloc_block_dllist(l) &*& node_ptr(l->head) &*& node_ptr(l->tail);
@*/

void reverse(dllist arg)
	//@ requires arg != 0 &*& dllist_ptr(arg);
	//@ ensures arg != 0 &*& dllist_ptr(arg);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ open dllist_ptr(arg);
	while (ptr != 0)
		//@ invariant ptr == 0 || node_ptr(ptr);
	{
		//@ open node_ptr(ptr);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node_ptr(ptr);
		ptr = temp1;
	}
	//@ close dllist_ptr(arg);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
}