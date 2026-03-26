typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@

predicate node_ptr(node n) = n == 0 ? true : malloc_block_node(n);

predicate dllist_ptr(dllist l) = l == 0 ? true : malloc_block_dllist(l);

@*/

void reverse(dllist arg)
	//@ requires dllist_ptr(arg) &*& arg != 0 &*& node_ptr(arg->head) &*& node_ptr(arg->tail);
	//@ ensures dllist_ptr(arg) &*& arg != 0 &*& node_ptr(arg->head) &*& node_ptr(arg->tail);
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	
	while (ptr != 0)
		//@ invariant dllist_ptr(arg) &*& arg != 0 &*& node_ptr(ptr) &*& node_ptr(arg->head) &*& node_ptr(arg->tail);
	{
		
		
		
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
	
	
	
}