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

predicate dllist(dllist l) =
    l->head |-> ?h &*& l->tail |-> ?t;

@*/

void reverse(dllist arg)
	//@ requires arg != 0 &*& dllist(arg);
	//@ ensures dllist(arg);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	while (ptr != 0)
		//@ invariant dllist(arg);
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