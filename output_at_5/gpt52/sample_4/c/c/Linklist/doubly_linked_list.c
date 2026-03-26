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
predicate dllist_struct(dllist d; node head, node tail) =
    d != 0 &*& d->head |-> head &*& d->tail |-> tail;
@*/

void reverse(dllist arg)
	//@ requires dllist_struct(arg, ?h, ?t);
	//@ ensures dllist_struct(arg, ?h2, ?t2);
 	
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	
	while (ptr != 0)
		//@ invariant dllist_struct(arg, ?hh, ?tt);
		
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