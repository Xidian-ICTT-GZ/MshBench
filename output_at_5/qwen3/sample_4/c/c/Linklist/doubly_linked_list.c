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
predicate list(node n) = n == 0 ? true : n->item ~~> _ &*& n->next |-> ? &*& n->prev |-> ? &*& list(n->next);
predicate dllist_list(dllist d) = d != 0 &*& d->head |-> ? &*& d->tail |-> ? &*& list(d->head) &*& (d->head == 0 || d->tail == d->head->prev);
@*/

//@ requires dllist_list(arg);
//@ ensures dllist_list(arg);
void reverse(dllist arg)
	
 	
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	
	while (ptr != 0)
		
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