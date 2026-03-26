typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@
predicate node_fields(node n; node next, node prev) =
    n != 0 &*& n->next |-> next &*& n->prev |-> prev &*& n->item |-> _;
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate dllist_struct(dllist d; node head, node tail) =
    d != 0 &*& d->head |-> head &*& d->tail |-> tail;
@*/

void reverse(dllist arg)
	//@ requires dllist_struct(arg, ?h, ?t) &*& (h == 0 ? true : node_fields(h, ?hn, ?hp));
	//@ ensures dllist_struct(arg, ?h2, ?t2) &*& (h2 == 0 ? true : node_fields(h2, ?h2n, ?h2p));
 	
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	
	while (ptr != 0)
		//@ invariant dllist_struct(arg, ?hh, ?tt) &*& (ptr == 0 ? true : node_fields(ptr, ?pn, ?pp));
		
	{
		
		
		
		//@ open node_fields(ptr, ?nxt, ?prv);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node_fields(ptr, temp2, temp1);
		
		
		
		ptr = temp1;
        
		
		
		
	}
	
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	
	
}