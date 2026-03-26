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
predicate node_struct(node n; int item, node next, node prev) =
    n != 0 &*& n->item |-> item &*& n->next |-> next &*& n->prev |-> prev;

predicate nodes_(node n) =
    n == 0 ?
        true
    :
        node_struct(n, ?it, ?nx, ?pr) &*& nodes_(nx);

predicate dllist_struct(dllist d; node head, node tail) =
    d != 0 &*& d->head |-> head &*& d->tail |-> tail &*& nodes_(head);
@*/

void reverse(dllist arg)
	//@ requires dllist_struct(arg, ?h, ?t);
	//@ ensures dllist_struct(arg, ?h2, ?t2);
 	
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	
	while (ptr != 0)
		//@ invariant arg->head |-> ?hh &*& arg->tail |-> ?tt &*& nodes_(hh) &*& (ptr == 0 ? true : node_struct(ptr, ?itp, ?nxp, ?prp) &*& nodes_(nxp));
		
	{
		//@ open node_struct(ptr, _, _, _);
		//@ open nodes_(ptr);
		
		
		
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		
		
		
		ptr = temp1;
        
		//@ close node_struct((node)ptr == 0 ? (node)0 : (node)0, 0, 0, 0);
		//@ close nodes_(ptr);
		
		
		
	}
	
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	
	
}