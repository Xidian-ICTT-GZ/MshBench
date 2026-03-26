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
predicate node_any(node n) =
    n == 0 ?
        true
    :
        n->item |-> ?i &*& n->next |-> ?nx &*& n->prev |-> ?pv;

predicate dllist_any(dllist l) =
    l->head |-> ?h &*& l->tail |-> ?t;
@*/

void reverse(dllist arg)
	//@ requires dllist_any(arg);
	//@ ensures dllist_any(arg);
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ open dllist_any(arg);
	//@ close node_any(ptr);
	while (ptr != 0)
		//@ invariant dllist_any(arg) &*& node_any(ptr);
	{
		
		//@ open node_any(ptr);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node_any(ptr);
		
		ptr = temp1;
		//@ close node_any(ptr);
        
	}
	//@ open node_any(ptr);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	
	//@ close dllist_any(arg);
	
}