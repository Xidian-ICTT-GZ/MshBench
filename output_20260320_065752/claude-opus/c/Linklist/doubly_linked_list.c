typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@ 
predicate node_pred(struct node *n) = 
	n != 0 &*& 
	n->next |-> ?next &*& 
	n->prev |-> ?prev &*& 
	n->item |-> _; 
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@
predicate dllist_pred(struct dllist *l) = 
	l != 0 &*& l->head |-> ?h &*& l->tail |-> ?t &*&
	(h == 0 ? t == 0 : true);
@*/

void reverse(dllist arg)
	//@ requires dllist_pred(arg);
	//@ ensures dllist_pred(arg);
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	//@ open dllist_pred(arg);
	while (ptr != 0)
		//@ invariant dllist_pred(arg) &*& ptr != 0 ? node_pred(ptr) : true;
	{
		//@ open node_pred(ptr);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node_pred(ptr);
		ptr = temp1;
	}
	//@ close dllist_pred(arg);
	
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
}