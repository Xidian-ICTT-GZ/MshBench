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
predicate node_cell(struct node *n; int item, struct node *next, struct node *prev) =
  n->item |-> item &*& n->next |-> next &*& n->prev |-> prev;

predicate dllist_cell(struct dllist *l; struct node *head, struct node *tail) =
  l->head |-> head &*& l->tail |-> tail;

predicate dllist_payload(struct dllist *l) =
  dllist_cell(l, ?h, ?t) &*&
  (h == 0 ? emp : true) &*&
  (t == 0 ? emp : true);
@*/

void reverse(dllist arg)
	//@ requires dllist_cell(arg, ?h, ?t);
	//@ ensures dllist_cell(arg, ?h2, ?t2);
{
	
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	
	
	while (ptr != 0)
		//@ invariant dllist_cell(arg, ?hh, ?tt);
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